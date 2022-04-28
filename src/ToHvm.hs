module ToHvm where

import Prelude hiding ( null , empty )

import Agda.Compiler.Common
import Agda.Compiler.ToTreeless

import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Internal ( conName, Clause, Telescope )
import Agda.Syntax.Literal
import Agda.Syntax.Treeless

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty

import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.Singleton

import Control.DeepSeq ( NFData )

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State

import Data.Char
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

import GHC.Generics ( Generic )

import Syntax
import Utils (safeTail, safeInit)

data HvmOptions = Options deriving (Generic, NFData)

data ToHvmEnv = ToHvmEnv
  { toHvmOptions :: HvmOptions
  , toHvmVars    :: [HvmAtom]
  }

initToHvmEnv :: HvmOptions -> ToHvmEnv
initToHvmEnv opts = ToHvmEnv opts []

addVarBinding :: HvmAtom -> ToHvmEnv -> ToHvmEnv
addVarBinding x env = env { toHvmVars = x : toHvmVars env }

data ToHvmState = ToHvmState
  { toHvmFresh     :: [HvmAtom]          -- Used for locally bound named variables
  , toHvmDefs      :: Map QName HvmAtom  -- Used for global definitions
  , toHvmUsedNames :: Set HvmAtom        -- Names that are already in use (both variables and definitions)
  }

-- This is an infinite supply of variable names
-- a, b, c, ..., z, a1, b1, ..., z1, a2, b2, ...
-- We never reuse variable names to make the code easier to
-- understand.
freshVars :: [HvmAtom]
freshVars = concat [ map (<> i) xs | i <- "": map show [1..] ]
  where
    xs = map (:"") ['a'..'z']

-- These are names that should not be used by the code we generate
reservedNames :: Set HvmAtom
reservedNames = Set.fromList
  [
  -- TODO: add more
  ]

initToHvmState :: ToHvmState
initToHvmState = ToHvmState
  { toHvmFresh     = freshVars
  , toHvmDefs      = Map.empty
  , toHvmUsedNames = reservedNames
  }

type ToHvmM a = StateT ToHvmState (ReaderT ToHvmEnv TCM) a

freshHvmAtom = do
  names <- gets toHvmFresh
  case names of
    [] -> fail "No more variables!"
    (x:names') -> do
      modify $ \st -> st { toHvmFresh = names' }
      ifM (isNameUsed x) freshHvmAtom $ {-otherwise-} do
        setNameUsed x
        return x

getEvaluationStrategy :: ToHvmM EvaluationStrategy
getEvaluationStrategy = return LazyEvaluation

getVarName :: Int -> ToHvmM HvmAtom
getVarName i = reader $ (!! i) . toHvmVars

withFreshVar :: (HvmAtom -> ToHvmM a) -> ToHvmM a
withFreshVar f = do
  x <- freshHvmAtom
  local (addVarBinding x) $ f x

withFreshVars :: Int -> ([HvmAtom] -> ToHvmM a) -> ToHvmM a
withFreshVars i f
  | i <= 0    = f []
  | otherwise = withFreshVar $ \x -> withFreshVars (i-1) (f . (x:))

saveDefName :: QName -> HvmAtom -> ToHvmM ()
saveDefName n a = modify $ \s -> s { toHvmDefs = Map.insert n a (toHvmDefs s) }

isNameUsed :: HvmAtom -> ToHvmM Bool
isNameUsed x = Set.member x <$> gets toHvmUsedNames

setNameUsed :: HvmAtom -> ToHvmM ()
setNameUsed x = modify $ \s ->
  s { toHvmUsedNames = Set.insert x (toHvmUsedNames s) }

-- Extended alphabetic characters that are allowed to appear in
-- a Hvm identifier
hvmExtendedAlphaChars :: Set Char
hvmExtendedAlphaChars = Set.fromList
  [ '!' , '$' , '%' , '&' , '*' , '+' , '-' , '.' , '/' , ':' , '<' , '=' , '>'
  , '?' , '@' , '^' , '_' , '~'
  ]

-- Categories of unicode characters that are allowed to appear in
-- a Hvm identifier
hvmAllowedUnicodeCats :: Set GeneralCategory
hvmAllowedUnicodeCats = Set.fromList
  [ UppercaseLetter , LowercaseLetter , TitlecaseLetter , ModifierLetter
  , OtherLetter , NonSpacingMark , SpacingCombiningMark , EnclosingMark
  , DecimalNumber , LetterNumber , OtherNumber , ConnectorPunctuation
  , DashPunctuation , OtherPunctuation , CurrencySymbol , MathSymbol
  , ModifierSymbol , OtherSymbol , PrivateUse
  ]

-- True if the character is allowed to be used in a Hvm identifier
isValidHvmChar :: Char -> Bool
isValidHvmChar x
  | isAscii x = isAlphaNum x || x `Set.member` hvmExtendedAlphaChars
  | otherwise = generalCategory x `Set.member` hvmAllowedUnicodeCats

-- Creates a valid Hvm name from a (qualified) Agda name.
-- Precondition: the given name is not already in toHvmDefs.
makeHvmName :: QName -> ToHvmM HvmAtom
makeHvmName n = do
  a <- go $ fixName $ prettyShow $ qnameName n
  saveDefName n a
  setNameUsed a
  return a
  where
    nextName = ('z':) -- TODO: do something smarter

    go s     = ifM (isNameUsed s) (go $ nextName s) (return s)

    fixName s = do
      let s'  = concat (map fixChar s)
      let (x:xs) = if isNumber (head s') then "z" ++ s' else s'
      (toUpper x):xs

    fixChar c
      | isValidHvmChar c = [c]
      | otherwise           = "\\x" ++ toHex (ord c) ++ ";"

    toHex 0 = ""
    toHex i = toHex (i `div` 16) ++ [fourBitsToChar (i `mod` 16)]

fourBitsToChar :: Int -> Char
fourBitsToChar i = "0123456789ABCDEF" !! i
{-# INLINE fourBitsToChar #-}

class ToHvm a b where
    toHvm :: a -> ToHvmM b

instance ToHvm QName HvmAtom where
    toHvm n = do
        r <- Map.lookup n <$> gets toHvmDefs
        case r of
            Nothing -> makeHvmName n
            Just a  -> return a

paramsNumber :: Num a => TTerm -> a
paramsNumber (TLam v) = 1 + paramsNumber v
paramsNumber _ = 0

traverseLams :: TTerm -> TTerm
traverseLams (TLam v) = traverseLams v
traverseLams t = t

makeLamFromParams :: [HvmAtom] -> HvmTerm -> HvmTerm
makeLamFromParams xs body = foldr Lam body xs

curryRuleName :: String -> Int -> String
curryRuleName f i = f ++ "_" ++ show i

{-
  (Id_0) = @a @b @c (Id_3 a b c)
  (Id_1 a) = @b @c (Id_3 a b c)
  (Id_2 a b) =  @c (Id_3 a b c)
  (Id_3 a b c)= c
-}
curryRule :: [HvmAtom] -> HvmAtom -> [HvmAtom] -> HvmTerm
curryRule cparams f lparams = Rule (Ctr (curryRuleName f cparamsLen) $ map Var cparams) (makeLamFromParams lparams (App (Var $ curryRuleName f paramsLen) (map Var cparams ++ map Var lparams)))
  where 
    cparamsLen = length cparams
    lparamsLen = length lparams
    paramsLen = cparamsLen + lparamsLen

instance ToHvm Definition [HvmTerm] where
    toHvm def
        | defNoCompilation def ||
          not (usableModality $ getModality def) = return []
    toHvm def = do
        let f = defName def
        case theDef def of
            Axiom {}         -> return []
            GeneralizableVar -> return []
            d@Function{} | d ^. funInline -> return []
            Function {}      -> do
                f' <- toHvm f
                strat <- getEvaluationStrategy
                maybeCompiled <- liftTCM $ toTreeless strat f
                case maybeCompiled of
                    Just l@(TLam _) -> do
                        let nparams = paramsNumber l
                        let body = traverseLams l
                        withFreshVars nparams $ \params -> do
                            body' <- toHvm body
                            let firstDefName = curryRuleName f' nparams
                            let d = Rule (Ctr firstDefName (map Var params)) body'
                            let ds = zipWith3 (\cparams lparams i -> curryRule cparams f' lparams) (inits params) (tails params) [0..(max 0 $ length params - 1)]
                            return $ ds ++ [d]
                    Just t -> do
                        body <- toHvm t
                        return [Rule (Ctr (curryRuleName f' 0) []) body]
                    Nothing   -> error $ "Could not compile Function " ++ f' ++ ": treeless transformation returned Nothing"
            Primitive {}     -> return []
            PrimitiveSort {} -> return []
            Datatype {}      -> return []
            Record {}        -> undefined
            Constructor { conSrcCon=chead, conArity=nargs } -> return []
            AbstractDefn {}  -> __IMPOSSIBLE__
            DataOrRecSig {}  -> __IMPOSSIBLE__

instance ToHvm TTerm HvmTerm where
    toHvm v = case v of
        TVar i  -> do
            name <- getVarName i
            start <- getEvaluationStrategy
            return $ Parenthesis $ Var name
        TPrim p -> undefined
        TDef d  -> do
            d' <- toHvm d
            -- Always evaluate Def first with 0 arguments (see Notes Thu 28 Apr)
            return $ App (Var $ curryRuleName d' 0) []
        TApp f args -> do
            f'    <- toHvm f
            args' <- traverse toHvm args
            case f' of
              Var ruleName -> return $ App (Var $ curryRuleName ruleName $ length args') args'
              _ -> return $ App f' args'
        TLam v  -> withFreshVar $ \x -> do
            body <- toHvm v
            return $ Lam x body
        TCon c -> do
            c' <- toHvm c
            return $ Parenthesis $ Var c'
        TLet u v -> undefined
        TCase i info v bs -> undefined
        TUnit -> undefined
        TSort -> undefined
        TErased    -> undefined
        TCoerce u  -> undefined
        TError err -> undefined
        TLit l     -> undefined
