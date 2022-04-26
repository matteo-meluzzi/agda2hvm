module Main where

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Compiler.ToTreeless

import Agda.Main (runAgda)

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
import GHC.Generics ( Generic )

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Maybe
import Data.List

import Data.Char
import Data.Function
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import GHC.Generics ( Generic )

import Lib

data HvmOptions = Options deriving (Generic, NFData)

backend' :: Backend' HvmOptions HvmOptions () () (Maybe HvmTerm)
backend' = Backend'
    {
        backendName             = "agda2HVM"
        , backendVersion        = Nothing
        , options               = Options
        , commandLineFlags      = []
        , isEnabled             = const True
        , preCompile            = return
        , postCompile           = \ _ _ _ -> return ()
        , preModule             = \ _ _ _ _ -> return $ Recompile ()
        , postModule            = hvmPostModule
        , compileDef            = hvmCompile
        , scopeCheckingSuffices = False
        , mayEraseType          = \ _ -> return True
    }

backend :: Backend
backend = Backend backend'

type HvmAtom = String
type HvmOp2 = Char
type HvmNum = Int
data HvmTerm =  Lam HvmAtom HvmTerm |
                App HvmTerm [HvmTerm] |
                Ctr HvmAtom [HvmTerm] |
                Op2 HvmOp2 HvmTerm HvmTerm |
                Let HvmAtom HvmTerm HvmTerm |
                Var HvmAtom |
                Num HvmNum |
                Parenthesis HvmTerm |
                Rule HvmTerm HvmTerm

showSExpr :: Maybe String -> [HvmTerm] -> String
showSExpr (Just head) [] = "(" ++ head ++  ")"
showSExpr (Just head) terms = "(" ++ head ++ " " ++ intercalate " " (map show terms) ++ ")"
showSExpr Nothing terms = "(" ++ intercalate " " (map show terms) ++ ")"

instance Show HvmTerm where
    show (Lam v t) = showSExpr (Just $ "@" ++ v ++ " " ++ show t) []
    show (App t1 t2) = showSExpr Nothing (t1:t2)
    show (Ctr n xs) = showSExpr (Just n) xs
    show (Op2 op t1 t2) = showSExpr (Just (op:"")) [t1, t2]
    show (Let n t1 t2) = "let " ++ n ++ " = " ++ show t1 ++ "; " ++ show t2
    show (Var n) = n
    show (Num i) = show i
    show (Parenthesis t) = showSExpr Nothing [t]
    show (Rule t1 t2) = show t1 ++ " = " ++ show t2

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

    fixName s =
      let s' = concat (map fixChar s) in
      if isNumber (head s') then "z" ++ s' else s'

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

instance ToHvm Definition (Maybe HvmTerm) where
    toHvm def
        | defNoCompilation def ||
          not (usableModality $ getModality def) = return Nothing
    toHvm def = do
        let f = defName def
        case theDef def of
            Axiom {}         -> return Nothing
            GeneralizableVar -> return Nothing
            d@Function{} | d ^. funInline -> return Nothing
            Function {}      -> do
                let f' = "pippo"
                maybeCompiled <- liftTCM $ toTreeless LazyEvaluation f
                case maybeCompiled of
                    Just t -> do
                        body <- toHvm t
                        return $ Just $ Rule (Ctr f' []) body
                    Nothing   -> error $ "Could not compile Function " ++ f' ++ ": treeless transformation returned Nothing"
            Primitive {}     -> return Nothing
            PrimitiveSort {} -> return Nothing
            Datatype {}      -> return Nothing
            Record {}        -> undefined
            Constructor { conSrcCon=chead, conArity=nargs } -> return Nothing
            AbstractDefn {}  -> __IMPOSSIBLE__
            DataOrRecSig {}  -> __IMPOSSIBLE__

instance ToHvm TTerm HvmTerm where
    toHvm v = case v of
        TVar i  -> return $ Parenthesis $ Var $ "param" ++ show i
        TPrim p -> undefined
        TDef d  -> return $ Parenthesis $ Var $ "pippo2"
        TApp f args -> do
            f'    <- toHvm f
            args' <- sequence $ map toHvm args
            return $ App f' args'
        TLam v  -> do
            v' <- toHvm v
            return $ Lam "param0" v'
        TCon c   -> return $ Parenthesis $ Var $ "pippo3"
        TLet u v -> undefined
        TCase i info v bs -> undefined
        TUnit -> undefined
        TSort -> undefined
        TErased    -> undefined
        TCoerce u  -> undefined
        TError err -> undefined
        TLit l     -> undefined


hvmCompile :: HvmOptions -> () -> IsMain -> Definition -> TCM (Maybe HvmTerm)
hvmCompile opts _ isMain def = 
    toHvm def 
    & (`evalStateT` initToHvmState)  
    & (`runReaderT` initToHvmEnv opts)

hvmPostModule :: HvmOptions -> () -> IsMain -> ModuleName -> [Maybe HvmTerm] -> TCM ()
hvmPostModule options _ isMain moduleName sexprs = do
    liftIO $ T.writeFile "out.hvm" (T.pack $ intercalate "\n\n" (map show $ catMaybes sexprs))

main :: IO ()
main = runAgda [backend]