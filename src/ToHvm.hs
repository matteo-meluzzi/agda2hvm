{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use lambda-case" #-}
{-# LANGUAGE FlexibleContexts #-}
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
import Utils (safeTail, safeInit, safeHead)

data HvmOptions = Options deriving (Generic, NFData)

data ToHvmEnv = ToHvmEnv
  { toHvmOptions :: HvmOptions
  , toHvmVars    :: [HvmAtom]
  , currentDef   :: HvmAtom
  }

initToHvmEnv :: HvmOptions -> ToHvmEnv
initToHvmEnv opts = ToHvmEnv opts [] ""

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

freshHvmAtom :: ToHvmM HvmAtom
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

getBindinds :: ToHvmM [HvmAtom]
getBindinds = reader toHvmVars

getVarName :: Int -> ToHvmM HvmAtom
getVarName i = reader $ (\vars -> if i < length vars then vars !! i else error $ "cannot get index " ++ show i ++ " in " ++ show vars) . toHvmVars

getCurrentDef :: ToHvmM HvmAtom
getCurrentDef = reader currentDef

withCurrentDef :: HvmAtom -> ToHvmM a -> ToHvmM a
withCurrentDef a = local (\env -> env { currentDef = a })

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
  [ '$' , '.', '_'
  ]

-- Categories of unicode characters that are allowed to appear in
-- a Hvm identifier
hvmAllowedUnicodeCats :: Set GeneralCategory
hvmAllowedUnicodeCats = Set.fromList
  [ UppercaseLetter , LowercaseLetter , DecimalNumber , DashPunctuation
  ]

-- True if the character is allowed to be used in a Hvm identifier
isValidHvmChar :: Char -> Bool
isValidHvmChar x
  | isAscii x = isAlphaNum x || x `Set.member` hvmExtendedAlphaChars
  | otherwise = generalCategory x `Set.member` hvmAllowedUnicodeCats

fixHvmName :: QName -> [Char]
fixHvmName n = fixName $ prettyShow $ qnameName n
  where 
    fixName "_-_" = "Monus"
    fixName s = do
      let s'  = concatMap fixChar s
      let (x:xs) = if (not . isLetter) (head s') then "z" ++ s' else s'
      toUpper x:xs
    fixChar c
      | isValidHvmChar c = [c]
      | otherwise           = "x" ++ toHex (ord c)

    toHex 0 = ""
    toHex i = toHex (i `div` 16) ++ [fourBitsToChar (i `mod` 16)]


-- Creates a valid Hvm name from a (qualified) Agda name.
-- Precondition: the given name is not already in toHvmDefs.
makeHvmName :: QName -> ToHvmM HvmAtom
makeHvmName n = do
  a <- go $ fixHvmName n
  saveDefName n a
  setNameUsed a
  return a
  where
    nextName = ('z':) -- TODO: do something smarter

    go s     = ifM (isNameUsed s) (go $ nextName s) (return s)

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

{-
  (Id_0) = @a @b @c (Id_3 a b c)
  (Id_3 a b c)= c
-}
curryRule :: [HvmAtom] -> HvmAtom -> [HvmAtom] -> HvmTerm
curryRule cparams f lparams = Rule (Ctr (Def f) $ map Var cparams) (makeLamFromParams lparams (App (Def f) (map Var cparams ++ map Var lparams)))
  where
    cparamsLen = length cparams
    lparamsLen = length lparams
    paramsLen = cparamsLen + lparamsLen
    
makeRule :: String -> [HvmAtom] -> HvmTerm -> ToHvmM [HvmTerm]
makeRule name params body = do
  let dn = Rule (Ctr (Def name) (map Var params)) body
  case params of
    [] -> do
      return [dn]
    params -> do
      let ds = zipWith3 (\cparams lparams i -> curryRule cparams name lparams) (inits params) (tails params) [0..(max 0 $ length params - 1)]
      return $ ds ++ [dn]
  where
    nparams = length params

instance ToHvm Definition [HvmTerm] where
    toHvm def
        | defNoCompilation def ||
          not (usableModality $ getModality def) = return []
    toHvm def = do
        let f = defName def
        f' <- toHvm f
        withCurrentDef f' $ do
          case theDef def of
              Axiom {}         -> return []
              GeneralizableVar -> return []
              d@Function{} | d ^. funInline -> return []
              Function {}      -> do
                  strat <- getEvaluationStrategy
                  maybeCompiled <- liftTCM $ toTreeless strat f
                  case maybeCompiled of
                      Just l@(TLam _) -> do
                          let nparams = paramsNumber l
                          withFreshVars nparams $ \params -> do
                            body <- toHvm $ traverseLams l
                            makeRule f' params body
                      Just t -> do
                          body <- toHvm t
                          return [Rule (Ctr (Def f') []) body]
                      Nothing   -> return []
              Primitive {}     -> return []
              PrimitiveSort {} -> return []
              Datatype {}      -> return []
              Record {}        -> return []
              Constructor { conSrcCon=chead, conArity=nparams } -> do
                let c = conName chead
                c' <- toHvm c
                withFreshVars nparams $ \params -> do
                  let ctr = Ctr (Var c') (map Var params)
                  makeRule c' params ctr

              AbstractDefn {}  -> __IMPOSSIBLE__
              DataOrRecSig {}  -> __IMPOSSIBLE__

instance ToHvm TTerm HvmTerm where
    toHvm v = case v of
        TVar i  -> do
          name <- getVarName i
          start <- getEvaluationStrategy
          return $ Parenthesis $ Var name
        TPrim p -> toHvm (p , [] :: [TTerm])
        TDef d  -> do
          d' <- toHvm d
          -- Always evaluate Def first with 0 arguments (see Notes Thu 28 Apr)
          return $ App (Def d') []
        TApp (TPrim p) args -> toHvm (p, args)
        TApp f args -> do
          f'    <- toHvm f
          args' <- traverse toHvm args
          case f' of
            Def ruleName -> return $ App (Def ruleName) args'
            _ -> return $ App f' args'
        TLam v  -> withFreshVar $ \x -> do
          body <- toHvm v
          return $ Lam x body
        TLit l -> toHvm l
        TCon c -> do
          c' <- toHvm c
          return $ App (Def c') []
        TLet u v -> do
          expr <- toHvm u
          def <- getCurrentDef
          bindings <- getBindinds
          let rbindings = reverse bindings
          withFreshVar $ \x -> do
            body <- toHvm v
            let ruleLet = Rule (Ctr (Def $ def ++ "_" ++ x) (map Var rbindings)) expr
            return $ Rules (Let x (App (Def $ def ++ "_" ++ x) (map Var rbindings)) body) [ruleLet]
        c@(TCase i info v bs) -> do
          defName <- getCurrentDef
          bindings' <- getBindinds
          let bindings = reverse bindings'
          x <- getVarName i
          cases <- traverse toHvm bs
          let ruleName = defName ++ "_split_" ++ x
          fallback <- if isUnreachable v
            then return Nothing
            else do
              v' <- toHvm v
              return $ Just $  Rule (Ctr (Def ruleName) (map Var bindings)) v'
          rules <- traverse (\(ctr, body) -> do
            let params = zipWith (\b ix -> if i == ix then ctr else Var b) bindings [(length bindings - 1), (length bindings - 2)..]
            return $ Rule (Ctr (Def ruleName) params) (Let x ctr body)
            ) cases
          case fallback of
            Nothing -> return $ Rules (App (Def ruleName) (map Var bindings)) rules
            Just fb -> return $ Rules (App (Def ruleName) (map Var bindings)) (rules ++ [fb])
        TUnit -> undefined
        TSort -> undefined
        TErased    -> return $ Var "Matteo"
        TCoerce u  -> undefined
        TError err -> return $ Var "error\n"  

instance ToHvm (TPrim, [TTerm]) HvmTerm where
  toHvm (p, args) = do
    args' <- traverse toHvm args
    unless (length args' >= 2) $ fail $ "primitive operation " <> show p <> " called with " <> show (length args) <> " arguments!"
    let o1 = head args'
    let o2 = head $ tail args'
    case p of
      PAdd -> return $ Op2 Add o1 o2
      PSub -> return $ Op2 Sub o1 o2
      PMul -> return $ Op2 Mul o1 o2
      PQuot -> return $ Op2 Div o1 o2
      PRem -> return $ Op2 Mod o1 o2
      PEqI -> return $ Op2 Eq o1 o2
      PLt -> return $ Op2 Lt o1 o2
      PGeq -> return $ Op2 GtEq o1 o2

      PAdd64 -> undefined
      PSub64 -> undefined
      PMul64 -> undefined
      PQuot64 -> undefined
      PRem64 -> undefined
      PLt64 -> undefined
      PEq64 -> undefined
      PEqF -> undefined
      PEqS -> undefined
      PEqC -> undefined
      PEqQ -> undefined
      PIf -> undefined
      PSeq -> return $ Var $ "PSeq " ++ show args'
      PITo64 -> undefined
      P64ToI -> undefined

instance ToHvm Literal HvmTerm where
  toHvm lit = case lit of
    LitNat x -> return $ Num x
    LitWord64 x -> undefined
    LitFloat  x -> undefined
    LitString x -> return $ Str $ T.unpack x
    LitChar   x -> undefined
    LitQName  x -> undefined
    LitMeta p x -> undefined


instance ToHvm TAlt (HvmTerm, HvmTerm) where
  toHvm alt = case alt of
    TACon c nargs v -> withFreshVars nargs $ \xs -> do
      body <- toHvm v
      let name = fixHvmName c
      let ctr = Ctr (Var name) (map Var xs)
      return (ctr, body)
    -- ^ Matches on the given constructor. If the match succeeds,
    -- the pattern variables are prepended to the current environment
    -- (pushes all existing variables aArity steps further away)
    TAGuard{} -> __IMPOSSIBLE__ -- TODO
    TALit lit body -> do
      lit' <- toHvm lit
      body' <- toHvm body
      return (lit', body') -- TODO