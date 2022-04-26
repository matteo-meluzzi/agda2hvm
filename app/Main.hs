module Main where

import Agda.Compiler.Backend

import Agda.Utils.Impossible
import Agda.Utils.Lens
import Agda.Utils.Pretty

import Control.DeepSeq ( NFData )
import GHC.Generics ( Generic )

import qualified Data.Text as T
import qualified Data.Text.IO as T

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Maybe
import Data.List

import Lib
import Agda.Main (runAgda)

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

type HvmCtr = String
type HvmVar = String
type HvmOp2 = String
type HvmNum = Int
data HvmTerm =  Lam HvmVar HvmTerm |
                App HvmTerm [HvmTerm] |
                Ctr HvmCtr [HvmTerm] |
                Op2 HvmOp2 HvmTerm HvmTerm |
                Let HvmVar HvmTerm HvmTerm |
                Var HvmVar |
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
    show (Op2 op t1 t2) = showSExpr (Just op) [t1, t2]
    show (Let n t1 t2) = "let " ++ n ++ " = " ++ show t1 ++ "; " ++ show t2
    show (Var n) = n
    show (Num i) = show i
    show (Parenthesis t) = showSExpr Nothing [t]
    show (Rule t1 t2) = show t1 ++ " = " ++ show t2

hvmName :: QName -> String
hvmName = prettyShow . qnameName

-- Args = [TTerm]

toHvm :: TTerm -> HvmTerm
toHvm v = case v of
    TVar i  -> Parenthesis $ Var $ "param" ++ show i
    TPrim p -> undefined
    TDef d  -> Parenthesis $ Var $ hvmName d
    TApp f args -> App (toHvm f) (map toHvm args)
    TLam v   -> Lam "param0" $ toHvm v
    TCon c   -> Parenthesis $ Var $ hvmName c
    TLet u v -> undefined
    TCase i info v bs -> undefined
    TUnit -> undefined
    TSort -> undefined
    TErased    -> undefined
    TCoerce u  -> undefined
    TError err -> undefined
    TLit l     -> undefined

paramsNumber :: Num a => TTerm -> a
paramsNumber (TLam v) = 1 + paramsNumber v
paramsNumber _ = 0

traverseLams :: TTerm -> TTerm
traverseLams (TLam v) = traverseLams v
traverseLams t = t

hvmCompile :: HvmOptions -> () -> IsMain -> Definition -> TCM (Maybe HvmTerm)
-- hvmCompile opts _ isMain def = return Nothing
hvmCompile opts _ isMain def = do
    let f = defName def
    case theDef def of
        Axiom {}         -> return Nothing
        GeneralizableVar -> return Nothing
        d@Function{} | d ^. funInline -> return Nothing
        Function {}      -> do
            let f' = hvmName f
            maybeCompiled <- liftTCM $ toTreeless LazyEvaluation f
            case maybeCompiled of
                -- Just (TLam l) -> do
                --     let nparams = paramsNumber l
                --     let params = map (\i -> Var $ "param" ++ show i) [nparams, nparams-1 .. 0]
                --     let body = traverseLams l
                --     return $ Just $ Rule (Ctr f' params) (toHvm body)
                Just t -> return $ Just $ Rule (Ctr f' []) (toHvm t)
                Nothing   -> error $ "Could not compile Function " ++ f' ++ ": treeless transformation returned Nothing"
        Primitive {}     -> return Nothing
        PrimitiveSort {} -> return Nothing
        Datatype {}      -> return Nothing
        Record {}        -> undefined
        Constructor { conSrcCon=chead, conArity=nargs } -> return Nothing
        AbstractDefn {}  -> __IMPOSSIBLE__
        DataOrRecSig {}  -> __IMPOSSIBLE__

hvmPostModule :: HvmOptions -> () -> IsMain -> ModuleName -> [Maybe HvmTerm] -> TCM ()
hvmPostModule options _ isMain moduleName sexprs = do
    liftIO $ T.writeFile "out.hvm" (T.pack $ intercalate "\n\n" (map show $ catMaybes sexprs))

main :: IO ()
main = runAgda [backend]

-- -- | The type checking monad transformer.
-- -- Adds readonly 'TCEnv' and mutable 'TCState'.
-- newtype TCMT m a = TCM { unTCM :: IORef TCState -> TCEnv -> m a }

-- -- | Type checking monad.
-- type TCM = TCMT IO

-- data Defn = Axiom -- ^ Postulate
--             { axiomConstTransp :: Bool
--               -- ^ Can transp for this postulate be constant?
--               --   Set to @True@ for bultins like String.
--             }
--           | DataOrRecSig
--             { datarecPars :: Int }
--             -- ^ Data or record type signature that doesn't yet have a definition
--           | GeneralizableVar -- ^ Generalizable variable (introduced in `generalize` block)
--           | AbstractDefn Defn
--             -- ^ Returned by 'getConstInfo' if definition is abstract.
--           | Function
--             { funClauses        :: [Clause]
--             , funCompiled       :: Maybe CompiledClauses
--               -- ^ 'Nothing' while function is still type-checked.
--               --   @Just cc@ after type and coverage checking and
--               --   translation to case trees.
--             , funSplitTree      :: Maybe SplitTree
--               -- ^ The split tree constructed by the coverage
--               --   checker. Needed to re-compile the clauses after
--               --   forcing translation.
--             , funTreeless       :: Maybe Compiled
--               -- ^ Intermediate representation for compiler backends.
--             , funCovering       :: [Clause]
--               -- ^ Covering clauses computed by coverage checking.
--               --   Erased by (IApply) confluence checking(?)
--             , funInv            :: FunctionInverse
--             , funMutual         :: Maybe [QName]
--               -- ^ Mutually recursive functions, @data@s and @record@s.
--               --   Does include this function.
--               --   Empty list if not recursive.
--               --   @Nothing@ if not yet computed (by positivity checker).
--             , funAbstr          :: IsAbstract
--             , funDelayed        :: Delayed
--               -- ^ Are the clauses of this definition delayed?
--             , funProjection     :: Maybe Projection
--               -- ^ Is it a record projection?
--               --   If yes, then return the name of the record type and index of
--               --   the record argument.  Start counting with 1, because 0 means that
--               --   it is already applied to the record. (Can happen in module
--               --   instantiation.) This information is used in the termination
--               --   checker.
--             , funFlags          :: Set FunctionFlag
--             , funTerminates     :: Maybe Bool
--               -- ^ Has this function been termination checked?  Did it pass?
--             , funExtLam         :: Maybe ExtLamInfo
--               -- ^ Is this function generated from an extended lambda?
--               --   If yes, then return the number of hidden and non-hidden lambda-lifted arguments
--             , funWith           :: Maybe QName
--               -- ^ Is this a generated with-function? If yes, then what's the
--               --   name of the parent function.
--             }
--           | Datatype
--             { dataPars           :: Nat            -- ^ Number of parameters.
--             , dataIxs            :: Nat            -- ^ Number of indices.
--             , dataClause         :: (Maybe Clause) -- ^ This might be in an instantiated module.
--             , dataCons           :: [QName]
--               -- ^ Constructor names , ordered according to the order of their definition.
--             , dataSort           :: Sort
--             , dataMutual         :: Maybe [QName]
--               -- ^ Mutually recursive functions, @data@s and @record@s.
--               --   Does include this data type.
--               --   Empty if not recursive.
--               --   @Nothing@ if not yet computed (by positivity checker).
--             , dataAbstr          :: IsAbstract
--             , dataPathCons       :: [QName]        -- ^ Path constructor names (subset of dataCons)
--             , dataTranspIx       :: Maybe QName    -- ^ if indexed datatype, name of the "index transport" function.
--             , dataTransp         :: Maybe QName
--               -- ^ transport function, should be available for all datatypes in supported sorts.
--             }
--           | Record
--             { recPars           :: Nat
--               -- ^ Number of parameters.
--             , recClause         :: Maybe Clause
--               -- ^ Was this record type created by a module application?
--               --   If yes, the clause is its definition (linking back to the original record type).
--             , recConHead        :: ConHead
--               -- ^ Constructor name and fields.
--             , recNamedCon       :: Bool
--               -- ^ Does this record have a @constructor@?
--             , recFields         :: [Dom QName]
--               -- ^ The record field names.
--             , recTel            :: Telescope
--               -- ^ The record field telescope. (Includes record parameters.)
--               --   Note: @TelV recTel _ == telView' recConType@.
--               --   Thus, @recTel@ is redundant.
--             , recMutual         :: Maybe [QName]
--               -- ^ Mutually recursive functions, @data@s and @record@s.
--               --   Does include this record.
--               --   Empty if not recursive.
--               --   @Nothing@ if not yet computed (by positivity checker).
--             , recEtaEquality'    :: EtaEquality
--               -- ^ Eta-expand at this record type?
--               --   @False@ for unguarded recursive records and coinductive records
--               --   unless the user specifies otherwise.
--             , recPatternMatching :: PatternOrCopattern
--               -- ^ In case eta-equality is off, do we allow pattern matching on the
--               --   constructor or construction by copattern matching?
--               --   Having both loses subject reduction, see issue #4560.
--               --   After positivity checking, this field is obsolete, part of 'EtaEquality'.
--             , recInduction      :: Maybe Induction
--               -- ^ 'Inductive' or 'CoInductive'?  Matters only for recursive records.
--               --   'Nothing' means that the user did not specify it, which is an error
--               --   for recursive records.
--             , recTerminates     :: Maybe Bool
--               -- ^ 'Just True' means that unfolding of the recursive record terminates,
--               --   'Just False' means that we have no evidence for termination,
--               --   and 'Nothing' means we have not run the termination checker yet.
--             , recAbstr          :: IsAbstract
--             , recComp           :: CompKit
--             }
--           | Constructor
--             { conPars   :: Int         -- ^ Number of parameters.
--             , conArity  :: Int         -- ^ Number of arguments (excluding parameters).
--             , conSrcCon :: ConHead     -- ^ Name of (original) constructor and fields. (This might be in a module instance.)
--             , conData   :: QName       -- ^ Name of datatype or record type.
--             , conAbstr  :: IsAbstract
--             , conInd    :: Induction   -- ^ Inductive or coinductive?
--             , conComp   :: CompKit     -- ^ Cubical composition.
--             , conProj   :: Maybe [QName] -- ^ Projections. 'Nothing' if not yet computed.
--             , conForced :: [IsForced]
--               -- ^ Which arguments are forced (i.e. determined by the type of the constructor)?
--               --   Either this list is empty (if the forcing analysis isn't run), or its length is @conArity@.
--             , conErased :: Maybe [Bool]
--               -- ^ Which arguments are erased at runtime (computed during compilation to treeless)?
--               --   'True' means erased, 'False' means retained.
--               --   'Nothing' if no erasure analysis has been performed yet.
--               --   The length of the list is @conArity@.
--             }
--           | Primitive  -- ^ Primitive or builtin functions.
--             { primAbstr :: IsAbstract
--             , primName  :: String
--             , primClauses :: [Clause]
--               -- ^ 'null' for primitive functions, @not null@ for builtin functions.
--             , primInv      :: FunctionInverse
--               -- ^ Builtin functions can have inverses. For instance, natural number addition.
--             , primCompiled :: Maybe CompiledClauses
--               -- ^ 'Nothing' for primitive functions,
--               --   @'Just' something@ for builtin functions.
--             }
--           | PrimitiveSort
--             { primName :: String
--             , primSort :: Sort
--             }
--     deriving (Data, Show, Generic)
