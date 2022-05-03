module Main where

import Prelude hiding ( null , empty )

import Agda.Compiler.Backend
import Agda.Compiler.Common

import Agda.Main ( runAgda )

import Agda.Interaction.Options ( OptDescr(..) , ArgDescr(..) )

import Agda.Syntax.Treeless ( EvaluationStrategy(..) )

import Agda.TypeChecking.Pretty

import Agda.Utils.Either
import Agda.Utils.Functor
import Agda.Utils.Null
import Agda.Utils.Pretty ( prettyShow )

import Control.DeepSeq ( NFData )

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Function
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T

import GHC.Generics ( Generic )

import ToHvm
import Syntax

import System.Process

backend' :: Backend' HvmOptions HvmOptions () () [HvmTerm]
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

optimize :: HvmTerm -> HvmTerm
optimize t = case t of
    App (App (Def n) []) args -> App (Def n) (map optimize args)

    Lam n t -> Lam n (optimize t)
    App t args -> App (optimize t) (map optimize args)
    Ctr t args -> Ctr (optimize t) (map optimize args)
    Op2 o t1 t2 -> Op2 o (optimize t1) (optimize t2)
    Let n t1 t2 -> Let n (optimize t1) (optimize t2)
    Var n -> Var n
    Def n -> Def n
    Num i -> Num i
    Str xs -> Str xs
    Parenthesis t -> Parenthesis t
    Rule t1 t2 -> Rule (optimize t1) (optimize t2)
    Rules t ts -> Rules (optimize t) (map optimize ts)

hvmCompile :: HvmOptions -> () -> IsMain -> Definition -> TCM [HvmTerm]
hvmCompile opts _ isMain def = do
    ts <- toHvm def
            & (`evalStateT` initToHvmState)
            & (`runReaderT` initToHvmEnv opts)
    return $ map optimize ts

hvmPostModule :: HvmOptions -> () -> IsMain -> ModuleName -> [[HvmTerm]] -> TCM ()
hvmPostModule options _ isMain modName sexprss = do
    let callMain = [Rule (Ctr (Var "Main") []) (App (Def "Main") [])]
    let putStrRule = [Rule (Ctr (Def "PutStrLn") [Var "a"]) (Var "a")]
    let t = intercalate "\n\n" $ map (intercalate "\n" . map show) (filter (not . Data.List.null) (sexprss ++ [putStrRule] ++ [callMain]))
    let fileName' = prettyShow (last $ mnameToList modName)
        fileName  = fileName' ++ ".hvm"
        filenameC = fileName' ++ ".c"
    liftIO $ T.writeFile fileName (T.pack t)
    liftIO $ callProcess "hvm" ["c", fileName]
    liftIO $ callProcess "clang" ["-Ofast", "-o", fileName', filenameC]

main :: IO ()
main = runAgda [backend]