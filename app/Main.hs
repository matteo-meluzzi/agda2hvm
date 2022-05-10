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
import System.Environment (getArgs)
import System.Directory

import Utils

type HvmModule = [[HvmTerm]]

backend' :: Backend' HvmOptions HvmOptions () HvmModule [HvmTerm]
backend' = Backend'
    {
        backendName             = "agda2HVM"
        , backendVersion        = Nothing
        , options               = Options
        , commandLineFlags      = []
        , isEnabled             = const True
        , preCompile            = hvmPreCompile
        , postCompile           = hvmPostCompile
        , preModule             = \ _ _ _ _ -> return $ Recompile ()
        , postModule            = hvmPostModule
        , compileDef            = hvmCompile
        , scopeCheckingSuffices = False
        , mayEraseType          = \ _ -> return True
    }

backend :: Backend
backend = Backend backend'

hvmPreCompile :: HvmOptions -> TCM HvmOptions
hvmPreCompile o = do
    liftIO $ createDirectoryIfMissing True "build"
    liftIO $ setCurrentDirectory "build"
    return o

comparison :: HvmAtom -> HvmAtom -> HvmTerm
comparison name symbol = Rule (Ctr (Def name) [Var "a", Var "b"]) (Rules (App (Def splitName) [App (Var symbol) [Var "a", Var "b"]]) [
                    Rule (Ctr (Def splitName) [Num 1]) (Var "True"),
                    Rule (Ctr (Def splitName) [Num 0]) (Var "False")])
                    where splitName = name ++ "_split"

hvmPostCompile :: HvmOptions -> IsMain -> Map ModuleName HvmModule -> TCM ()
hvmPostCompile opts isMain modulesDict = do
    let ms = Map.elems modulesDict
    let m  = concat ms
    let uss = whileChange m (\s -> map (filter (`isKeeper` concat s)) s)

    -- let callMain = [Rule (Ctr (Var "Main") [Var "n"]) (App (Def "Main") [Var "n"])]
    let callMain = [Rule (Ctr (Var "Main") []) (App (Def "Main") [])]
    let comparisonRules = [comparison "Eq" "==", comparison "Gt" ">", comparison "Lt" "<"]
    let monusRule = [Rule (Ctr (Def "Monus") [Var "a", Var "b"]) (Rules (App (Def "Monus_split") [App (Var ">") [Var "a", Var "b"], Var "a", Var "b"]) [
                        Rule (Ctr (Def "Monus_split") [Num 1, Var "a", Var "b"]) (App (Var "-") [Var "a", Var "b"]),
                        Rule (Ctr (Def "Monus_split") [Num 0, Var "a", Var "b"]) (Num 0)])]
    let ifRule = [Rule (Ctr (Def "If") [Var "True", Var "t", Var "e"]) (Var "t"), Rule (Ctr (Def "If") [Var "False", Var "t", Var "e"]) (Var "e")]
    let t = intercalate "\n\n" $ map (intercalate "\n" . map show) (filter (not . Data.List.null) (uss  ++ [comparisonRules] ++ [ifRule] ++ [monusRule] ++ [callMain]))
    let fileName' = "main" -- How do I know the name of the original file?
        fileName  = fileName' ++ ".hvm"
        filenameC = fileName' ++ ".c"
    liftIO $ T.writeFile ("./" ++ fileName) (T.pack t)
    liftIO $ callProcess "hvm" ["c", fileName]
    liftIO $ callProcess "clang" ["-Ofast", "-lpthread", "-o", fileName', filenameC]
    where
        -- isKeeper t ts = True
        isKeeper (Rule (Ctr (Def "Main") _) _) ts = True
        isKeeper t ts = t `used` ts

flatten :: HvmTerm -> [HvmTerm]
flatten term = term:(case term of
    Lam n t -> flatten t
    App t args -> flatten t ++ concatMap flatten args
    Ctr t args -> flatten t ++ concatMap flatten args
    Op2 o t1 t2 -> flatten t1 ++ flatten t2
    Let n t1 t2 -> flatten t1 ++ flatten t2
    Var n -> []
    Def n -> []
    Num i -> []
    Str xs -> []
    Parenthesis t -> flatten t
    Rule t1 t2 -> flatten t1 ++ flatten t2
    Rules t ts -> flatten t ++ concatMap flatten ts
    )

contains :: HvmTerm -> (HvmTerm -> Bool) -> Bool
contains term p = any p $ flatten term

optimize :: HvmTerm -> HvmTerm
optimize t = case t of
    App (App (Def n) []) args -> App (Def n) (map optimize args)
    Let n t1 t2 | not $ t2 `contains` (== Var n) -> optimize t2

    Lam n t -> Lam n (optimize t)
    App t args -> App (optimize t) (map optimize args)
    Ctr t args -> Ctr (optimize t) (map optimize args)
    Op2 o t1 t2 -> Op2 o (optimize t1) (optimize t2)
    Let n t1 t2 -> Let n (optimize t1) (optimize t2)
    Var n -> Var n
    Def n -> Def n
    Num i -> Num i
    Str xs -> Str xs
    Parenthesis t -> Parenthesis (optimize t)
    Rule t1 t2 -> Rule (optimize t1) (optimize t2)
    Rules t ts -> Rules (optimize t) (map optimize ts)

hvmCompile :: HvmOptions -> () -> IsMain -> Definition -> TCM [HvmTerm]
hvmCompile opts _ isMain def = do
    ts <- toHvm def
            & (`evalStateT` initToHvmState)
            & (`runReaderT` initToHvmEnv opts)
    return $ map optimize ts

definitions :: [HvmTerm] -> [HvmAtom]
definitions [] = []
definitions (Rule (Ctr (Def name) _) _:xs) = name:definitions xs
definitions (_:xs) = definitions xs

used :: HvmTerm -> [HvmTerm] -> Bool
used r@(Rule (Ctr (Def name) params) _) rules = any (`contains` (\case
        App (Def n) args -> name == n && length params == length args
        _ -> False
    )) $ filter (/= r) rules
used r rules = False

whileChange :: Eq t => t -> (t -> t) -> t
whileChange last f = do
    let new = f last
    if new == last then last else whileChange new f

hvmPostModule :: HvmOptions -> () -> IsMain -> ModuleName -> [[HvmTerm]] -> TCM HvmModule
hvmPostModule options _ isMain modName sexprss = do

    return sexprss

main :: IO ()
main = runAgda [backend]
