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

hvmPostModule :: HvmOptions -> () -> IsMain -> ModuleName -> [[HvmTerm]] -> TCM ()
hvmPostModule options _ isMain modName sexprss = do
    let ts = concat sexprss
    let uss = whileChange sexprss (\s -> map (filter (`isKeeper` concat s)) s)

    let callMain = [Rule (Ctr (Var "Main") []) (App (Def "Main") [])]
    let putStrRule = [Rule (Ctr (Def "PutStrLn") [Var "a"]) (Var "a")]
    let eqRule = [Rule (Ctr (Def "Eq") [Var "a", Var "b"]) (Rules (App (Def "Eq_split") [App (Var "==") [Var "a", Var "b"]]) [
                    Rule (Ctr (Def "Eq_split") [Num 1]) (Var "True"),
                    Rule (Ctr (Def "Eq_split") [Num 0]) (Var "False")])]
    let monusRule = [Rule (Ctr (Def "Monus") [Var "a", Var "b"]) (Rules (App (Def "Monus_split") [App (Var ">") [Var "a", Var "b"], Var "a", Var "b"]) [
                        Rule (Ctr (Def "Monus_split") [Num 1, Var "a", Var "b"]) (App (Var "-") [Var "a", Var "b"]),
                        Rule (Ctr (Def "Monus_split") [Num 0, Var "a", Var "b"]) (Num 0)])]
    let t = intercalate "\n\n" $ map (intercalate "\n" . map show) (filter (not . Data.List.null) (uss ++ [putStrRule] ++ [eqRule] ++ [monusRule] ++ [callMain]))
    let fileName' = prettyShow (last $ mnameToList modName)
        fileName  = fileName' ++ ".hvm"
        filenameC = fileName' ++ ".c"
    liftIO $ createDirectoryIfMissing True "build"
    liftIO $ T.writeFile ("./build/" ++ fileName) (T.pack t)
    -- liftIO $ callProcess "hvm" ["c", fileName]
    -- liftIO $ callProcess "clang" ["-Ofast", "-lpthread", "-o", fileName', filenameC]
    where
        isKeeper (Rule (Ctr (Def "Main") _) _) ts = True
        isKeeper t ts = t `used` ts

main :: IO ()
main = runAgda [backend]

-- data List a = Nil | Cons a (List a)

-- -- Folds over a list
-- fold :: List t1 -> (t1 -> t2 -> t2) -> t2 -> t2
-- fold Nil         c n = n
-- fold (Cons x xs) c n = c x (fold xs c n)

-- -- A list from 0 to n
-- range :: (Eq a, Num a) => a -> List a -> List a
-- range 0 xs = xs
-- range n xs =
--   let m = n - 1
--   in range m (Cons m xs)

-- -- Sums a big list with fold
-- main :: IO ()
-- main = do
--   n <- read.head <$> getArgs :: IO Int
--   let size = 1000000 * n
--   let list = range size Nil
--   print $ fold list (+) 0
