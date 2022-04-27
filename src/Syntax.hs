module Syntax where

import Data.List

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
