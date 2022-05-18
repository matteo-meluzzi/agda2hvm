module Syntax where

import Data.List

type HvmAtom = String
data HvmOp2 = Add |
              Sub |
              Mul |
              Div |
              Mod |
              And |
              Or  |
              Not |
              ShR |
              ShL |
              Lt  |
              LtEq |
              Eq |
              Gt |
              GtEq |
              NEq |
              Seq
            deriving Eq
instance Show HvmOp2 where
    show Add = "+"
    show Sub = "-"
    show Mul = "*"
    show Div = "/"
    show Mod = "%"
    show And = "&"
    show Or = "|"
    show Not = "^"
    show ShR = ">>"
    show ShL = "<<"
    show Lt = "Lt_2"
    show LtEq = "LtEq_2"
    show Eq = "Eq_2"
    show Gt = "Gt_2"
    show GtEq = "GtEq_2"
    show NEq = "NEq_2"
    show Seq = "Seq_2"

data HvmTerm =  Lam HvmAtom HvmTerm |
                App HvmTerm [HvmTerm] |
                Ctr HvmTerm [HvmTerm] |
                Op2 HvmOp2 HvmTerm HvmTerm |
                Let HvmAtom HvmTerm HvmTerm |
                Var HvmAtom |
                Def HvmAtom |
                Num Integer |
                Str String |
                Parenthesis HvmTerm |
                Rule HvmTerm HvmTerm |
                Rules HvmTerm [HvmTerm]
            deriving Eq


showSExpr :: Maybe String -> [HvmTerm] -> String
showSExpr (Just head) [] = "(" ++ head ++  ")"
showSExpr (Just head) terms = "(" ++ head ++ " " ++ intercalate " " (map show terms) ++ ")"
showSExpr Nothing terms = "(" ++ intercalate " " (map show terms) ++ ")"

instance Show HvmTerm where
    show (Lam v t) = showSExpr (Just $ "@" ++ v ++ " " ++ show t) []
    show (App (Def d) xs) = showSExpr (Just $ d ++ "_" ++ (show . length) xs) xs
    show (App t1 t2) = showSExpr Nothing (t1:t2)
    show (Ctr (Def n) xs) = showSExpr (Just $ n ++ "_" ++ (show . length) xs) xs
    show (Ctr n xs) = showSExpr (Just $ show n) xs
    show (Op2 op t1 t2) = showSExpr (Just $ show op) [t1, t2]
    show (Let n t1 t2) = "let " ++ n ++ " = " ++ show t1 ++ "; " ++ show t2
    show (Var n) = n
    show (Def n) = n
    show (Num i) = show i
    show (Str xs) = show xs
    show (Parenthesis t) = showSExpr Nothing [t]
    show (Rule t1 t2) = show t1 ++ " = " ++ show t2
    show (Rules x xs) = show x ++ "\n\t" ++ intercalate "\n\t" (map show xs)
