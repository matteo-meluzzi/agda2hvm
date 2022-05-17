module Optimize where
import Syntax

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
    -- App (App (Def n) []) args -> App (Def n) (map optimize args)
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

removeUnused :: [[HvmTerm]] -> [[HvmTerm]]
removeUnused defs = whileChange defs (\s -> map (filter (`isKeeper` concat s)) s)
    where
        isKeeper t ts = True
        -- isKeeper (Rule (Ctr (Def "Main") _) _) ts = True
        -- isKeeper t ts = t `used` ts
