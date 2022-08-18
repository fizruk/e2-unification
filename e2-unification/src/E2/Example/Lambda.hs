{-# LANGUAGE OverloadedStrings #-}
module E2.Example.Lambda where

import           Data.Void
import           E2.Rule
import           E2.Term
import           E2.Term.Unification

-- | Rewrite rules for lambda calculus with pairs.
rulesLambda :: [Rule Variable Void]
rulesLambda =
  [ app (lam (MetaVar "m1" [Var Z])) (MetaVar "m2" [])
      :-> MetaVar "m1" [MetaVar "m2" []]
  , first (pair (MetaVar "m1" []) (MetaVar "m2" []))
      :-> MetaVar "m1" []
  , second (pair (MetaVar "m1" []) (MetaVar "m2" []))
      :-> MetaVar "m2" []
  ]

-- * Constructors

-- | A helper to create application terms \(t_1\;t_2\)
app :: Term Variable a -> Term Variable a -> Term Variable a
app f x = Con "APP" [Regular f, Regular x]

-- | A helper to create lambda abstraction terms \(\lambda x. t\)
lam :: Term Variable (Inc a) -> Term Variable a
lam body = Con "LAM" [Scoped body]

-- | A helper to create first project terms \(\pi_1\;t\)
first :: Term Variable a -> Term Variable a
first p = Con "FIRST" [Regular p]

-- | A helper to create second project terms \(\pi_2\;t\)
second :: Term Variable a -> Term Variable a
second p = Con "SECOND" [Regular p]

-- | A helper to create pair terms \(\langle t_1, t_2 \rangle\)
pair :: Term Variable a -> Term Variable a -> Term Variable a
pair f s = Con "PAIR" [Regular f, Regular s]

-- * Example terms and constraints

-- |
-- >>> putStrLn $ ppTerm' ex1
-- APP(LAM(x₁.m1[x₁]), m2[])
ex1 :: Term Variable a
ex1 = Con "APP" [ Regular (Con "LAM" [ Scoped (MetaVar "m1" [Var Z]) ]), Regular (MetaVar "m2" []) ]

-- |
-- >>> putStrLn $ ppTerm' ex2
-- m1[m2[]]
ex2 :: Term Variable a
ex2 = MetaVar "m1" [MetaVar "m2" []]

-- |
-- >>> putStrLn $ ppTerm' ex3
-- APP(m[], x)
ex3 :: Term'
ex3 = Con "APP" [ Regular (MetaVar "m" []), Regular (Var "x") ]

-- |
-- >>> putStrLn $ ppConstraint' ex4
-- APP(m[y], x) =?= y
ex4 :: Constraint Variable Variable
ex4 = Ground (app (MetaVar "m" [Var "y"]) (Var "x") :==: Var "y")

-- |
-- >>> putStrLn $ ppConstraint' ex5
-- forall x₁.forall x₂.m1[x₂, x₁] =?= APP(x₁, x₂)
--
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 5 rulesLambda [ ex5 ]
-- m1[x₁, x₂] -> APP(x₂, x₁)
ex5 :: Constraint Variable Variable
ex5 = Forall $ Forall $
  Ground (MetaVar "m1" [Var Z, Var (S Z)]
    :==: Con "APP" [Regular (Var (S Z)), Regular (Var Z)] )

-- |
-- >>> putStrLn $ ppConstraint' ex6
-- APP(m[], PAIR(LAM(x₁.APP(x₁, y)), g)) =?= APP(g, y)
--
-- FIXME: unification does not finish in reasonable time!
ex6 :: Constraint Variable Variable
ex6 = Ground (app (MetaVar "m" []) (Con "PAIR" [Regular (lam (app (Var Z) (Var (S "y")))), Regular (Var "g")]) :==: app (Var "g") (Var "y"))

-- |
-- >>> putStrLn $ ppConstraint' ex7
-- m[y, g] =?= APP(g, y)
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 5 rulesLambda [ ex7 ]
-- m[x₁, x₂] -> APP(x₂, x₁)
ex7 :: Constraint Variable Variable
ex7 = Ground (MetaVar "m" [Var "y", Var "g"] :==: app (Var "g") (Var "y"))

-- |
-- >>> putStrLn $ ppConstraint' ex8
-- APP(m[y], g) =?= APP(g, y)
--
-- FIXME: takes too long
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 4 rulesLambda [ ex8 ]
-- m[x₁] -> LAM(x₂.APP(x₂, x₁))
ex8 :: Constraint Variable Variable
ex8 = Ground (app (MetaVar "m" [Var "y"]) (Var "g") :==: app (Var "g") (Var "y"))

-- |
-- >>> putStrLn $ ppConstraint' ex9
-- m[PAIR(y, g)] =?= g
--
-- FIXME: takes a bit too long and contains unresolved metavariable!
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 4 rulesLambda [ ex9 ]
-- m[x₁] -> APP(LAM(x₂.SECOND(x₁)), m₉[x₁])
--
-- >>> putStrLn $ ppMetaSubsts' $ defaultUnify $ unifyBFSviaDFS 1 5 rulesLambda [ ex9 ]
-- m[x₁] -> SECOND(x₁)
ex9 :: Constraint Variable Variable
ex9 = Ground (MetaVar "m" [pair (Var "y") (Var "g")] :==: Var "g")

ex10 :: Constraint Variable Variable
ex10 = Ground (MetaVar "m" [Var "b", Var "b"] :==: Var "b")

ex10' :: GroundConstraint Variable Variable
ex10' = MetaVar "m" [Var "b", Var "b"] :==: Var "b"

