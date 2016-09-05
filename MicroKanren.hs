{-# LANGUAGE TupleSections #-}
{-
Modifications by @ahmadsalim

Original Author: @seantalts (under BSD-3 license)

Ported from:
https://github.com/seantalts/hasktrip/blob/master/doc/MicroKanren.md
-}

module MicroKanren where

import Data.List (transpose)
import Data.Maybe (fromMaybe)

data Term = Var Int | Atom String
  deriving (Show, Eq)

type Substitution = [(Int, Term)]

walk :: Substitution -> Term -> Term
walk th x@(Var i) = fromMaybe x . fmap (walk th) $ lookup i th
walk _  x         = x

unify :: Term -> Term -> Substitution -> Maybe Substitution
unify lhs rhs th = (++ th) <$> unifyExpr (walk th lhs) (walk th rhs)
  where unifyExpr (Atom a) (Atom b) | a == b = return []
        unifyExpr (Var  i) r                 = return [(i, r)]
        unifyExpr l        (Var  i)          = return [(i, l)]
        unifyExpr _        _                 = Nothing

type Goal = (Substitution, Int) -> [(Substitution, Int)]

infixr 6 ===

(===) :: Term -> Term -> Goal
(a === b) (th, cnt) = maybe [] (return . (, cnt)) (unify a b th)

fresh :: (Term -> Goal) -> Goal
fresh f (th, cnt) = f (Var cnt) (th, cnt + 1)

disj :: Goal -> Goal -> Goal
disj g1 g2 st = (concat . transpose) [(g1 st), (g2 st)]

conj :: Goal -> Goal -> Goal
conj g1 g2 st = g1 st >>= g2

emptyState :: (Substitution, Int)
emptyState = ([], 0)

fives :: Term -> Goal
fives x = disj (x === (Atom "5")) (fives x)

sixes :: Term -> Goal
sixes x = disj (x === (Atom "6")) (sixes x)

fivesOrSixes :: Goal
fivesOrSixes = fresh $ \x -> disj (fives x) (sixes x)

aAndB :: Goal
aAndB = conj (fresh (\a -> a === (Atom "7")))
             (fresh (\b -> disj
                         (b === (Atom "5"))
                         (b === (Atom "6"))))

mkTests :: IO ()
mkTests = do
  print $ aAndB emptyState
  print $ take 4 $ (fives (Var 0)) emptyState
  print $ take 6 $ fivesOrSixes emptyState
