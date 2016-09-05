{-# LANGUAGE TupleSections, DeriveDataTypeable #-}
{-
Modifications by @ahmadsalim

Original Author: @seantalts (under BSD-3 license)

Ported from:
https://github.com/seantalts/hasktrip/blob/master/doc/MicroKanren.md
-}

module MicroKanren where

import Data.List (transpose)
import Data.Maybe (fromMaybe)

import Data.Data
import Data.Typeable

import Control.Monad

import Generic.Random.Data

import Test.QuickCheck hiding ((===))

data Term = UVar Int | Var Int | Atom String
  deriving (Show, Eq, Data, Typeable)

instance Arbitrary Term where
  arbitrary = sized generatorSR

data Statement =
    Fresh Statement
  | Statement :&: Statement
  | Statement :|: Statement
  | Term :=: Term
  | Call String [Term]
  deriving (Show, Eq, Data, Typeable)

instance Arbitrary Statement where
  arbitrary = sized generatorSR

data Definition = Definition {- Name -} String {- Parameters -} Int

type Substitution = [(Int, Term)]

walk :: Substitution -> Term -> Term
walk th x@(UVar i) = maybe x (walk th) $ lookup i th
walk _  x         = x

unify :: Term -> Term -> Substitution -> Maybe Substitution
unify lhs rhs th = (++ th) <$> unifyExpr (walk th lhs) (walk th rhs)
  where unifyExpr (Atom a) (Atom b) | a == b = return []
        unifyExpr (UVar  i) r                 = return [(i, r)]
        unifyExpr l        (UVar  i)          = return [(i, l)]
        unifyExpr _        _                  = Nothing

type Goal = (Substitution, Int) -> [(Substitution, Int)]

infixr 6 ===

(===) :: Term -> Term -> Goal
(a === b) (th, cnt) = maybe [] (return . (, cnt)) (unify a b th)

fresh :: (Term -> Goal) -> Goal
fresh f (th, cnt) = f (UVar cnt) (th, cnt + 1)

disj :: Goal -> Goal -> Goal
disj g1 g2 st = (concat . transpose) [g1 st, g2 st]

conj :: Goal -> Goal -> Goal
conj g1 g2 = g1 >=> g2

interpretTerm :: [Term] -> Term -> Term
interpretTerm ctxt (Var i) =
  if 0 <= i && i < length ctxt
  then ctxt !! i
  else error "Looking up variable out of bounds"
interpretTerm ctxt tm = tm

interpretStatement :: [Term] -> Statement -> Goal
interpretStatement ctxt (Fresh stmt) =
  fresh (\x -> interpretStatement (x:ctxt) stmt)
interpretStatement ctxt (stmt1 :&: stmt2) =
  conj (interpretStatement ctxt stmt1) (interpretStatement ctxt stmt2)
interpretStatement ctxt (stmt1 :|: stmt2) =
  disj (interpretStatement ctxt stmt1) (interpretStatement ctxt stmt2)
interpretStatement ctxt (tm1 :=: tm2) =
  interpretTerm ctxt tm1 === interpretTerm ctxt tm2
interpretStatement ctxt (Call stmt1 stmt2) = error "Call not supported"

validTerm :: Int -> Term -> Bool
validTerm _ct (UVar _t) = False
validTerm ct  (Var x)   = 0 <= x && x < ct
validTerm _ct (Atom _t) = True

validStatement :: Int -> Statement -> Bool
validStatement ct (Fresh st)     = validStatement (ct + 1) st
validStatement ct (st1 :&: st2)  = validStatement ct st1 && validStatement ct st2
validStatement ct (st1 :|: st2)  = validStatement ct st1 && validStatement ct st2
validStatement ct (tm1 :=: tm2)  = validTerm ct tm1 && validTerm ct tm2
validStatement ct (Call st1 st2) = False

-- Examples

emptyState :: (Substitution, Int)
emptyState = ([], 0)

fives :: Term -> Goal
fives x = disj (x === (Atom "5")) (fives x)

sixes :: Term -> Goal
sixes x = disj (x === (Atom "6")) (sixes x)

fivesOrSixes :: Goal
fivesOrSixes = fresh $ \x -> disj (fives x) (sixes x)

aAndB :: Statement
aAndB = Fresh (Var 0 :=: Atom "7") :&:
          Fresh ((Var 0 :=: Atom "5") :|: (Var 0 :=: Atom "6"))

mkTests :: IO ()
mkTests = do
  print $ interpretStatement [] aAndB emptyState
  print $ take 4 $ fives (UVar 0) emptyState
  print $ take 6 $ fivesOrSixes emptyState

prop_disj (st1, st2) = validStatement 0 st1 && validStatement 0 st2 ==> interpretStatement [] (st1 :|: st2) emptyState == interpretStatement [] (st2 :|: st1) emptyState
