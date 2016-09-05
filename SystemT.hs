{-# LANGUAGE DeriveDataTypeable #-}
{- Author: @ahmadsalim -}
module SystemT where

import Data.Maybe
import Data.Data
import Data.Typeable

import Generic.Random.Data

import Test.QuickCheck

infixr 6 :*:
infixr 2 :=>:

data Type = NatTy
          | Type :*: Type
          | Type :=>: Type
    deriving (Eq, Show, Data, Typeable)

instance Arbitrary Type where
  arbitrary = sized generatorSR

type Ctxt a = [a]

data Term = Var Int
          | Lam Type Term
          | App Term Term
          | Prod Term Term
          | Fst Term
          | Snd Term
          | Zero
          | Succ Term
          | Rec Term Term Term
      deriving (Eq, Show, Data, Typeable)

instance Arbitrary Term where
  arbitrary = sized generatorSR

data Val = VFun Type (Val -> Maybe Val)
         | VProd Val Val
         | VNat Integer

instance Show Val where
  show (VFun _ f)      = "<function>"
  show (VProd v1 v2) = "(" ++ show v1 ++ "," ++ show v2 ++ ")"
  show (VNat i)      = show i

inferType :: Ctxt Type -> Term -> Maybe Type
inferType ctxt (Var x) =
  if 0 <= x && x < length ctxt
  then return (ctxt !! x)
  else Nothing
inferType ctxt (Lam ty tm)   = (ty :=>:) <$> inferType (ty : ctxt) tm
inferType ctxt (App tm1 tm2) = do
  ty1 <- inferType ctxt tm1
  ty2 <- inferType ctxt tm2
  case (ty1, ty2) of
    (sg :=>: tu, sg') | sg == sg' -> return tu
    _                             -> Nothing
inferType ctxt (Prod tm1 tm2) = do
   ty1 <- inferType ctxt tm1
   ty2 <- inferType ctxt tm2
   return (ty1 :*: ty2)
inferType ctxt (Fst tm) = do
   ty <- inferType ctxt tm
   case ty of
     (sg :*: tu) -> return sg
     _           -> Nothing

inferType ctxt (Snd tm) = do
   ty <- inferType ctxt tm
   case ty of
     (sg :*: tu) -> return tu
     _           -> Nothing

inferType ctxt Zero = return NatTy
inferType ctxt (Succ tm) = do
   ty <- inferType ctxt tm
   case ty of
     NatTy -> return NatTy
     _     -> Nothing
inferType ctxt (Rec tmz tms tmn) = do
   tyz <- inferType ctxt tmz
   tys <- inferType ctxt tms
   tmn <- inferType ctxt tmn
   case (tyz, tys, tmn) of
     (tu, tu' :=>: tu'', NatTy) | tu == tu'
                                  && tu' == tu'' -> return tu
     _ -> Nothing

eval :: Ctxt Val -> Term -> Maybe Val
eval ctxt (Var x) =
  if 0 <= x && x < length ctxt
   then return (ctxt !! x)
   else Nothing
eval ctxt (Lam ty tm) =
  return (VFun ty (\x -> eval (x:ctxt) tm))
eval ctxt (App tm1 tm2) = do
  v1 <- eval ctxt tm1
  v2 <- eval ctxt tm2
  case v1 of
    VFun _ f -> f v2
    _        -> Nothing
eval ctxt (Prod tm1 tm2) = do
  v1 <- eval ctxt tm1
  v2 <- eval ctxt tm2
  return (VProd v1 v2)
eval ctxt (Fst tm) = do
  v <- eval ctxt tm
  case v of
    VProd v1 v2 -> return v1
    _           -> Nothing
eval ctxt (Snd tm) = do
  v <- eval ctxt tm
  case v of
    VProd v1 v2 -> return v2
    _           -> Nothing
eval ctxt Zero = return (VNat 0)
eval ctxt (Succ tm) = do
  v <- eval ctxt tm
  case v of
    VNat n -> return (VNat (n + 1))
    _      -> Nothing
eval ctxt (Rec tmz tms tmn) = do
  vfz <- eval ctxt tmz
  vfs <- eval ctxt tms
  vn  <- eval ctxt tmn
  case (vfs, vn) of
    (VFun NatTy f, VNat x) ->
      let go n | n == 0    = return vfz
               | n > 0     = f =<< go (n - 1)
               | otherwise = Nothing
      in go x
    _      -> Nothing

-- Examples

plus :: Term
plus = Lam NatTy (Lam NatTy (Rec (Var 0) (Lam NatTy (Succ (Var 0))) (Var 1)))

times :: Term
times = Lam NatTy (Lam NatTy (Rec Zero (Lam NatTy  (App (App plus (Var 0)) (Var 1))) (Var 1)))

elim :: Type -> Term
elim ty = Lam ty
           (Lam (NatTy :=>: ty :=>: ty)
            (Lam NatTy
              (Snd (Rec (Prod Zero (Var 2)) (Lam (NatTy :*: ty) (Prod (Succ (Fst (Var 0)))  (App (App (Var 2) (Fst (Var 0))) (Snd (Var 0)))) ) (Var 0)))))

-- Property

prop_typesafe tm =
  let mty = inferType [] tm
  in isJust mty ==> isJust (eval [] tm)
