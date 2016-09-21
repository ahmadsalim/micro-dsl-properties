{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module FJ where

import Control.Monad
import Data.List
import Data.Maybe
import Data.Tuple

newtype Name = Name String
  deriving (Show, Eq)

type ClassName  = Name
type FieldName  = Name
type MethodName = Name

newtype Prog = Prog { classes :: [Class] }
  deriving (Show, Eq)

data Class = Class
            { className :: Name
            , superclass :: ClassName
            , fields :: [Field]
            , constructor :: Constructor
            , methods :: [Method]
            }
   deriving (Show, Eq)

data Field = Field
             { fieldType :: ClassName
             , fieldName  :: Name
             }
  deriving (Show, Eq)

data Constructor = Constructor
                   { constructorArguments       :: [Field]
                   , constructorSuperArguments  :: [Field]
                   }
  deriving (Show, Eq)

data Method = Method
              { methodReturnType :: ClassName
              , methodName       :: Name
              , methodParameters :: [(ClassName, Name)]
              , methodBodyExpr   :: Expr
              }
  deriving (Show, Eq)

data Expr = Var Name
          | FieldAccess Expr      FieldName
          | MethodCall  Expr      MethodName [Expr]
          | New         ClassName [Expr]
          | Cast        ClassName Expr
  deriving (Show, Eq)

infixr 6 :=>:

data MethodType = [ClassName] :=>: ClassName
  deriving (Show, Eq)

isSubtype :: Prog -> ClassName -> ClassName -> Bool
isSubtype prog cn cn' | cn == cn' = True
isSubtype prog cn cn' =
  fromMaybe False (do c <- find ((== cn) . className) (classes prog)
                      return $ isSubtype prog (superclass c) cn')

fieldsOf :: Prog -> Name -> Maybe [Field]
fieldsOf prog (Name "Object") = return []
fieldsOf prog nm              = do
  c <- find ((== nm) . className) (classes prog)
  (++) <$> fieldsOf prog (superclass c) <*> pure (fields c)

methodsOf :: Prog -> Name -> Maybe [Method]
methodsOf prog (Name "Object") = return []
methodsOf prog nm               = do
  c <- find ((== nm) . className) (classes prog)
  (++) <$> methodsOf prog (superclass c) <*> pure (methods c)

methodType :: Prog -> MethodName -> ClassName -> Maybe MethodType
methodType prog mn cn = do
  mets <- reverse <$> methodsOf prog cn
  m <- find ((== mn) . methodName) mets
  return (map fst (methodParameters m) :=>: methodReturnType m)

methodBody :: Prog -> MethodName -> ClassName -> Maybe Expr
methodBody prog mn cn = do
  mets <- reverse <$> methodsOf prog cn
  m <- find ((== mn) . methodName) mets
  return (methodBodyExpr m)

checkScope :: Prog -> Bool
checkScope prog = all (checkClassScope prog) (classes prog)

checkClassScope :: Prog -> Class -> Bool
checkClassScope prog (Class cn sn cflds (Constructor iflds sflds) meths) =
     iflds == sflds ++ cflds
  && elem sflds (fieldsOf prog sn)
  && all (checkMethodScope prog) meths

checkMethodScope :: Prog -> Method -> Bool
checkMethodScope prog (Method rty mnm pars mbody) = checkExpressionScope prog (map snd pars ++ [Name "this"]) mbody

checkExpressionScope :: Prog -> [Name] -> Expr -> Bool
checkExpressionScope prog env (Var nm)            = nm `elem` env
checkExpressionScope prog env (FieldAccess e f)   =
  checkExpressionScope prog env e && any (any (any ((== f) . fieldName)) . fieldsOf prog . className) (classes prog)
checkExpressionScope prog env (MethodCall e m es) =
   checkExpressionScope prog env e &&
   any (any (any (\m' -> length (methodParameters m') == length es && ((== m) . methodName $ m'))) . methodsOf prog . className) (classes prog) &&
   all (checkExpressionScope prog env) es
checkExpressionScope prog env (New c es)          = length (fieldsOf prog c) == length es && all (checkExpressionScope prog env) es
checkExpressionScope prog env (Cast c e)          = checkExpressionScope prog env e

checkTypes :: Prog -> Bool
checkTypes prog = all (checkClassType prog) (classes prog)

checkClassType :: Prog -> Class -> Bool
checkClassType prog (Class cn sn cflds (Constructor iflds sflds) meths) =
     iflds == sflds ++ cflds
  && elem sflds (fieldsOf prog sn)
  && all (checkMethodType prog cn) meths

checkMethodType :: Prog -> ClassName -> Method -> Bool
checkMethodType prog cn (Method rty mnm pars mbody) = fromMaybe False $ do
  c <- find ((== cn) . className) (classes prog)
  guard $ all (\(sparty :=>: srty) -> map fst pars == sparty && rty == srty) (methodType prog mnm (superclass c))
  bodyty <- typeExpression prog (pars ++ [(cn, Name "this")]) mbody
  return $ isSubtype prog bodyty rty

typeExpression :: Prog -> [(ClassName, Name)] -> Expr -> Maybe ClassName
typeExpression prog env (Var x) = lookup x (map swap env)
typeExpression prog env (FieldAccess e0 fi) = do
  e0ty <- typeExpression prog env e0
  fs  <- fieldsOf prog e0ty
  fieldType <$> find ((== fi) . fieldName) fs
typeExpression prog env (MethodCall e0 m es) = do
  e0ty <- typeExpression prog env e0
  (parstys :=>: mrety) <- methodType prog m e0ty
  guard $ length es == length parstys
  ets <- mapM (typeExpression prog env) es
  guard $ all (uncurry (isSubtype prog)) (zip ets parstys)
  return mrety
typeExpression prog env (New cn es) = do
  fts <- map fieldType <$> fieldsOf prog cn
  guard $ length es == length fts
  ets <- mapM (typeExpression prog env) es
  guard $ all (uncurry (isSubtype prog)) (zip ets fts)
  return cn
typeExpression prog env (Cast tc e) = do
  ety <- typeExpression prog env e
  return {-
    Aif not (isSubtype prog ety tc) && not (isSubtype prog tc ety)
    then tc {- STUPID WARNING -}
    else -} tc

-- Example Programs

animalProg :: Prog
animalProg = Prog [
  Class (Name "Animal") (Name "Object") [Field (Name "Object") (Name "happiness")]
        (Constructor [Field (Name "Object") (Name "happiness")] [])
        [Method (Name "Object") (Name "friend") [(Name "Animal", Name "other")]
                (FieldAccess (Var (Name "other")) (Name "happiness"))]
  ]
