{-# LANGUAGE DeriveDataTypeable, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module FJ where


import Data.Data
import Data.Typeable
import Data.List
import Data.Maybe
import Data.Tuple

import Data.Generics.Uniplate.Data

import Control.Monad

newtype Name = Name { unName :: String }
  deriving (Show, Eq, Data, Typeable)

type ClassName  = Name
type FieldName  = Name
type MethodName = Name

newtype Prog = Prog { classes :: [Class] }
  deriving (Show, Eq, Data, Typeable)

data Class = Class
            { className :: Name
            , superclass :: ClassName
            , fields :: [Field]
            , constructor :: Constructor
            , methods :: [Method]
            }
   deriving (Show, Eq, Data, Typeable)

data Field = Field
             { fieldType :: ClassName
             , fieldName  :: Name
             }
  deriving (Show, Eq, Data, Typeable)

data Constructor = Constructor
                   { constructorArguments       :: [Field]
                   , constructorSuperArguments  :: [Field]
                   }
  deriving (Show, Eq, Data, Typeable)

data Method = Method
              { methodReturnType :: ClassName
              , methodName       :: Name
              , methodParameters :: [(ClassName, Name)]
              , methodBodyExpr   :: Expr
              }
  deriving (Show, Eq, Data, Typeable)

data Expr = Var         (Maybe ClassName) Name
          | FieldAccess (Maybe ClassName) Expr      FieldName
          | MethodCall  (Maybe ClassName) Expr      MethodName [Expr]
          | New         (Maybe ClassName) ClassName [Expr]
          | Cast        (Maybe ClassName) ClassName Expr
  deriving (Show, Eq, Data, Typeable)

infixr 6 :=>:

data MethodType = [ClassName] :=>: ClassName
  deriving (Show, Eq)

isSubtype :: Prog -> ClassName -> ClassName -> Bool
isSubtype _prog cn cn' | cn == cn' = True
isSubtype prog cn cn' =
  fromMaybe False (do c <- find ((== cn) . className) (classes prog)
                      return $ isSubtype prog (superclass c) cn')

fieldsOf :: Prog -> Name -> Maybe [Field]
fieldsOf _prog (Name "Object") = return []
fieldsOf prog nm              = do
  c <- find ((== nm) . className) (classes prog)
  (++) <$> fieldsOf prog (superclass c) <*> pure (fields c)

methodsOf :: Prog -> Name -> Maybe [Method]
methodsOf _prog (Name "Object") = return []
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
checkMethodScope prog (Method _rty _mnm pars mbody) = checkExpressionScope prog (map snd pars ++ [Name "this"]) mbody

checkExpressionScope :: Prog -> [Name] -> Expr -> Bool
checkExpressionScope _prog env (Var Nothing nm)            = nm `elem` env
checkExpressionScope prog env (FieldAccess Nothing e f)   =
  checkExpressionScope prog env e && any (any (any ((== f) . fieldName)) . fieldsOf prog . className) (classes prog)
checkExpressionScope prog env (MethodCall Nothing e m es) =
   checkExpressionScope prog env e &&
   any (any (any (\m' -> length (methodParameters m') == length es && ((== m) . methodName $ m'))) . methodsOf prog . className) (classes prog) &&
   all (checkExpressionScope prog env) es
checkExpressionScope prog env (New Nothing c es)          = length (fieldsOf prog c) == length es && all (checkExpressionScope prog env) es
checkExpressionScope prog env (Cast Nothing _c e)         = checkExpressionScope prog env e
checkExpressionScope prog env _                           = False

checkTypes :: Prog -> Maybe Prog
checkTypes prog = Prog <$> mapM (checkClassType prog) (classes prog)

checkClassType :: Prog -> Class -> Maybe Class
checkClassType prog (Class cn sn cflds (Constructor iflds sflds) meths) = do
     guard $ iflds == sflds ++ cflds
     guard $ elem sflds (fieldsOf prog sn)
     meths' <- mapM (checkMethodType prog cn) meths
     return (Class cn sn cflds (Constructor iflds sflds) meths')

checkMethodType :: Prog -> ClassName -> Method -> Maybe Method
checkMethodType prog cn (Method rty mnm pars mbody) = do
  c <- find ((== cn) . className) (classes prog)
  guard $ all (\(sparty :=>: srty) -> map fst pars == sparty && rty == srty) (methodType prog mnm (superclass c))
  (bodyty, mbody') <- typeExpression prog (pars ++ [(cn, Name "this")]) mbody
  guard $ isSubtype prog bodyty rty
  return $ Method rty mnm pars mbody'

typeExpression :: Prog -> [(ClassName, Name)] -> Expr -> Maybe (ClassName, Expr)
-- a pair of result type and type-annotated expression
typeExpression prog env (Var Nothing x) =
  let xty = lookup x (map swap env)
  in (,) <$> xty <*> return (Var xty x)
typeExpression prog env (FieldAccess Nothing e0 fi) = do
  (e0ty, e0') <- typeExpression prog env e0
  fs  <- fieldsOf prog e0ty
  fty <- fieldType <$> find ((== fi) . fieldName) fs
  return (fty, FieldAccess (Just fty) e0' fi)
typeExpression prog env (MethodCall Nothing e0 m es) = do
  (e0ty, e0') <- typeExpression prog env e0
  (parstys :=>: mrety) <- methodType prog m e0ty
  guard $ length es == length parstys
  (ets, es') <- unzip <$> mapM (typeExpression prog env) es
  guard $ all (uncurry (isSubtype prog)) (zip ets parstys)
  return (mrety, MethodCall (Just mrety) e0' m es')
typeExpression prog env (New Nothing cn es) = do
  fts <- map fieldType <$> fieldsOf prog cn
  guard $ length es == length fts
  (ets, es') <- unzip <$> mapM (typeExpression prog env) es
  guard $ all (uncurry (isSubtype prog)) (zip ets fts)
  return (cn, New (Just cn) cn es')
typeExpression prog env (Cast Nothing tc e) = do
  (_ety, e') <- typeExpression prog env e
  return {-
    Aif not (isSubtype prog ety tc) && not (isSubtype prog tc ety)
    then tc {- STUPID WARNING -}
    else -} (tc, Cast (Just tc) tc e')
typeExpression _prog _env _ = Nothing

-- Refactorigns

renameField :: Prog -> ClassName -> FieldName -> FieldName -> Either String Prog
renameField prog classnm oldfieldnm newfieldnm = do
  _ <- do
    class'      <- fromMaybe (Left $ "Unknown class: " ++ unName classnm)
                             (return <$> find ((== classnm) . className) (classes prog))
    unless (any ((== oldfieldnm) . fieldName) $ fields class') $
          Left ("Class " ++ unName classnm ++ "does not have field " ++ unName oldfieldnm)
    when   (any (any ((== newfieldnm) . fieldName)) $ fieldsOf prog classnm) $
          Left ("Class " ++ unName classnm ++ "or one of its superclasses already have field " ++ unName newfieldnm)
  let prog' = rewriteBi (\(c :: Class) ->
                            if className c == classnm
                            then do
                              oldField <- find ((== oldfieldnm) . fieldName) (fields c)
                              return c { fields = Field (fieldType oldField) newfieldnm : delete oldField (fields c) }
                            else Nothing) prog
  return $ rewriteBi (\(e :: Expr) ->
                        case e of
                          FieldAccess (Just c) e f ->
                            if isSubtype prog' c classnm && f == oldfieldnm
                            then return $ FieldAccess (Just c) e newfieldnm
                            else Nothing
                          _ -> Nothing) prog'

-- Example Programs

animalProg :: Prog
animalProg = Prog [
  Class (Name "Animal") (Name "Object") [Field (Name "Object") (Name "happiness")]
        (Constructor [Field (Name "Object") (Name "happiness")] [])
        [Method (Name "Object") (Name "friend") [(Name "Animal", Name "other")]
                (FieldAccess Nothing (Var Nothing (Name "other")) (Name "happiness"))]
  ]

renameHappiness :: Prog
renameHappiness =
  let Just animalProgTyped    = checkTypes animalProg
      Right animalProgRenamed = renameField animalProgTyped (Name "Animal") (Name "happiness") (Name "excitement")
  in animalProgRenamed
