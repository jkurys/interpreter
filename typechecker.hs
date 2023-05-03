module TypeChecker where
import Control.Monad.Trans.State.Lazy
import AbsMylang
import Data.Map as Map
import qualified Control.Monad as CM
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Data.Maybe (isNothing)
import Data.Functor.Identity (Identity (runIdentity))
import Control.Monad.Trans.Reader

type ErrorState = String

type Location = Int

data Function = Func [FnArg] Type deriving Show

data FnArg = Ref Type | NoRef Type deriving Show

type FnEnv = Map.Map Ident Function

type VarEnv = Map.Map Ident Location

type VarState = Map.Map Location Type

data Env = Env {
    varEnv :: VarEnv,
    fnEnv :: FnEnv
} deriving Show

data CheckerState = CheckerState {
    varState :: VarState,
    nextLoc :: Int,
    returnType :: Type
}

type CheckerMonadT s e r m a = StateT s (ExceptT e (ReaderT r m)) a

runCheckerMonadT :: (Monad m) => CheckerMonadT s e r m a -> s -> r -> m (Either e a)
runCheckerMonadT m = runReaderT . runExceptT . evalStateT m

type CheckerMonad a = CheckerMonadT CheckerState ErrorState Env Identity a

runCheckerMonad :: CheckerMonad a -> CheckerState -> Env -> Either ErrorState a
runCheckerMonad env m = runIdentity . runCheckerMonadT env m

getVariable :: BNFC'Position -> Ident -> CheckerMonad Type
getVariable p name = do
    CheckerState { varState = s } <- get
    Env { varEnv = env } <- askChecker
    let loc = Map.lookup name env

    case loc of {
        Nothing -> addError p ("Variable " ++ show name ++ " was not initialized") >> return (Void BNFC'NoPosition);
        Just varLoc -> do
            let varType = Map.lookup varLoc s
            case varType of {
                Nothing -> addError p "Unexpected error happened" >> return (Void BNFC'NoPosition);
                Just t -> return t
            }
    }

askChecker :: CheckerMonad Env
askChecker = lift $ lift ask

emptyEnv :: Env
emptyEnv = Env { varEnv = Map.empty, fnEnv = Map.empty }

localEnv :: (Env -> Env) -> CheckerMonad a -> CheckerMonad a
localEnv = mapStateT . mapExceptT . local

getReturnType :: CheckerMonad Type
getReturnType = do
    CheckerState { returnType = r } <- get
    return r

putReturnType :: Type -> CheckerMonad ()
putReturnType newRet = do
    CheckerState { varState = s, nextLoc = n, returnType = r } <- get
    put CheckerState { varState = s, nextLoc = n, returnType = newRet }

declareVariable :: Ident -> Type -> Env -> CheckerMonad Env
declareVariable name val env = do
    CheckerState { varState = s, nextLoc = n, returnType = r } <- get
    let Env { varEnv = v, fnEnv = f } = env
    let newV = Map.insert name n v
    let newS = Map.insert n val s
    put CheckerState { varState = newS, nextLoc = n + 1, returnType = r }
    return Env { varEnv = newV, fnEnv = f }

getFunction :: Ident -> CheckerMonad (Maybe Function)
getFunction name = do
    Env { fnEnv = f } <- askChecker
    return $ Map.lookup name f

declareArgs :: [Arg] -> Env -> CheckerMonad Env
declareArgs (arg:args) env = do
    let (name, val) = case arg of {
        ArgVal _ (Value _ t name) -> (name, t);
        ArgRef _ t name -> (name, t)
    }
    env' <- declareVariable name val env
    declareArgs args env'
declareArgs [] env = return env

addError :: BNFC'Position -> ErrorState -> CheckerMonad ()
addError p err = lift $ throwE $ showPosition p ++ " " ++ err ++ ".\n"

isInt :: Type -> Bool
isInt (Int _) = True
isInt _ = False

isBool :: Type -> Bool
isBool (Bool _) = True
isBool _ = False

eqType :: Type -> Type -> Bool
eqType (Int _) (Int _) = True
eqType (Bool _) (Bool _) = True
eqType (Str _) (Str _) = True
eqType (Void _) (Void _) = True
eqType (Arr _ t1) (Arr _ t2) = t1 `eqType` t2
eqType (Fun _ args1 return1) (Fun _ args2 return2) = go args1 args2 && return1 `eqType` return2 where
    go (arg1:args1) (arg2:args2) = arg1 `eqType` arg2 && go args1 args2
    go [] [] = True
    go _ [] = False
    go [] _ = False
eqType _ _ = False

isLValue :: Expr -> Bool
isLValue (EVar _ _) = True
isLValue _ = False

eqArgs :: BNFC'Position -> [FnArg] -> [Expr] -> CheckerMonad Bool
eqArgs p (arg:args) (e:es) = do
    t <- evalExprType e
    otherArgsResult <- eqArgs p args es
    argResult <- case arg of {
        Ref t' -> do
            let l = isLValue e
            CM.unless l (addError p "Not an l-value")
            let eq = t `eqType` t'
            return $ l && eq
        ;
        NoRef t' -> return $ t `eqType` t'
    }
    return $ otherArgsResult && argResult
eqArgs _ [] [] = return True
eqArgs _ [] _ = return False
eqArgs _ _ [] = return False

showType :: Show a => Type' a -> String
showType (Int _) = "Int"
showType (Str _) = "String"
showType (Bool _) = "Bool"
showType (Void _) = "Void"
showType (Arr _ t) = show t ++ "[]"
showType (Tup _ ts) = "|" ++ go ts ++ "|" where
    go [t] = show t
    go (t:ts) = show t ++ ", " ++ show ts
showType (Fun _ args return) = "(" ++ go args ++ ") -> " ++ show return where
    go [arg] = show arg
    go (arg:args) = show arg ++ ", " ++ show args

showArgs :: [Type] -> String
showArgs args = "(" ++ go args ++ ")" where
    go [arg] = showType arg
    go (arg:args) = showType arg ++ ", " ++ go args

showFnArgs :: [FnArg] -> String
showFnArgs args = "(" ++ go args ++ ")" where
    go [Ref t] = "&" ++ showType t
    go [NoRef t] = showType t
    go ((Ref t):args) = "&" ++ showType t ++ ", " ++ go args
    go ((NoRef t):args) = showType t ++ ", " ++ go args

argToType :: FnArg -> Type
argToType (Ref t) = t
argToType (NoRef t) = t

argToFnArg :: Arg -> FnArg
argToFnArg (ArgVal _ (Value _ t _)) = NoRef t
argToFnArg (ArgRef _ t _) = Ref t

showPosition :: BNFC'Position -> String
showPosition (Just (i1, i2)) = "(" ++ show i1 ++ ":" ++ show i2 ++ ")"
showPosition Nothing = ""

evalArrType :: Type -> [Expr] -> CheckerMonad Type
evalArrType t (e:es) = do
    e' <- evalExprType e
    if not (e' `eqType` t)
        then addError (hasPosition t) ("Values inside array have different types: " ++ showType t ++ " and " ++ showType e') >> return (Void BNFC'NoPosition)
        else evalArrType t es
evalArrType t [] = return $ Arr (hasPosition t) t

evalExprType :: Expr -> CheckerMonad Type
evalExprType (EVar p name) = getVariable p name
evalExprType (ELitInt p _) = return $ Int p
evalExprType (ELitFalse p) = return $ Bool p
evalExprType (ELitTrue p) = return $ Bool p
evalExprType (ERel p e1 _ e2) = do
    e1' <- evalExprType e1
    e2' <- evalExprType e2
    CM.unless (e1' `eqType` e2') $ addError p $ "Left side of comparison is type " ++ showType e1' ++ ", but right side is type " ++ showType e2'
    return $ Bool p
evalExprType (EArr _ (e:es)) = do
    e' <- evalExprType e
    evalArrType e' es
evalExprType (EAdd p e1 _ e2) = do
    e1' <- evalExprType e1
    e2' <- evalExprType e2
    if not (isInt e1') || not (isInt e2')
        then addError p "Non-integer expression inside add" >> return (Void BNFC'NoPosition)
        else return $ Int p
evalExprType (EMul p e1 _ e2) = do
    e1' <- evalExprType e1
    e2' <- evalExprType e2
    if not (isInt e1') || not (isInt e2')
        then addError p "Non-integer expression inside mul" >> return (Void BNFC'NoPosition)
        else return $ Int p
evalExprType (EAnd p e1 e2) = do
    e1' <- evalExprType e1
    e2' <- evalExprType e2
    if not (isBool e1') || not (isBool e2')
        then addError p "Non-boolean expression inside and" >> return (Void BNFC'NoPosition)
        else return $ Bool p
evalExprType (EOr p e1 e2) = do
    e1' <- evalExprType e1
    e2' <- evalExprType e2
    if not (isBool e1') || not (isBool e2')
        then addError p "Non-boolean expression inside or" >> return (Void BNFC'NoPosition)
        else return $ Bool p
evalExprType (EString p _) = return $ Str p
evalExprType (Neg p e) = do
    e' <- evalExprType e
    if not (isInt e')
        then addError p "Negated non-integer expression" >> return (Void BNFC'NoPosition)
        else return $ Int p
evalExprType (Not p e) = do
    e' <- evalExprType e
    if not (isBool e')
        then addError p "Logical NOT applied to a non-boolean expression" >> return (Void BNFC'NoPosition)
        else return $ Bool p
evalExprType (EApp p fnName fnArgs) = do
    var <- getFunction fnName
    if isNothing var
        then addError p ("Function of name " ++ show fnName ++ " was not found") >> return (Void BNFC'NoPosition)
        else do
            let Just (Func args returnType) = var
            argTypesMatch <- eqArgs p args fnArgs
            types <- mapM evalExprType fnArgs
            if argTypesMatch
                then return returnType
                else addError p ("Function arguments do not match. Expected " ++ showFnArgs args ++ ", but got " ++ showArgs types) >> return (Void BNFC'NoPosition);

checkStmt :: Stmt -> CheckerMonad ()
checkStmt (Empty _) = return ()
checkStmt (Cond p e s) = do
    e' <- evalExprType e
    case e' of {
        Bool _ -> return ();
        _ -> addError p "Non-bool expression inside if condition"
    }
    checkStmt s
checkStmt (CondElse p e s1 s2) = do
    e' <- evalExprType e
    case e' of {
        Bool _ -> return ();
        _ -> addError p "Non-bool expression inside if condition"
    }
    checkStmt s1
    checkStmt s2
checkStmt (While p e s) = do
    e' <- evalExprType e
    case e' of {
        Bool _ -> return ();
        _ -> addError p "Non-bool expression inside while condition"
    }
    checkStmt s
checkStmt (Ass p (LVar p2 name) e) = do
    var <- getVariable p2 name
    e' <- evalExprType e
    CM.unless (e' `eqType` var) $ addError p ("Invalid assignment to variable " ++ show name ++".\nTried to assign " ++ showType e' ++ " to " ++ showType var)
checkStmt (Ass p (LArr p2 name e1) e2) = do
    arr <- getVariable p2 name
    indexType <- evalExprType e1
    assignType <- evalExprType e2
    if not (isInt indexType)
        then addError p ("Tried to access array index with a non-Int type: " ++ showType indexType ++ ".\n")
        else case arr of {
            Arr _ arrType -> CM.unless (assignType `eqType` arrType) $ addError p ("Array type mismatch: assigning " ++ showType assignType ++ " to array of " ++ showType arrType ++ ".\n");
            _ -> addError p ("Tried to access non-array variable " ++ show arr ++ " as array. \n")
        }
checkStmt (Print _ e) = CM.void $ evalExprType e
checkStmt (Break _) = return ()
checkStmt (Cont _) = return ()
checkStmt (Decr p name) = do
    var <- getVariable p name
    case var of {
        Int _ -> return ();
        _ -> addError p $ "Tried to decrement non-integer variable " ++ show name
    }
    return ()
checkStmt (Incr p name) = do
    var <- getVariable p name
    case var of {
        Int _ -> return ();
        _ -> addError p $ "Tried to increment non-integer variable " ++ show name
    }
    return ()
checkStmt (BStmt p block) = checkBlock block
checkStmt (Ret p e) = do
    e' <- evalExprType e
    ret <- getReturnType
    CM.unless (e' `eqType` ret) $ addError p ("Expected the return type to be " ++ showType ret ++ ", but found " ++ showType e')
checkStmt (VRet p) = do
    ret <- getReturnType
    CM.unless (Void BNFC'NoPosition `eqType` ret) $ addError p ("Used return with no type in a function with return type " ++ showType ret)
checkStmt (SExp _ e) = CM.void $ evalExprType e

declareVariables :: BNFC'Position -> Type -> [Item] -> Env -> CheckerMonad Env
declareVariables p t ((NoInit _ name):defs) env = declareVariable name t env >>= declareVariables p t defs
declareVariables p t ((Init _ name e):defs) env = do
    t' <- evalExprType e
    CM.unless (t' `eqType` t) (addError p $ "Result of the expression doesn't match the declared type.\n Declared type: " ++ showType t ++ ". Instead got: " ++ showType t')
    nextEnv <- declareVariable name t env
    declareVariables p t defs nextEnv
declareVariables _ _ [] env = return env

checkBlock :: Block -> CheckerMonad ()
checkBlock (Block p stmts) = do
    state <- get
    localEnv id $ go stmts
        where
        go :: [Stmt] -> CheckerMonad ()
        go (stmt:stmts) = do
            env <- askChecker
            case stmt of {
                Decl p' t defs -> declareVariables p' t defs env >>= (\env' -> localEnv (const env') (go stmts));
                _ -> checkStmt stmt >> go stmts
            }
        go [] = return ()

checkDef :: TopDef -> CheckerMonad ()
checkDef (FnDef _ returnType fnName args fnBody) = do
    oldRet <- getReturnType
    env <- askChecker
    nextEnv <- declareArgs args env
    putReturnType returnType
    localEnv (const nextEnv) (checkBlock fnBody)
    putReturnType oldRet
checkDef (VarDef p varType varName e) = do
    e' <- evalExprType e
    CM.unless (e' `eqType` varType) $ addError p ("Variable " ++ show varName ++ " has type " ++ showType varType ++ ", but the expression assigned has type " ++ showType e')

declGlobal :: TopDef -> Env -> CheckerMonad Env
declGlobal (VarDef _ varType varName _) env = declareVariable varName varType env
declGlobal (FnDef _ returnType fnName args fnBody) Env { fnEnv = f, varEnv = v } = do
    let fnArgs = Prelude.map argToFnArg args
    let fun = Func fnArgs returnType
    let newF = Map.insert fnName fun f
    return $ Env { varEnv = v, fnEnv = newF }

declGlobals :: Program -> Env -> CheckerMonad Env
declGlobals (Program p (def:defs)) env = declGlobal def env >>= declGlobals (Program p defs)
declGlobals (Program _ []) env = return env

checkDefs :: Program -> CheckerMonad ()
checkDefs (Program p (def:defs)) = checkDef def >> checkDefs (Program p defs)
checkDefs (Program _ []) = return ()

typeCheck :: Program -> CheckerMonad ()
typeCheck p = do
    env <- declGlobals p emptyEnv
    let Env { fnEnv = f } = env
    let maybeMain = Map.lookup (Ident "main") f
    CM.when (isNothing maybeMain) (addError BNFC'NoPosition "No function named \"main\" in the program")
    localEnv (const env) (checkDefs p)
