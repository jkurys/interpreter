import ParMylang   ( pProgram, myLexer )
import System.Environment(getArgs)
import AbsMylang
import qualified Data.Map as Map
import Control.Monad.Trans.State.Lazy
import qualified Control.Monad as CM
import qualified TypeChecker as TC
import Data.Functor.Identity
import Data.Maybe (isNothing)
import Control.Monad.Trans.Except (runExceptT)
import TypeChecker (runCheckerMonad)

data FnArg = NoRef Ident | Ref Ident deriving Show

data Function = Func [FnArg] Block deriving Show

type FunctionEnv = Map.Map Ident Function

data VarValue = IntVal Integer | BoolVal Bool | StrVal String | VoidVal | ArrVal [VarValue] deriving Eq

instance Show VarValue where
    show (IntVal n) = show n
    show (BoolVal b) = show b
    show (StrVal s) = s
    show VoidVal = ""
    show (ArrVal arr) = show arr

type VarState = Map.Map Location VarValue

type Location = Int

type VarEnv = Map.Map Ident Location

data IntState = IntState {
    fnEnv :: FunctionEnv,
    varState :: VarState,
    varEnv :: VarEnv,
    printState :: String,
    returnState :: Maybe VarValue
}

instance Show IntState where
    show IntState {printState = p} = p

type Error = String

type InterpreterMonad = State IntState

simplifyArg :: Arg -> FnArg
simplifyArg (ArgVal _ (Value _ _ name)) = NoRef name
simplifyArg (ArgRef _ _ name) = Ref name

getVariable :: Ident -> InterpreterMonad VarValue
getVariable name = do
    IntState { varState = s, varEnv = env, printState = p, fnEnv = f } <- get
    let loc = Map.lookup name env

    case loc of {
        Nothing -> addPrint ("Variable " ++ show name ++ " was not initialized.\n") >> return VoidVal;
        Just varLoc -> do
            let varType = Map.lookup varLoc s
            case varType of {
                Nothing -> addPrint "Unexpected error happened.\n" >> return VoidVal;
                Just t -> return t
            }
    }

getEnv :: InterpreterMonad VarEnv
getEnv = do
    IntState { varState = s, varEnv = env, printState = p, fnEnv = f } <- get
    return env

putEnv :: VarEnv -> InterpreterMonad ()
putEnv newEnv = do
    IntState { varState = s, varEnv = env, printState = p, fnEnv = f, returnState = r } <- get
    put IntState { varState = s, varEnv = newEnv, printState = p, fnEnv = f, returnState = r }

getFunction :: Ident -> InterpreterMonad Function
getFunction fnName = do
    IntState { fnEnv = f } <- get
    let Just fn = Map.lookup fnName f
    return fn

declareFunction :: Ident -> Function -> InterpreterMonad ()
declareFunction name fn = do
    IntState { varState = s, varEnv = env, printState = p, fnEnv = f, returnState = r } <- get
    let newF = Map.insert name fn f
    put IntState { varState = s, varEnv = env, printState = p, fnEnv = newF, returnState = r }

declareVariable :: Ident -> VarValue -> InterpreterMonad ()
declareVariable name val = do
    IntState { varState = s, varEnv = env, printState = p, fnEnv = f, returnState = r } <- get
    let newLoc = Map.size env
    let newEnv = Map.insert name newLoc env
    let newS = Map.insert newLoc val s
    put IntState { varState = newS, varEnv = newEnv, printState = p, fnEnv = f, returnState = r }

declareReference :: Ident -> Ident -> InterpreterMonad ()
declareReference oldName newName = do
    IntState { varState = s, varEnv = env, printState = p, fnEnv = f, returnState = r } <- get
    let Just loc = Map.lookup oldName env
    let newEnv = Map.insert newName loc env
    put IntState { varState = s, varEnv = newEnv, printState = p, fnEnv = f, returnState = r }

modifyVariable :: Ident -> VarValue -> InterpreterMonad ()
modifyVariable name val = do
    IntState { varState = s, varEnv = env, printState = p, fnEnv = f, returnState = r } <- get
    let Just loc = Map.lookup name env
    let newS = Map.insert loc val s
    put IntState { varState = newS, varEnv = env, printState = p, fnEnv = f, returnState = r }

getLValue :: Expr -> Ident
getLValue (EVar _ s) = s

declareArguments :: [FnArg] -> [Expr] -> InterpreterMonad ()
declareArguments (arg:args) (e:es) = do
    val <- evalExp e
    case arg of {
        Ref name -> declareReference (getLValue e) name;
        NoRef name -> declareVariable name val
    }
    declareArguments args es
declareArguments [] [] = return ()

addPrint :: String -> InterpreterMonad ()
addPrint printStr = do
    IntState { varState = v, varEnv = env, fnEnv = f, printState = p, returnState = r } <- get
    let newP = p ++ printStr
    put IntState { varState = v, varEnv = env, fnEnv = f, printState = newP, returnState = r }

getReturnState :: InterpreterMonad (Maybe VarValue)
getReturnState = do
    IntState { returnState = r } <- get
    return r

putReturnState :: VarValue -> InterpreterMonad ()
putReturnState newR = do
    IntState { varState = v, varEnv = env, fnEnv = f, printState = p, returnState = r } <- get
    put IntState { varState = v, varEnv = env, fnEnv = f, printState = p, returnState = Just newR }

evalExp :: Expr -> InterpreterMonad VarValue
evalExp (EVar _ varName) = getVariable varName
evalExp (ELitInt _ n) = return $ IntVal n
evalExp (ELitFalse _) = return $ BoolVal False
evalExp (ELitTrue _) = return $ BoolVal True
evalExp (EString _ s) = return $ StrVal s
evalExp (Neg _ e) = evalExp e >>= (\(IntVal e') -> return $ IntVal ((-1) * e'))
evalExp (Not _ e) = evalExp e >>= (\(BoolVal e') -> return $ BoolVal (not e'))
evalExp (EAdd _ e1 op e2) = do
    e1' <- evalExp e1
    e2' <- evalExp e2
    let IntVal n1 = e1'
    let IntVal n2 = e2'
    let f = case op of {
        (Plus _) -> (+);
        (Minus _) -> (-)
    }
    return $ IntVal (n1 `f` n2)
evalExp (EMul _ e1 op e2) = do
    e1' <- evalExp e1
    e2' <- evalExp e2
    let IntVal n1 = e1'
    let IntVal n2 = e2'
    let f = case op of {
        (Times _) -> (*);
        (Div _) -> div;
        (Mod _) -> mod
    }
    return $ IntVal (n1 `f` n2)
evalExp (EEmptyArr _) = return $ ArrVal []
evalExp (EArr p (e:es)) = do
    IntState{ varState = v } <- get
    e' <- evalExp e
    prevResult <- evalExp (EArr p es)
    let ArrVal es' = prevResult
    return $ ArrVal (e':es')
evalExp (EArr _ []) = return $ ArrVal []
evalExp (EAcc _ arrName e) = do
    e' <- evalExp e
    let IntVal index = e'
    arr <- getVariable arrName
    let ArrVal array = arr
    return $ if index >= toInteger (length array) || index < 0 then VoidVal else array !! fromInteger index
evalExp (ERel _ e1 (EQU _) e2) = do
    e1' <- evalExp e1
    e2' <- evalExp e2
    return $ BoolVal $ e1' == e2'
evalExp (ERel _ e1 op e2) = do
    e1' <- evalExp e1
    e2' <- evalExp e2
    let IntVal n1 = e1'
    let IntVal n2 = e2'
    let f = case op of {
        (LE _) -> (<=);
        (LTH _) -> (<);
        (GE _) -> (>=);
        (GTH _) -> (>)
    }
    return $ BoolVal (n1 `f` n2)
evalExp (EAnd _ e1 e2) = evalExp e1 >>= (\(BoolVal b1) -> evalExp e2 >>= (\(BoolVal b2) -> return $ BoolVal $ b1 && b2))
evalExp (EOr _ e1 e2) = evalExp e1 >>= (\(BoolVal b1) -> evalExp e2 >>= (\(BoolVal b2) -> return $ BoolVal $ b1 || b2))
evalExp (EApp _ fnName es) = do
    Func argNames block <- getFunction fnName
    oldEnv <- getEnv
    declareArguments argNames es
    ret <- execFn block
    putEnv oldEnv
    putReturnState VoidVal
    return ret

-- evalExp _ = return VoidVal

execStmt :: Stmt -> InterpreterMonad ()
execStmt (Empty _) = return ()
execStmt (BStmt _ block) = execBlock block
execStmt (Decl _ t (item:items)) = do
    state <- get
    let (varName, newVarVal) = case item of {
        (NoInit _ name) -> (name, VoidVal);
        (Init _ name e) -> (name, evalState (evalExp e) state)
    }
    declareVariable varName newVarVal
execStmt (Ass _ (LVar _ varName) e) = do
    newVarVal <- evalExp e
    modifyVariable varName newVarVal
execStmt (Incr _ varName) = do
    oldVar <- getVariable varName
    let IntVal oldVarVal = oldVar
    let newVarVal = IntVal $ oldVarVal + 1
    modifyVariable varName newVarVal
execStmt (Decr _ varName) = do
    oldVar <- getVariable varName
    let IntVal oldVarVal = oldVar
    let newVarVal = IntVal $ oldVarVal - 1
    modifyVariable varName newVarVal
execStmt (Cond _ e s) = evalExp e >>= (\(BoolVal b) -> CM.when b $ execStmt s)
execStmt (CondElse _ e s1 s2) = evalExp e >>= (\(BoolVal b) -> if b then execStmt s1 else execStmt s2)
execStmt (While p e s) = evalExp e >>= (\(BoolVal b) -> CM.when b $ execStmt s >> execStmt (While p e s))
execStmt (SExp _ e) = CM.void $ evalExp e
execStmt (Print _ e) = do
    e' <- evalExp e
    addPrint $ show e'
execStmt (Ret _ e) = do
    e' <- evalExp e
    putReturnState e'
execStmt (VRet _) = do
    putReturnState VoidVal
-- execStmt _ = return ()

execFn :: Block -> InterpreterMonad VarValue
execFn (Block p stmts) = do
    oldEnv <- getEnv
    go stmts
    putEnv oldEnv
    maybeRet <- getReturnState
    let Just ret = maybeRet
    return ret
        where
        go :: [Stmt] -> InterpreterMonad ()
        go (stmt:stmts) = do
            execStmt stmt
            maybeRet <- getReturnState
            CM.when (isNothing maybeRet) (go stmts)
        go [] = return ()

execBlock :: Block -> InterpreterMonad ()
execBlock (Block p stmts) = do
    oldEnv <- getEnv
    go stmts
    putEnv oldEnv
        where
        go :: [Stmt] -> InterpreterMonad ()
        go (stmt:stmts) = do
            execStmt stmt
            go stmts
        go [] = return ()

topDef :: TopDef -> InterpreterMonad ()
topDef (VarDef _ _ varName e) = do
    newVarValue <- evalExp e
    declareVariable varName newVarValue
topDef (FnDef _ _ fnName args fnBody) = do
    let args' = map simplifyArg args
    declareFunction fnName (Func args' fnBody)

runProgram :: Program -> InterpreterMonad ()
runProgram (Program _ []) = do
    Func _ block <- getFunction (Ident "main")
    execBlock block

runProgram (Program p (def: defs)) = do
    topDef def
    runProgram (Program p defs)

main = do
    args <- getArgs
    case args of
        [path] -> do
            file <- readFile path
            let lex = myLexer file
            case pProgram lex of
                Left err -> error err
                Right program -> do
                    -- let errors = show $ runIdentity $ execState (TC.typeCheck program) $ Identity TC.CheckerState { TC.varState = Map.empty, TC.varEnv = Map.empty, TC.fnEnv = Map.empty, TC.errorState = "", TC.nextLoc = 0, TC.returnType = Void BNFC'NoPosition }
                    let result = runCheckerMonad (TC.typeCheck program) TC.CheckerState { TC.varState = Map.empty, TC.errorState = "", TC.nextLoc = 0, TC.returnType = Void BNFC'NoPosition } TC.Env{ TC.fnEnv = Map.empty, TC.varEnv = Map.empty }
                    case result of {
                        Left err -> putStr err;
                        Right _ -> print $ runIdentity $ execStateT (runProgram program) IntState { fnEnv = Map.empty, varState = Map.empty, varEnv = Map.empty, printState = "", returnState = Nothing }
                    }
        _ -> error "no file provided"

        --POTENCJALNIE KWADRATOWE DODAWANIE NAPISÓW
        --BRAKUJE DZIELENIA PRZEZ ZERO
        --SPRAWDZIĆ CZY MOŻNA ODWOŁYWAĆ SIĘ DO ZMIENNYCH W FUNKCJI