import ParMylang   ( pProgram, myLexer )
import System.Environment(getArgs)
import AbsMylang
import qualified Data.Map as Map
import Control.Monad.Trans.State.Lazy
import qualified Control.Monad as CM
import qualified TypeChecker as TC
import Data.Functor.Identity
import Data.Maybe (isNothing)
import Control.Monad.Trans.Except
import TypeChecker (runCheckerMonad)
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import System.IO(hPutStr, stderr)

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

data Env = Env {
    fnEnv :: FunctionEnv,
    varEnv :: VarEnv
}

emptyEnv :: Env
emptyEnv = Env { varEnv = Map.empty, fnEnv = Map.empty }

data IntState = IntState {
    varState :: VarState,
    returnState :: Maybe VarValue,
    nextLoc :: Location
}

type Error = String

type InterpreterMonadT s e r m a = StateT s (ExceptT e (ReaderT r m)) a

runInterpreterMonadT :: (Monad m) => InterpreterMonadT s e r m a -> s -> r -> m (Either e a)
runInterpreterMonadT m = runReaderT . runExceptT . evalStateT m

type InterpreterMonad a = InterpreterMonadT IntState Error Env IO a

runInterpreterMonad :: InterpreterMonad a -> IntState -> Env -> IO (Either Error a)
runInterpreterMonad = runInterpreterMonadT

throwRuntimeError :: Error -> InterpreterMonad ()
throwRuntimeError err = lift $ throwE $ err ++ ".\n"

askInt :: InterpreterMonad Env
askInt = lift $ lift ask

localEnv :: (Env -> Env) -> InterpreterMonad a -> InterpreterMonad a
localEnv = mapStateT . mapExceptT . local

simplifyArg :: Arg -> FnArg
simplifyArg (ArgVal _ (Value _ _ name)) = NoRef name
simplifyArg (ArgRef _ _ name) = Ref name

getVariable :: Ident -> InterpreterMonad VarValue
getVariable name = do
    IntState { varState = s } <- get
    Env { varEnv = v, fnEnv = f } <- askInt
    let loc = Map.lookup name v

    case loc of {
        Nothing -> addPrint ("Variable " ++ show name ++ " was not initialized.\n") >> return VoidVal;
        Just varLoc -> do
            let varType = Map.lookup varLoc s
            case varType of {
                Nothing -> addPrint "Unexpected error happened.\n" >> return VoidVal;
                Just t -> return t
            }
    }

getFunction :: Ident -> Env -> InterpreterMonad (Maybe Function)
getFunction name env = do
    let Env { varEnv = v, fnEnv = f } = env
    return $ Map.lookup name f

declareVariable :: Ident -> VarValue -> Env -> InterpreterMonad Env
declareVariable name val Env { varEnv = v, fnEnv = f } = do
    IntState { varState = s, returnState = r, nextLoc = n } <- get
    let newV = Map.insert name n v
    let newS = Map.insert n val s
    let newEnv = Env { varEnv = newV, fnEnv = f }
    put IntState { varState = newS, returnState = r, nextLoc = n + 1 }
    return newEnv

declareReference :: Ident -> Ident -> Env -> InterpreterMonad Env
declareReference oldName newName Env { varEnv = v, fnEnv = f } = do
    let Just loc = Map.lookup oldName v
    let newV = Map.insert newName loc v
    let newEnv = Env { varEnv = newV, fnEnv = f }
    return newEnv


modifyVariable :: Ident -> VarValue -> InterpreterMonad ()
modifyVariable name val = do
    IntState { varState = s, returnState = r, nextLoc = n } <- get
    Env { varEnv = v, fnEnv = f } <- askInt
    let Just loc = Map.lookup name v
    let newS = Map.insert loc val s
    put IntState { varState = newS, returnState = r, nextLoc = n }

getLValue :: Expr -> Ident
getLValue (EVar _ s) = s

declareArguments :: [FnArg] -> [Expr] -> Env -> InterpreterMonad Env
declareArguments ((Ref name):args) (e:es) env = do
    val <- evalExp e
    env' <- declareReference (getLValue e) name env
    declareArguments args es env'
declareArguments ((NoRef name):args) (e:es) env = do
    val <- evalExp e
    env' <- declareVariable name val env
    declareArguments args es env'

declareArguments [] [] env = return env

addPrint :: String -> InterpreterMonad ()
addPrint printStr = lift $ lift $ lift $ putStr printStr

getReturnState :: InterpreterMonad (Maybe VarValue)
getReturnState = do
    IntState { returnState = r } <- get
    return r

putReturnState :: VarValue -> InterpreterMonad ()
putReturnState newR = do
    IntState { varState = v, returnState = r, nextLoc = n } <- get
    put IntState { varState = v, returnState = Just newR, nextLoc = n }

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
    env <- askInt
    maybeRet <- getReturnState
    let Just oldRet = maybeRet
    fun <- getFunction fnName env
    let Just (Func argNames block) = fun
    nextEnv <- declareArguments argNames es env
    ret <- localEnv (const nextEnv) (execFn block)
    putReturnState oldRet
    return ret

execStmt :: Stmt -> InterpreterMonad ()
execStmt (Empty _) = return ()
execStmt (BStmt _ block) = execBlock block
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
    CM.when (e' == VoidVal) (throwRuntimeError "Use of uninitialized variable")
    addPrint $ show e'
execStmt (Ret _ e) = do
    e' <- evalExp e
    putReturnState e'
execStmt (VRet _) = do
    putReturnState VoidVal

execFn :: Block -> InterpreterMonad VarValue
execFn (Block p stmts) = do
    go stmts
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

execDecl :: [Item] -> Env -> InterpreterMonad Env
execDecl ((NoInit _ name):defs) env = declareVariable name VoidVal env >>= execDecl defs
execDecl ((Init _ name e):defs) env = do
    val <- evalExp e
    declareVariable name val env >>= execDecl defs
execDecl [] env = return env

execBlock :: Block -> InterpreterMonad ()
execBlock (Block p stmts) = do
    env <- askInt
    CM.void $ go stmts env
        where
        go :: [Stmt] -> Env -> InterpreterMonad Env
        go (stmt:stmts) env = do
            case stmt of {
                Decl _ _ items -> execDecl items env >>= (\env' -> localEnv (const env') (go stmts env'));
                _ -> execStmt stmt >> go stmts env
            }
        go [] env = return env

declGlobal :: TopDef -> Env -> InterpreterMonad Env
declGlobal (FnDef _ _ fnName args fnBody) env = do
    let Env { varEnv = v, fnEnv = f } = env
    let fnArgs = Prelude.map simplifyArg args
    let fun = Func fnArgs fnBody
    let newF = Map.insert fnName fun f
    return Env { varEnv = v, fnEnv = newF }
declGlobal (VarDef _ _ varName e) env = do
    newVarValue <- evalExp e
    declareVariable varName newVarValue env

declGlobals :: [TopDef] -> Env -> InterpreterMonad Env
declGlobals (def:defs) env = declGlobal def env >>= declGlobals defs
declGlobals [] env = return env

runProgram :: Program -> InterpreterMonad ()
runProgram (Program _ defs) = do
    env <- declGlobals defs emptyEnv
    maybeFun <- getFunction (Ident "main") env
    let Just (Func _ block) = maybeFun
    localEnv (const env) (execBlock block)

main = do
    args <- getArgs
    case args of
        [path] -> do
            file <- readFile path
            let lex = myLexer file
            case pProgram lex of
                Left err -> error err
                Right program -> do
                    let result = runCheckerMonad (TC.typeCheck program) TC.CheckerState { TC.varState = Map.empty, TC.nextLoc = 0, TC.returnType = Void BNFC'NoPosition } TC.emptyEnv
                    case result of {
                        Left err -> hPutStr stderr err;
                        Right _ -> do
                            result <- runInterpreterMonad (runProgram program) IntState { varState = Map.empty, returnState = Nothing, nextLoc = 0 } emptyEnv
                            case result of {
                                Left err -> hPutStr stderr err;
                                Right _ -> return ()
                            }
                    }
        _ -> error "no file provided"

        --BRAKUJE DZIELENIA PRZEZ ZERO