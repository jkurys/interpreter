module Interpreter(printXD) where

printXD :: (Show a) => a -> IO()
printXD tree = print $ show tree