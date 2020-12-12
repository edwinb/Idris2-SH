module Main

import System.Concurrency.Raw

main : IO ()
main = do
    sema <- makeSemaphore 0
    fork $ do
        putStrLn "Hello"
        semaphorePost sema
        semaphorePost sema
    semaphoreWait sema
    semaphoreWait sema
    putStrLn "Goodbye"
