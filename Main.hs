module Main where

import Hspl
import System.IO

append :: [Rule]
append =
  [ ((comp "append" [tNil, tVar "X", tVar "X"]), [])
  , ((comp "append" [tCons (tVar "X") (tVar "Y"), tVar "Z", tCons (tVar "X") (tVar "W")]),
     [(comp "append" [tVar "Y", tVar "Z", tVar "W"])])]

printResults :: [Subst] -> IO ()
printResults [] = putStrLn "false."
printResults (s : ss) = do
  putStr (prettySubst s "")
  hFlush stdout
  inkey where
    inkey = do
      c <- getChar
      case c of
        ';' -> putStr "\n" >> printResults ss
        '.' -> putStr "\n"
        _ -> inkey

main = printResults (evaltop (comp "append" [tVar "X", tVar "Y", tList [TInt 1, TInt 2, TInt 3]]) append)
