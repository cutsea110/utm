module Main (main) where

import Test.DocTest (doctest)

main :: IO ()
main = doctest
  [ "-isrc"
  , "src/Compiler.hs"
  , "src/UTM.hs"
  , "src/UTMEval.hs"
  , "src/UTMEncoding.hs"
  , "src/TuringMachine.hs"
  , "src/TM1.hs"
  ]
