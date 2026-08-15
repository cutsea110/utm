module Main (main) where

import Test.DocTest (doctest)

main :: IO ()
main = doctest
  [ "-isrc"
  , "src/Compiler.hs"
  , "src/Eval.hs"
  , "src/UTM.hs"
  , "src/TM1.hs"
  ]
