{-# LANGUAGE TypeFamilies #-}
module Main (main) where

import Data.List (nub)
import Compiler (defEnv)
import TuringMachine (TuringMachine(..))
import UTM  as U
import UTMEncoding (encode, decodeConfiguration)
import UTMEval (eval)
import UTMProgram (utm)

import TM1
import TM2
import TM3

data UTMTarget = UTMTarget

data UTMState = Run U.Q
              | ReturnL U.Q
  deriving (Show, Eq)

delta :: U.Delta
(_, delta) = utm defEnv

instance TuringMachine UTMTarget where
  type State  UTMTarget = UTMState
  type Symbol UTMTarget = U.S

  states _  = nub (    [Run q | ((q, _), _) <- delta]
                    ++ [Run q | (_, (q, _)) <- delta]
                    ++ [ReturnL q | (_, (q, _)) <- delta]
                  )
  symbols _ = U.allSymbols

  initialState _   = Run (U.S 0)
  blankSymbol _    = U.B
  transition _ (Run q) s = case lookup (q, s) delta of
    Just (q', U.Move d)   -> Just (Run q', s, d)
    Just (q', U.Write s') -> Just (ReturnL q', s', U.R)
    Just (q', U.Nop)      -> Just (ReturnL q', s,  U.R)
    Nothing               -> Nothing
  transition _ (ReturnL q) s = Just (Run q, s, U.L)

main :: IO ()
main = do
  putStrLn "=== TM1 ==="
  let tape1b = encode TM1 ([TM1.One], TM1.One, [])
  putStrLn $ "BEGIN: " ++ show (decodeConfiguration TM1 tape1b)
  let tape1e = UTMEval.eval (S 0, delta) tape1b
  putStrLn $ "END:   " ++ show (decodeConfiguration TM1 tape1e)

  putStrLn "=== TM2 ==="
  let tape2b = encode TM2 ([TM2.Empty, TM2.Empty], TM2.Empty, [TM2.Empty, TM2.Done])
  putStrLn $ "BEGIN: " ++ show (decodeConfiguration TM2 tape2b)
  let tape2e = UTMEval.eval (S 0, delta) tape2b
  putStrLn $ "END:   " ++ show (decodeConfiguration TM2 tape2e)

  putStrLn "=== TM3 ==="
  let tape3b = encode TM3 ([], TM3.A, [TM3.B, TM3.C])
  putStrLn $ "BEGIN: " ++ show (decodeConfiguration TM3 tape3b)
  let tape3e = UTMEval.eval (S 0, delta) tape3b
  putStrLn $ "END:   " ++ show (decodeConfiguration TM3 tape3e)

  putStrLn "=== TM3 over UTM over UTM ==="
  let tape4b = encode UTMTarget tape3b
  let (_, innerb) = decodeConfiguration UTMTarget tape4b
  putStrLn $ "BEGIN:   " ++ show (decodeConfiguration UTMTarget tape4b)
  putStrLn $ "- INNER: " ++ show (decodeConfiguration TM3 innerb)
  let tape4e = UTMEval.eval (S 0, delta) tape4b
  let (_, innere) = decodeConfiguration UTMTarget tape4e
  putStrLn $ "END:     " ++ show (decodeConfiguration UTMTarget tape4e)
  putStrLn $ "- INNER: " ++ show (decodeConfiguration TM3 innere)
