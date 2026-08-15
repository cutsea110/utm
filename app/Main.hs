module Main (main) where

import UTM  (Tape, S(..), addOne)
import UTMEval (eval)

t :: Tape
t = ([I, I, I], I, [])

r :: Tape
r = eval addOne t

main :: IO ()
main = print $ pair conv (t, r)
  where
    pair f (x, y) = (f x,f y)
    conv (ls, c, rs) = reverse ls ++ c:rs
