module Main (main) where

import Eval (eval)
import TM   (Tape, S(..), addOne)

t :: Tape
t = ([I, I, I], I, [])

r :: Tape
r = eval addOne t

main :: IO ()
main = print $ pair conv (t, r)
  where
    pair f (x, y) = (f x,f y)
    conv (ls, c, rs) = reverse ls ++ c:rs
