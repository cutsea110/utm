module Eval (eval) where

import qualified TM

hd :: [TM.S] -> TM.S
hd []    = TM.B
hd (h:_) = h

tl :: [TM.S] -> [TM.S]
tl []    = []
tl (_:t) = t

cons :: (TM.S, [TM.S]) -> [TM.S]
cons (TM.B, t) = t
cons (h,    t) = h:t

moveL :: TM.Tape -> TM.Tape
moveL (ls, h, rs) = (tl ls, hd ls, cons (h, rs))

moveR :: TM.Tape -> TM.Tape
moveR (ls, h, rs) = (cons (h, ls), hd rs, tl rs)

move :: TM.D -> TM.Tape -> TM.Tape
move TM.L = moveL
move TM.R = moveR

exec :: TM.Delta -> (TM.Q, TM.Tape) -> TM.Tape
exec delta (q, tape@(ls, h, rs)) =
  case lookup (q, h) delta of
    Just (q', TM.Write s) -> exec delta (q', (ls, s, rs))
    Just (q', TM.Move d)  -> exec delta (q', move d (ls, h, rs))
    Nothing               -> tape

eval :: (TM.Q, TM.Delta) -> TM.Tape -> TM.Tape
eval (state, delta) tape = exec delta (state, tape)
