module UTMEval (eval, run) where

import qualified UTM

hd :: [UTM.S] -> UTM.S
hd []    = UTM.B
hd (h:_) = h

tl :: [UTM.S] -> [UTM.S]
tl []    = []
tl (_:t) = t

cons :: (UTM.S, [UTM.S]) -> [UTM.S]
cons (UTM.B, []) = []
cons (h,     t)  = h:t

moveL :: UTM.Tape -> UTM.Tape
moveL (ls, h, rs) = (tl ls, hd ls, cons (h, rs))

moveR :: UTM.Tape -> UTM.Tape
moveR (ls, h, rs) = (cons (h, ls), hd rs, tl rs)

move :: UTM.D -> UTM.Tape -> UTM.Tape
move UTM.L = moveL
move UTM.R = moveR

exec :: UTM.Delta -> (UTM.Q, UTM.Tape) -> (UTM.Q, UTM.Tape)
exec delta config@(q, tape@(ls, h, rs)) =
  case lookup (q, h) delta of
    Just (q', UTM.Write s) -> exec delta (q', (ls, s, rs))
    Just (q', UTM.Move d)  -> exec delta (q', move d (ls, h, rs))
    Just (q', UTM.Nop)     -> exec delta (q', tape)
    Nothing                -> config

{-| プログラムを停止するまで実行し、最終状態とテープを返す。
遷移が定義されていない状態で停止するため、呼び出し側は停止状態を観察できる。

>>> run UTM.addOne ([], UTM.I, [])
(S 2,([],I,[O]))
-}
run :: UTM.Program -> UTM.Tape -> (UTM.Q, UTM.Tape)
run (state, delta) tape = exec delta (state, tape)

eval :: (UTM.Q, UTM.Delta) -> UTM.Tape -> UTM.Tape
eval program tape = snd (run program tape)
