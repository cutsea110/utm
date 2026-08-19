module UTMEval (eval, run, Result(..)) where

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

data Result
  = Finished UTM.Tape
  | Failed UTM.HaltReason UTM.Tape
  | Stuck UTM.Q UTM.Tape
  deriving (Show, Eq)

{-| プログラムを停止するまで実行し、停止結果を返す。
'UTM.TargetHalted' は対象 TM の正常終了、その他の 'UTM.HaltReason' は UTM 側の異常終了として扱う。

>>> import qualified UTM
>>> let targetHalt = (UTM.S 0, [((UTM.S 0, UTM.I), (UTM.Halt UTM.TargetHalted, UTM.Nop))])
>>> run targetHalt ([], UTM.I, [])
Finished ([],I,[])
>>> run (UTM.S 0, []) ([], UTM.I, [])
Stuck (S 0) ([],I,[])
-}
run :: UTM.Program -> UTM.Tape -> Result
run program tape = case exec delta (state, tape) of
  (UTM.Halt UTM.TargetHalted, finalTape) -> Finished finalTape
  (UTM.Halt reason, finalTape)            -> Failed reason finalTape
  (finalState, finalTape)                 -> Stuck finalState finalTape
  where
    (state, delta) = program

eval :: (UTM.Q, UTM.Delta) -> UTM.Tape -> UTM.Tape
eval program tape = case run program tape of
  Finished finalTape -> finalTape
  Failed _ finalTape -> finalTape
  Stuck _ finalTape  -> finalTape
