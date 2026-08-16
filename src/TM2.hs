{-# LANGUAGE TypeFamilies #-}
module TM2 where

import TuringMachine (TuringMachine(..))
import qualified UTM


data Level = Down
           | Up
  deriving (Show, Eq)

data Sym = Empty
         | Mark
         | Done
  deriving (Show, Eq)

data Q = Begin
       | Progress
       | Stop
       deriving (Show, Eq)

type Delta = [((Q, Sym), (Q, Sym, Level))]

type Ladder = ([Sym], Sym, [Sym])

{-| ハシゴを登って停止するチューリングマシンのプログラム
  1. 空の足場に対して、マークをつけて上へ登る
  2. マークのついた足場に対して、上へ移動する
  3. 終わりのついた足場に対して、下へ移動して停止する
-}
tm2 :: Delta
tm2 =
  [ ((Begin, Empty),    (Progress, Mark, Up))
  , ((Progress, Empty), (Progress, Mark, Up))
  , ((Progress, Mark),  (Progress, Mark, Up))
  , ((Progress, Done),  (Stop,     Done, Down))
  ]

{-| チューリングマシンの1ステップの実行
>>> step tm2 (Begin, ([Empty, Empty], Empty, [Empty, Empty]))
Just (Progress,([Mark,Empty,Empty],Empty,[Empty]))
>>> step tm2 (Progress, ([Empty], Mark, [Empty, Empty]))
Just (Progress,([Mark,Empty],Empty,[Empty]))
>>> step tm2 (Progress, ([Mark], Done, [Empty, Empty]))
Just (Stop,([],Mark,[Done,Empty,Empty]))
-}
step :: Delta -> (Q, Ladder) -> Maybe (Q, Ladder)
step delta (state, (ls, h, rs)) =
  case lookup (state, h) delta of
    Just (newState, newSym, dir) ->
      Just (newState, move dir (ls, newSym, rs))
    Nothing -> Nothing
  where
    move Down  (l, s, r) = (tl l, hd l, cons (s, r))
    move Up    (l, s, r) = (cons (s, l), hd r, tl r)

    hd []    = Empty
    hd (x:_) = x

    tl []     = []
    tl (_:xs) = xs

    cons (Empty, []) = []
    cons (x, xs)     = x:xs

{-| チューリングマシンの実行
>>> eval tm2 (Begin, ([Empty, Empty], Empty, [Empty, Done]))
(Stop,([Mark,Empty,Empty],Mark,[Done]))
>>> eval tm2 (Progress, ([Empty], Mark, [Mark, Done, Empty]))
(Stop,([Mark,Empty],Mark,[Done,Empty]))
-}
eval :: Delta -> (Q, Ladder) -> (Q, Ladder)
eval delta (state, ladder) =
  case step delta (state, ladder) of
    Just (newState, newLadder) -> eval delta (newState, newLadder)
    Nothing                    -> (state, ladder)

-- | witness type
data TM2 = TM2

instance TuringMachine TM2 where
  type State TM2 = Q
  type Symbol TM2 = Sym

  states  _ = [Begin, Progress, Stop]
  symbols _ = [Empty, Mark, Done]

  initialState _ = Begin
  blankSymbol _ = Empty
  transition _ q s = case lookup (q, s) tm2 of
    Just (q', s', Down) -> Just (q', s', UTM.L)
    Just (q', s', Up)   -> Just (q', s', UTM.R)
    Nothing             -> Nothing
