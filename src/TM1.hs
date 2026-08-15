module TM1 where

import Prelude hiding (Left, Right)

data Dir = Left
         | Right
  deriving (Show, Eq)

data Sym = Zero
         | One
         | Blank
  deriving (Show, Eq)

data Q = Carry
       | Halt
  deriving (Show, Eq)

type Program = [((Q, Sym), (Q, Sym, Dir))]

type Tape = ([Sym], Sym, [Sym])

initialState :: Q
initialState = Carry

{- | 整数に対して1を加算するチューリングマシンのプログラム
  1. 1 + 1 = 10
  2. 1 + 0 = 01
  3. 0 + 1 = 01
  4. 0 + 0 = 00
-}
tm1 :: Program
tm1 =
  [ ((Carry, One),   (Carry, Zero, Left))
  , ((Carry, Zero),  (Halt,  One,  Right))
  , ((Carry, Blank), (Halt,  One,  Right))
  ]

{- | チューリングマシンの1ステップの実行
  - 入力: プログラムと現在の状態とテープ
  - 出力: 次の状態とテープ、または終了を示すNothing
>>> step tm1 (Carry, ([One, One], One, [Blank, Blank]))
Just (Carry,([One],One,[Zero,Blank,Blank]))

>>> step tm1 (Carry, ([One], Zero, [Blank, Blank]))
Just (Halt,([One,One],Blank,[Blank]))

>>> step tm1 (Halt, ([One], One, [Blank, Blank]))
Nothing
-}
step :: Program -> (Q, Tape) -> Maybe (Q, Tape)
step program (state, (ls, h, rs)) =
  case lookup (state, h) program of
    Just (newState, newSym, dir) ->
      Just (newState, move dir (ls, newSym, rs))
    Nothing -> Nothing
  where
    move Left  (l, s, r) = (tl l, hd l, cons (s, r))
    move Right (l, s, r) = (cons (s, l), hd r, tl r)

    hd []    = Blank
    hd (x:_) = x

    tl []     = []
    tl (_:xs) = xs

    cons (Blank, []) = []
    cons (x, xs)     = x:xs

{- | チューリングマシンの実行
  - 入力: プログラムと初期状態とテープ
  - 出力: 終了時の状態とテープ
>>> eval tm1 (Carry, ([One, One], One, [Blank, Blank]))
(Halt,([One],Zero,[Zero,Zero,Blank,Blank]))

>>> eval tm1 (Carry, ([One], Zero, [Blank, Blank]))
(Halt,([One,One],Blank,[Blank]))

>>> eval tm1 (Halt, ([One], One, [Blank, Blank]))
(Halt,([One],One,[Blank,Blank]))
-}
eval :: Program -> (Q, Tape) -> (Q, Tape)
eval program (state, tape) =
  case step program (state, tape) of
    Just (newState, newTape) -> eval program (newState, newTape)
    Nothing                  -> (state, tape)
