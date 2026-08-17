{-# LANGUAGE TypeFamilies #-}
module TM3 where

import TuringMachine (TuringMachine(..))
import qualified UTM

data Dir = L
         | R
  deriving (Show, Eq)

data Sym = Blank
         | A
         | B
         | C
  deriving (Show, Eq)

data Q = Scan
       | Halt
  deriving (Show, Eq)

type Program = [((Q, Sym), (Q, Sym, Dir))]

type Tape = ([Sym], Sym, [Sym])

{-| チューリングマシンのプログラム
        1. A -> B
        2. B -> C
        3. C -> A
-}
tm3 :: Program
tm3 = [ ((Scan, A), (Scan, B, R))
      , ((Scan, B), (Scan, C, R))
      , ((Scan, C), (Scan, A, R))
      , ((Scan, Blank), (Halt, Blank, L))
      ]

{-| チューリングマシンの1ステップの実行
  - 入力: A, B, C のいずれかの文字列
  - 出力: A, B, C のいずれかの文字列を右に1つずらす

>>> step tm3 (Scan, ([], TM3.A, [TM3.B, TM3.C]))
Just (Scan,([B],B,[C]))

-}
step :: Program -> (Q, Tape) -> Maybe (Q, Tape)
step program (state, (ls, h, rs)) =
  case lookup (state, h) program of
    Just (newState, newSym, dir) ->
      Just (newState, move dir (ls, newSym, rs))
    Nothing -> Nothing
  where
    move L  (l, s, r) = (tl l, hd l, cons (s, r))
    move R (l, s, r) = (cons (s, l), hd r, tl r)

    hd []    = Blank
    hd (x:_) = x

    tl []     = []
    tl (_:xs) = xs

    cons (Blank, []) = []
    cons (x,     xs) = x : xs

{-| チューリングマシンの実行
>>> eval tm3 (Scan, ([], TM3.A, [TM3.B, TM3.C]))
(Halt,([C,B],A,[]))
-}
eval:: Program -> (Q, Tape) -> (Q, Tape)
eval program (state, tape) =
  case step program (state, tape) of
    Just (newState, newTape) -> eval program (newState, newTape)
    Nothing                  -> (state, tape)

-- | witness type
data TM3 = TM3

instance TuringMachine TM3 where
  type State  TM3 = Q
  type Symbol TM3 = Sym

  states  _ = [Scan, Halt]
  symbols _ = [Blank, A, B, C]

  initialState _ = Scan
  blankSymbol  _ = Blank
  transition _ q s = case lookup (q, s) tm3 of
    Just (q', s', L) -> Just (q', s', UTM.L)
    Just (q', s', R) -> Just (q', s', UTM.R)
    Nothing          -> Nothing
