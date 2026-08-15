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

tm1 :: Program
tm1 =
  [ ((Carry, One),   (Carry, Zero, Left))
  , ((Carry, Zero),  (Halt, One, Right))
  , ((Carry, Blank), (Halt, One, Right))
  ]
