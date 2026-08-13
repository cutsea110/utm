module TM where

-- | delta
data D = R -- ^ move right
       | L -- ^ move left
       deriving (Show, Eq)

-- | symbol
data S = B  -- ^ blank
       | I  -- ^ 1
       | O  -- ^ 0
       | MI -- ^ marked 1
       | MO -- ^ marked 0
       | HB -- ^ head on blank
       | HI -- ^ head on 1
       | HO -- ^ head on 0
       | PD -- ^ partition delta
       | PC -- ^ partition current state
       | WQ -- ^ partition work Q
       | WS -- ^ partition work S
       | VT -- ^ virtual tape
       | TS -- ^ tuple separator
       | AS -- ^ assoc list separator
       | SP -- ^ delta code separator
       deriving (Show, Eq)

-- | utm tape format
--                                                                 |<----      virtual head position     ---->|
--                                                                 |                        v                 |
-- +-----------------------------------+-------------+-------------+-------------+---------------..-----------+
-- |D10,11>10,101,1#10,01>11,011,0# .. |C101101BBBBBB|Q101101BBBBBB|S101101BBBBBB|T10_11___1o110 .. 011__111_0|
-- +-----------------------------------+-------------+-------------+-------------+---------------..-----------+
-- |<--       delta function        -->|<- current ->|<-- workQ -->|<-- workS -->|<--    virtual tape    -->|
--                                          state
charS :: S -> Char
charS B  = '_'
charS I  = '1'
charS O  = '0'
charS MI = 'I'
charS MO = 'O'
charS HB = '^'
charS HI = 'i'
charS HO = 'o'
charS PD = 'D'
charS PC = 'C'
charS WQ = 'Q'
charS WS = 'S'
charS VT = 'T'
charS TS = ','
charS AS = '>'
charS SP = '#'

data A = Move D
       | Write S
       | Nop
       deriving (Show, Eq)

data Q = S Int
       deriving (Show, Eq)

type Delta = [((Q, S), (Q, A))]

type Program = (Q, Delta)

type Tape = ([S], S, [S])
conv :: Tape -> [S]
conv (ls, h, rs) = reverse ls ++ h:rs
showTape :: Tape -> [String]
showTape (ls, h, rs) = [map charS tape, replicate idx ' ' ++ "^"]
  where
    idx = length ls
    tape = reverse ls ++ [h] ++ rs

addOne :: Program
addOne = (S 0, [ ((S 0, I), (S 1, Write O))
               , ((S 0, O), (S 2, Write I))
               , ((S 0, B), (S 2, Write I))
               , ((S 1, I), (S 0, Move L))
               , ((S 1, O), (S 0, Move L))
               ])
