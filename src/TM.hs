module TM where

-- | delta
data D = R -- ^ move right
       | L -- ^ move left
       deriving (Show, Eq)

-- | symbol
-- マークはコピーと比較(検索)で使うだけでそれ以外の箇所では使わない。
-- コピーと比較関数の中だけで存在しうるものとする。
-- またコピーと比較が目的なので通常はIとOのみ対象でBをマークすることはない。Bを見た時点で通常処理は終了を意味する。
-- 一方ヘッドはBを指すのでHBが存在する。
-- 仮想ヘッドはエンコードされたチューリングマシンのヘッドなので仮想テープエリアVT内のみ移動する。
-- utm のヘッドは ([S],S,[S]) の第2要素位置で表現されるものでテープ全域を走査しうる。
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

-- | allSymbols: 全てのシンボル
allSymbols :: [S]
allSymbols = [B, I, O, MI, MO, HB, HI, HO, PD, PC, WQ, WS, VT, TS, AS, SP]

-- | writableSymbols: 書き込み可能なシンボル
writableSymbols :: [S]
writableSymbols = [B, I, O]

-- | 限定利用シンボル (コピーと照合の関数でのみ出現可能)
restrictedSymbols :: [S]
restrictedSymbols = [MI, MO, HB, HI, HO]

-- | readOnlySymbol: 上書き禁止部のシンボル
readOnlySymbols :: [S]
readOnlySymbols = [PD, PC, WQ, WS, VT, TS, AS, SP]


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
