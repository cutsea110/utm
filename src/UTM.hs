module UTM where

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
       | TS -- ^ transition start
       | ST -- ^ stop transition
       | SP -- ^ delta code separator
       deriving (Show, Eq)

-- | allSymbols: 全てのシンボル
allSymbols :: [S]
allSymbols = [B, I, O, MI, MO, HB, HI, HO, PD, PC, WQ, WS, VT, TS, ST, SP]

-- | writableSymbols: 書き込み可能なシンボル
writableSymbols :: [S]
writableSymbols = [B, I, O]

-- | 限定利用シンボル (コピーと照合の関数でのみ出現可能)
restrictedSymbols :: [S]
restrictedSymbols = [MI, MO, HB, HI, HO]

-- | readOnlySymbol: 上書き禁止部のシンボル
readOnlySymbols :: [S]
readOnlySymbols = [PD, PC, WQ, WS, VT, TS, ST, SP]


-- | utm tape format (v0 format)
--                                                                  |<----      virtual head position     ---->|
--                                                                  |                        v                 |
-- +------------------------------------+-------------+-------------+-------------+---------------..-----------+
-- |D@10#11#10#101#1;10#01#11#011#0; .. |C101101BBBBBB|Q101101BBBBBB|S101101BBBBBB|T10_11___1o110 .. 011__111_0|
-- +------------------------------------+-------------+-------------+-------------+---------------..-----------+
-- |<--        delta function        -->|<- current ->|<-- workQ -->|<-- workS -->|<--    virtual tape    -->|
--                                          state
-- 意味
-- - @ = TS: transition の区切り
-- - # = SP: フィールドの区切り
-- - ; = ST: transition の終了
-- - C: 現在状態
-- - Q, S: 作業用の状態とシンボル
-- - T: 仮想テープ
--
-- 補足
--  1. d の符号化
--    0: L
--    1: R
--  2. 状態・シンボルの符号化
--    state, symbols の列挙順を 0-origin な正数に昇順に割り当てて二進数にした表現を I と O の列で表す。
--  3. 仮想テープの制約
--    今の HI, HO, HB は 1セルが 0, 1, 空白の TM を直接表現する形式である。
--    よって v0 ではターゲットの TM のシンボル集合をこの 3 記号以下に制限する必要がある。拡張は今はしない。
--    拡張するにはターゲットのシンボルが複数セルにまたがるので複数セルをまとめて 1 記号として扱う必要がある。
--    その場合には専用のセル境界シンボルを導入してコピーや比較中のマークの扱いもその可変長セル表現にあわせて設計しなおす。
--  4. 不変条件
--    T には仮想ヘッド記号がいつの時点でも丁度 1 個だけある。
--    D は不変である。
--      - D はターゲット TM の遷移表を符号化した読み取り専用領域であり UTM の実行中に変更されることはない。
--        一方 UTM の delta は Compiler が生成する実行器コードであり、ターゲット TM ごとに変わらない。
--    Q と S は作業後に空白に戻すこと。
--
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
charS TS = '@'
charS ST = ';'
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
