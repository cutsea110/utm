module UTM where

-- | delta
data D = R -- ^ move right
       | L -- ^ move left
       deriving (Show, Eq)

-- | symbol
-- マークはコピーと比較(検索)で使うだけでそれ以外の箇所では使わない。
-- コピーと比較関数の中だけで存在しうるものとする。
-- またコピーと比較が目的なので通常はIとOのみ対象でBをマークすることはない。Bを見た時点で通常処理は終了を意味する。
-- utm のヘッドは ([S],S,[S]) の第2要素位置で表現されるものでテープ全域を走査しうる。
data S = B  -- ^ blank
       | I  -- ^ 1
       | O  -- ^ 0
       | SI -- ^ source marked 1
       | SO -- ^ source marked 0
       | EF -- ^ 左拡張中のコピー先終端 frontier
       | TI -- ^ target marked 1
       | TO -- ^ target marked 0
       | PD -- ^ partition delta
       | PC -- ^ partition current state
       | WQ -- ^ partition work Q
       | WS -- ^ partition work S
       | WB -- ^ partition blank code (template)
       | VT -- ^ virtual tape
       | TS -- ^ transition start
       | MTS -- ^ marked transition start
       | ST -- ^ stop transition
       | SP -- ^ delta code separator
       | VC -- ^ virtual tape cell header
       | HVC -- ^ virtual tape cell header with target TM's virtual head
       deriving (Show, Eq)

-- | allSymbols: 全てのシンボル
allSymbols :: [S]
allSymbols = [B, I, O, SI, SO, EF, TI, TO, PD, PC, WQ, WS, WB, VT, TS, MTS, ST, SP, VC, HVC]

-- | writableSymbols: 書き込み可能なシンボル
writableSymbols :: [S]
writableSymbols = [B, I, O]

-- | 限定利用シンボル (コピーと照合の関数でのみ出現可能)
restrictedSymbols :: [S]
restrictedSymbols = [SI, SO, EF, TI, TO]

-- | readOnlySymbol: 上書き禁止部のシンボル
readOnlySymbols :: [S]
readOnlySymbols = [PD, PC, WQ, WS, WB, VT, TS, MTS, ST, SP, VC, HVC]


-- | utm tape format (v1 format)                                                                 virtual head pos
--                                                                                            |          v                 |
-- +------------------------------------+-------------+-------------+-------------+-----------+---------------..-----------+
-- |D@10#11#10#101#1;10#01#11#011#0; .. |C101101BBBBBB|Q101101BBBBBB|S101101BBBBBB|%000.._    |T|10|11.../01|11.. |11|10...|
-- +------------------------------------+-------------+-------------+-------------+-----------+---------------..-----------+
-- |<--        delta function        -->|<- current ->|<-- workQ -->|<-- workS -->|<- blank ->|<--    virtual tape    -->|
--                                          state
-- 意味
-- - @ = TS: transition の区切り
-- - # = SP: フィールドの区切り
-- - ; = ST: transition の終了
-- - C: 現在状態
-- - Q, S: 作業用の状態とシンボル
-- - %: blankCode のテンプレート (左右の仮想テープの拡張時にこれで初期化する)
-- - T: 仮想テープ
--
-- 補足
--  1. d の符号化
--    0: L
--    1: R
--  2. 状態・シンボルの符号化
--    state, symbols の列挙順を 0-origin な正数に昇順に割り当てて二進数にした表現を I と O の列で表す。
--  3. 不変条件
--    T には仮想ヘッド記号がいつの時点でも丁度 1 個だけある。
--    D は不変である。
--      - D はターゲット TM の遷移表を符号化した読み取り専用領域である。
--        遷移探索中はカーソルとして TS を一時的に MTS へ置換することがあるが、
--        対象 TM の1ステップ完了時には必ず TS へ復元する。
--        一方 UTM の delta は Compiler が生成する実行器コードであり、ターゲット TM ごとに変わらない。
--      - D の 1 遷移規則は以下の形式
--        TS q SP a SP q' SP b SP d ST
--        これは対象 TM の遷移規則 (q, a) -> (q', b, d) を符号化したものである。
--        - a, b はターゲット TM のシンボルで symbolWidth セルの固定幅コードである。
--          各フィールドの境界は SP である。
--    Q と S は作業後に空白に戻すこと。
--    WB blankCode B
--      - blankCode はターゲット TM の blank symbol の symbolWidth ビットのコードである。
--      - WB 領域は実行中に書き換えない。
--    VT (VC code | HVC code)*
--      通常セル: VC  <固定幅 symbolWidth セル>
--      ヘッド付: HVC <固定幅 symbolWidth セル>
--      - VC, HVC はセル先頭記号
--      - 仮想テープ内には HVC が常にちょうど 1 個存在する。
--      - 各セルのセル長はターゲット TM の symbolWidth とする。
--      - WS は同じ固定幅のコードを保持し、終端 B を持つ。
--
charS :: S -> Char
charS B   = '_'
charS I   = '1'
charS O   = '0'
charS SI  = 'I'
charS SO  = 'O'
charS EF  = '.'
charS TI  = 'i'
charS TO  = 'o'
charS PD  = 'D'
charS PC  = 'C'
charS WQ  = 'Q'
charS WS  = 'S'
charS WB  = '%'
charS VT  = 'T'
charS TS  = '@'
charS MTS = '*'
charS ST  = ';'
charS SP  = '#'
charS VC  = '|'
charS HVC = '/'

data A = Move D
       | Write S
       | Nop
       deriving (Show, Eq)

data HaltReason
  = TargetHalted
  | VirtualTapeLeftBoundaryExceeded
  | InvalidVirtualTape
  | InvalidTransitionTable
  deriving (Show, Eq)

-- | UTM の制御状態。'Halt' 状態には遷移を定義しない。
data Q
  = S Int
  | Halt HaltReason
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
