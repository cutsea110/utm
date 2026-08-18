module UTMEncoding where

import Data.List (unfoldr)
import qualified UTM
import qualified TuringMachine as TM

data Codebook q s = Codebook
  { stateTable  :: [(q, [UTM.S])]
  , symbolTable :: [(s, [UTM.S])]
  , stateWidth  :: Int
  , symbolWidth :: Int
  , blankCode   :: [UTM.S]
  }
  deriving (Show, Eq)

makeCodebook :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
             => tm -> Codebook (TM.State tm) (TM.Symbol tm)
makeCodebook tm
  | null qs = error "makeCodebook: target TM has no states"
  | blank `notElem` ss = error "makeCodebook: blank symbol is not in the symbol list"
  | otherwise = Codebook
      { stateTable  = zip qs (map encodeBinary [0..])
      , symbolTable = encodedSymTable
      , stateWidth  = length (encodeBinary (length qs - 1))
      , symbolWidth = width
      , blankCode   = blankCode
      }
  where
    qs = TM.states tm
    ss = TM.symbols tm
    blank = TM.blankSymbol tm
    blankCode = case lookup blank encodedSymTable of
      Just code -> code
      Nothing   -> error "makeCodebook: blank symbol not found in symbol table"
    width = max 1 (ceiling (logBase 2 (fromIntegral (length ss)) :: Double))
    encodedSymTable = [ (k, replicate (width - length v) UTM.O ++ v)
                      | (k, v) <- zip ss (map encodeBinary [0..])
                      ]

encodeProgram :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
              => tm -> [UTM.S]
encodeProgram tm = encodeProgramWith tm (makeCodebook tm)

encodeProgramWith :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
                  => tm -> Codebook (TM.State tm) (TM.Symbol tm) -> [UTM.S]
encodeProgramWith tm codebook = concatMap (encodeTransitionWith codebook) transitions
  where states       = TM.states tm
        symbols      = TM.symbols tm
        transitions  = [ (q, s, q', s', d)
                       | q <- states
                       , s <- symbols
                       , Just (q', s', d) <- [TM.transition tm q s]
                       ]

{-| 状態 q, シンボル s に対する遷移 (q', s', d) を UTM のプログラムとしてエンコードする。
>>> import TM1
>>> encodeTransition TM1 (TM1.Carry, TM1.One, TM1.Halt, TM1.Zero, UTM.L)
[TS,O,SP,O,I,SP,I,SP,O,O,SP,O,ST]
>>>encodeTransition TM1 (TM1.Carry, TM1.Zero, TM1.Carry, TM1.One, UTM.R)
[TS,O,SP,O,O,SP,O,SP,O,I,SP,I,ST]
-}
encodeTransition :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
                 => tm -> (TM.State tm, TM.Symbol tm, TM.State tm, TM.Symbol tm, UTM.D) -> [UTM.S]
encodeTransition tm = encodeTransitionWith (makeCodebook tm)

encodeTransitionWith :: (Eq q, Eq s)
                     => Codebook q s -> (q, s, q, s, UTM.D) -> [UTM.S]
encodeTransitionWith codebook (q, s, q', s', d)
  = [UTM.TS] ++ encodeStateWith codebook q
  ++ [UTM.SP] ++ encodeSymbolWith codebook s
  ++ [UTM.SP] ++ encodeStateWith codebook q'
  ++ [UTM.SP] ++ encodeSymbolWith codebook s'
  ++ [UTM.SP, encodeDirection d, UTM.ST]

{-| 状態は 0..n-1 の整数で表現されるので、2進数に変換して返す。
>>> import TM1
>>> encodeState TM1 TM1.Carry
[O]
>>> encodeState TM1 TM1.Halt
[I]
-}
encodeState :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
                   => tm -> TM.State tm -> [UTM.S]
encodeState tm = encodeStateWith (makeCodebook tm)

encodeStateWith :: Eq q => Codebook q s -> q -> [UTM.S]
encodeStateWith codebook q = case lookup q (stateTable codebook) of
  Just code -> code
  Nothing   -> error "encodeState: state not found in codebook"

{-| 非負整数を I, O の二進表現へ変換する
>>> encodeBinary 0
[O]
>>> encodeBinary 1
[I]
>>> encodeBinary 2
[I,O]
>>> encodeBinary 3
[I,I]
>>> encodeBinary 4
[I,O,O]
>>> encodeBinary 5
[I,O,I]
>>> encodeBinary 6
[I,I,O]
>>> encodeBinary 42
[I,O,I,O,I,O]
>>> encodeBinary 255
[I,I,I,I,I,I,I,I]
-}
encodeBinary :: Int -> [UTM.S]
encodeBinary 0 = [UTM.O]
encodeBinary n = reverse $ unfoldr psi n
  where
    psi 0 = Nothing
    psi m = Just (if odd m then UTM.I else UTM.O, m `div` 2)

encodeSymbolWith :: Eq s => Codebook q s -> s -> [UTM.S]
encodeSymbolWith codebook s = case lookup s (symbolTable codebook) of
  Just code -> code
  Nothing   -> error "encodeSymbol: symbol not found in codebook"

encodeDirection :: UTM.D -> UTM.S
encodeDirection UTM.L = UTM.O
encodeDirection UTM.R = UTM.I

encodeVirtualTape :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
                  => tm -> ([TM.Symbol tm], TM.Symbol tm, [TM.Symbol tm]) -> [UTM.S]
encodeVirtualTape tm = encodeVirtualTapeWith (makeCodebook tm)

encodeVirtualTapeWith :: Eq s => Codebook q s -> ([s], s, [s]) -> [UTM.S]
encodeVirtualTapeWith codebook (ls, h, rs) = concat $ buffer ++ cells
  where cells  = reverse (map normalCell ls) ++ [headCell h] ++ map normalCell rs
        normalCell s = UTM.VC  : encodeSymbolWith codebook s
        headCell s   = UTM.HVC : encodeSymbolWith codebook s
        blockWidth   = symbolWidth codebook + 1
        -- 左端に伸びるためのバッファを事前追加。
        buffer = [replicate (blockWidth * length cells) UTM.B]

{-| UTM のテープにエンコードする
>>> import TM1
>>> encode TM1 ([TM1.One], TM1.One, [TM1.Blank, TM1.Blank])
([],PD,[TS,O,SP,O,O,SP,I,SP,O,I,SP,I,ST,TS,O,SP,O,I,SP,O,SP,O,O,SP,O,ST,TS,O,SP,I,O,SP,I,SP,O,I,SP,I,ST,PC,O,B,WQ,B,B,WS,B,B,B,WB,I,O,B,VT,B,B,B,B,B,B,B,B,B,B,B,B,VC,O,I,HVC,O,I,VC,I,O,VC,I,O])
-}
encode :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
       => tm -> ([TM.Symbol tm], TM.Symbol tm, [TM.Symbol tm]) -> UTM.Tape
encode tm input = fromSymbols $
  [UTM.PD] ++ encodeProgramWith tm codebook
  ++ [UTM.PC] ++ initialStateArea
  ++ [UTM.WQ] ++ emptyStateArea
  ++ [UTM.WS] ++ emptySymbolArea
  ++ [UTM.WB] ++ blankCode codebook ++ [UTM.B]
  ++ [UTM.VT] ++ encodeVirtualTapeWith codebook input
  where
    codebook = makeCodebook tm
    initialStateArea =
      let code = encodeStateWith codebook (TM.initialState tm)
      in code ++ replicate (stateWidth codebook + 1 - length code) UTM.B -- +1 は終端記号として使う B
    emptyStateArea  = replicate (stateWidth codebook + 1) UTM.B          -- +1 は終端記号として使う B
    emptySymbolArea = replicate (symbolWidth codebook + 1) UTM.B         -- +1 は終端記号として使う B

-- | UTM のヘッダ初期位置にセットする薄い補助関数
fromSymbols :: [UTM.S] -> UTM.Tape
fromSymbols [] = error $ "fromSymbols: empty list"
fromSymbols (h:rs) = ([], h, rs)

{-| 状態は TM.states から得られる状態数を n とすると 0..n-1 なので log2 n セルで表現できる
>>> import TM1
>>> stateCapacity TM1
1
-}
stateCapacity :: TM.TuringMachine tm => tm -> Int
stateCapacity tm = case TM.states tm of
  [] -> error "stateCapacity: target TM has no states"
  qs -> length (encodeBinary (length qs - 1))

{-| UTM テープからターゲット TM の論理構成を復元する。
VT 左の確保用バッファと両端の余分な空白は、ターゲットテープの意味論に
影響しないため正規化して除去する。

>>> import TM1
>>> decodeConfiguration TM1 (encode TM1 ([TM1.One], TM1.One, [TM1.Blank, TM1.Blank]))
(Carry,([One],One,[Blank,Blank]))

ヘッド位置と右側の非空白記号も復元する。

>>> decodeConfiguration TM1 (encode TM1 ([], TM1.Zero, [TM1.One, TM1.Blank]))
(Carry,([],Zero,[One,Blank]))

UTM の1ステップ後は、書込みとヘッド移動を含む構成を復元する。

>>> import Compiler (defEnv)
>>> import UTMProgram (utmStep)
>>> import qualified UTMEval
>>> let stepProgram = (UTM.S 0, snd (utmStep defEnv))
>>> decodeConfiguration TM1 (UTMEval.eval stepProgram (encode TM1 ([TM1.One], TM1.One, [TM1.Blank, TM1.Blank])))
(Carry,([],One,[Zero,Blank,Blank]))
-}
decodeConfiguration :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
                    => tm -> UTM.Tape -> (TM.State tm, ([TM.Symbol tm], TM.Symbol tm, [TM.Symbol tm]))
decodeConfiguration tm (ls, h, rs) = (currentState, virtualTape)
  where
    codebook = makeCodebook tm
    tape' = reverse ls ++ h:rs
    width = symbolWidth codebook
    swap (k, v) = (v, k)

    currentState = case lookup stateCode (map swap (stateTable codebook)) of
        Just s  -> s
        Nothing -> error $ "decodeConfiguration: state not found in codebook: " ++ show stateCode
      where
        stateCode = takeWhile isBit (after UTM.PC)

    virtualTape = (reverse (map decodeSymbol leftCells), decodeSymbol headCell, map decodeSymbol rightCells)
      where
        cells = parseCells $ dropWhile (== UTM.B) (after UTM.VT)

        parseCells [] = []
        parseCells (header:rest)
          | header `notElem` [UTM.VC, UTM.HVC] = error $ "decodeConfiguration: invalid virtual tape cell header: " ++ show header
          | length bits /= width = error "decodeConfiguration: incomplete virtual tape cell"
          | not (all isBit bits) = error $ "decodeConfiguration: invalid virtual tape cell bits: " ++ show bits
          | otherwise = (header:bits) : parseCells rest'
          where
            (bits, rest') = splitAt width rest

        (leftCells, headCell, rightCells) = case break isHead cells of
          (left, headCell':right)
            | any isHead right -> error "decodeConfiguration: multiple virtual tape heads"
            | otherwise        -> (left, headCell', right)
          _ -> error "decodeConfiguration: virtual tape head not found"
          where
            isHead (UTM.HVC:_) = True
            isHead _           = False

    decodeSymbol cell = case cell of
      UTM.VC:bits  -> decodeBits bits
      UTM.HVC:bits -> decodeBits bits
      _            -> error $ "decodeConfiguration: invalid virtual tape cell: " ++ show cell
      where
        symbolDict = map swap (symbolTable codebook)
        decodeBits bits = case lookup bits symbolDict of
          Just symbol -> symbol
          Nothing -> error $ "decodeConfiguration: invalid virtual tape symbol: " ++ show bits

    after marker = drop 1 (dropWhile (/= marker) tape')

    isBit UTM.I = True
    isBit UTM.O = True
    isBit _     = False
