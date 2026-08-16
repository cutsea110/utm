module UTMEncoding where

import Data.List (unfoldr)
import qualified UTM
import qualified TuringMachine as TM

data Codebook q s = Codebook
  { stateTable  :: [(q, [UTM.S])]
  , symbolTable :: [(s, UTM.S)]
  , stateWidth  :: Int
  }

makeCodebook :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
             => tm -> Codebook (TM.State tm) (TM.Symbol tm)
makeCodebook tm
  | null qs = error "makeCodebook: target TM has no states"
  | blank `notElem` ss = error "makeCodebook: blank symbol is not in the symbol list"
  | length nonBlankSymbols > 2 = error "makeCodebook: target TM has more than 2 non-blank symbols"
  | otherwise = Codebook
      { stateTable  = zip qs (map encodeBinary [0..])
      , symbolTable = zip nonBlankSymbols [UTM.O, UTM.I] ++ [(blank, UTM.B)]
      , stateWidth  = length (encodeBinary (length qs - 1))
      }
  where
    qs = TM.states tm
    ss = TM.symbols tm
    blank = TM.blankSymbol tm
    nonBlankSymbols = filter (/= blank) ss

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
[TS,O,SP,I,SP,I,SP,O,SP,O,ST]
>>>encodeTransition TM1 (TM1.Carry, TM1.Zero, TM1.Carry, TM1.One, UTM.R)
[TS,O,SP,O,SP,O,SP,I,SP,I,ST]
-}
encodeTransition :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
                 => tm -> (TM.State tm, TM.Symbol tm, TM.State tm, TM.Symbol tm, UTM.D) -> [UTM.S]
encodeTransition tm = encodeTransitionWith (makeCodebook tm)

encodeTransitionWith :: (Eq q, Eq s)
                     => Codebook q s -> (q, s, q, s, UTM.D) -> [UTM.S]
encodeTransitionWith codebook (q, s, q', s', d)
  = UTM.TS:encodeStateWith codebook q
  ++ [UTM.SP, encodeSymbolWith codebook s, UTM.SP]
  ++ encodeStateWith codebook q'
  ++ [UTM.SP, encodeSymbolWith codebook s', UTM.SP, encodeDirection d, UTM.ST]

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

{-| シンボルは B, I, O のいずれかであることが制約となっているので 1 シンボルで返される
>>> import TM1
>>> encodeSymbol TM1 TM1.Zero
O
>>> encodeSymbol TM1 TM1.One
I
>>> encodeSymbol TM1 TM1.Blank
B
-}
encodeSymbol :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
             => tm -> TM.Symbol tm -> UTM.S
encodeSymbol tm = encodeSymbolWith (makeCodebook tm)

encodeSymbolWith :: Eq s => Codebook q s -> s -> UTM.S
encodeSymbolWith codebook s = case lookup s (symbolTable codebook) of
  Just code -> code
  Nothing   -> error "encodeSymbol: symbol not found in codebook"

{-| ヘッドが指すシンボルは B, I, O のいずれかであることが制約となっているので 1 シンボルで返される
>>> import TM1
>>> encodeHead TM1 TM1.Zero
HO
>>> encodeHead TM1 TM1.One
HI
>>> encodeHead TM1 TM1.Blank
HB
-}
encodeHead :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
           => tm -> TM.Symbol tm -> UTM.S
encodeHead tm = encodeHeadWith (makeCodebook tm)

encodeHeadWith :: Eq s => Codebook q s -> s -> UTM.S
encodeHeadWith codebook = headSymbol . encodeSymbolWith codebook

headSymbol :: UTM.S -> UTM.S
headSymbol UTM.B = UTM.HB
headSymbol UTM.I = UTM.HI
headSymbol UTM.O = UTM.HO
headSymbol s     = error $ "headSymbol: invalid symbol for head: " ++ show s

encodeDirection :: UTM.D -> UTM.S
encodeDirection UTM.L = UTM.O
encodeDirection UTM.R = UTM.I

encodeVirtualTape :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
                  => tm -> ([TM.Symbol tm], TM.Symbol tm, [TM.Symbol tm]) -> [UTM.S]
encodeVirtualTape tm = encodeVirtualTapeWith (makeCodebook tm)

encodeVirtualTapeWith :: Eq s => Codebook q s -> ([s], s, [s]) -> [UTM.S]
encodeVirtualTapeWith codebook (ls, h, rs) = buffer ++ cells
  where cells  = reverse (map (encodeSymbolWith codebook) ls) ++ [encodeHeadWith codebook h] ++ map (encodeSymbolWith codebook) rs
        -- 左端に伸びるためのバッファを事前追加。
        -- TODO: 境界を超えて左に伸びた場合の処理をどうするか検討する必要がある。
        buffer = replicate (length cells) UTM.B

{-| UTM のテープにエンコードする
>>> import TM1
>>> encode TM1 ([TM1.One], TM1.One, [TM1.Blank, TM1.Blank])
([],PD,[TS,O,SP,O,SP,I,SP,I,SP,I,ST,TS,O,SP,I,SP,O,SP,O,SP,O,ST,TS,O,SP,B,SP,I,SP,I,SP,I,ST,PC,O,B,WQ,B,B,WS,B,B,VT,B,B,B,B,I,HI,B,B])
-}
encode :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
       => tm -> ([TM.Symbol tm], TM.Symbol tm, [TM.Symbol tm]) -> UTM.Tape
encode tm input = fromSymbols $
  [UTM.PD] ++ encodeProgramWith tm codebook
  ++ [UTM.PC] ++ initialStateArea
  ++ [UTM.WQ] ++ emptyStateArea
  ++ [UTM.WS] ++ emptySymbolArea
  ++ [UTM.VT] ++ encodeVirtualTapeWith codebook input
  where
    codebook = makeCodebook tm
    initialStateArea =
      let code = encodeStateWith codebook (TM.initialState tm)
      in code ++ replicate (stateWidth codebook + 1 - length code) UTM.B -- +1 は終端記号として使う B
    emptyStateArea  = replicate (stateWidth codebook + 1) UTM.B          -- +1 は終端記号として使う B
    emptySymbolArea = replicate (symbolCapacity tm + 1) UTM.B            -- +1 は終端記号として使う B

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

{-| シンボルは現状空白を含めて 3 シンボルに制限しているので 1 セルで表現できる
>>> import TM1
>>> symbolCapacity TM1
1
-}
symbolCapacity :: TM.TuringMachine tm => tm -> Int
symbolCapacity _ = 1
