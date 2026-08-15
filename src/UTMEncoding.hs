module UTMEncoding where

import Data.List (unfoldr, (\\))
import qualified UTM
import qualified TuringMachine as TM

encodeProgram :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
              => tm -> [UTM.S]
encodeProgram tm = concatMap (encodeTransition tm) transitions
  where states       = TM.states tm
        symbols      = TM.symbols tm
        transitions  = [ (q, s, q', s', d)
                       | q <- states
                       , s <- symbols
                       , Just (q', s', d) <- [TM.transition tm q s]
                       ]

encodeTransition :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
                 => tm -> (TM.State tm, TM.Symbol tm, TM.State tm, TM.Symbol tm, UTM.D) -> [UTM.S]
encodeTransition tm (q, s, q', s', d)
  = UTM.TS:encodeState tm q
  ++ [UTM.SP, encodeSymbol tm s, UTM.SP]
  ++ encodeState tm q'
  ++ [UTM.SP, encodeSymbol tm s', UTM.SP, encodeDirection d, UTM.ST]

encodeState :: (TM.TuringMachine tm, Eq (TM.State tm))
                   => tm -> TM.State tm -> [UTM.S]
encodeState tm q = case lookup q dict of
  Just code -> code
  Nothing   -> error "encodeInitialState: state not found in dictionary"
  where dict = zip (TM.states tm) $ map encodeBinary [0..]

encodeBinary :: Int -> [UTM.S]
encodeBinary 0 = [UTM.O]
encodeBinary n = reverse $ unfoldr psi n
  where
    psi 0 = Nothing
    psi m = Just (if odd m then UTM.I else UTM.O, m `div` 2)

-- | シンボルは B, I, O のいずれかであることが制約となっているので 1 シンボルで返される
encodeSymbol :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
             => tm -> TM.Symbol tm -> UTM.S
encodeSymbol tm s = case lookup s dict of
        Just code -> code
        Nothing   -> error "encodeBlankSymbol: symbol not found in dictionary"
  where dict | length twoSymbols <= 2 = zip twoSymbols [UTM.O, UTM.I] ++ [(TM.blankSymbol tm, UTM.B)]
             | otherwise = error "encodeSymbol: target TM has more than 2 non-blank symbols"
        twoSymbols = TM.symbols tm \\ [TM.blankSymbol tm]

encodeHead :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
           => tm -> TM.Symbol tm -> UTM.S
encodeHead tm s = case lookup s dict of
  Just code -> code
  Nothing   -> error "encodeHead: symbol not found in dictionary"
  where dict | length twoSymbols <= 2 = zip twoSymbols [UTM.HO, UTM.HI] ++ [(TM.blankSymbol tm, UTM.HB)]
             | otherwise = error "encodeHead: target TM has more than 2 non-blank symbols"
        twoSymbols = TM.symbols tm \\ [TM.blankSymbol tm]

encodeDirection :: UTM.D -> UTM.S
encodeDirection UTM.L = UTM.O
encodeDirection UTM.R = UTM.I

encodeVirtualTape :: (TM.TuringMachine tm, Eq (TM.Symbol tm))
                  => tm -> ([TM.Symbol tm], TM.Symbol tm, [TM.Symbol tm]) -> [UTM.S]
encodeVirtualTape tm (ls, h, rs) = buffer ++ cells
  where cells  = reverse (map (encodeSymbol tm) ls) ++ [encodeHead tm h] ++ map (encodeSymbol tm) rs
        -- 左端に伸びるためのバッファを事前追加。
        -- TODO: 境界を超えて左に伸びた場合の処理をどうするか検討する必要がある。
        buffer = replicate (length cells) UTM.B

encode :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
       => tm -> ([TM.Symbol tm], TM.Symbol tm, [TM.Symbol tm]) -> UTM.Tape
encode tm input = fromSymbols $
  [UTM.PD] ++ encodeProgram tm
  ++ [UTM.PC] ++ initialStateArea
  ++ [UTM.WQ] ++ emptyStateArea
  ++ [UTM.WS] ++ emptySymbolArea
  ++ [UTM.VT] ++ encodeVirtualTape tm input
  where initialStateArea
          = let code = encodeState tm (TM.initialState tm)
            in code ++ replicate (stateCapacity tm + 1 - length code) UTM.B -- +1 は終端記号として使う B
        emptyStateArea  = replicate (stateCapacity tm + 1) UTM.B          -- +1 は終端記号として使う B
        emptySymbolArea = replicate (symbolCapacity tm) UTM.B

-- | UTM のヘッダ初期位置にセットする薄い補助関数
fromSymbols :: [UTM.S] -> UTM.Tape
fromSymbols [] = error $ "fromSymbols: empty list"
fromSymbols (h:rs) = ([], h, rs)

-- 状態は TM.states から得られる状態数を n とすると 0..n-1 なので log2 n セルで表現できる
stateCapacity :: TM.TuringMachine tm => tm -> Int
stateCapacity tm = case TM.states tm of
  [] -> error "stateCapacity: target TM has no states"
  qs -> length (encodeBinary (length qs - 1))

-- シンボルは現状空白を含めて 3 シンボルに制限しているので 1 セルで表現できる
symbolCapacity :: TM.TuringMachine tm => tm -> Int
symbolCapacity _ = 1
