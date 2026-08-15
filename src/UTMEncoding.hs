module UTMEncoding where

import qualified UTM
import qualified TuringMachine as TM

encodeProgram :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
              => tm -> [UTM.S]
encodeProgram tm
  = concatMap (encodeTransition tm) transitions
  ++ encodeInitialState tm initialState
  ++ encodeBlankSymbol tm blankSymbol
  where states       = TM.states tm
        symbols      = TM.symbols tm
        initialState = TM.initialState tm
        blankSymbol  = TM.blankSymbol tm
        transitions  = [ (q, s, q', s', d)
                       | q <- states
                       , s <- symbols
                       , Just (q', s', d) <- [TM.transition tm q s]
                       ]

encodeTransition :: TM.TuringMachine tm
                 => tm -> (TM.State tm, TM.Symbol tm, TM.State tm, TM.Symbol tm, UTM.D) -> [UTM.S]
encodeTransition tm (q, s, q', s', d) = undefined

encodeInitialState :: TM.TuringMachine tm
                   => tm -> TM.State tm -> [UTM.S]
encodeInitialState tm q = undefined

encodeBlankSymbol :: TM.TuringMachine tm
                  => tm -> TM.Symbol tm -> [UTM.S]
encodeBlankSymbol tm s = undefined

encode :: (TM.TuringMachine tm, Eq (TM.State tm), Eq (TM.Symbol tm))
       => tm -> ([TM.Symbol tm], TM.Symbol tm, [TM.Symbol tm]) -> UTM.Tape
encode = undefined


