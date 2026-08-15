{-# LANGUAGE TypeFamilies #-}
module TuringMachine where

import qualified UTM

class TuringMachine tm where
  type State tm
  type Symbol tm

  -- Q
  states  :: tm -> [State tm]
  -- Σ
  symbols :: tm -> [Symbol tm]

  initialState :: tm -> State tm
  blankSymbol  :: tm -> Symbol tm
  transition :: tm -> State tm -> Symbol tm -> Maybe (State tm, Symbol tm, UTM.D)
