module UTMProgram where

import Compiler
import UTM

utmStep :: Compiler
utmStep = undefined

{-| VT にいる状態から現在の仮想ヘッドをVTから取得してWorkQにコピーする
>>> test copyCurrentHeadToWS ([O, I, B, B, WS], VT, [B,I,B,B,O,HO,B,B])
S__10T_1__0o__ --> S0_10T_1__0o__
     ^              ^
>>> test copyCurrentHeadToWS ([O, I, B, B, WS], VT, [B,I,B,B,O,HI,B,B])
S__10T_1__0i__ --> S1_10T_1__0i__
     ^              ^
>>> test copyCurrentHeadToWS ([O, I, B, I, WS], VT, [B,I,B,B,O,HB,B,B])
S1_10T_1__0^__ --> S__10T_1__0^__
     ^              ^
-}
copyCurrentHeadToWS :: Compiler
copyCurrentHeadToWS = findHead
        `compose`
          branch (== UTM.HO)
            (findAndSetWS UTM.O)
            (branch (== UTM.HI)
              (findAndSetWS UTM.I)
              (findAndSetWS UTM.B))
  where
    findHead :: Compiler
    findHead = while (`notElem` [UTM.HO, UTM.HI, UTM.HB]) moveR

    findAndSetWS :: UTM.S -> Compiler
    findAndSetWS s = while (/= UTM.WS) moveL `compose` moveR `compose` write s
