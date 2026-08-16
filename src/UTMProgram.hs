module UTMProgram where

import Compiler
import UTM

forever :: Compiler -> Compiler
forever = while (const True)

{-| UTM の実行器コードを生成する。つまり万能チューリングマシンの delta 関数を生成する。
>>> import TM1
>>> import UTMEncoding
>>> import UTMEval
>>> let (_, delta) = utm defEnv
>>> let tape1 = encode TM1 ([TM1.One], TM1.One, [TM1.Blank, TM1.Blank])

TM1 は 1 インクリメントするチューリングマシンで、11を与えて100を得るようテープをセットしたもの。
これをエンコードして UTM のテープに変換し、UTM の delta 関数を使ってシミュレーションする。

>>> test utm tape1
D@0#0#1#1#1;@0#1#0#0#0;@0#_#1#1#1;C0_Q__S__T____1i__ --> D@0#0#1#1#1;@0#1#0#0#0;@0#_#1#1#1;C1_Q__S__T___1o0__
^                                                                                                  ^

TM2 はハシゴを登るチューリングマシンで、空の足場にマークをつけて上へ登り、マークのついた足場に対して上へ移動し、終わりのついた足場に対して下へ移動して停止する。
これをエンコードして UTM のテープに変換し、UTM の delta 関数を使ってシミュレーションする。

>>> import TM2
>>> let tape2 = encode TM2 ([Empty],Empty,[Mark,Empty,Done])
>>> test utm tape2
D@0#_#1#0#1;@1#_#1#0#1;@1#0#1#0#1;@1#1#10#1#0;C0__Q___S__T______^0_1 --> D@0#_#1#0#1;@1#_#1#0#1;@1#0#1#0#1;@1#1#10#1#0;C10_Q___S__T______00o1
^                                                                                                                                ^
-}
utm :: Compiler
utm = forever utmStep

{-| ターゲット TM の1ステップをシミュレートする。

>>> import TM1
>>> import UTMEncoding
>>> test utmStep (encode TM1 ([One], One, [Blank, Blank]))
D@0#0#1#1#1;@0#1#0#0#0;@0#_#1#1#1;C0_Q__S__T____1i__ --> D@0#0#1#1#1;@0#1#0#0#0;@0#_#1#1#1;C0_Q__S__T____i0__
^                                                                    ^
-}
utmStep :: Compiler
utmStep = copyCurrentHeadToWS
          `compose` findTransition
          `compose` writeVirtualSymbol
          `compose` moveVirtualHeadByDirection
          `compose` updateCurrentState
          `compose` cleanupStep

{-| VT にいる状態から現在の仮想ヘッドをVTから取得してWorkSにコピーする
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
          branch (== UTM.HO) (findAndSetWS UTM.O)
            (branch (== UTM.HI) (findAndSetWS UTM.I)
              (branch (== UTM.HB) (findAndSetWS UTM.B)
                (halt UTM.InvalidVirtualTape)))
  where
    findHead :: Compiler
    findHead = while (`notElem` [UTM.HB, UTM.HO, UTM.HI]) moveR

    findAndSetWS :: UTM.S -> Compiler
    findAndSetWS s = while (/= UTM.WS) moveL `compose` moveR `compose` write s

{-| PD の先頭から状態遷移表を引く。

最小の遷移表を使い、選んだ遷移だけを 'MTS' にし、遷移先状態を 'WQ'
へコピーすることを確認する。

>>> test findTransition ([WS, B, WQ, B, O, PC, ST, I, SP, B, SP, I, SP, I, SP, O, TS, PD], I, [])
D@0#1#1#_#1;C0_Q_S1 --> D*0#1#1#_#1;C0_Q1S1
                  ^           ^

先頭候補が不一致なら 'TS' に戻して次の候補を選ぶ。

>>> test findTransition ([WS, B, WQ, B, O, PC, ST, I, SP, B, SP, O, SP, I, SP, O, TS, ST, I, SP, B, SP, I, SP, O, SP, O, TS, PD], I, [])
D@0#0#1#_#1;@0#1#0#_#1;C0_Q_S1 --> D@0#0#1#_#1;*0#1#0#_#1;C0_Q0S1
                             ^                      ^

状態 'q' が不一致の候補も同じように飛ばす。

>>> test findTransition ([WS, B, WQ, B, O, PC, ST, I, SP, B, SP, O, SP, I, SP, O, TS, ST, I, SP, B, SP, I, SP, I, SP, I, TS, PD], I, [])
D@1#1#1#_#1;@0#1#0#_#1;C0_Q_S1 --> D@1#1#1#_#1;*0#1#0#_#1;C0_Q0S1
                             ^                      ^

候補がなければ、すべての 'MTS' を戻して正常終了する。

>>> test findTransition ([WS, B, WQ, B, O, PC, ST, I, SP, B, SP, I, SP, O, SP, O, TS, PD], I, [])
D@0#0#1#_#1;C0_Q_S1 --> D@0#0#1#_#1;C0_Q_S__
                  ^                        ^
-}
findTransition :: Compiler
findTransition = moveTo (UTM.L, UTM.PD)
                 `compose` moveR
                 `compose` while (== UTM.TS) tryTransition
                 `compose`
                 branch (== UTM.PC) targetHalted
                   (branch (== UTM.MTS) transitionMatched
                     (halt UTM.InvalidTransitionTable))


  where
    tryTransition :: Compiler
    tryTransition = markTransitionStart `compose` matchQ

    matchQ :: Compiler
    matchQ = moveAfter (UTM.R, UTM.PC)
             `compose` matchUntil UTM.B (UTM.L, UTM.MTS) UTM.SP
             `compose` branch (== UTM.SP) matchS nextTransition

    matchS :: Compiler
    matchS = moveR
             `compose` branch (== UTM.O) (matchesWS UTM.O)
                         (branch (== UTM.I) (matchesWS UTM.I)
                           (branch (== UTM.B) (matchesWS UTM.B)
                             (halt UTM.InvalidTransitionTable)))

    matchesWS :: UTM.S -> Compiler
    matchesWS s = moveTo (UTM.R, UTM.WS)
                  `compose` moveR
                  `compose` branch (== s) (moveTo (UTM.L, UTM.MTS)) nextTransition

    nextTransition :: Compiler
    nextTransition = moveTo (UTM.L, UTM.MTS)
                     `compose` unmarkTransitionStart
                     `compose` while (/= UTM.ST) moveR
                     `compose` moveR

    transitionMatched :: Compiler
    transitionMatched = moveAfter (UTM.R, UTM.SP)
                        `compose` moveAfter (UTM.R, UTM.SP)
                        `compose` copyQ

    copyQ :: Compiler
    copyQ = copyToUntil (UTM.R, UTM.WQ) UTM.SP

    targetHalted :: Compiler
    targetHalted = moveAfter (UTM.R, UTM.WS)
                   `compose` eraseR
                   `compose` halt UTM.TargetHalted

writeVirtualSymbol :: Compiler
writeVirtualSymbol = moveTo (UTM.L, UTM.MTS)
                     `compose` moveAfter (UTM.R, UTM.SP)
                     `compose` moveAfter (UTM.R, UTM.SP)
                     `compose` moveAfter (UTM.R, UTM.SP)
                     `compose`
                     branch (== UTM.B) (updateHead UTM.HB)
                       (branch (== UTM.I) (updateHead UTM.HI)
                         (branch (== UTM.O) (updateHead UTM.HO)
                           (halt UTM.InvalidTransitionTable)))
                     `compose` moveTo (UTM.L, UTM.MTS)
  where
    updateHead :: UTM.S -> Compiler
    updateHead s = moveAfter (UTM.R, UTM.VT)
                   `compose` while (`notElem` [UTM.HB, UTM.HI, UTM.HO]) moveR
                   `compose` write s

{-| 選択済み遷移の方向ビットに従って仮想ヘッドを動かす。

>>> test moveVirtualHeadByDirection ([], MTS, [O, SP, I, SP, I, SP, B, SP, O, ST, VT, B, HO, I])
*0#1#1#_#0;T_o1 --> *0#1#1#_#0;T^01
^                   ^

>>> test moveVirtualHeadByDirection ([], MTS, [O, SP, I, SP, I, SP, B, SP, I, ST, VT, I, HI, B])
*0#1#1#_#1;T1i_ --> *0#1#1#_#1;T11^
^                   ^
-}
moveVirtualHeadByDirection :: Compiler
moveVirtualHeadByDirection = moveTo (UTM.L, UTM.MTS)
                             `compose` moveAfter (UTM.R, UTM.SP)
                             `compose` moveAfter (UTM.R, UTM.SP)
                             `compose` moveAfter (UTM.R, UTM.SP)
                             `compose` moveAfter (UTM.R, UTM.SP)
                             `compose`
                             (branch (== UTM.O) moveLeft
                               (branch (== UTM.I) moveRight
                                 (halt UTM.InvalidTransitionTable)))
                             `compose` moveTo (UTM.L, UTM.MTS)
  where
    moveLeft :: Compiler
    moveLeft = moveAfter (UTM.R, UTM.VT)
               `compose` while (`notElem` [UTM.HB, UTM.HI, UTM.HO]) moveR
               `compose` moveVirtualHeadL

    moveRight :: Compiler
    moveRight = moveAfter (UTM.R, UTM.VT)
                `compose` while (`notElem` [UTM.HB, UTM.HI, UTM.HO]) moveR
                `compose` moveVirtualHeadR

{-| WQ の状態列で PC の状態列を置き換える。

>>> test updateCurrentState ([], MTS, [O, SP, I, SP, I, SP, B, SP, O, ST, PC, O, B, B, WQ, I, O, B, WS, B])
*0#1#1#_#0;C0__Q10_S_ --> *0#1#1#_#0;C10_Q10_S_
^                         ^
-}
updateCurrentState :: Compiler
updateCurrentState = moveAfter (UTM.R, UTM.PC)
                     `compose` eraseR
                     `compose` moveAfter (UTM.R, UTM.WQ)
                     `compose` copyTo (UTM.L, UTM.PC)
                     `compose` moveTo (UTM.L, UTM.MTS)

{-| 作業領域を消去し、選択中の遷移印を戻す。

>>> test cleanupStep ([], MTS, [O, SP, I, SP, I, SP, B, SP, O, ST, PC, I, O, B, WQ, I, O, B, WS, I, B, VT, HO])
*0#1#1#_#0;C10_Q10_S1_To --> @0#1#1#_#0;C10_Q___S__To
^                            ^
-}
cleanupStep :: Compiler
cleanupStep = moveAfter (UTM.R, UTM.WQ)
              `compose` eraseR
              `compose` moveAfter (UTM.R, UTM.WS)
              `compose` eraseR
              `compose` moveTo (UTM.L, UTM.MTS)
              `compose` unmarkTransitionStart
