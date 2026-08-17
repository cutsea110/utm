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
>>> test copyCurrentHeadToWS ([B,B,B,WS], VT, [VC,I,O,I,HVC,O,I,I,VC,O,O,I])
S___T|101/011|001 --> S011T|101/011|001
    ^                           ^
>>> test copyCurrentHeadToWS ([B,B,B,B,WS], VT, [VC,I,O,I,O,HVC,I,O,O,I,VC,I,I,I,I])
S____T|1010/1001|1111 --> S1001T|1010/1001|1111
     ^                                ^
>>> test copyCurrentHeadToWS ([B,B,WS], VT, [VC,I,HVC,O,VC,I])
S__T|1/0|1 --> S0_T|1/0|1
   ^                  ^
-}
copyCurrentHeadToWS :: Compiler
copyCurrentHeadToWS = findHead `compose` moveR `compose` copyTo (UTM.L, UTM.WS)
  where
    findHead :: Compiler
    findHead = moveAfter (UTM.R, UTM.VT)
               `compose` while (`notElem` [UTM.HVC, UTM.B]) moveR
               `compose` branch (== UTM.HVC) nop (halt UTM.InvalidVirtualTape)
    nop :: Compiler
    nop env = (env, [])

{-| PD の先頭から状態遷移表を引く。

最小の遷移表を使い、選んだ遷移だけを 'MTS' にし、遷移先状態を 'WQ'
へコピーすることを確認する。

>>> test findTransition ([WS, B, WQ, B, O, PC, ST, I, SP, O, O, SP, I, SP, I, O, SP, O, TS, PD], O, [I, B])
D@0#01#1#00#1;C0_Q_S01_ --> D*0#01#1#00#1;C0_Q1S01
                    ^              ^

先頭候補が不一致なら 'TS' に戻して次の候補を選ぶ。

>>> test findTransition ([WS, B, WQ, B, O, PC, ST, I, SP, I, I, SP, I, SP, I, O, SP, O, TS, ST, O, SP, O, O, SP, I, SP, O, I, SP, I, TS, PD], O, [I, B])
D@1#10#1#00#0;@0#01#1#11#1;C0_Q_S01_ --> D@1#10#1#00#0;*0#01#1#11#1;C0_Q1S01
                                 ^                           ^

状態 'q' が不一致の候補も同じように飛ばす。

>>> test findTransition ([WS, B, WQ, B, O, PC, ST, I, SP, I, I, SP, I, SP, I, O, SP, O, TS, ST, O, SP, O, O, SP, I, SP, I, O, SP, I, TS, PD], O, [I, B])
D@1#01#1#00#0;@0#01#1#11#1;C0_Q_S01_ --> D@1#01#1#00#0;*0#01#1#11#1;C0_Q1S01
                                 ^                           ^

候補がなければ、すべての 'MTS' を戻して正常終了する。

>>> test findTransition ([WS, B, WQ, B, O, PC, ST, O, SP, O, O, SP, I, SP, O, I, SP, O, TS, PD], O, [I, B])
D@0#10#1#00#0;C0_Q_S01_ --> D@0#10#1#00#0;C0_Q_S___
                    ^                             ^
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
             `compose` matchUntil UTM.SP (UTM.R, UTM.WS) UTM.B
             `compose` branch (== UTM.B) (moveTo (UTM.L, UTM.MTS)) nextTransition

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
writeVirtualSymbol = eraseHeadCode
                     `compose` moveTo (UTM.L, UTM.MTS)
                     `compose` moveAfter (UTM.R, UTM.SP)
                     `compose` moveAfter (UTM.R, UTM.SP)
                     `compose` moveAfter (UTM.R, UTM.SP)
                     `compose` copyToUntil (UTM.R, UTM.HVC) UTM.SP
                     `compose` moveTo (UTM.L, UTM.MTS)
  where
    eraseHeadCode :: Compiler
    eraseHeadCode = moveAfter (UTM.R, UTM.VT)
                    `compose` while (`notElem` [UTM.HVC, UTM.B]) moveR
                    `compose` branch (== UTM.HVC) (moveR `compose` eraseR) (halt UTM.InvalidVirtualTape)


{-| 選択済み遷移の方向ビットに従って仮想ヘッドを動かす。

>>> test moveVirtualHeadByDirection ([], MTS, [O,SP,O,I,SP,I,SP,O,O,SP,O,ST,VT,VC,I,O,HVC,O,I,VC,I,I])
*0#01#1#00#0;T|10/01|11 --> *0#01#1#00#0;T/10|01|11
^                           ^

>>> test moveVirtualHeadByDirection ([], MTS, [O,SP,O,I,SP,I,SP,O,O,SP,I,ST,VT,VC,I,O,HVC,O,I,VC,I,I])
*0#01#1#00#1;T|10/01|11 --> *0#01#1#00#1;T|10|01/11
^                           ^
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
               `compose` while (/= UTM.HVC) moveR
               `compose` moveVirtualHeadL

    moveRight :: Compiler
    moveRight = moveAfter (UTM.R, UTM.VT)
                `compose` while (/= UTM.HVC) moveR
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
