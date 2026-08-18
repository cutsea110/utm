module UTMProgram where

import Compiler
import UTM

-- | 開始時: 本体の開始位置
--   終了時: 本体に依存する停止位置
forever :: Compiler -> Compiler
forever = while (const True)

{-| UTM の実行器コードを生成する。つまり万能チューリングマシンの delta 関数を生成する。

開始時: 'PD'
終了時: 選択した遷移の 'TS'、または停止時は 'WS' を消去した直後の 'B'
>>> import TM1
>>> import UTMEncoding
>>> import UTMEval
>>> let (_, delta) = utm defEnv
>>> let tape1 = encode TM1 ([TM1.One], TM1.One, [TM1.Blank, TM1.Blank])

TM1 は 1 インクリメントするチューリングマシンで、11を与えて100を得るようテープをセットしたもの。
これをエンコードして UTM のテープに変換し、UTM の delta 関数を使ってシミュレーションする。

>>> test utm tape1
D@0#00#1#01#1;@0#01#0#00#0;@0#10#1#01#1;C0_Q__S___%10_T|10|10|10|10|01/01|10|10 --> D@0#00#1#01#1;@0#01#0#00#0;@0#10#1#01#1;C1_Q__S___%10_T|10|10|10|01/00|00|10|10
^                                                                                                                                    ^

TM2 はハシゴを登るチューリングマシンで、空の足場にマークをつけて上へ登り、マークのついた足場に対して上へ移動し、終わりのついた足場に対して下へ移動して停止する。
これをエンコードして UTM のテープに変換し、UTM の delta 関数を使ってシミュレーションする。

>>> import TM2
>>> let tape2 = encode TM2 ([Empty],Empty,[Mark,Empty,Done])
>>> test utm tape2
D@0#00#1#01#1;@1#00#1#01#1;@1#01#1#01#1;@1#10#10#10#0;C0__Q___S___%00_T|00|00|00|00|00|00/00|01|00|10 --> D@0#00#1#01#1;@1#00#1#01#1;@1#01#1#01#1;@1#10#10#10#0;C10_Q___S___%00_T|00|00|00|00|00|00|01|01/01|10
^                                                                                                                                                                          ^

TM3 は 4 種類のシンボルを持つチューリングマシンで、AをBに、BをCに、CをAに変換し、空白に到達したら停止する。
これは UTM のテープ表現に使う文字 1, 2 を超えているため多セルでターゲット TM の 1 シンボルを扱う例になっている。

>>> import TM3
>>> let tape3 = encode TM3 ([],TM3.A,[TM3.B,TM3.C])
>>> test utm tape3
D@0#00#1#00#0;@0#01#0#10#1;@0#10#0#11#1;@0#11#0#01#1;C0_Q__S___%00_T|00|00|00/01|10|11 --> D@0#00#1#00#0;@0#01#0#10#1;@0#10#0#11#1;@0#11#0#01#1;C1_Q__S___%00_T|00|00|00|10|11/01|00
^                                                                                                                                                        ^
-}
utm :: Compiler
utm = forever utmStep

{-| ターゲット TM の1ステップをシミュレートする。

開始時: 'PD'
終了時: 選択した遷移の 'TS'、または停止時は 'WS' を消去した直後の 'B'

>>> import TM1
>>> import UTMEncoding
>>> test utmStep (encode TM1 ([One], One, [Blank, Blank]))
D@0#00#1#01#1;@0#01#0#00#0;@0#10#1#01#1;C0_Q__S___%10_T|10|10|10|10|01/01|10|10 --> D@0#00#1#01#1;@0#01#0#00#0;@0#10#1#01#1;C0_Q__S___%10_T|10|10|10|10/01|00|10|10
^                                                                                                 ^
-}
utmStep :: Compiler
utmStep = copyCurrentHeadToWS
          `compose` findTransition
          `compose` writeVirtualSymbol
          `compose` moveVirtualHeadByDirection
          `compose` updateCurrentState
          `compose` cleanupStep

{-| 'VT' から現在の仮想ヘッド記号を取得して 'WS' にコピーする。

開始時: 'VT'
終了時: コピー元 'HVC' セルの符号列の最上位桁
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
    -- 開始時: 任意位置
    -- 終了時: 'HVC'
    findHead = moveAfter (UTM.R, UTM.VT)
               `compose` while (== UTM.B) moveR -- go through buffer
               `compose` while (`notElem` [UTM.HVC, UTM.B]) moveR
               `compose` branch (== UTM.HVC) nop (halt UTM.InvalidVirtualTape)
    nop :: Compiler
    -- 開始時: 現在セル
    -- 終了時: 同じセル
    nop env = (env, [])

{-| 'PD' の先頭から状態遷移表を引く。

開始時: 'PD'
終了時: 選択済みの 'MTS'、または停止時は 'WS' を消去した直後の 'B'

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
    -- | 開始時: 候補遷移の 'TS'
    --   終了時: q の照合結果位置
    tryTransition :: Compiler
    tryTransition = markTransitionStart `compose` matchQ

    -- | 開始時: 'MTS'
    --   終了時: s フィールドの先頭、または不一致位置
    matchQ :: Compiler
    matchQ = moveAfter (UTM.R, UTM.PC)
             `compose` matchUntil UTM.B (UTM.L, UTM.MTS) UTM.SP
             `compose` branch (== UTM.SP) matchS nextTransition

    -- | 開始時: s フィールドの先頭
    --   終了時: 'MTS'、または不一致位置
    matchS :: Compiler
    matchS = moveR
             `compose` matchUntil UTM.SP (UTM.R, UTM.WS) UTM.B
             `compose` branch (== UTM.B) (moveTo (UTM.L, UTM.MTS)) nextTransition

    -- | 開始時: 不一致位置
    --   終了時: 次候補の 'TS'、または遷移表末尾の 'PC'
    nextTransition :: Compiler
    nextTransition = moveTo (UTM.L, UTM.MTS)
                     `compose` unmarkTransitionStart
                     `compose` while (/= UTM.ST) moveR
                     `compose` moveR

    -- | 開始時: 選択済みの 'MTS'
    --   終了時: 同じ 'MTS'
    transitionMatched :: Compiler
    transitionMatched = moveAfter (UTM.R, UTM.SP)
                        `compose` moveAfter (UTM.R, UTM.SP)
                        `compose` copyQ

    -- | 開始時: q' フィールドの最上位桁
    --   終了時: q' の終端 'SP'
    copyQ :: Compiler
    copyQ = copyToUntil (UTM.R, UTM.WQ) UTM.SP

    -- | 開始時: 'PC'
    --   終了時: 'WS' を消去した直後の 'B'（停止）
    targetHalted :: Compiler
    targetHalted = moveAfter (UTM.R, UTM.WS)
                   `compose` eraseR
                   `compose` halt UTM.TargetHalted

{-| 選択済み遷移の b フィールドで、現在の仮想ヘッドセルの符号列を更新する。

開始時: 選択済みの 'MTS'
終了時: 同じ 'MTS'
-}
writeVirtualSymbol :: Compiler
writeVirtualSymbol = eraseHeadCode
                     `compose` moveTo (UTM.L, UTM.MTS)
                     `compose` moveAfter (UTM.R, UTM.SP)
                     `compose` moveAfter (UTM.R, UTM.SP)
                     `compose` moveAfter (UTM.R, UTM.SP)
                     `compose` copyToUntil (UTM.R, UTM.HVC) UTM.SP
                     `compose` moveTo (UTM.L, UTM.MTS)
  where
    -- | 開始時: 任意位置
    --   終了時: 'HVC' の符号列を消去した直後の 'B'
    eraseHeadCode :: Compiler
    eraseHeadCode = moveAfter (UTM.R, UTM.VT)
                    `compose` while (`notElem` [UTM.HVC, UTM.B]) moveR
                    `compose` branch (== UTM.HVC) (moveR `compose` eraseR) (halt UTM.InvalidVirtualTape)


{-| 選択済み遷移の方向ビットに従って仮想ヘッドを動かす。

開始時: 選択済みの 'MTS'
終了時: 同じ 'MTS'

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
    -- | 開始時: 方向ビット
    --   終了時: 移動先仮想セルの 'HVC'
    moveLeft :: Compiler
    moveLeft = moveAfter (UTM.R, UTM.VT)
               `compose` while (/= UTM.HVC) moveR
               `compose` moveVirtualHeadL

    -- | 開始時: 方向ビット
    --   終了時: 移動先仮想セルの 'HVC'
    moveRight :: Compiler
    moveRight = moveAfter (UTM.R, UTM.VT)
                `compose` while (/= UTM.HVC) moveR
                `compose` moveVirtualHeadR

{-| 'WQ' の状態列で 'PC' の状態列を置き換える。

開始時: 選択済みの 'MTS'
終了時: 同じ 'MTS'

>>> test updateCurrentState ([], MTS, [PC,I,B,B,WQ,I,O,B,WS,B,WB,O,I,B,VT,HVC,I,O])
*C1__Q10_S_%01_T/10 --> *C10_Q10_S_%01_T/10
^                       ^
-}
updateCurrentState :: Compiler
updateCurrentState = moveAfter (UTM.R, UTM.PC)
                     `compose` eraseR
                     `compose` moveAfter (UTM.R, UTM.WQ)
                     `compose` copyTo (UTM.L, UTM.PC)
                     `compose` moveTo (UTM.L, UTM.MTS)

{-| 作業領域を消去し、選択中の遷移印を戻す。

開始時: 選択済みの 'MTS'
終了時: 同じ遷移開始セルを復元した 'TS'

>>> test cleanupStep ([], MTS, [PC,I,B,WQ,I,B,WS,O,I,B,WB,O,I,B,VT,HVC,O,I])
*C1_Q1_S01_%01_T/01 --> @C1_Q__S___%01_T/01
^                       ^
-}
cleanupStep :: Compiler
cleanupStep = moveAfter (UTM.R, UTM.WQ)
              `compose` eraseR
              `compose` moveAfter (UTM.R, UTM.WS)
              `compose` eraseR
              `compose` moveTo (UTM.L, UTM.MTS)
              `compose` unmarkTransitionStart
