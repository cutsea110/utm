module Compiler where

import UTM (Q(..), HaltReason(..), Delta, A(..), S(..), D(..), Tape, showTape
           , allSymbols, writableSymbols, restrictedSymbols)
import UTMEval (eval, run)

data Env = Env { state :: Int
               }
         deriving (Show, Eq)

get :: Env -> UTM.Q
get env = UTM.S (state env)
next :: Env -> Env
next env = env { state = state env + 1 }
defEnv :: Env
defEnv = Env { state = 0 }

type Compiler = Env -> (Env, UTM.Delta)

{-| 逐次実行: c1の停止状態にc2を続けて実行する。

開始時: 'c1' の開始位置
終了時: 'c2' の終了位置
>>> test (moveR `compose` write I) ([B, B], B, [B, B])
_____ --> ___1_
  ^          ^
>>> test (moveL `compose` write O) ([B, B], B, [B, B])
_____ --> _0___
  ^        ^
-}
compose :: Compiler -> Compiler -> Compiler
(c1 `compose` c2) env0 = (env2, code1 ++ code2)
  where
    (env1, code1) = c1 env0
    (env2, code2) = c2 env1

{-| 条件分岐: ヘッドがcondを満たすときc1を、それ以外のときc2を実行する。

開始時: 分岐判定位置
終了時: 選択された枝の終了位置
>>> test (branch (== UTM.I) (write O) (write I)) ([B, B], I, [B, B])
__1__ --> __0__
  ^         ^
>>> test (branch (== UTM.I) (write O) (write I)) ([B, B], O, [B, B])
__0__ --> __1__
  ^         ^
-}
branch :: (S -> Bool) -> Compiler -> Compiler -> Compiler
branch predicate c1 c2 branchInitialEnv =
  (joinEnv, dispatch ++ c1Code ++ c2Code ++ join)
  where
    branchInitialState = get branchInitialEnv

    c1InitialEnv = next branchInitialEnv
    (c1FinalEnv, c1Code) = c1 c1InitialEnv
    c1InitialState = get c1InitialEnv
    c1FinalState = get c1FinalEnv

    c2InitialEnv = next c1FinalEnv
    (c2FinalEnv, c2Code) = c2 c2InitialEnv
    c2InitialState = get c2InitialEnv
    c2FinalState = get c2FinalEnv

    joinEnv = next c2FinalEnv
    joinState = get joinEnv

    dispatch = [ ((branchInitialState, symbol),
                  (if predicate symbol then c1InitialState else c2InitialState, UTM.Nop))
               | symbol <- allSymbols
               ]

    join = [ ((finalState, symbol), (joinState, UTM.Nop))
           | finalState <- [c1FinalState, c2FinalState]
           , symbol <- allSymbols
           ]

{-| ループ: ヘッドがpredicateを満たすときbodyを実行し、それ以外のとき停止する。

開始時: 判定位置
終了時: 'predicate' が偽になった判定位置
したがって 'body' は次の反復で読む位置にヘッドを置いて終了しなければならない。
>>> test (while (/= UTM.B) moveR) ([I, I], I, [I, I])
11111 --> 11111_
  ^            ^
>>> test (while (/= UTM.B) moveR) ([I, I], I, [I, B])
1111_ --> 1111_
  ^           ^
>>> test (while (/= UTM.B) moveR) ([I, I], B, [I, I])
11_11 --> 11_11
  ^         ^
-}
while :: (S -> Bool) -> Compiler -> Compiler
while predicate body whileInitialEnv =
  (whileFinalEnv, dispatch ++ bodyCode ++ loop)
  where
    whileInitialState = get whileInitialEnv

    bodyInitialEnv = next whileInitialEnv
    (bodyFinalEnv, bodyCode) = body bodyInitialEnv
    bodyInitialState = get bodyInitialEnv
    bodyFinalState = get bodyFinalEnv

    whileFinalEnv = next bodyFinalEnv
    whileFinalState = get whileFinalEnv

    dispatch = [ ((whileInitialState, symbol),
                  (if predicate symbol then bodyInitialState else whileFinalState, UTM.Nop))
               | symbol <- allSymbols
               ]

    loop = [ ((bodyFinalState, symbol), (whileInitialState, UTM.Nop))
           | symbol <- allSymbols
           ]

{-| 指定した理由で UTM を停止させる。
停止状態には遷移を定義しないため、'UTMEval.run' はその理由を最終状態として返す。

開始時: 現在位置
終了時: 現在位置（停止）

>>> run (S 0, snd (halt UTM.VirtualTapeLeftBoundaryExceeded defEnv)) ([], UTM.B, [])
Failed VirtualTapeLeftBoundaryExceeded ([],B,[])
-}
halt :: UTM.HaltReason -> Compiler
halt reason env0 = (next env0, code)
  where
    code = [ ((get env0, symbol), (UTM.Halt reason, UTM.Nop))
           | symbol <- allSymbols
           ]

{-| 遷移探索中のカーソルとして、現在位置の 'TS' を 'MTS' に置換する。
通常の 'write' では読み取り専用の 'TS' / 'MTS' を変更できない。

開始時: 置換対象のセル
終了時: 同じセル

>>> test markTransitionStart ([B], TS, [B])
_@_ --> _*_
 ^       ^
-}
markTransitionStart :: Compiler
markTransitionStart = rewriteTransitionStart UTM.TS UTM.MTS

{-| 'MTS' を通常の 'TS' へ復元する。

開始時: 置換対象のセル
終了時: 同じセル

>>> test unmarkTransitionStart ([B], MTS, [B])
_*_ --> _@_
 ^       ^
-}
unmarkTransitionStart :: Compiler
unmarkTransitionStart = rewriteTransitionStart UTM.MTS UTM.TS

-- | 開始時: 'from' のセル
--   終了時: 同じセル（'to' に置換済み）
rewriteTransitionStart :: UTM.S -> UTM.S -> Compiler
rewriteTransitionStart from to env0 = (next env0, [((get env0, from), (get env1, UTM.Write to))])
  where
    env1 = next env0

-- | 開始時: 空白セル 'B'
--   終了時: 同じセル（'HVC' に置換済み）
createVirtualHead :: Compiler
createVirtualHead env0 = (env1, [((get env0, UTM.B), (get env1, UTM.Write UTM.HVC))])
  where
    env1 = next env0

-- | 開始時: 'VC' のセル
--   終了時: 同じセル（'HVC' に置換済み）
markVirtualHead :: Compiler
markVirtualHead = rewriteVirtualHead UTM.VC UTM.HVC

-- | 開始時: 'HVC' のセル
--   終了時: 同じセル（'VC' に置換済み）
unmarkVirtualHead :: Compiler
unmarkVirtualHead = rewriteVirtualHead UTM.HVC UTM.VC

-- | 開始時: 'from' のセル
--   終了時: 同じセル（'to' に置換済み）
rewriteVirtualHead :: UTM.S -> UTM.S -> Compiler
rewriteVirtualHead from to env0 = (env1, [((get env0, from), (get env1, UTM.Write to))])
  where
    env1 = next env0

{-| 仮想ヘッドを左へ1セル移動する。
'UTM.VT' に到達した場合や仮想テープ内に不正な記号があった場合は、既存の仮想ヘッドを保ったまま停止する。

開始時: 移動前セルの 'HVC'
終了時: 移動先セルの 'HVC'

>>> test moveVirtualHeadL ([O,I,VC,VT,B,I,O,WB], HVC, [I,O,VC,I,I])
%01_T|10/10|11 --> %01_T/10|10|11
        ^               ^

>>> test moveVirtualHeadL ([VT,B,I,O,WB], HVC, [I,O,VC,I,I])
%01_T/10|11 --> %01_T______/01|10|11
     ^                     ^
-}
moveVirtualHeadL :: Compiler
moveVirtualHeadL = moveL
                   `compose` while isPlainBit moveL
                   `compose` branch (== UTM.VC) moveToExistingCell
                     (branch (== UTM.B) consumeLeftBuffer
                       (branch (== UTM.VT) expandLeftBuffer
                         (halt UTM.InvalidVirtualTape)))
  where moveToExistingCell :: Compiler
        -- 開始時: 左隣仮想テープブロックの 'VC'
        -- 終了時: そのブロックの 'HVC'
        moveToExistingCell = markVirtualHead
                             `compose` moveR
                             `compose` skipSeqR
                             `compose`
                               branch (== UTM.HVC) (unmarkVirtualHead `compose` moveL `compose` skipSeqL)
                                 (halt UTM.InvalidVirtualTape)

        consumeLeftBuffer :: Compiler
        -- 開始時: 未使用ブロック右端の 'B'
        -- 終了時: 新しく実体化したブロックの 'HVC'
        consumeLeftBuffer = seekBlankCodeEnd
                            `compose` copyBlankCode
                            `compose` createNewVirtualHead
                            `compose` restoreNewBlankCode
                            `compose` demoteOldVirtualHead
                            `compose` restoreBlankTemplate
                            `compose` seekNewVirtualHead

        seekBlankCodeEnd :: Compiler
        -- 開始時: 未使用ブロック右端の 'B'
        -- 終了時: 'WB' の blank code の最下位桁
        seekBlankCodeEnd = moveAfter (UTM.L, UTM.WB)
                           `compose` skipSeqR
                           `compose` moveL

        createNewVirtualHead :: Compiler
        -- 開始時: 'WB'
        -- 終了時: 新しく実体化したブロックの 'HVC'
        createNewVirtualHead = moveTo (UTM.R, UTM.HVC)
                               `compose` moveL
                               `compose` while (`elem` [UTM.SI, UTM.SO]) moveL
                               `compose`
                                 branch (== UTM.B) createVirtualHead
                                   (halt UTM.InvalidVirtualTape)

        restoreNewBlankCode :: Compiler
        -- 開始時: 新しく実体化したブロックの 'HVC'
        -- 終了時: 旧仮想ヘッドの 'HVC'
        restoreNewBlankCode = moveR
                              `compose` unmarkBits
                              `compose` moveTo (UTM.R, UTM.HVC)

        demoteOldVirtualHead :: Compiler
        -- 開始時: 旧仮想ヘッドの 'HVC'
        -- 終了時: 同じ位置の 'VC'
        demoteOldVirtualHead = unmarkVirtualHead

        restoreBlankTemplate :: Compiler
        -- 開始時: 旧仮想ヘッドの 'VC'
        -- 終了時: 'WB' の blank code 終端 'B'
        restoreBlankTemplate = moveAfter (UTM.L, UTM.WB)
                               `compose` unmarkBits

        seekNewVirtualHead :: Compiler
        -- 開始時: 'WB' の blank code 終端 'B'
        -- 終了時: 新しく実体化したブロックの 'HVC'
        seekNewVirtualHead = moveTo (UTM.R, UTM.HVC)

        copyBlankCode :: Compiler
        -- 開始時: 'WB' の blank code の最下位桁
        -- 終了時: 'WB'
        copyBlankCode = while (/= UTM.WB) copyBit
          where
            copyBit :: Compiler
            -- 開始時: 'WB' の未コピー最下位桁
            -- 終了時: 次の未コピー桁、または 'WB'
            copyBit = branch (== UTM.I) copyI
                        (branch (== UTM.O) copyO
                          (halt UTM.InvalidVirtualTape))

            copyI :: Compiler
            -- 開始時: 'WB' の未コピー 'I'
            -- 終了時: 次の未コピー桁、または 'WB'
            copyI = markAndCopyBit UTM.SI

            copyO :: Compiler
            -- 開始時: 'WB' の未コピー 'O'
            -- 終了時: 次の未コピー桁、または 'WB'
            copyO = markAndCopyBit UTM.SO

            markAndCopyBit :: UTM.S -> Compiler
            -- 開始時: 'WB' の未コピー最下位桁
            -- 終了時: 次の未コピー桁、または 'WB'
            markAndCopyBit s = write s
                               `compose` moveTo (UTM.R, UTM.HVC)
                               `compose` moveL
                               `compose` while (`elem` [UTM.SI, UTM.SO]) moveL
                               `compose`
                                 branch (/= UTM.B) (halt UTM.InvalidVirtualTape)
                                   ( write s
                                     `compose` moveTo (UTM.L, UTM.WB)
                                     `compose` moveR
                                     `compose` skipSeqR
                                     `compose` moveL
                                   )
        unmarkBits :: Compiler
        -- 開始時: 'SI' / 'SO' の連続列先頭
        -- 終了時: 列直後の非マーク
        unmarkBits = while (`elem` [UTM.SI, UTM.SO]) unmarkBit
          where unmarkBit :: Compiler
                -- 開始時: 'SI' または 'SO'
                -- 終了時: その右隣
                unmarkBit = branch (== UTM.SI) (write UTM.I)
                              (branch (== UTM.SO) (write UTM.O)
                                (halt UTM.InvalidVirtualTape))
                            `compose` moveR

        expandLeftBuffer :: Compiler
        -- 開始時: 'VT'
        -- 終了時: 新しく確保した左端ブロックの 'HVC'
        expandLeftBuffer = appendSentinel
                           `compose` migrateCurrentBlock
                           `compose`
                             while (== UTM.VC)
                               (markVirtualHead `compose` migrateCurrentBlock)
                           `compose`
                             branch (== UTM.HVC) (clearFrontier `compose` moveTo (UTM.L, UTM.HVC))
                               (halt UTM.InvalidVirtualTape)

        appendSentinel :: Compiler
        -- 開始時: 'VT'
        -- 終了時: コピー元の cursor の 'HVC'
        appendSentinel = moveTo (UTM.R, UTM.B)
                         `compose` write UTM.EF
                         `compose` moveAfter (UTM.L, UTM.WB)
                         `compose` copyVirtualBlockToEnd UTM.HVC
                         `compose` moveTo (UTM.R, UTM.HVC)

        migrateCurrentBlock :: Compiler
        -- 開始時: コピー元の cursor の 'HVC'
        -- 終了時: 次の旧ブロックの `VC` または sentinel の `HVC`
        migrateCurrentBlock = moveR
                              `compose` copyVirtualBlockToEnd UTM.VC
                              `compose` moveTo (UTM.L, UTM.HVC)
                              `compose` rewriteVirtualHead UTM.HVC UTM.B
                              `compose` moveR
                              `compose` eraseR

        clearFrontier :: Compiler
        -- 開始時: sentinel の 'HVC'
        -- 終了時: B (元の EF)
        clearFrontier = moveTo (UTM.R, UTM.EF) `compose` rewriteVirtualHead UTM.EF UTM.B

        copyVirtualBlockToEnd :: UTM.S -> Compiler
        -- 開始時: コピー元符号列の最上位桁
        -- 終了時: コピー元符号列の最上位桁
        -- 前提: 右端にコピー先終端マーカーの 'EF' が1個ある
        -- 結果: 元の 'EF' は header となり、その右に符号列と次の 'EF' を作る
        copyVirtualBlockToEnd header = copyFirstBit
                                       `compose` copyRemainingBits
                                       `compose` restoreSource
          where
            copyFirstBit :: Compiler
            -- 開始時: コピー元符号列の最上位桁
            -- 終了時: 次のコピー元桁、またはコピー元終端
            copyFirstBit = branch (== UTM.I) copyFirstI
                             (branch (== UTM.O) copyFirstO
                               (halt UTM.InvalidVirtualTape))

            copyFirstI :: Compiler
            -- 開始時: コピー元の最上位 'I'
            -- 終了時: 次のコピー元桁、またはコピー元終端
            copyFirstI = copyFirstMarked UTM.SI UTM.I

            copyFirstO :: Compiler
            -- 開始時: コピー元の最上位 'O'
            -- 終了時: 次のコピー元桁、またはコピー元終端
            copyFirstO = copyFirstMarked UTM.SO UTM.O

            copyFirstMarked :: UTM.S -> UTM.S -> Compiler
            -- 開始時: コピー元の最上位桁
            -- 終了時: 次のコピー元桁、またはコピー元終端
            copyFirstMarked sourceMark bit = write sourceMark
                                               `compose` moveTo (UTM.R, UTM.EF)
                                               `compose` rewriteVirtualHead UTM.EF header
                                               `compose` moveR
                                               `compose` write bit
                                               `compose` moveR
                                               `compose` rewriteVirtualHead UTM.B UTM.EF
                                               `compose` nextSource

            copyRemainingBits :: Compiler
            -- 開始時: 次の未コピー元桁、またはコピー元終端
            -- 終了時: コピー元終端
            copyRemainingBits = while isPlainBit copyRemainingBit

            copyRemainingBit :: Compiler
            -- 開始時: コピー元の1桁
            -- 終了時: 次のコピー元桁、またはコピー元終端
            copyRemainingBit = branch (== UTM.I) copyRemainingI
                               (branch (== UTM.O) copyRemainingO
                                 (halt UTM.InvalidVirtualTape))

            copyRemainingI :: Compiler
            -- 開始時: コピー元の 'I'
            -- 終了時: 次のコピー元桁、またはコピー元終端
            copyRemainingI = copyRemainingMarked UTM.SI UTM.I

            copyRemainingO :: Compiler
            -- 開始時: コピー元の 'O'
            -- 終了時: 次のコピー元桁、またはコピー元終端
            copyRemainingO = copyRemainingMarked UTM.SO UTM.O

            copyRemainingMarked :: UTM.S -> UTM.S -> Compiler
            -- 開始時: コピー元の1桁
            -- 終了時: 次のコピー元桁、またはコピー元終端
            copyRemainingMarked sourceMark bit = write sourceMark
                                                   `compose` moveTo (UTM.R, UTM.EF)
                                                   `compose` write bit
                                                   `compose` moveR
                                                   `compose` rewriteVirtualHead UTM.B UTM.EF
                                                   `compose` nextSource

            nextSource :: Compiler
            -- 開始時: コピー先終端マーカーの 'EF'
            -- 終了時: 次のコピー元桁、またはコピー元終端
            nextSource = while (not . isSourceMark) moveL `compose` moveR

            restoreSource :: Compiler
            -- 開始時: コピー元終端
            -- 終了時: コピー元符号列の最上位桁
            restoreSource = moveL `compose` while isSourceMark restoreBit `compose` moveR

            restoreBit :: Compiler
            -- 開始時: コピー元マーク
            -- 終了時: その左隣
            restoreBit = branch (== UTM.SI) (write UTM.I) (write UTM.O) `compose` moveL

            isSourceMark :: UTM.S -> Bool
            isSourceMark UTM.SI = True
            isSourceMark UTM.SO = True
            isSourceMark _      = False


{-| 仮想ヘッドを右へ1セル移動する。
次セルが 'VC' ならそれを 'HVC' に置換する。右端の 'B' なら、'WB' の
blank code を使って新しいヘッド付きセルを追加する。

開始時: 移動前セルの 'HVC'
終了時: 移動先セルの 'HVC'

>>> test moveVirtualHeadR ([O,I,VC,VT,B,I,O,WB], HVC, [I,O,VC,I,I])
%01_T|10/10|11 --> %01_T|10|10/11
        ^                     ^

>>> test moveVirtualHeadR ([O,I,VC,VT,B,I,O,WB], HVC, [I,O])
%01_T|10/10 --> %01_T|10|10/01
        ^                  ^
-}
moveVirtualHeadR :: Compiler
moveVirtualHeadR = moveR
                   `compose` while isPlainBit moveR
                   `compose` branch (== UTM.VC)
                      ( markVirtualHead
                        `compose` moveL
                        `compose` skipSeqL
                        `compose` branch (== UTM.HVC)
                           (unmarkVirtualHead `compose` moveR `compose` skipSeqR)
                           (halt UTM.InvalidVirtualTape)
                      )
                      (branch (== UTM.B)
                        ( createVirtualHead
                           `compose` moveL
                           `compose` skipSeqL
                           `compose` branch (== UTM.HVC) unmarkVirtualHead (halt UTM.InvalidVirtualTape)
                           `compose` moveTo (UTM.L, UTM.WB)
                           `compose` moveR
                           `compose` copyTo (UTM.R, UTM.HVC)
                           `compose` moveTo (UTM.R, UTM.HVC)
                        )
                        (halt UTM.InvalidVirtualTape))

{-| 現在セルを指定記号で書き換えるプリミティブ。

開始時: 書換え対象のセル
終了時: 同じセル
>>> test (write I) ([B, B], B, [B, B])
_____ --> __1__
  ^         ^
>>> test (write O) ([B, B], B, [B, B])
_____ --> __0__
  ^         ^
>>> test (write B) ([O, O], O, [O, O])
00000 --> 00_00
  ^         ^
>>> test (write B) ([I, I], I, [I, I])
11111 --> 11_11
  ^         ^
-}
write :: UTM.S -> Compiler
write s env0
  | s `elem` candidates = (env1, code)
  | otherwise = error $ "try to write invalid symbol: " ++ show s
  where code = [ ((get env0, symbol), (get env1, UTM.Write s))
               | symbol <- candidates
               ]
        env1 = next env0
        -- テープの delta を除く範囲のみ書き換え可能。従って s には以下のいずれかのみ受け入れる
        candidates = writableSymbols ++ restrictedSymbols

-- | 開始時: 消去列の端
--   終了時: 最初に見つかった 'B' のセル
erase :: UTM.D -> Compiler
erase d = while p (write UTM.B `compose` move d)
  where
    p :: UTM.S -> Bool
    p c | c == UTM.B                 = False
        | c `elem` writableSymbols   = True
        | otherwise                  = False

{-| eraseR: 右へ1,0を空白に置き換えながら移動し、空白で停止する。

開始時: 消去列の左端
終了時: 右の最初の 'B'
>>> test eraseR ([I, I], I, [I, I])
11111 --> 11____
  ^            ^
>>> test eraseR ([O, O], O, [O, O])
00000 --> 00____
  ^            ^
>>> test eraseR ([B, B], B, [B, B])
_____ --> _____
  ^         ^
-}
eraseR :: Compiler
eraseR = erase UTM.R

{-| eraseL: 左へ1,0を空白に置き換えながら移動し、空白で停止する。

開始時: 消去列の右端
終了時: 左の最初の 'B'
>>> test eraseL ([I, I], I, [I, I])
11111 --> ____11
  ^       ^
>>> test eraseL ([O, O], O, [O, O])
00000 --> ____00
  ^       ^
>>> test eraseL ([B, B], B, [B, B])
_____ --> _____
  ^         ^
-}
eraseL :: Compiler
eraseL = erase UTM.L

-- | 開始時: 現在セル
--   終了時: 指定方向に1セル隣
move :: UTM.D -> Compiler
move d env0 = (env1, code)
  where code = [ ((get env0, symbol), (get env1, UTM.Move d))
               | symbol <- allSymbols
               ]
        env1 = next env0

{-| moveR: 右へ1つ移動する。

開始時: 現在セル
終了時: 右隣セル
>>> test moveR ([I, I], I, [I, I])
11111 --> 11111
  ^          ^
>>> test moveR ([O, O], O, [O, O])
00000 --> 00000
  ^          ^
>>> test moveR ([B, B], B, [B, B])
_____ --> _____
  ^          ^
-}
moveR :: Compiler
moveR = move UTM.R

{-| moveL: 左へ1つ移動する。

開始時: 現在セル
終了時: 左隣セル
>>> test moveL ([I, I], I, [I, I])
11111 --> 11111
  ^        ^
>>> test moveL ([O, O], O, [O, O])
00000 --> 00000
  ^        ^
>>> test moveL ([B, B], B, [B, B])
_____ --> _____
  ^        ^
-}
moveL :: Compiler
moveL = move UTM.L

{-| moveTo: 指定方向で最初に見つかるシンボルまで移動する。

開始時: 任意の探索開始位置
終了時: 見つけた 'symbol' のセル
>>> test (moveTo (R, SP)) ([I, I], I, [B, B, SP, I])
111__#1 --> 111__#1
  ^              ^
>>> test (moveTo (L, SP)) ([I, I, B, B, SP], I, [])
#__111 --> #__111
     ^     ^
-}
moveTo :: (UTM.D, UTM.S) -> Compiler
moveTo (direction, symbol) = while (/= symbol) (move direction)

{-| moveAfter: 指定方向で最初に見つかるシンボルの右隣へ移動する。

開始時: 任意の探索開始位置
終了時: 見つけた 'symbol' の物理的な右隣
注記: 探索方向が左の場合も終了位置は右隣。
>>> test (moveAfter (R, SP)) ([I, I], I, [B, B, SP, I])
111__#1 --> 111__#1
  ^               ^
>>> test (moveAfter (L, SP)) ([I, I, B, B, SP], I, [])
#__111 --> #__111
     ^      ^
-}
moveAfter :: (UTM.D, UTM.S) -> Compiler
moveAfter target = moveTo target `compose` moveR

isPlainBit :: S -> Bool
isPlainBit UTM.I = True
isPlainBit UTM.O = True
isPlainBit _     = False

-- | 開始時: ビット列の端または非ビット
--   終了時: 指定方向で最初の非ビット
skipSeq :: UTM.D -> Compiler
skipSeq direction = while isPlainBit (move direction)

{-| 右へ1,0の列をスキップして空白で停止する。

開始時: 列の左端
終了時: 列の右隣の非ビット
>>> test skipSeqR ([I, I], I, [I, I])
11111 --> 11111_
  ^            ^
>>> test skipSeqR ([O, O], O, [O, O])
00000 --> 00000_
  ^            ^
>>> test skipSeqR ([I, I], I, [O, O])
11100 --> 11100_
  ^            ^
>>> test skipSeqR ([O, O], O, [I, I])
00011 --> 00011_
  ^            ^
>>> test skipSeqR ([I, I], B, [O, O])
11_00 --> 11_00
  ^         ^
>>> test skipSeqR ([O, O], B, [I, I])
00_11 --> 00_11
  ^         ^
-}
skipSeqR :: Compiler
skipSeqR = skipSeq UTM.R

{-| 左へ1,0の列をスキップして空白で停止する。

開始時: 列の右端
終了時: 列の左隣の非ビット
>>> test skipSeqL ([I, I], I, [I, I])
11111 --> _11111
  ^       ^
>>> test skipSeqL ([O, O], O, [O, O])
00000 --> _00000
  ^       ^
>>> test skipSeqL ([I, I], I, [O, O])
11100 --> _11100
  ^       ^
>>> test skipSeqL ([O, O], O, [I, I])
00011 --> _00011
  ^       ^
>>> test skipSeqL ([I, I], B, [O, O])
11_00 --> 11_00
  ^         ^
>>> test skipSeqL ([O, O], B, [I, I])
00_11 --> 00_11
  ^         ^
-}
skipSeqL :: Compiler
skipSeqL = skipSeq UTM.L

{-| copyTo: 非破壊的コピー。

開始時: コピー元ビット列の最上位桁
終了時: コピー元ビット列の最上位桁
>>> test (copyTo (R, SP)) ([], I, [I, I, B, B, SP])
111__# --> 111__#111
^          ^
>>> test (copyTo (R, SP)) ([], O, [O, O, B, B, SP])
000__# --> 000__#000
^          ^
>>> test (copyTo (L, SP)) ([B, B, B, B, SP], I, [O, I, I, B, B, SP])
#____1011__# --> #10111011__#
     ^                ^
-}
copyTo :: (UTM.D, UTM.S) -> Compiler
copyTo target = copyToUntil target UTM.B

{-| 'copyTo' のコピー元終端記号を指定する版。
コピー元は現在位置を最上位桁とするビット列で、'sourceEnd' の直前までを
コピーする。

開始時: コピー元ビット列の最上位桁
終了時: コピー元ビット列の最上位桁

>>> test (copyToUntil (R, WQ) SP) ([], I, [O, SP, WQ])
10#Q --> 10#Q10
^        ^
-}
copyToUntil :: (UTM.D, UTM.S) -> UTM.S -> Compiler
copyToUntil (markerDirection, marker) sourceEnd = copyBits `compose` restoreSource
  where
    copyBits :: Compiler
    -- 開始時: 未コピー部分の先頭
    -- 終了時: コピー元の終端
    copyBits = while isSourceBit copyBit

    copyBit :: Compiler
    -- 開始時: コピー元の1ビット
    -- 終了時: 次の未コピー元ビット
    copyBit = branch (== UTM.I) copyI copyO

    copyI :: Compiler
    -- 開始時: 'I'
    -- 終了時: 次の未コピー元ビット
    copyI = copyMarked UTM.SI UTM.I

    copyO :: Compiler
    -- 開始時: 'O'
    -- 終了時: 次の未コピー元ビット
    copyO = copyMarked UTM.SO UTM.O

    copyMarked :: UTM.S -> UTM.S -> Compiler
    -- 開始時: コピー元の1ビット
    -- 終了時: 次の未コピー元ビット
    copyMarked sourceMark bit
      = foldl1 compose [write sourceMark, moveAfter (markerDirection, marker), skipSeqR, write bit, nextSource]

    seekMarkedSource :: Compiler
    -- 開始時: コピー先側
    -- 終了時: 直近のコピー元マーク
    seekMarkedSource = while (not . isMark) (move (opposite markerDirection))

    nextSource :: Compiler
    -- 開始時: コピー元マーク
    -- 終了時: 次の未コピー元ビットまたは終端
    nextSource = case markerDirection of
      UTM.R -> seekMarkedSource `compose` moveR
      UTM.L -> seekMarkedSource `compose` while isMark moveR

    restoreSource :: Compiler
    -- 開始時: コピー元終端の直後
    -- 終了時: コピー元ビット列の最上位桁
    restoreSource = moveL `compose` while isMark restoreBit `compose` moveR

    restoreBit :: Compiler
    -- 開始時: コピー元マーク
    -- 終了時: その左隣
    restoreBit = branch (== UTM.SI) (write UTM.I) (write UTM.O) `compose` moveL

    isMark :: UTM.S -> Bool
    isMark UTM.SI = True
    isMark UTM.SO = True
    isMark _      = False

    isSourceBit :: UTM.S -> Bool
    isSourceBit s
      | s == sourceEnd = False
      | otherwise      = isPlainBit s

    opposite :: UTM.D -> UTM.D
    opposite UTM.L = UTM.R
    opposite UTM.R = UTM.L

{-| ビット列どうしの終端記号をそれぞれ指定して照合する版。
現在位置から 'sourceEnd' の直前までと、指定マーカーの右側から
'targetEnd' の直前までを比較する。

開始時: 比較元ビット列の最上位桁
終了時: 比較先の終端、または不一致を表す位置

>>> test (matchUntil B (R, SP) B) ([], I, [O, I, B, B, SP, I, O, I])
101__#101 --> 101__#101_
^                      ^
>>> test (matchUntil B (L, SP) B) ([B, I, O, I, SP], I, [O, O])
#101_100 --> #101_100
     ^          ^
>>> test (matchUntil B (R, SP) B) ([], I, [O, I, B, B, SP, I, O])
101__#10 --> 101__#10
^              ^
>>> test (matchUntil B (R, SP) B) ([], I, [O, B, B, SP, I, O, I])
10__#101 --> 10__#101
^                   ^

比較先の終端も指定できる。

>>> test (matchUntil B (R, TS) SP) ([], I, [O, I, B, B, TS, I, O, I, SP])
101__@101# --> 101__@101#
^                       ^
>>> test (matchUntil B (R, TS) ST) ([], I, [O, I, B, B, TS, I, O, I, ST])
101__@101; --> 101__@101;
^                       ^

コピー元を 'SP' 終端、比較先を 'B' 終端にもできる。

>>> test (matchUntil SP (R, TS) B) ([], I, [O, SP, B, B, TS, I, O, B])
10#__@10_ --> 10#__@10_
^                     ^
-}
matchUntil :: UTM.S -> (UTM.D, UTM.S) -> UTM.S -> Compiler
matchUntil sourceEnd (markerDirection, marker) targetEnd = compareBits `compose` finish
  where
    compareBits :: Compiler
    -- 開始時: 比較元の先頭
    -- 終了時: 比較元の終端または不一致位置
    compareBits = while continueSource compareBit

    compareBit :: Compiler
    -- 開始時: 比較元の1ビット
    -- 終了時: 次の比較元ビットまたは不一致位置
    compareBit = branch (== UTM.I) compareI compareO

    compareI :: Compiler
    -- 開始時: 比較元の 'I'
    -- 終了時: 次の比較元ビットまたは不一致位置
    compareI = compareMarked UTM.SI UTM.TI UTM.I

    compareO :: Compiler
    -- 開始時: 比較元の 'O'
    -- 終了時: 次の比較元ビットまたは不一致位置
    compareO = compareMarked UTM.SO UTM.TO UTM.O

    compareMarked :: UTM.S -> UTM.S -> UTM.S -> Compiler
    -- 開始時: 比較元の1ビット
    -- 終了時: 次の比較元ビットまたは比較先の不一致位置
    compareMarked sourceMark targetMark bit = foldl1 compose
      [ write sourceMark
      , moveAfter (markerDirection, marker)
      , skipTargetMarks
      , branch (== bit)
          (write targetMark `compose` restoreSource bit `compose` moveR)
          (branch (== targetEnd) seekSourceMark (branch (== UTM.I) (write UTM.TI) (write UTM.TO)))
      ]

    finish :: Compiler
    -- 開始時: 比較元終端またはマーク
    -- 終了時: 比較先の判定位置
    finish = branch isSourceMark sourceLonger
           $ branch isTargetMark targetMismatch finishAfterSource

    sourceLonger :: Compiler
    -- 開始時: 比較元マーク
    -- 終了時: 比較元終端の直後
    sourceLonger = foldl1 compose
      [ moveAfter (markerDirection, marker)
      , restoreTarget
      , seekSourceMark
      , restoreSourceMark
      ]

    targetMismatch :: Compiler
    -- 開始時: 比較先マーク
    -- 終了時: 比較先の不一致位置の左隣
    targetMismatch = foldl1 compose
      [ seekSourceMark
      , restoreSourceMark
      , moveAfter (markerDirection, marker)
      , restoreTarget
      , moveL
      ]

    finishAfterSource :: Compiler
    -- 開始時: 比較元終端
    -- 終了時: 比較先終端または余りの先頭
    finishAfterSource = foldl1 compose
      [ moveAfter (markerDirection, marker)
      , skipTargetMarks
      , branch (== targetEnd) cleanupFromTarget targetLonger
      ]

    targetLonger :: Compiler
    -- 開始時: 比較先に余った最初のビット
    -- 終了時: その左隣
    targetLonger = branch (== UTM.I) (write UTM.TI) (write UTM.TO)
                 `compose` cleanupFromTarget
                 `compose` moveL

    seekSourceMark :: Compiler
    -- 開始時: 比較先側
    -- 終了時: 直近の比較元マーク
    seekSourceMark = while (not . isSourceMark) (move (opposite markerDirection))

    restoreSource :: UTM.S -> Compiler
    restoreSource bit = seekSourceMark `compose` write bit

    restoreSourceMark :: Compiler
    -- 開始時: 比較元マーク
    -- 終了時: 同じセル
    restoreSourceMark = branch (== UTM.SI) (write UTM.I) (write UTM.O)

    skipTargetMarks :: Compiler
    -- 開始時: 比較先の先頭
    -- 終了時: 最初の非比較先マーク
    skipTargetMarks = while isTargetMark moveR

    restoreTarget :: Compiler
    -- 開始時: 比較先マーク列の先頭
    -- 終了時: 列直後の非マーク
    restoreTarget = while isTargetMark restoreBit

    restoreBit :: Compiler
    -- 開始時: 比較先マーク
    -- 終了時: その右隣
    restoreBit = branch (== UTM.TI) (write UTM.I) (write UTM.O) `compose` moveR

    cleanupFromTarget :: Compiler
    -- 開始時: 比較先側
    -- 終了時: 復元済み比較先列の直後
    cleanupFromTarget = moveAfter (UTM.L, marker) `compose` restoreTarget

    continueSource :: UTM.S -> Bool
    continueSource UTM.SI = False
    continueSource UTM.SO = False
    continueSource UTM.TI = False
    continueSource UTM.TO = False
    continueSource s | s == sourceEnd = False
    continueSource s      = isPlainBit s

    isSourceMark :: UTM.S -> Bool
    isSourceMark UTM.SI = True
    isSourceMark UTM.SO = True
    isSourceMark _      = False

    isTargetMark :: UTM.S -> Bool
    isTargetMark UTM.TI = True
    isTargetMark UTM.TO = True
    isTargetMark _      = False

    opposite :: UTM.D -> UTM.D
    opposite UTM.L = UTM.R
    opposite UTM.R = UTM.L

-- | テスト用ユーティリティ
test :: Compiler -> Tape -> IO ()
test comp ini = do
  let (_, p) = comp defEnv
      res    = eval (S 0, p) ini
  putStr $ merge (showTape ini) (showTape res)
  where
    merge :: [String] -> [String] -> String
    merge [lu, ll] [ru, rl] = unlines [lu ++ " --> " ++ ru, ll' ++ "     " ++ rl]
      where ll'  = ll ++ replicate (length lu - length ll) ' '
    merge _        _        = error "merge: invalid input"
