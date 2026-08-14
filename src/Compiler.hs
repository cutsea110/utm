module Compiler where

import TM (Q(..), Delta, A(..), S(..), D(..), Tape, showTape
          , allSymbols, readOnlySymbols, writableSymbols, restrictedSymbols)
import Eval (eval)

data Env = Env { state :: Int
               }
         deriving (Show, Eq)

get :: Env -> TM.Q
get env = TM.S (state env)
next :: Env -> Env
next env = env { state = state env + 1 }
defEnv :: Env
defEnv = Env { state = 0 }

type Compiler = Env -> (Env, TM.Delta)

{- | write: primitives
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
write :: TM.S -> Compiler
write s env0
  | s `elem` candidates = (env1, code)
  | otherwise = error $ "try to write invalid symbol: " ++ show s
  where code = [ ((get env0, symbol), (get env1, TM.Write s))
               | symbol <- candidates
               ]
        env1 = next env0
        -- テープの delta を除く範囲のみ書き換え可能。従って s には以下のいずれかのみ受け入れる
        candidates = writableSymbols ++ restrictedSymbols

-- | erase: primitive
erase :: TM.D -> Compiler
erase d = while p (write TM.B `compose` move d)
  where
    p :: TM.S -> Bool
    p c | c == TM.B                  = False
        | c `elem` writableSymbols   = True
        | c `elem` readOnlySymbols   = error $ "try to erase read-only symbol: " ++ show c
        | c `elem` restrictedSymbols = error $ "try to erase restricted symbol: " ++ show c
        | otherwise                  = error $ "unexpected case: " ++ show c

{- | eraseR: 右へ1,0を空白に置き換えながら移動し、空白で停止
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
eraseR = erase TM.R

{- | eraseL: 左へ1,0を空白に置き換えながら移動し、空白で停止
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
eraseL = erase TM.L

-- | move: primitives
move :: TM.D -> Compiler
move d env0 = (env1, code)
  where code = [ ((get env0, symbol), (get env1, TM.Move d))
               | symbol <- allSymbols
               ]
        env1 = next env0

{- | moveR: 右へ1つ移動
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
moveR = move TM.R

{- | moveL: 左へ1つ移動
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
moveL = move TM.L

{- | moveTo: 指定方向で最初に見つかるシンボルまで移動する
>>> test (moveTo (R, SP)) ([I, I], I, [B, B, SP, I])
111__#1 --> 111__#1
  ^              ^
>>> test (moveTo (L, SP)) ([I, I, B, B, SP], I, [])
#__111 --> #__111
     ^     ^
-}
moveTo :: (TM.D, TM.S) -> Compiler
moveTo (direction, symbol) = while (/= symbol) (move direction)

{- | moveAfter: 指定方向で最初に見つかるシンボルの右隣へ移動する
>>> test (moveAfter (R, SP)) ([I, I], I, [B, B, SP, I])
111__#1 --> 111__#1
  ^               ^
>>> test (moveAfter (L, SP)) ([I, I, B, B, SP], I, [])
#__111 --> #__111
     ^      ^
-}
moveAfter :: (TM.D, TM.S) -> Compiler
moveAfter target = moveTo target `compose` moveR

{- | 逐次実行: c1の停止状態にc2を続けて実行する
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

{- | 条件分岐: ヘッドがcondを満たすときc1を、それ以外のときc2を実行する
>>> test (branch (== TM.I) (write O) (write I)) ([B, B], I, [B, B])
__1__ --> __0__
  ^         ^
>>> test (branch (== TM.I) (write O) (write I)) ([B, B], O, [B, B])
__0__ --> __1__
  ^         ^
-}
branch :: (S -> Bool) -> Compiler -> Compiler -> Compiler
branch predicate c1 c2 branchInitialEnv =
  (joinEnv, dispatch ++ c1Code ++ c2Code ++ join)
  where
    -- branchInitialState で条件を調べ、c1 または c2 の開始状態へ進む。
    -- 両方の終了状態は joinState に集め、branch の終了状態とする。
    branchInitialState = get branchInitialEnv

    -- c1 に渡す開始状態と、c1 が返す終了状態。
    c1InitialEnv = next branchInitialEnv
    (c1FinalEnv, c1Code) = c1 c1InitialEnv
    c1InitialState = get c1InitialEnv
    c1FinalState = get c1FinalEnv

    -- c1 の終了状態とは別の状態を、c2 の開始状態として確保する。
    c2InitialEnv = next c1FinalEnv
    (c2FinalEnv, c2Code) = c2 c2InitialEnv
    c2InitialState = get c2InitialEnv
    c2FinalState = get c2FinalEnv

    -- 二つの分岐を合流させる停止状態。後続の compose はここから始まる。
    joinEnv = next c2FinalEnv
    joinState = get joinEnv

    dispatch = [ ((branchInitialState, symbol),
                  (if predicate symbol then c1InitialState else c2InitialState, TM.Nop))
               | symbol <- allSymbols
               ]

    -- c1 と c2 の停止状態を共通の合流状態へつなぐ。branch はこの
    -- 合流状態を返すため、compose で後続のコンパイラをどちらの分岐の
    -- 後にも接続できる。
    join = [ ((finalState, symbol), (joinState, TM.Nop))
           | finalState <- [c1FinalState, c2FinalState]
           , symbol <- allSymbols
           ]

{- | ループ: ヘッドが preddicate を満たすとき body を実行し、それ以外のとき停止する
>>> test (while (/= TM.B) moveR) ([I, I], I, [I, I])
11111 --> 11111_
  ^            ^
>>> test (while (/= TM.B) moveR) ([I, I], I, [I, B])
1111_ --> 1111_
  ^           ^
>>> test (while (/= TM.B) moveR) ([I, I], B, [I, I])
11_11 --> 11_11
  ^         ^
-}
while :: (S -> Bool) -> Compiler -> Compiler
while predicate body whileInitialEnv =
  (whileFinalEnv, dispatch ++ bodyCode ++ loop)
  where
    -- whileInitialState で条件を調べ、条件を満たすと本体を実行する。
    whileInitialState = get whileInitialEnv

    -- 本体に渡す開始状態と、本体が返す終了状態。
    bodyInitialEnv = next whileInitialEnv
    (bodyFinalEnv, bodyCode) = body bodyInitialEnv
    bodyInitialState = get bodyInitialEnv
    bodyFinalState = get bodyFinalEnv

    -- 条件が偽のときに停止する状態。後続の compose はここから始まる。
    whileFinalEnv = next bodyFinalEnv
    whileFinalState = get whileFinalEnv

    dispatch = [ ((whileInitialState, symbol),
                  (if predicate symbol then bodyInitialState else whileFinalState, TM.Nop))
               | symbol <- allSymbols
               ]

    -- 本体の終了状態から、条件を再び調べる状態へ戻る。
    loop = [ ((bodyFinalState, symbol), (whileInitialState, TM.Nop))
           | symbol <- allSymbols
           ]

{- | 右へ1,0の列をスキップして空白で停止
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
skipSeqR = while (not . isPlainB) moveR
  where
    isPlainB :: TM.S -> Bool
    isPlainB TM.I = False
    isPlainB TM.O = False
    isPlainB TM.B = True
    isPlainB s    = error $ "skipSeqR: unexpected symbol while skipping non-Blanks: " ++ show s

{- | 左へ1,0の列をスキップして空白で停止
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
skipSeqL = while (not . isPlainB) moveL
  where
    isPlainB :: TM.S -> Bool
    isPlainB TM.I = False
    isPlainB TM.O = False
    isPlainB TM.B = True
    isPlainB s    = error $ "skipSeqL: unexpected symbol while skipping non-Blanks: " ++ show s

{- | copyTo: 非破壊的コピー
>>> test (copyTo (R, SP)) ([I, I], I, [B, B, SP])
111__# --> 111__#111
  ^        ^
>>> test (copyTo (R, SP)) ([O, O], O, [B, B, SP])
000__# --> 000__#000
  ^        ^
>>> test (copyTo (L, SP)) ([I, O, I, B, B, B, B, SP], I, [B, B, SP])
#____1011__# --> #10111011__#
        ^             ^
-}
copyTo :: (TM.D, TM.S) -> Compiler
copyTo (markerDirection, marker) = toMostSignificant `compose` copyBits `compose` restoreSource
  where
    toMostSignificant :: Compiler
    toMostSignificant = skipSeqL `compose` moveR

    copyBits :: Compiler
    copyBits = while isPlainBit copyBit

    copyBit :: Compiler
    copyBit = branch (== TM.I) copyI copyO

    copyI :: Compiler
    copyI = copyMarked TM.MI TM.I

    copyO :: Compiler
    copyO = copyMarked TM.MO TM.O

    copyMarked :: TM.S -> TM.S -> Compiler
    copyMarked sourceMark bit
      = foldl1 compose [write sourceMark, moveAfter (markerDirection, marker), skipSeqR, write bit, nextSource]

    seekMarkedSource :: Compiler
    seekMarkedSource = while (not . isMark) (move (opposite markerDirection))

    nextSource :: Compiler
    nextSource = case markerDirection of
      TM.R -> seekMarkedSource `compose` moveR
      TM.L -> seekMarkedSource `compose` while isMark moveR

    restoreSource :: Compiler
    restoreSource = moveL `compose` while isMark restoreBit `compose` moveR

    restoreBit :: Compiler
    restoreBit = branch (== TM.MI) (write TM.I) (write TM.O) `compose` moveL

    isPlainBit :: TM.S -> Bool
    isPlainBit TM.I = True
    isPlainBit TM.O = True
    isPlainBit TM.B = False
    isPlainBit s    = error $ "copyTo: unexpected source symbol: " ++ show s

    isMark :: TM.S -> Bool
    isMark TM.MI = True
    isMark TM.MO = True
    isMark _     = False

    opposite :: TM.D -> TM.D
    opposite TM.L = TM.R
    opposite TM.R = TM.L

{- | 現在位置を最下位桁とするビット列と、指定方向で最初に見つかる
区切り記号の右側にあるビット列を比較する。成功時はコピー先列の末尾の
空白 (`B`) で、不一致時は食い違った桁（または余った桁）の `I` / `O` で
停止する。終了時には、両方の列を含むテープは入力時と同じ状態へ復元される。

>>> test (matchTo (R, SP)) ([O, I], I, [B, B, SP, I, O, I])
101__#101 --> 101__#101_
  ^                    ^
>>> test (matchTo (L, SP)) ([O, I, B, I, O, I, SP], O, [])
#101_100 --> #101_100
       ^        ^
>>> test (matchTo (R, SP)) ([O, I], I, [B, B, SP, I, O])
101__#10 --> 101__#10
  ^            ^
>>> test (matchTo (R, SP)) ([I], O, [B, B, SP, I, O, I])
10__#101 --> 10__#101
 ^                  ^
-}
matchTo :: (TM.D, TM.S) -> Compiler
matchTo (markerDirection, marker) = toMostSignificant `compose` compareBits `compose` finish
  where
    toMostSignificant :: Compiler
    toMostSignificant = skipSeqL `compose` moveR

    compareBits :: Compiler
    compareBits = while continueSource compareBit

    compareBit :: Compiler
    compareBit = branch (== TM.I) compareI compareO

    compareI :: Compiler
    compareI = compareMarked TM.MI TM.HI TM.I

    compareO :: Compiler
    compareO = compareMarked TM.MO TM.HO TM.O

    compareMarked :: TM.S -> TM.S -> TM.S -> Compiler
    compareMarked sourceMark targetMark bit = foldl1 compose
      [ write sourceMark
      , moveAfter (markerDirection, marker)
      , skipTargetMarks
      , branch (== bit)
          (write targetMark `compose` restoreSource bit `compose` moveR)
          (branch (== TM.B) seekSourceMark (branch (== TM.I) (write TM.HI) (write TM.HO)))
      ]

    finish :: Compiler
    finish = branch isSourceMark sourceLonger
           $ branch isTargetMark targetMismatch finishAfterSource

    sourceLonger :: Compiler
    sourceLonger = foldl1 compose
      [ moveAfter (markerDirection, marker)
      , restoreTarget
      , seekSourceMark
      , restoreSourceMark
      ]

    targetMismatch :: Compiler
    targetMismatch = foldl1 compose
      [ seekSourceMark
      , restoreSourceMark
      , moveAfter (markerDirection, marker)
      , restoreTarget
      , moveL
      ]

    finishAfterSource :: Compiler
    finishAfterSource = foldl1 compose
      [ moveAfter (markerDirection, marker)
      , skipTargetMarks
      , branch (== TM.B) cleanupFromTarget targetLonger
      ]

    targetLonger :: Compiler
    targetLonger = branch (== TM.I) (write TM.HI) (write TM.HO)
                 `compose` cleanupFromTarget
                 `compose` moveL

    seekSourceMark :: Compiler
    seekSourceMark = while (not . isSourceMark) (move (opposite markerDirection))

    restoreSource :: TM.S -> Compiler
    restoreSource bit = seekSourceMark `compose` write bit

    restoreSourceMark :: Compiler
    restoreSourceMark = branch (== TM.MI) (write TM.I) (write TM.O)

    skipTargetMarks :: Compiler
    skipTargetMarks = while isTargetMark moveR

    restoreTarget :: Compiler
    restoreTarget = while isTargetMark restoreBit

    restoreBit :: Compiler
    restoreBit = branch (== TM.HI) (write TM.I) (write TM.O) `compose` moveR

    cleanupFromTarget :: Compiler
    cleanupFromTarget = moveAfter (TM.L, marker) `compose` restoreTarget

    continueSource :: TM.S -> Bool
    continueSource TM.I  = True
    continueSource TM.O  = True
    continueSource TM.B  = False
    continueSource TM.MI = False
    continueSource TM.MO = False
    continueSource TM.HI = False
    continueSource TM.HO = False
    continueSource s     = error $ "matchTo: unexpected source symbol: " ++ show s

    isSourceMark :: TM.S -> Bool
    isSourceMark TM.MI = True
    isSourceMark TM.MO = True
    isSourceMark _     = False

    isTargetMark :: TM.S -> Bool
    isTargetMark TM.HI = True
    isTargetMark TM.HO = True
    isTargetMark TM.I  = False
    isTargetMark TM.O  = False
    isTargetMark TM.B  = False
    isTargetMark s     = error $ "matchTo: unexpected target symbol: " ++ show s

    opposite :: TM.D -> TM.D
    opposite TM.L = TM.R
    opposite TM.R = TM.L

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
