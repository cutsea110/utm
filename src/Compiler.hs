module Compiler where

import TM (Q(..), Delta, A(..), S(..), D(..), Tape, showTape)
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


-- | write: primitives
write :: TM.S -> Compiler
write s env0 = (env1, code)
  where code = [ ((get env0, symbol), (get env1, TM.Write s))
               | symbol <- [TM.I, TM.O, TM.B]
               ]
        env1 = next env0

-- | erase: primitive
erase :: TM.D -> Compiler
erase d = while (/= TM.B) (write TM.B `compose` move d)

-- | eraseR: 右へ1,0を空白に置き換えながら移動し、空白で停止
eraseR :: Compiler
eraseR = erase TM.R

eraseL :: Compiler
eraseL = erase TM.L

-- | move: primitives
move :: TM.D -> Compiler
move d env0 = (env1, code)
  where code = [ ((get env0, symbol), (get env1, TM.Move d))
               | symbol <- [TM.I, TM.O, TM.B]
               ]
        env1 = next env0

-- | moveR: 右へ1つ移動
moveR :: Compiler
moveR = move TM.R

-- | moveL: 左へ1つ移動
moveL :: Compiler
moveL = move TM.L

-- | 逐次実行: c1の停止状態にc2を続けて実行する
compose :: Compiler -> Compiler -> Compiler
(c1 `compose` c2) env0 = (env2, code1 ++ code2)
  where
    (env1, code1) = c1 env0
    (env2, code2) = c2 env1

-- | 条件分岐: ヘッドがcondを満たすときc1を、それ以外のときc2を実行する
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
               | symbol <- [TM.I, TM.O, TM.B]
               ]

    -- c1 と c2 の停止状態を共通の合流状態へつなぐ。branch はこの
    -- 合流状態を返すため、compose で後続のコンパイラをどちらの分岐の
    -- 後にも接続できる。
    join = [ ((finalState, symbol), (joinState, TM.Nop))
           | finalState <- [c1FinalState, c2FinalState]
           , symbol <- [TM.I, TM.O, TM.B]
           ]

-- | ループ: ヘッドが preddicate を満たすとき body を実行し、それ以外のとき停止する
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
               | symbol <- [TM.I, TM.O, TM.B]
               ]

    -- 本体の終了状態から、条件を再び調べる状態へ戻る。
    loop = [ ((bodyFinalState, symbol), (whileInitialState, TM.Nop))
           | symbol <- [TM.I, TM.O, TM.B]
           ]

-- | 右へ1をスキップして0,空白で停止
skip1sR :: Compiler
skip1sR = while (== TM.I) moveR

-- | 左へ1をスキップして0,空白で停止
skip1sL :: Compiler
skip1sL = while (== TM.I) moveL

-- | 右へ0をスキップして1,空白で停止
skip0sR :: Compiler
skip0sR = while (== TM.O) moveR

-- | 左へ0をスキップして1,空白で停止
skip0sL :: Compiler
skip0sL = while (== TM.O) moveL

-- | 右へ空白をスキップして1,0で停止
skipBlankR :: Compiler
skipBlankR = while (== TM.B) moveR

-- | 左へ空白をスキップして1,0で停止
skipBlankL :: Compiler
skipBlankL = while (== TM.B) moveL

-- | 右へ1,0の列をスキップして空白で停止
skipSeqR :: Compiler
skipSeqR = while (/= TM.B) moveR

-- | 左へ1,0の列をスキップして空白で停止
skipSeqL :: Compiler
skipSeqL = while (/= TM.B) moveL

-- | 最下位桁にいる状態から1を加える
add1 :: Compiler
add1 env0 = (env2, code)
  where
    code = [ ((s0, TM.I), (s1, TM.Write TM.O))
           , ((s0, TM.O), (s2, TM.Write TM.I))
           , ((s0, TM.B), (s2, TM.Write TM.I))
           , ((s1, TM.I), (s0, TM.Move TM.L))
           , ((s1, TM.O), (s0, TM.Move TM.L))
           ]
    s0   = get env0
    s1   = get env1
    s2   = get env2
    env1 = next env0
    env2 = next env1

-- | 最下位桁にいる状態から1を減らす
sub1 :: Compiler
sub1 env0 = (env2, code)
  where
    code = [ ((s0, TM.I), (s2, TM.Write TM.O))
           , ((s0, TM.O), (s1, TM.Write TM.I))
           , ((s0, TM.B), (s2, TM.Write TM.B))
           , ((s1, TM.I), (s0, TM.Move TM.L))
           , ((s1, TM.O), (s0, TM.Move TM.L))
           ]
    s0   = get env0
    s1   = get env1
    s2   = get env2
    env1 = next env0
    env2 = next env1

-- | 非破壊的二項演算 (桁数指定) : 2引数目を破壊しないが保存領域確保のために適切な桁数を指定する必要がある
--   x y と2つの列が空白で区切られている状態で y の最下位桁にいる状態から、x + y を計算する
--   x y の列が最終的に x `op` y な2進数列と y の列になる (y が保存される)
bin :: Int -> Compiler -> Compiler
bin digit op = initBackup `compose` backHome `compose` skip0sL `compose` while (/= TM.B) step `compose` recover
  where
    initBackup = foldl1 compose (replicate (digit+1) moveR ++ [write TM.O])
    backHome   = foldl1 compose [skipSeqL, skipBlankL]
    step       = foldl1 compose [ skipSeqR, moveL
                                , sub1, skipSeqL, skipBlankL, op
                                , skipSeqR, skipBlankR, skipSeqR, skipBlankR, skipSeqR, moveL, add1
                                , skipSeqL, skipBlankL, skip0sL
                                ]
    recover    = foldl1 compose [moveR, skipSeqR, skipBlankR, skipSeqR, moveL, plus', moveR, eraseR, skipBlankL]

-- | 非破壊加算
plus :: Int -> Compiler
plus digit = bin digit add1

-- | 非破壊的減算
minus :: Int -> Compiler
minus digit = bin digit sub1

-- | 破壊的二項演算 (2引数目を0に破壊します)
--   x y と2つの列が空白で区切られている状態で y の最下位桁にいる状態から、x + y を計算する
--   x y の列が最終的に x `op` y な2進数列と 00.. の列になる
bin' :: Compiler -> Compiler
bin' op = skip0sL `compose` while (/= TM.B) body
  where
    body = foldl1 compose [skipSeqR, moveL, step1, skip0sL]
    sub1L = sub1 `compose` skipSeqL
    back  = foldl1 compose [skipSeqR, skipBlankR, skipSeqR, moveL]
    step1 = foldl1 compose [sub1L, skipBlankL, op, back]

-- | 破壊的加算
plus' :: Compiler
plus' = bin' add1

-- | 破壊的減算
minus' :: Compiler
minus' = bin' sub1

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
