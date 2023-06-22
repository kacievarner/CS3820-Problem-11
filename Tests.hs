{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, KindSignatures #-}
module Tests where

-- GHC
import System.Exit
import System.Environment
-- import System.IO.Silently

-- External
import Test.HUnit

-- Lib
import Problem11

--------------------------------------------------------------------------------
-- util
--------------------------------------------------------------------------------

err :: String -> String
err problem = problem ++ " is type-checking, not undefined, and not an infinite loop?\
                         \But you still have something wrong with it."

--------------------------------------------------------------------------------
-- Thms
--------------------------------------------------------------------------------

lt :: RTC2 Lt1 m (S m)
lt = Inst Lt1

lt_refl :: RTC2 Lt1 m m
lt_refl = Refl

lt_trans :: RTC2 Lt1 m (S (S m))
lt_trans = Trans lt lt

lt_refl_trans :: RTC2 Lt1 m m
lt_refl_trans = Trans lt_refl lt_refl

-- deeper nesting
lt_trans1 = Trans (lt_trans) (lt_trans)
lt_trans2 = Trans (lt_trans1) (lt_trans1)

build :: Int -> RTC2 Lt1 m m
build 0 = lt_refl
build n = Trans rel rel
  where rel = build (n - 1)


gt :: RTC2 Gt1 (S n) n
gt = conv2' lt

gt_refl :: RTC2 Gt1 m m
gt_refl = conv2' Refl

gt_trans :: RTC2 Gt1 (S (S m)) m
gt_trans = conv2' lt_trans

gt_trans2 :: RTC2 Gt1 (S m) m
gt_trans2 = conv2' (Trans lt lt_refl)

gt_refl_trans :: RTC2 Gt1 m m
gt_refl_trans = conv2' lt_refl_trans

--------------------------------------------------------------------------------
-- p1
--------------------------------------------------------------------------------

conv2' :: RTC2 Lt1 m n -> RTC2 Gt1 n m
conv2' = conv2


p1 :: Test
p1 = test $ [
  finite gt == () @? err "conv2",
  finite gt_refl == () @? err "conv2",
  finite gt_trans == () @? err "conv2",
  finite gt_trans2 == () @? err "conv2",
  finite (build 10) == () @? err "conv2",
  finite gt_refl_trans == () @? err "conv2",
  finite (conv2' lt_trans1) == () @? err "conv2",
  finite (conv2' lt_trans2) == () @? err "conv2"
  ]

  
--------------------------------------------------------------------------------
-- p2
--------------------------------------------------------------------------------

oneToTwo' :: RTC1 r m p -> RTC2 r m p
oneToTwo' = oneToTwo

twoToOne' :: RTC2 r m p -> RTC1 r m p
twoToOne' = twoToOne

refl1 :: RTC1 Lt1 m m
refl1 = Done
    
refl2 :: RTC2 Lt1 m m
refl2 = oneToTwo' Done

refl1_gt :: RTC1 Gt1 m m
refl1_gt = Done
refl2_gt :: RTC2 Gt1 m m
refl2_gt = oneToTwo' refl1_gt

trans :: RTC2 Lt1 m (S m)
trans = oneToTwo' (Step Lt1 Done)
trans2 :: RTC2 Gt1 (S m) m
trans2 = oneToTwo' (Step Gt1 Done)

p2 :: Test
p2 = test [
  finite refl1 == () @? err "oneToTwo",
  finite refl2 == () @? err "oneToTwo",
  finite refl1_gt == () @? err "oneToTwo",
  finite refl2_gt == () @? err "oneToTwo",
  finite trans == () @? err "oneToTwo",
  finite trans2 == () @? err "oneToTwo",
  -- twoToOne
  finite (twoToOne' lt) == () @? err "twoToOne",
  finite (twoToOne' lt_refl) == () @? err "twoToOne",
  finite (twoToOne' lt_trans) == () @? err "twoToOne",
  finite (twoToOne' lt_trans1) == () @? err "twoToOne",
  finite (twoToOne' lt_trans2) == () @? err "twoToOne",
  finite (twoToOne' lt_refl_trans) == () @? err "twoToOne",
  finite (twoToOne' gt) == () @? err "twoToOne",
  finite (twoToOne' gt_refl) == () @? err "twoToOne",
  finite (twoToOne' gt_trans) == () @? err "twoToOne",
  finite (twoToOne' gt_trans2) == () @? err "twoToOne",
  finite (twoToOne' gt_refl_trans) == () @? err "twoToOne",
  finite (twoToOne' . build $ 5) == () @? err "oneToTwo",
  finite (twoToOne' . build $ 10) == () @? err "oneToTwo"  
  ]
    
--------------------------------------------------------------------------------
-- p3
--------------------------------------------------------------------------------

conv1' :: RTC1 Lt1 m n -> RTC1 Gt1 n m
conv1' = conv1

p3 :: Test
p3 = test [
  finite refl   == () @? err "conv1",
  finite trans1 == () @? err "conv1",
  finite trans2 == () @? err "conv1",
  finite trans3 == () @? err "conv1",
  finite trans3' == () @? err "conv1"
  ]
  where
    refl :: RTC1 Gt1 m m
    refl = conv1' refl1
    
    trans1 :: RTC1 Gt1 (S m) m
    trans1 = conv1' (Step Lt1 Done)

    trans2 :: RTC1 Gt1 (S (S m)) (S m)
    trans2 = conv1' (Step Lt1 Done)

    trans3  :: RTC1 Gt1 (S (S m)) m
    trans3 = conv1' (Step Lt1 (Step Lt1 Done))
    
    trans3' :: RTC1 Gt1 (S (S m)) m
    trans3' = Step Gt1 trans1



--------------------------------------------------------------------------------
-- main
--------------------------------------------------------------------------------

argMap :: Int -> Test
argMap 1 = p1
argMap 2 = p2
argMap 3 = p3
argMap _ = test [p1, p2, p3]

hd :: [a] -> Maybe a
hd (x : _) = Just x
hd []       = Nothing

main :: IO ()
main = do
  args <- getArgs
  let tests = case read <$> (hd args) of
                Just x -> argMap x
                Nothing -> argMap 42
  results <- runTestTT tests
  if (errors results + failures results == 0)
    then
      exitWith ExitSuccess
    else
      exitWith (ExitFailure 1)
