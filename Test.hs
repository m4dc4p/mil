{-# LANGUAGE FlexibleInstances #-}
-- | Tests for register-based machine and compiler. 
-- Needs to be run from directory above tests/.
import Test.HUnit

import qualified Habit.Compiler.Register.Eval as ER (eval)
import qualified Habit.Compiler.Register.Machine as MR

main = runTestTT allTests

allTests = test [testMap
                , testMap2
                , testMap3
                , testMap4
                , testMap5
                , testMap6
                , testSimple
                , testComp
                , testFib
                , testAdd ]

-- | Test Map.hs
testMap = 
    let expected = 
            dataV "Map.Cons" .
                  dataL (dataS "Map.C" ) .
                  dataL (dataV "Map.Cons" .
                               dataL (dataS "Map.C") .
                               dataL (dataV "Map.Nil" []) $
                               dataE) $
                  dataE
    in expectResult "Map gives [Map.C,Map.C]" 
                    "tests\\Map.hs"
                    expected

-- | Test Map2.hs
testMap2 = 
    let expected = 
            dataV "Map2.Cons" .
                  dataL (dataS "Map2.B") .
                  dataL (dataV "Map2.Cons" .
                               dataL (dataS "Map2.C") .
                               dataL (dataV "Map2.Nil" []) $ 
                               dataE) $ 
                  dataE
    in expectResult "Map2 gives [Map2.B,Map2.C]" 
                    "tests\\Map2.hs"
                    expected

-- | Test Map3.hs.
testMap3 = 
    let expected = dataS "Map3.False" 
    in expectResult "Map3 gives [Map3.False]" 
                    "tests\\Map3.hs"
                    expected

-- | Test Map4.hs
testMap4 = 
    let expected = 
            dataV "Map4.Cons" .
                  dataL (dataS "Map4.A") .
                  dataL (dataV "Map4.Cons" .
                               dataL (dataS "Map4.B") .
                               dataL (dataV "Map4.Nil" []) $
                               dataE) $
                  dataE
    in expectResult "Map4 gives [Map4.A, Map4.B]" 
                    "tests\\Map4.hs"
                    expected
-- | Test Map5.hs
testMap5 = 
    let expected = 
            dataV "Map5.Cons" .
                  dataL (dataS "Map5.B") .
                  dataL (dataV "Map5.Cons" .
                               dataL (dataS "Map5.C") .
                               dataL (dataV "Map5.Nil" []) $ 
                               dataE) $ 
                  dataE
    in expectResult "Map5 gives [Map5.B,Map5.C]" 
                    "tests\\Map5.hs"
                    expected

-- | Test Map6.hs
testMap6 = 
    let expected = 
            dataV "Map6.Cons" .
                  dataL (dataS "Map6.C") .
                  dataL (dataV "Map6.Cons" .
                               dataL (dataS "Map6.C") .
                               dataL (dataV "Map6.Nil" []) $ 
                               dataE) $ 
                  dataE
    in expectResult "Map6 gives [Map6.C,Map6.C]" 
                    "tests\\Map6.hs"
                    expected
-- | Test Simple.hs
testSimple = 
    let expected = 
            dataV "Simple.Cons" .
                  dataL (dataS "Simple.Nil") .
                  dataL (dataV "Simple.Cons" .
                               dataL (dataS "Simple.Nil") .
                               dataL (dataV "Simple.Nil" []) $
                               dataE) $
                  dataE
    in expectResult "Simple gives [Simple.Nil,Simple.Nil]"
                    "tests\\Simple.hs"
                    expected

-- | Test Comp.hs
testComp = 
    let expected = dataS "Comp.A"
    in expectResult "Comp gives Comp.A" 
                    "tests\\Comp.hs"
                    expected

-- | Test Add.hs
testAdd = 
    let expected = mkNum "Add" 1
    in expectResult "Add gives 1" 
                    "tests\\Add.hs"
                    expected

-- | Test Fib.hs
testFib = 
    let expected = mkNum "Fib" 34
    in expectResult "Fib gives 34" 
                    "tests\\Fib.hs"
                    expected

-- | Convenience function to construct peano numbers.
mkNum :: String -> Int -> Val
mkNum mod 0 = dataV (mod ++ ".Z") dataE
mkNum mod n = dataV (mod ++ ".S") (dataL (mkNum mod (n - 1)) dataE)

expectResult :: String -> String -> Val -> Test
expectResult msg path expected = TestCase $ do 
  result <- ER.eval path
  case result of 
    Left s -> error $ "Error evaluating " ++ msg ++ ": " ++ s
    Right v -> assertEqual msg expected (toVal v)
  


-- | Values our tests understand
data Val = LitV String
         | DataV Tag [Val]
         | IntV Int
         | ErrorV String
           deriving (Eq, Show)

type Tag = String

-- | Help construct a list of values.
dataL :: Val -> [Val] -> [Val]
dataL v1 = (v1 :)

-- | Help constructing one value in a list.
dataV :: Tag -> [Val] -> Val
dataV t vs = DataV t vs

-- | Help construct a singleton value.
dataS :: Tag -> Val
dataS t = DataV t []

-- | End a list of values.
dataE :: [Val]
dataE = []

-- | Make a string literal.
litV :: String -> Val
litV = LitV

-- | Make an integer value
intV :: Int -> Val
intV = IntV

-- | Convert a value to a test value we understand
class ToVal a where
    toVal :: a -> Val

instance ToVal (MR.Val) where
    toVal (MR.Num i) = IntV i
    toVal (MR.Data t vs) = DataV t (map toVal vs)
    toVal (MR.Str s) = LitV s
