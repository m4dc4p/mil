{-# LANGUAGE TypeSynonymInstances #-}

import Prelude hiding (abs, succ)
import Text.PrettyPrint 
import Compiler.Hoopl
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified Printer.Common as PP
import Printer.LambdaCase
import Syntax.Common
import Syntax.LambdaCase hiding (Alt)
-- import qualified PrioSetLC as Prio

import qualified Syntax.LambdaCase as LC
import MIL hiding (_case)
import Util
import OptMIL
import LCToMIL
import DeadBlocks
import LCM

progM :: ([Name], ProgM C C) -> [Def] -> IO ()
progM prelude@(prims, _) progs = do
  putStrLn "\n ========= LambdaCase ================="
  putStrLn (render $ vcat (map printDef progs)) 
  putStrLn "\n ========= Unoptimized MIL ============"
  putStrLn (render $ printProgM (deadBlocks tops . compile tops prelude $ progs))

  let optProgs = mostOpt tops prelude . (compile tops prelude) $ progs

  putStrLn "\n ========= Optimized MIL =============="
  putStrLn (render $ printProgM optProgs)
           
    where
      tops = map fst progs

      printDef :: Def -> Doc
      printDef def = text (show (ppr def))

m205 :: Graph Stmt C C
m205 = mkFirst (BlockEntry undefined undefined ["g", "f", "x"]) <*>
       mkMiddles [Bind "v209" undefined {-"\ \app g * x/"-}
                , Bind "v1" undefined {-"\ \invoke v209/"-}
                , Bind "v208" undefined {-"\ \app f * v1/"-} 
                , Bind "v2" undefined {-"\ \invoke v208/"-}
                , Bind "v206" undefined {-"\ \goto return()"-} 
                , Bind "v207" undefined {-"\ \app v206 * v2/"-}] <*>
       mkLast (Done undefined undefined undefined {-"\ \invoke v207/"-})

-- Optimize a hand-writen MIL program.
milTest :: SimpleUniqueMonad (ProgM C C) -> IO ()
milTest prog = do
  let p = runSimpleUniqueMonad prog
      blocks = map (fst . fst) . allBlocks  
  putStrLn ("============== Original ================")
  putStrLn (render . printProgM $ p)
  putStrLn ("============== Optimized ===============")
  putStrLn (render . printProgM . mostOpt (blocks p) prelude $ p)

{-
   
   funny g y [] = []
   funny g y (x:xs) = (g y) x (funny g y xs)

===

mkData_Nil (): Nil
funny {} g: blockfunny(g)
blockfunny (g): closure absBody261 {g}
absBody261 {g} y: blockabsBody261(g, y)
blockabsBody261 (g, y): closure absBody292 {g, y}
absBody292 {g, y} xs:
  case xs of
    Nil -> altBodyNil310()
    Cons x xs' -> altBodyCons312(g, x, xs', y)
altBodyNil310 ():
  result307 <- mkData_Nil()
  mkData_Nil()
altBodyCons312 (g, x, xs', y):
  v314 <- g @ y
  v315 <- v314 @ x
  v316 <- blockfunny(g)
  v317 <- v316 @ y
  v318 <- v317 @ xs'
  v315 @ v318

-}
funnyFold = [("funny", 
              lam "g" $ \g ->
              lam "y" $ \y ->
              lam "xs" $ \xs ->
                _case xs (alt "Nil" [] (const mkNil) .
                          alt "Cons" ["x", "xs'"] 
                                (\ [x, xs'] ->
                                   (((g `app` y) `app` x) `app`
                                    ((((var "funny") `app` g) `app` y) `app`
                                     xs')))))]

{-

compose f g x = f (g x)

===

compose {} f: blockcompose(f)
blockcompose (f): closure absBody217 {f}
absBody217 {f} g: blockabsBody217(f, g)
blockabsBody217 (f, g): closure absBody226 {f, g}
absBody226 {f, g} x:
  v230 <- g @ x
  f @ v230
-}
compose = [("compose", composeDef)]
composeDef = lam "f" $ \f -> 
              lam "g" $ \g ->
              lam "x" $ \x -> f `app` (g `app` x)

{-

main = compose foo bar x
compose f g x = f (g x)

===

compose {} f: blockcompose(f)
blockcompose (f): closure absBody217 {f}
absBody217 {f} g: blockabsBody217(f, g)
blockabsBody217 (f, g): closure absBody226 {f, g}
absBody226 {f, g} x:
  v230 <- g @ x
  f @ v230
main (bar, foo, x):
  v233 <- blockcompose(foo)
  v234 <- v233 @ bar
  v234 @ x
-}
origExample = [("main", 
                var "compose" `app` 
                    var "a" `app` 
                    var "b" `app` 
                    var "x")
              , head compose]
{-
  hello = do
    v <- print p
    return ()

===

mkData_Unit (): Unit
print (): thunk printThunk []
printThunkBody (a): printThunk*(a)
printThunk {} a: thunk printThunkBody [a]
hello (p): thunk blockhello [p]
blockhello (p):
  v202 <- print()
  v203 <- v202 @ p
  v <- invoke v203
  mkData_Unit()

-}
hello = [("hello", bindE "_" (mPrint `app` lit 0) $ \_ -> ret mkUnit)]

{- Monadic compose (from mon6)

kleisli :: (b -> m c) -> (a -> m b) -> a -> m c

kleisli f g x = do
  v1 <- g x
  v2 <- f v1
  return v2

===

kleisli {} f: blockkleisli(f)
blockkleisli (f): closure absBody221 {f}
absBody221 {f} g: blockabsBody221(f, g)
blockabsBody221 (f, g): closure absBody232 {g, f}
absBody232 {g, f} x:
  v238 <- g @ x
  v1 <- invoke v238
  v237 <- f @ v1
  invoke v237

-}
kleisli = [("kleisli",
            lam "f" $ \f ->
            lam "g" $ \g ->
            lam "x" $ \x ->
              bindE "v1" (g `app` x) $ \v1 -> f `app` v1)]

{-

===

-}
printTest1 = [threeBinds, main]
  where
    main = ("main",
              bindE "()" (var "threeBinds" `app` 
                          (mPrint `app` var "a") `app` 
                          (mPrint `app` var "a") `app` 
                          (mPrint `app` var "a")) ret)
    threeBinds = ("threeBinds",
                  lam "f" $ \f ->
                  lam "g" $ \g ->
                  lam "h" $ \h ->
                    bindE "()" f $ \_ ->
                    bindE "()" g $ \_ -> 
                    bindE "()" h $ ret)

{-

  main = threeBinds print print print
  threeBinds f g h = do
    f
    g
    h
===

print (): thunk printThunk []
printThunkBody (a): printThunk*(a)
printThunk {} a: thunk printThunkBody [a]
main ():
  v201 <- print()
  v202 <- blockthreeBinds(v201)
  v203 <- print()
  v204 <- v202 @ v203
  v205 <- print()
  v204 @ v205
threeBinds {} f: blockthreeBinds(f)
blockthreeBinds (f): closure absBody220 {f}
absBody220 {f} g: blockabsBody220(f, g)
blockabsBody220 (f, g): closure absBody227 {f, g}
absBody227 {f, g} h:
  () <- invoke f
  () <- invoke g
  invoke h

-}
printTest2 = [doBinds, main]
  where
    main = ("main",
              var "doBinds" `app` mPrint `app` mPrint `app` mPrint)
    doBinds = ("doBinds",
                  lam "f" $ \f ->
                  lam "g" $ \g ->
                  lam "h" $ \h ->
                    bindE "()" f $ \_ ->
                    bindE "()" g $ \_ -> 
                    bindE "()" h $ id)

printTest3 = [threeBinds, main]
  where
    main = ("main",
              lam "x" $ \x -> 
                bindE "()" (var "threeBinds" `app` 
                    (mPrint `app` var "a") `app` 
                    (mPrint `app` var "a") `app` 
                    (mPrint `app` var "a")) $ \_ -> x)
    threeBinds = ("threeBinds",
                  lam "f" $ \f ->
                  lam "g" $ \g ->
                  lam "h" $ \h ->
                    bindE "()" f $ \_ ->
                    bindE "()" g $ \_ -> 
                    bindE "()" h $ \_ -> mkUnit)

{-
threeBinds = (\h :: #.t -> (\g :: #.t -> (\f :: #.t -> () :: #.t <- f;
                                                       () :: #.t <- g;
                                                       () :: #.t <- h;
                                                       Unit{})))
main = () :: #.t <- (((threeBinds ((print{} z))) ((print{} y))) ((print{} x)));
       Unit{}
================================================================================
printBody (a): print*(a)
print {} a: thunk printBody [a]
main (z, y, x):
  v201 <- print @ z
  v203 <- print @ y
  v204 <- closure absBodyabsBodythreeBinds {v201, v203}
  v205 <- print @ x
  v206 <- v204 @ v205
  () <- invoke v206
  mkData_Unit()
threeBinds {} h: closure absBodythreeBinds {h}
absBodythreeBinds {h} g: closure absBodyabsBodythreeBinds {h, g}
absBodyabsBodythreeBinds {h, g} f:
  thunk blockabsBodyabsBodythreeBinds [h, g, f]
blockabsBodyabsBodythreeBinds (h, g, f):
  () <- invoke f
  () <- invoke g
  () <- invoke h
  mkData_Unit()
-}
printTest4 = [threeBinds, main]
  where
    main = ("main",
            bindE "()" (var "threeBinds" `app` 
                        (mPrint `app` var "z") `app` 
                        (mPrint `app` var "y") `app` 
                        (mPrint `app` var "x")) $ \_ -> mkUnit)
    threeBinds = ("threeBinds",
                  lam "h" $ \h ->
                  lam "g" $ \g ->
                  lam "f" $ \f ->
                    bindE "()" f $ \_ ->
                    bindE "()" g $ \_ -> 
                    bindE "()" h $ \_ -> mkUnit)

{-
main = ((oneBind print{}) a)
oneBind = (\z :: #.t -> (\a :: #.t -> () :: #.t <- (z a);
                                      Unit{}))
================================================================================
printBody (a): print*(a)
print {} a: thunk printBody [a]
oneBind {} z: closure absBodyoneBind {z}
absBodyoneBind {z} a: thunk blockabsBodyoneBind [z, a]
blockabsBodyoneBind (z, a):
  v203 <- z @ a
  () <- invoke v203
  mkData_Unit()
main (a):
  v206 <- closure absBodyoneBind {print}
  v206 @ a
-}
printTest5 = [main, oneBind]
  where
    main = ("main",
            var "oneBind" `app` mPrint `app` var "a")
    oneBind = ("oneBind",
               lam "z" $ \z ->
               lam "a" $ \a ->
                 bindE "()" (z `app` a) $ ret)
{-
  if x > 10 
  then x + 1 + y
  else x + 1 + z
-}
lcmTest1 = [("lcmTest1"
            , lam "x" $ \x ->
              lam "y" $ \y ->
              lam "z" $ \z ->
                _case (x `gt` lit 10) 
                   (alt "True" [] (const $ x `plus` lit 1 `plus` y) .
                    alt "False" [] (const $ x `plus` lit 1 `plus` z)))]

lcmTest2 = [("lcmTest2"
            , lam "x" $ \x ->
              lam "y" $ \y ->
              lam "z" $ \z ->
                _case (x `gt` lit 10)
                   (alt "True" [] (const (var "foo" `app` x `app` y)) .
                    alt "False" [] (const (var "foo" `app` x `app` z))))]

-- Test that we recognized (f x) as anticipatable.
lcmTest3 = [("lcmTest3"
            , lam "x" $ \x ->
              lam "f" $ \f ->
              lam "g" $ \g ->
                (g `app` (f `app` x) `app` (f `app` x)))]


-- Test anticipatibility across procedures.
lcmTest4 = [("main", var "lcmTest3" `app` lit 2 `app` var "plus" `app` var "times")
           ,("lcmTest3"
            , lam "x" $ \x ->
              lam "f" $ \f ->
                lam "g" $ \g ->
                  (g `app` (f `app` x `app` x) `app` (f `app` x `app` x)))]
            
lcmTest5 = [("lcmTest5"
            , lam "x" $ \x ->
              lam "y" $ \y ->
              lam "z" $ \z ->
                _case (y `gt` z)
                   (alt "True" [] (const (var "foo" `app` x)) .
                    (alt "False" [] (const (_case (x `gt` z)
                                            (alt "True" [] (const (var "foo" `app` x `app` y)) .
                                             (alt "False" [] (const (var "foo" `app` x `app` z)))))))))]

-- A program where anticipatability of "foo @ a" oscillates
-- throughout. It is anticipated after ``lam "a" $ \a ->''
-- not anticipated after ``_case (var "foo" `app` a)'', and
-- anticipated again ``alt "D" ''.
lcmTest6 = [("lcmTest6"
            , lam "a" $ \a ->
              _case (var "foo" `app` a)
                 (alt "A" [] 
                  (const 
                   (_case a 
                    (alt "C" [] 
                     (const a) .
                     (alt "D" [] 
                      (const (var "foo" `app` a))))))))]

lcmTest7 = [("lcmTest6"
            , lam "a" $ \a ->
              _case a
                 (alt "A" [] 
                  (const 
                   (_case (var "foo" `app` a)
                    (alt "C" [] 
                     (const a) .
                     (alt "D" [] 
                      (const (var "foo" `app` a))))))))]
                
{-
  compose2 x f g = g (f x) f

===

compose2 {} x: blockcompose2(x)
blockcompose2 (x): closure absBody221 {x}
absBody221 {x} f: blockabsBody221(x, f)
blockabsBody221 (x, f): closure absBody232 {f, x}
absBody232 {f, x} g:
  v237 <- f @ x
  v238 <- g @ v237
  v238 @ f

-}
sortOfCompose = [("sortOfCompose"
                 , lam "x" $ \x ->
                   lam "f" $ \f ->
                   lam "g" $ \g ->
                     (g `app` (f `app` x) `app` f))]

-- Fully applied primitive
{-
primtest x y = x + y

===

primTest {} x: blockprimTest(x)
blockprimTest (x): closure absBody208 {x}
absBody208 {x} y: plus*(x, y)
-}
primTest1 = [("primTest"
            , lam "x" $ \x ->
              lam "y" $ \y -> plus x y)]
         
-- Partially apply primitive    
{-
primtest x = (x +)

===

plusClo2 {a} b: plus*(a, b)
primTest {} x: closure plusClo2 {x}
-}
primTest2 = [("primTest"
            , lam "x" $ \x -> var "plus" `app` x)]
             

{-
fact n a =
    case n - 1 of
      True -> a
      False -> fact (n - 1) (n * a)

main = fact 4 1
===

main ():
  v201 <- num 4
  v202 <- blockfact(v201)
  v203 <- num 1
  v202 @ v203
fact {} n: blockfact(n)
blockfact (n): closure absBody243 {n}
absBody243 {n} a:
  v276 <- num 1
  v277 <- lt*(n, v276)
  case v277 of
    True -> altBodyTrue265(a)
    False -> altBodyFalse267(a, n)
altBodyTrue265 (a): return a
altBodyFalse267 (a, n):
  v270 <- num 1
  v271 <- minus*(n, v270)
  v272 <- blockfact(v271)
  v274 <- times*(n, a)
  v272 @ v274

-}
fact = [("fact"
        , lam "n" $ \n ->
          lam "a" $ \a ->
            _case (n `lt` lit 1)
               (alt "True" [] (const a) .
                    alt "False" [] (const (var "fact" `app` (n `minus` lit 1) `app` (n `times` a)))))
       ,("main"
        , var "fact" `app` lit 4 `app` lit 1)]
         

{-
factCPS n k = 
    case n < 1 of
      True -> k 1
      False -> factCPS (n - 1) (\a -> k (n * a))

main = factCPS 4 id
id x = x
===

id {} x: return x
main (id):
  v204 <- num 4
  v205 <- blockfactCPS(v204)
  v205 @ id
factCPS {} n: blockfactCPS(n)
blockfactCPS (n): closure absBody259 {n}
absBody259 {n} k:
  v306 <- num 1
  v307 <- lt*(n, v306)
  case v307 of
    True -> altBodyTrue288(k)
    False -> altBodyFalse291(k, n)
altBodyTrue288 (k):
  v290 <- num 1
  k @ v290
altBodyFalse291 (k, n):
  v294 <- num 1
  v295 <- minus*(n, v294)
  v296 <- blockfactCPS(v295)
  v304 <- closure absBody297 {k, n}
  v296 @ v304
absBody297 {k, n} a:
  v303 <- times*(n, a)
  k @ v303
-}
factCPS = [("factCPS"
          , lam "n" $ \n ->
            lam "k" $ \k ->
              _case (n `lt` lit 1)
                 (alt "True" [] (const (k `app` lit 1)) .
                  alt "False" [] (const (var "factCPS" `app` 
                                         (n `minus` lit 1) `app` 
                                         (lam "a" $ \a -> 
                                          k `app` (n `times` a))))))
          ,("main"
           , var "factCPS" `app` lit 4 `app` var "id")
          ,("id"
           , lam "x" $ \x -> x)]

{-- 
Does not rewrite

  block1 (m):
    a <- invoke m
    a <- invoke m
    b <- invoke m
    return a

Can't rewrite the end because of an intervening
invoke. --}
testBindReturn1 :: UniqueMonad m => m (ProgM C C)
testBindReturn1 = do
  l1 <- freshLabel
  return $ mkFirst (BlockEntry "block1" l1 []) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkMiddle (Bind "b" (Run "m")) <*>
           mkLast (Done "block1" l1 (Return "a"))

{-
Should rewrite

block1 ():
  a <- invoke m
  b <- invoke m
  a <- invoke m
  return a

to

block1 ():
  a <- invoke m
  b <- invoke m
  invoke m

-}
testBindReturn2 :: UniqueMonad m => m (ProgM C C)
testBindReturn2 = do
  l1 <- freshLabel
  return $ mkFirst (BlockEntry "block1" l1 []) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkMiddle (Bind "b" (Run "m")) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkLast (Done "block1" l1 (Return "a"))

{-
Should rewrite

block1 ():
  a <- invoke m
  a <- invoke m
  return a

to

block1 ():
  a <- invoke m
  invoke m

-}
testBindReturn3 :: UniqueMonad m => m (ProgM C C)
testBindReturn3 = do
  l1 <- freshLabel
  return $ mkFirst (BlockEntry "block1" l1 []) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkLast (Done "block1" l1 (Return "a"))

{-
block1 ():
  a <- m
  b <- m
  a <- m
  return a

becomes

block1 (): 
  a <- m
  b <- m
  m
-}
testBindReturn4 :: UniqueMonad m => m (ProgM C C)
testBindReturn4 = do
  l1 <- freshLabel
  return $ mkFirst (BlockEntry "block1" l1 []) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkMiddle (Bind "b" (Run "m")) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkLast (Done "block1" l1 (Return "a"))

{-
block1 ():
  a <- m
  b <- return a
  c <- return b
  return c

becomes

block1 (): m

-}
testBindReturn5 :: UniqueMonad m => m (ProgM C C)
testBindReturn5 = do
  l1 <- freshLabel
  return $ mkFirst (BlockEntry "block1" l1 []) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkMiddle (Bind "b" (Return "a")) <*>
           mkMiddle (Bind "c" (Return "b")) <*>
           mkLast (Done "block1" l1 (Return "c"))

{-
Shows how this interacts with dead-code elimination.

block1 ():
  a < - m
  b <- return a
  c <- return b
  x <- clo block1 {}
  z <- C [] 
  return c

becomes

block1 (): m

-}
testBindReturn6 :: UniqueMonad m => m (ProgM C C)
testBindReturn6 = do
  l1 <- freshLabel
  return $ mkFirst (BlockEntry "block1" l1 []) <*>
           mkMiddle (Bind "a" (Run "m")) <*>
           mkMiddle (Bind "b" (Return "a")) <*>
           mkMiddle (Bind "c" (Return "b")) <*>
           mkMiddle (Bind "x" (Closure ("block1", l1) [])) <*>
           mkMiddle (Bind "z" (Constr "C" [])) <*>
           mkLast (Done "block1" l1 (Return "c"))

{-- 

main foo bar x = 
  let compse f g x = f (g x)
  in compose foo bar x

===

main (bar, foo, x):
  v234 <- blockabsBody201(foo)
  v235 <- v234 @ bar
  v235 @ x
blockabsBody201 (f): closure absBody219 {f}
absBody219 {f} g: blockabsBody219(f, g)
blockabsBody219 (f, g): closure absBody228 {f, g}
absBody228 {f, g} x:
  v232 <- g @ x
  f @ v232

 --}
origExample2 = [("main", 
                      _let "compose" composeDef $ \compose ->
                      compose `app` var "foo" `app` var "bar" `app` var "x")]

{-- From Mark
f x = let g y = x + y

       in g

===

f {} x: closure absBody208 {x}
absBody208 {x} y: plus*(x, y)

--}
letPlus = [("f", 
              lam "x" $ \x -> 
              _let "g" (lam "y" $ \y -> x `plus` y) $ \g -> g)]

{-- Mutually recursive -- will not compile correctly. No fix planned.
h z = let f y = y + g y
          g y = y + f y 
      in f z

===

h {} z:
  f <- closure absBody218 {g}
  f @ z
absBody218 {g} y:
  v224 <- plus*(y, g)
  v224 @ y
--}
letRec = [("h", 
              lam "z" $ \z -> 
              _let "f" (lam "y" $ \y -> y `plus` (var "g") `app` y) $ \f ->
              _let "g" (lam "y" $ \y -> y `plus` (var "f") `app` y) $ \g ->
              f `app` z)]

{-- Lambda-lifted mutually recursive version of the above.
f y g = y + g y f
g y f = y + f y g

h z = f z g

====

h {} z:
  v203 <- blockf(z)
  v203 @ g
g {} y: blockg(y)
blockg (y): closure absBody217 {y}
absBody217 {y} f:
  v224 <- blockf(y)
  v225 <- v224 @ g
  plus*(y, v225)
f {} y: blockf(y)
blockf (y): closure absBody239 {y}
absBody239 {y} g:
  v246 <- blockg(y)
  v247 <- v246 @ f
  plus*(y, v247)

--}
letRecLifted = [("f", lam "y" $ \y -> lam "g" $ \g -> y `plus` (g `app` y `app` var "f"))
               ,("g", lam "y" $ \y -> lam "f" $ \f -> y `plus` (f `app` y `app` var "g"))
               ,("h", lam "z" $ \z -> var "f" `app` z `app` var "g")]

{- 

  map f [] = []
  map f (x:xs) = f x : map f xs

===

mkData_Cons {} t1: closure Constr_Cons_1 {t1}
Constr_Cons_1 {t1} t2: Constr_Cons_0(t1, t2)
Constr_Cons_0 (t1, t2): Cons* t1 t2
mkData_Nil (): Nil*
map {} f: blockmap(f)
blockmap (f): closure absBody230 {f}
absBody230 {f} xs:
  case xs of
    Nil -> altBodyNil248()
    Cons x xs -> altBodyCons250(f, x, xs)
altBodyNil248 ():
  result245 <- mkData_Nil()
  mkData_Nil()
altBodyCons250 (f, x, xs):
  v252 <- mkData_Cons()
  v253 <- f @ x
  v254 <- v252 @ v253
  v255 <- blockmap(f)
  v256 <- v255 @ xs
  v254 @ v256

-}
myMap = [("map",
         lam "f" $ \f ->
         lam "xs" $ \xs ->
           _case xs $ (alt "Nil" [] (\_ -> mkNil) . 
            (alt "Cons" ["x", "xs"] (\ [x, xs] -> mkCons `app` (f `app` x) `app` (var "map" `app` f `app` xs)))))]

-- A function that return a variable directly
myId = ("id", lam "x" $ \x -> x)

-- A function that executes a monadic primitive
-- directly, with no function application
simplePrint = [("simplePrint", lam "x" $ \x -> bindE "()" (mPrint `app` x) $ \x -> ret x)]

-- A function where the result of a Case statement is
-- applied to an argument
caseTest1 = [("caseTest1",
           lam "f" $ \f ->
           lam "g" $ \g ->
           lam "x" $ \x ->
             (_case x $ (alt "True" [] (\_ -> f)) .
               (alt "False" [] (\_ -> g))) `app` x)]

-- A case statement on the right side of a bind
-- that evaluates to one of two monadic functions.
caseTest2 = [("caseTest2",
           lam "f" $ \f ->
           lam "g" $ \g ->
           lam "x" $ \x ->
             bindE "()" ((_case x $ (alt "True" [] (\_ -> f)) .
               (alt "False" [] (\_ -> g))) `app` x) $ \_ -> ret mkUnit)]

caseTest3 = [("caseTest3",
               lam "x" $ \x ->
               _case x $ (alt "True" [] (const mReadChar)) .
                (alt "False" [] (const (ret (lit 42)))))]


-- Ensure we don't evaulate monadic
-- expressions during function application.
mCase = [("mCase"
         , (lam "f" $ \f ->
            lam "r" $ \r ->
            f `app` (bindE "x" r $ \x -> x)) `app` 
          (lam "_" $ \_ -> lit 42) `app` 
          mPrint)]

monadTest1 = [("monadTest1"
              , bindE "c" mReadChar $ \c -> 
                bindE "()" (mPrint `app` c) ret)]

-- We run the monadic action
-- in the case arm.
monadTest2 = [("monadTest2"
              , bindE "c" mReadChar $ \c -> 
                _case c $ (alt "c" [] (\_ -> bindE "()" (mPrint `app` c) ret)))]

-- Ensure we don't evaulate monadic arguments with
-- function application.
monadTest3 = [("monadTest3"
              , var "f" `app` (bindE "()" (mPrint `app` lit 1) ret))
             ,("f" 
              , lam "x" $ \_ -> lit 1)]

monadTest4 = [("monadTest4"
               , _let "f" (bindE "()" (mPrint `app` lit 1) ret) $ \_ ->
                 mPrint `app` lit 2)]

-- Optimization goes really wrong here.
monadTest5 = [("monadTest5"
               , _let "f" (bindE "()" (mPrint `app` lit 1) ret) $ \f ->
                 _let "g" (lam "x" $ \_ -> bindE "()" (mPrint `app` lit 2) ret) $ \g ->
                 bindE "()" (g `app` f) ret)]

monadTest6 = [("monadTest6"
               , _let "f" (bindE "()" (mPrint `app` lit 1) ret) $ \f ->
                 _let "g" (lam "x" $ \_ -> bindE "()" (mPrint `app` lit 2) ret) $ \g ->
                 g `app` f)]

{-

From http://blog.omega-prime.co.uk/?p=135

main :: IO ()
main = do
    arr <- newArray_ (0, 200)
    go arr 2 0 100

go :: IOUArray Int Int -> Int -> Int -> Int -> IO ()
go arr stride x y | x < y     = do unsafeWrite arr (x * stride) 1337
                                   go arr stride (x + 1) y
                  | otherwise = return ()
-}
arrExample = [("main"
              , bindE "arr" (mNewArray 0 200) $ \arr ->
                var "go" `app` lit 2 `app` lit 0 `app` lit 100)
             ,("go", 
               lam "arr" $ \arr -> 
               lam "stride" $ \stride ->
               lam "x" $ \x ->
               lam "y" $ \y ->
                 _case (x `lt` y) $ 
                   (alt "True" [] $ \_ -> 
                      bindE "()" (mUnsafeWrite arr (x `times` stride) 1337) $ \_ ->
                        bindE "()" (var "go" `app` arr `app` stride `app` (x `plus` lit 1) `app` y) $ \v -> ret v) .
                   (alt "False" [] $ \_ -> ret mkUnit))]
  where
    mUnsafeWrite a i n = EPrim "unsafeWrite" typ [] `app` a `app` i `app` lit n
    mNewArray i l = EPrim "newArray_" typ [] `app` lit i `app` lit l

uncurry1 = [("uncurry1",
           lam "f" $ \f ->
           lam "g" $ \g ->
           lam "xs" $ \xs ->
           lam "test" $ \test ->
             _case test $
                (alt "True" [] $ \_ -> var "map" `app` f `app` xs) .
                (alt "False" [] $ \_ -> var "map" `app` g `app` xs))] ++ myMap

{- An example to demonstrate uncurrying across case statements.
   Does not work as "xs" appears as in a goto but it is not
   passed as an argument. -}
uncurry2 = [("uncurry2",
           lam "f" $ \f ->
           lam "g" $ \g ->
           lam "xs" $ \xs ->
           lam "test" $ \test ->
             _let "map1" (var "mapCap" `app` xs) $ \map1 ->
             _case test $
                (alt "True" [] $ \_ -> map1 `app` test `app` f) .
                (alt "False" [] $ \_ -> map1 `app` test `app` g))
           ,("mapCap",
            lam "xs" $ \xs ->
            lam "t" $ \t ->
            lam "f" $ \ f -> f `app` xs `app` t)]

uncurry3 = [("uncurry3",
           lam "f" $ \f ->
           lam "xs" $ \xs ->
           lam "test" $ \test ->
             _let "map1" (var "mapCap" `app` xs) $ \map1 ->
               map1 `app` f)
           ,("mapCap",
            lam "xs" $ \xs ->
            lam "f" $ \ f -> f `app` xs)]

myConst = [("const",
            lam "a" $ \a ->
            lam "b" $ \_ ->
              a)]

{- An example to demonstrate uncurrying across case statements.

Incorrectly rewrites :(

 ========= LambdaCase =================
uncurry4 = let val mapCap :: #.t
                 = (\xs :: #.t -> (\t :: #.t -> (\f :: #.t -> ((f xs) t))))
in let val map1 :: #.t
         = (mapCap xs) in case 1 of
                            1 -> ((map1 t) f)

 ========= Unoptimized MIL ============
L200 uncurry4 (t, f, xs):
  mapCap <- letBodymapCapL201()
  map1 <- letBodymap1L207(mapCap, xs)
  result213 <- caseEvalL211(map1, t, f)
  return result213
L201 letBodymapCapL201 (): closure absBodyL202 {}
L202 absBodyL202 {} xs: closure absBodyL203 {xs}
L203 absBodyL203 {xs} t: closure absBodyL204 {xs, t}
L204 absBodyL204 {xs, t} f: absBlockL205(xs, t, f)
L205 absBlockL205 (xs, t, f):
  v206 <- f @ xs
  v206 @ t
L207 letBodymap1L207 (mapCap, xs): mapCap @ xs
L208 altBody1L208 (map1, t, f):
  v209 <- map1 @ t
  v210 <- v209 @ f
  return v210
L211 caseEvalL211 (map1, t, f):
  v212 <- num 1
  case v212 of 1 -> altBody1L208(map1, t, f)

 ========= Optimized MIL ==============
L200 uncurry4 (t, f, xs):
  map1 <- closure absBodyL203 {xs}
  caseEvalL211(map1, t, f)
L203 absBodyL203 {xs} t: closure absBodyL204 {xs, t}
L204 absBodyL204 {xs, t} f: absBlockL205(xs, t, f)
L205 absBlockL205 (xs, t, f):
  v206 <- f @ xs
  v206 @ t
L208 altBody1L208 (map1, t, f): absBlockL205(xs, t, f)
L211 caseEvalL211 (map1, t, f):
  v212 <- num 1
  case v212 of 1 -> altBody1L208(map1, t, f)

-}
uncurry4 = [("uncurry4",
             _let "cap" (lam "ys" $ \ys ->
                            lam "g" $ \g ->
                            lam "v" $ \v -> g `app` v `app` ys) $ \cap ->
             _let "cap1" (cap `app` var "xs") $ \cap1 ->
             _case (var "t") $
                (alt "True" [] $ \_ -> cap1 `app` var "f" `app` var "y") .
                (alt "False" [] $ \_ -> cap1 `app` var "f" `app` var "n"))]

uncurry5 = [("uncurry5",
           lam "f" $ \f ->
           lam "xs" $ \xs ->
             _let "map1" (var "mapCap" `app` xs) $ \map1 ->
             _case (lit 1) $
                (alt "1" [] $ \_ -> 
                   _let "map2" (map1 `app` f) $ \map2  ->
                   _case (lit 2) $ 
                      (alt "1" [] $ \_ -> map2 `app` f) . 
                      (alt "2" [] $ \_ -> map2 `app` xs)) .
                (alt "0" [] $ \_ -> 
                   _let "map2" (map1 `app` xs) $ \map2  ->
                   _case (lit 3) $ 
                      (alt "1" [] $ \_ -> map2 `app` f) . 
                      (alt "3" [] $ \_ -> map2 `app` xs)))
           ,("mapCap",
            lam "xs" $ \xs ->
            lam "t" $ \t ->
            lam "f" $ \ f -> f `app` xs `app` t)]

uncurry_fig_compose_a = [("compose1", 
                          lam "f" $ \f -> var "compose" `app` f)
                        , head compose]


uncurry_fig_eg :: UniqueMonad m => m (ProgM C C)
uncurry_fig_eg = do
  main <- freshLabel
  k0 <- freshLabel
  k1 <- freshLabel
  add <- freshLabel
  toInt <- freshLabel
  let mainP = mkFirst (BlockEntry "main" main ["s"]) <*>
              mkMiddle (Bind "n" (Goto ("toInt", toInt) ["s"])) <*>
              mkMiddle (Bind "v0" (Closure ("k0",k0) [])) <*>
              mkMiddle (Bind "v1" (Enter "v0" "n")) <*>
              mkMiddle (Bind "v2" (Enter "v1" "n")) <*>
              mkLast (Done "main" main (Return "v2"))
      k0P = mkFirst (CloEntry "k0" k0 [] "a") <*> 
            mkLast (Done "k0" k0 (Closure ("k1", k1) ["a"]))
      k1P = mkFirst (CloEntry "k1" k1 ["a"] "b") <*>
            mkLast (Done "k1" k1 (Goto ("add", add) ["a", "b"]))
      addP = mkFirst (BlockEntry "add" add ["a", "b"]) <*>
             mkLast (Done "add" add (Prim "plus" ["a", "b"]))
      toIntP = mkFirst (BlockEntry "toInt" toInt ["s"]) <*>
               mkLast (Done "toInt" toInt (Prim "toInt" ["s"]))
  return $ mainP |*><*| k0P |*><*| k1P |*><*| addP |*><*| toIntP

mil_print = [("hello", bindE "_" (mPrint `app` lit 0) $ \_ -> ret mkUnit)
            ,("main", 
                    bindE "_" (var "hello") $ \_ -> 
                    bindE "_" (var "hello") $ \_ -> ret mkUnit)]

mil_twice = [("twice", 
                     lam "f" $ \f ->
                     lam "x" $ \x -> 
                       _let "m" (var "kleisli" `app` f `app` f `app` x) $ \m ->
                         m)] ++ kleisli


mil_bind = [("bind", lam "f" $ \f ->
               lam "x" $ \x -> 
                 bindE "y" (f `app` x) $ \y ->
                   (lam "z" $ \z -> z `app` y) `app` y)]

-- Safe decrement
safeDec = [("dec", 
                 lam "i" $ \i ->
                   _case (i `gt` lit 0) $
                    (alt "True" [] $ \_ -> mkJust (i `minus` (lit 1))) .
                    (alt "False" [] $ \_ -> mkNothing))
          ,("loop",
                  lam "n" $ \n ->
                  lam "f" $ \f ->
                    _case (var "dec" `app` n) $
                     (alt "Just" ["i"] $ \[i] -> f `app` (var "loop" `app` i `app` f)) .
                     (alt "Nothing" [] $ \_ -> f `app` (lit 0)))]

-- Safe decrement with a monadic action.
safeDecM = [("dec", 
                 lam "i" $ \i ->
                   _case (i `gt` lit 0) $
                    (alt "True" [] $ \_ -> mkJust (i `minus` (lit 1))) .
                    (alt "False" [] $ \_ -> mkNothing))
          ,("loop",
                  lam "n" $ \n ->
                  lam "f" $ \f ->
                    bindE "t" (_case (var "dec" `app` n) $
                     (alt "Just" ["i"] $ \[i] -> bindE "()" (f `app` i) $ \_ -> var "loop" `app` i `app` f) .
                     (alt "Nothing" [] $ \_ -> f `app` (lit 0))) $ \t -> ret t)]


_case :: Expr -> ([LC.Alt] -> [LC.Alt]) -> Expr
_case c f = ECase c (f [])

alt :: Id -> [Id] -> ([Expr] -> Expr) -> [LC.Alt] -> [LC.Alt]
alt cons vs f = (LC.Alt cons [] vs (f (map var vs)) :)

mPrint = EPrim "print" typ []
mReadChar = EPrim "readChar" typ []
mkUnit = ECon "Unit" [] typ
ret = (EPrim "return" typ [] `app`)

mkJust :: Expr -> Expr
mkJust expr = (ECon "Just" [typ] typ) `app` expr

mkNothing :: Expr
mkNothing = ECon "Nothing" [] typ

mkNil :: Expr
mkNil = ECon "Nil" [] typ

mkCons :: Expr
mkCons = ECon "Cons" [typ, typ] typ

bindE :: Id -> Expr -> (Expr -> Expr) -> Expr
bindE v body rest = EBind v typ body (rest (var v))

lam :: Id -> (Expr -> Expr) -> Expr
lam v body = ELam v typ (body (var v))

plus, minus, times, div :: Expr -> Expr -> Expr

lt, gt, lte, gte, eq, neq :: Expr -> Expr -> Expr

infixl 6 `plus`, `minus`
infixl 7 `times`, `div`
infix 4 `lt`, `gt`, `lte`, `gte`, `eq`, `neq`

plus a b = var "plus" `app` a `app` b
minus a b = var "minus" `app` a `app` b
times a b = var "times" `app` a `app` b
div a b = var "div" `app` a `app` b

lt a b = var "lt" `app` a `app` b
gt a b = var "gt" `app` a `app` b
lte a b = var "lte" `app` a `app` b
gte a b = var "gte" `app` a `app` b
neq a b = var "neq" `app` a `app` b
eq a b = var "eq" `app` a `app` b

infixl 0 `app`
app :: Expr -> Expr -> Expr
app f g = EApp f g

var :: Id -> Expr
var n = EVar n typ

lit :: Integer -> Expr
lit n = ENat n 

-- Allows a single name to be defined in a let.
_let :: Id -> Expr -> (Expr -> Expr) -> Expr
_let n body rest = ELet (Decls [Nonrec (Defn n typ (Right body))]) (rest (var n))

prim :: Id -> Int -> Expr
-- prim n cnt = EPrim n (take (cnt + 1) $ repeat typ) 
prim n _ = var n

typ = TyLabel "t"

instance Printable Def where
  ppr (name, body) = PP.text name PP.<+> PP.text "=" PP.<+> ppr body
