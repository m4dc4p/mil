{-# LANGUAGE TypeSynonymInstances #-}

import Prelude hiding (abs, succ)
import Text.PrettyPrint 
import Compiler.Hoopl
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified Printer.Common as PP

import Printer.LambdaCase
import Syntax.LambdaCase hiding (Alt)
import qualified Syntax.LambdaCase as LC
import MIL hiding (_case)
import Util
import OptMIL
import LCToMIL
import LCM

progM :: [(Name, Expr)] -> ([Name], ProgM C C) -> IO ()
progM progs prelude = do
    putStrLn "\n ========= Unoptimized ============"
    printResult progs (map (addLive tops) . map (compile tops prelude) . map (: []) $ progs)

    let optProgs = mostOpt tops prelude . (compile tops prelude) $ progs

    putStrLn "\n ========= Optimized Together ============="
    putStrLn (render $ printProgM optProgs)

    -- let (used, killed, ant) = anticipated optProgs
    --     avail = available ant killed optProgs
    --     early = earliest ant avail
    --     postpone = postponable early used optProgs
    --     late = latest early postpone used (allSuccessors optProgs)

    -- putStrLn "\n ========= Used Expressions ============="
    -- putStrLn (render $ printExprs used)

    -- putStrLn "\n ========= Killed Expressions ============="
    -- putStrLn (render $ printExprs killed)

    -- putStrLn "\n ========= Anticipated Expressions ============="
    -- putStrLn (render $ printExprs ant)

    -- putStrLn "\n ========= Available Expressions ============="
    -- putStrLn (render $ printExprs avail)

    -- putStrLn "\n ========= Earliest Expressions ============="
    -- putStrLn (render $ printExprs early)

    -- putStrLn "\n ========= Postponable Expressions ============="
    -- putStrLn (render $ printExprs postpone)

    -- putStrLn "\n ========= Latest Expressions ============="
    -- putStrLn (render $ printExprs late)

  where
    tops = map fst progs

    printExprs = vcat . map printExprMap . Map.toList 

    printWithDef :: (Def, ProgM C C) -> Doc
    printWithDef (def, comp) = text (show (ppr def)) $+$ 
                               vcat' (maybeGraphCC empty printBlockM comp)
                                     
    printExprMap ((n, _), exprs) = brackets $ text n <> colon <+> commaSep printTailM (Set.elems exprs)
    showTails = commaSep printTailM 

    printResult defs progs = putStrLn (render (vcat' (map ((text "" $+$) . printWithDef) (zip defs progs))))

                     
  

-- f g y [] = []
-- f g y (x:xs) = (g y) x (f g y xs)

funnyFold = ("funny", 
             lam "g" $ \g ->
             lam "y" $ \y ->
             lam "xs" $ \xs ->
               _case xs (alt "Nil" [] (const mkNil) .
                         alt "Cons" ["x", "xs'"] 
                               (\ [x, xs'] ->
                                  (((g `app` y) `app` x) `app`
                                   ((((var "funny") `app` g) `app` y) `app`
                                      xs')))))

compose :: Def
compose = ("compose", composeDef)

composeDef = lam "f" $ \f -> 
              lam "g" $ \g ->
              lam "x" $ \x -> f `app` (g `app` x)

origExample = [("main", var "compose" `app` var "foo" `app` var "bar" `app` var "x")
              , compose]

hello = ("hello", bindE "v" (mPrint `app` var "p") $ 
                  \v -> mkUnit)

{-
  if x > 10 
  then x + 1 + y
  else x + 1 + z
-}

lcmTest1 = ("lcmTest1"
           , lam "x" $ \x ->
             lam "y" $ \y ->
             lam "z" $ \z ->
               _case (x `gt` lit 10) 
                  (alt "True" [] (const $ x `plus` lit 1 `plus` y) .
                   alt "False" [] (const $ x `plus` lit 1 `plus` z)))

-- Monadic compose (from mon6)
kleisli = ("kleisli",
           lam "f" $ \f ->
           lam "g" $ \g ->
           lam "x" $ \x ->
             bindE "v1" (g `app` x) $ \v1 ->
             bindE "v2" (f `app` v1) id)

threeBinds = ("threeBinds",
              lam "f" $ \f ->
              lam "g" $ \g ->
              lam "h" $ \h ->
                bindE "()" f $ \_ ->
                bindE "()" g $ \_ -> 
                bindE "()" h $ \_ -> mkUnit)

printThree = [threeBinds, main]
  where
    main = ("main",
              var "threeBinds" `app` mPrint `app` mPrint `app` mPrint)
                

lcmTest2 = ("lcmTest2"
           , lam "x" $ \x ->
             lam "y" $ \y ->
             lam "z" $ \z ->
               _case (x `gt` lit 10)
                  (alt "True" [] (const (var "foo" `app` x `app` y)) .
                   alt "False" [] (const (var "foo" `app` x `app` z))))

-- Test that we recognized (f x) as anticipatable.
lcmTest3 = ("lcmTest3"
           , lam "x" $ \x ->
             lam "f" $ \f ->
             lam "g" $ \g ->
             (g `app` (f `app` x) `app` (f `app` x)))


-- Test anticipatibility across procedures.
lcmTest4 = [("main", var "lcmTest3" `app` lit 2 `app` var "plus" `app` var "times")
           ,("lcmTest3"
            , lam "x" $ \x ->
              lam "f" $ \f ->
                lam "g" $ \g ->
                  (g `app` (f `app` x `app` x) `app` (f `app` x `app` x)))]
            
lcmTest5 = ("lcmTest5"
           , lam "x" $ \x ->
             lam "y" $ \y ->
             lam "z" $ \z ->
               _case (y `gt` z)
                (alt "True" [] (const (var "foo" `app` x)) .
                 (alt "False" [] (const (_case (x `gt` z)
                                         (alt "True" [] (const (var "foo" `app` x `app` y)) .
                                          (alt "False" [] (const (var "foo" `app` x `app` z)))))))))

-- A program where anticipatability of "foo @ a" oscillates
-- throughout. It is anticipated after ``lam "a" $ \a ->''
-- not anticipated after ``_case (var "foo" `app` a)'', and
-- anticipated again ``alt "D" ''.
lcmTest6 = ("lcmTest6"
            , lam "a" $ \a ->
              _case (var "foo" `app` a)
                 (alt "A" [] 
                  (const 
                   (_case a 
                    (alt "C" [] 
                     (const a) .
                     (alt "D" [] 
                      (const (var "foo" `app` a))))))))

lcmTest7 = ("lcmTest6"
            , lam "a" $ \a ->
              _case a
                 (alt "A" [] 
                  (const 
                   (_case (var "foo" `app` a)
                    (alt "C" [] 
                     (const a) .
                     (alt "D" [] 
                      (const (var "foo" `app` a))))))))
                
compose2 = ("compose2"
           , lam "x" $ \x ->
             lam "f" $ \f ->
             lam "g" $ \g ->
             (g `app` (f `app` x) `app` f))

-- Fully applied primitive
primTest1 = ("primTest"
            , lam "x" $ \x ->
              lam "y" $ \y -> plus x y)
         
-- Partially apply primitive    
primTest2 = ("primTest"
            , lam "x" $ \x -> var "plus" `app` x)
             

fact = [("fact"
        , lam "n" $ \n ->
          lam "a" $ \a ->
            _case (n `lt` lit 1)
               (alt "True" [] (const a) .
                    alt "False" [] (const (var "fact" `app` (n `minus` lit 1) `app` (n `times` a)))))
       ,("main"
        , var "fact" `app` lit 4 `app` lit 1)]
         

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

factCP2S = [("factCPS"
          , lam "n" $ \n ->
            lam "k" $ \k ->
              _case n 
                 (alt "False" [] (const (var "factCPS" `app` 
                                         (n `minus` lit 1) `app` 
                                         (lam "a" $ \a -> k)))))
          ,("main"
           , var "factCPS" `app` var "id")]

-- Optimize a hand-writen MIL program.
milTest :: SimpleUniqueMonad (ProgM C C) -> IO ()
milTest prog = do
  let p = runSimpleUniqueMonad prog
      blocks = map (fst . fst) . allBlocks  
  putStrLn ("============== Original ================")
  putStrLn (render . printProgM $ p)
  putStrLn ("============== Optimized ===============")
  putStrLn (render . printProgM . mostOpt (blocks p) prelude $ p)

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
           mkMiddle (Bind "z" (ConstrM "C" [])) <*>
           mkLast (Done "block1" l1 (Return "c"))

_case :: Expr -> ([LC.Alt] -> [LC.Alt]) -> Expr
_case c f = ECase c (f [])

alt :: Name -> [Name] -> ([Expr] -> Expr) -> [LC.Alt] -> [LC.Alt]
alt cons vs f = (LC.Alt cons [] vs (f (map var vs)) :)

mPrint = EPrim "print" []
mkUnit = ECon "()" [] []

mkNil :: Expr
mkNil = ECon "Nil" [] []

bindE :: String -> Expr -> (Expr -> Expr) -> Expr
bindE v body rest = 
  let var = EVar v
  in EBind v typ body (rest var)

lam :: String -> (Expr -> Expr) -> Expr
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

var :: String -> Expr
var = EVar

lit :: Integer -> Expr
lit n = ELit (Lit n typ)

prim :: Name -> Int -> Expr
-- prim n cnt = EPrim n (take (cnt + 1) $ repeat typ) 
prim n _ = var n

typ = TyLabel "t"

instance Printable Def where
  ppr (name, body) = PP.text name PP.<+> PP.text "=" PP.<+> ppr body
