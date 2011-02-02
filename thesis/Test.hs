
import Prelude hiding (abs, succ)
import Text.PrettyPrint 
import Compiler.Hoopl
import Data.Set (Set)
import qualified Data.Set as Set

import Lambda3
import MIL
import Util

abs :: Var -> (Expr -> Expr) -> Expr
abs v f = Abs v [] (f (Var v))

isNil :: Def 
isNil = ("isNil", def)
  where
    def = abs "xs" $ \xs -> Case xs [Alt "Nil" [] true
                                       , Alt "Cons" ["a", "b"] false]
mapNot :: Def
mapNot = ("mapNot", def)
  where
    def = App (App (Var "myMap") 
                     (Var "isnt"))
          (cons (Constr "A" []) nil)

applyNil :: Def
applyNil = ("applyNil", def)
  where
    def = App (Var "nil") nil

isnt :: Def
isnt = ("isnt", def)
  where
    def = abs "f" $ \f -> Case f [Alt "True" [] false
                                 , Alt "False" [] true]

notNil :: Def
notNil = ("notNil", def)
  where
    def = abs "xs" $ \xs -> App (Var "isnt") (App (Var "nil") xs)

compose :: Def
compose = ("compose", composeDef)
composeDef = abs "f" $ \f -> 
              abs "g" $ \g ->
              abs "x" $ \x -> App f (App g x)

myMap :: Def
myMap = ("myMap", def)
  where
    def = abs "f" $ \f ->
          abs "xs" $ \xs ->
          Case xs [Alt "Nil" [] nil
                  , Alt "Cons" ["x", "xs"] (cons (App f (Var "x"))
                                                   (App (App (Var "myMap") f)
                                                        (Var "xs")))]

funky :: Def
funky  = ("funky", def)
  where
    -- \x y -> (case y of True -> (\z -> z))  x
    def = abs "x" $ \x ->
          abs "y" $ \y ->
          App (Case y [Alt "True" [] (abs "z" id)]) x

-- Live variables were screwed up with this one. You get the same
-- argument in the closure and the argument position:
--
--   bad = (\x {x}. Pair x x) y
--   [x] L1_absBody0 (x) {x}: Pair x x
--   [x,y] L3_bad (x,y):
--           v2 <- closure L1_absBody0 {x}
--           v2 @ y
--
-- Now fixed.
badClosure = ("bad", def)
  where
    --  (\x {}. Pair (g x) x) y
    def = App (abs "x" $ \x -> Constr "Pair" [x, x])
          (Var "y")

kennedy1 = [("kennedy1", def)
           , myFst
           , ("g", abs "x" id)]
  where
    -- From "Compiling with Continuations, Continued" by Andrew Knnedy
    -- Section 2.3, Problem 1
    --
    --   def = fst ((\x -> (g x, x)) y)
    -- 
    def = App (Var "fst") 
          (App (abs "x" $ \x -> 
                  Constr "Pair" [App (Var "g") 
                                     x, x]) 
           (Var "y"))

myFst = ("fst", fstDef)
  where
    fstDef = abs "p" $ \p -> Case p [Alt "Pair" ["l", "r"] (Var "l")]

origExample = [("main", App (App composeDef 
                            (Var "foo")) (Var "bar"))
              , compose]

-- demontrates cross-procedure uncurrying
origExampleX = [("main", App (App (Var "compose")
                            (Var "foo")) (Var "bar"))
              , compose]

origExample2 = [("main", App (App (App composeDef 
                                   (Var "foo")) 
                              (Var "bar"))
                 (Var "baz"))
              , compose]

-- demontrates cross-procedure uncurrying
origExample2X = [("main", App (App (App (Var "compose")
                                   (Var "foo")) 
                              (Var "bar"))
                 (Var "baz"))
              , compose]

const3 = [const3Def
         , ("main", App (App (App (Var "const3")
                                  (Var "1")) 
                              (Var "2")) 
                        (Var "3"))]
  where
    const3Def = ("const3", abs "a" $ \_ ->
                   abs "b" $ \_ ->
                   abs "c" $ \c -> c)

cons :: Expr -> Expr -> Expr                                        
cons x xs = Constr "Cons" [x, xs]

nil :: Expr
nil = Constr "Nil" []

false :: Expr
false = Constr "False" []

zero :: Expr
zero = Constr "Z" []

succ :: Expr -> Expr
succ z = Constr "S" [z]

true :: Expr
true = Constr "True" []

foldrX = [("foldr", foldrDef)
         , ("main", App (App (App (Var "foldr") 
                                  (Var "add"))
                             zero)
                        (cons (succ zero) nil))]
  where
    foldrDef = abs "f" $ \f ->
               abs "b" $ \b ->
               abs "as" $ \as ->
                 Case as [Alt "Nil" [] b
                         , Alt "Cons" ["a", "as'"] 
                                 (App (App (App (Var "foldr") f)
                                           (App (App f (Var "a")) b))
                                      (Var "as'"))]
                                  

-- f g y [] = []
-- f g y (x:xs) = (g y) x (f g y xs)

funnyFold = [("funny", 
             abs "f" $ \f ->
             abs "g" $ \g ->
             abs "y" $ \y ->
             abs "xs" $ \xs ->
               Case xs [Alt "Nil" [] nil
                       , Alt "Cons" ["x", "xs'"]
                             (App (App (App g y) (Var "x"))
                                 (App (App (App f g)
                                           y)
                                      (Var "xs'")))])]
         
                             
defs = [[isnt
        , mapNot
        , notNil
        , myMap]
       ,[isNil]
       , [applyNil]
       , [funky]
       , funnyFold
       , const3
       , kennedy1
       , origExample
       , origExampleX 
       , origExample2
       , origExample2X]
       

main = mapM_ progM defs

-- | Compile, run live analysis and pretty-print a 
-- lambda-definition to it's monadic form. Also prints
-- the live variables for each label.

progM progs = do
  let tops = map fst progs

      addLive = fst . usingLive addLiveRewriter tops
      opt2 = bindSubst 
      opt3 = fst . usingLive deadRewriter tops 
      opt4 = fst . usingLive deadRewriter tops . collapse
      -- deadBlocks tends to eliminate entry points
      -- we would need for separate compilation.
      opt5 = deadBlocks tops
      opt6 = inlineBlocks tops

      printLive :: FactBase LiveFact -> Block StmtM C x -> Doc
      printLive live p = 
        let label = fst (getEntryLabel p)
            vars = maybe [] Set.elems (lookupFact label live)
            livePrefix = if null vars
                         then text "[nothing live]"
                         else brackets (commaSep text vars) 
        in livePrefix <+> printBlockM p 

      printWithLive :: (Def, ProgM C C) -> Doc
      printWithLive (def, comp) = 
        let live = findLive tops comp
        in printDef def $+$
           vcat' (maybeGraphCC empty (printLive live) comp)

      printWithDef :: (Def, ProgM C C) -> Doc
      printWithDef (def, comp) = 
        printDef def $+$ vcat' (maybeGraphCC empty printBlockM comp)

      compileEach :: Def -> (Int, [ProgM C C]) -> (Int, [ProgM C C])
      compileEach p (i, ps) = 
        let (j, p') = compileM tops i p
        in (j, (addLive p') : ps)

      -- Compiles all procedures together so we do get inter-procedure
      -- optimization.
      compileAll opts = opts . foldr (|*><*|) emptyClosedGraph . snd . foldr compileEach (0, []) 

      -- Compiles all procedures independently, so 
      -- we don't get any inter-procedure optimization
      compileInd opt = map opt . snd . foldr compileEach (0, []) 

      printResult defs progs = putStrLn (render (vcat' (map ((text "" $+$) . printWithDef) (zip defs progs))))
                     
  putStrLn "\n ========= Unoptimized ============"
  printResult (prepareExpr tops progs) (compileInd id progs)
--  putStrLn "\n ========= Optimized Individually ============="
--  printResult (prepareExpr tops progs) (compileInd (opt6 . opt5 . opt4 . opt3 . opt2) progs)
  putStrLn "\n ========= Optimized Together ============="
  putStrLn (render (printProgM (compileAll (opt6 . opt5 . opt4 . opt3 . opt2) progs)))
           
