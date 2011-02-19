{-# LANGUAGE TypeSynonymInstances #-}

import Prelude hiding (abs, succ)
import Text.PrettyPrint 
import Compiler.Hoopl
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Printer.Common as PP

import Printer.LambdaCase
import Syntax.LambdaCase hiding (Alt)
import qualified Syntax.LambdaCase as LC
import MIL
import Util
import OptMIL
import LCToMIL
import LCM

progM progs prelude = do
    putStrLn "\n ========= Unoptimized ============"
    printResult progs (map (addLive tops) . map (compile tops predefined) . map (: []) $ progs)
    let optProgs = mostOpt tops . addLive tops . (compile tops predefined) $ progs
    putStrLn "\n ========= Optimized Together ============="
    putStrLn (render $ printProgM optProgs)
    putStrLn "\n ========= Anticipated Expressions ============="
    putStrLn (printAnticipated $ anticipated optProgs)

  where
    predefined = snd prelude
    tops = map fst progs ++ fst prelude

    printAnticipated :: [(Dest, AntFact)] -> String
    printAnticipated [] = "[]"
    printAnticipated ants = 
      let printAnt ((n, _), (AF (_, (env, exprs)))) = n ++ " " ++ show env ++ ": [" ++ 
                                           showTails (Set.elems exprs) ++ "]"
          showTails = render . commaSep printTailM 
      in foldr1 (\a b -> a ++ "\n" ++ b) (map printAnt ants)
    printWithDef :: (Def, ProgM C C) -> Doc
    printWithDef (def, comp) = text (show (ppr def)) $+$ 
                               vcat' (maybeGraphCC empty printBlockM comp)

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

lcmTest2 = ("lcmTest2"
           , lam "x" $ \x ->
             lam "y" $ \y ->
             lam "z" $ \z ->
               _case (x `gt` lit 10)
                  (alt "True" [] (const (var "foo" `app` x `app` y)) .
                   alt "False" [] (const (var "foo" `app` x `app` z))))

lcmTest3 = ("lcmTest3"
           , lam "x" $ \x ->
             lam "f" $ \f ->
             lam "g" $ \g ->
             (g `app` (f `app` x) `app` (f `app` x)))

compose2 = ("compose2"
           , lam "x" $ \x ->
             lam "f" $ \f ->
             lam "g" $ \g ->
             (g `app` (f `app` x) `app` f))

primTest1 = ("primTest"
            , lam "x" $ \x ->
              lam "y" $ \y -> plus x y)
             

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
