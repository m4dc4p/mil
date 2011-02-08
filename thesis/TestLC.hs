{-# LANGUAGE TypeSynonymInstances #-}

import Prelude hiding (abs, succ)
import Text.PrettyPrint 
import Compiler.Hoopl
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Printer.Common as PP

import Printer.LambdaCase
import Syntax.LambdaCase
import MIL
import Util
import OptMIL
import LCToMIL

progM progs = do
  let tops = map fst progs

      printWithDef :: (Def, ProgM C C) -> Doc
      printWithDef (def, comp) = text (showsPrec 0 (ppr def) "") $+$ 
                                 vcat' (maybeGraphCC empty printBlockM comp)

      printResult defs progs = putStrLn (render (vcat' (map ((text "" $+$) . printWithDef) (zip defs progs))))

      compileEach :: Def -> (Int, [ProgM C C]) -> (Int, [ProgM C C])
      compileEach p (i, ps) = 
        let (j, p') = compileM tops i p
        in (j,  addLive tops p' : ps)

      -- Compiles all procedures independently, so 
      -- we don't get any inter-procedure optimization
      compileInd = snd . foldr compileEach (0, []) 

      -- Compiles all procedures together so we do get inter-procedure
      -- optimization.
      compileAll opts = opts . foldr (|*><*|) emptyClosedGraph . snd . foldr compileEach (0, []) 
                     
  putStrLn "\n ========= Unoptimized ============"
  printResult progs (compileInd progs)
--  putStrLn "\n ========= Optimized Individually ============="
--  printResult (prepareExpr tops progs) (compileInd (inlineBlocks . deadBlocks . opt4 . opt3 . bindSubst) progs)
  putStrLn "\n ========= Optimized Together ============="
  putStrLn (render (printProgM (compileAll (mostOpt tops) progs)))


compose :: Def
compose = ("compose", composeDef)

composeDef = lam "f" $ \f -> 
              lam "g" $ \g ->
              lam "x" $ \x -> f `app` (g `app` x)

origExample = [("main", var "compose"  `app` var "foo" `app` var "bar")
              , compose]

hello = ("hello", bindE "v" 
                  (EApp mPrint (EVar "p")) $ \v -> mkUnit)

mPrint = EPrim "print" []
mkUnit = ECon "()" [] []

bindE :: String -> Expr -> (Expr -> Expr) -> Expr
bindE v body rest = 
  let var = EVar v
  in EBind v typ body (rest var)

lam :: String -> (Expr -> Expr) -> Expr
lam v body = body (var v)


infixl 0 `app`
app :: Expr -> Expr -> Expr
app f g = EApp f g

var :: String -> Expr
var = EVar

typ = error "type"    

instance Printable Def where
  ppr (name, body) = PP.text name PP.<+> PP.text "=" PP.<+> ppr body
