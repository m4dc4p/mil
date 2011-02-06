import Prelude hiding (abs, succ)
import Text.PrettyPrint 
import Compiler.Hoopl
import Data.Set (Set)
import qualified Data.Set as Set

import Syntax.LambdaCase
import MIL
import Util
import OptMIL
import LCToMIL

progM progs = do
  let tops = map fst progs


      printWithDef :: (Def, ProgM C C) -> Doc
      printWithDef (def, comp) = vcat' (maybeGraphCC empty printBlockM comp)

      printResult defs progs = putStrLn (render (vcat' (map ((text "" $+$) . printWithDef) (zip defs progs))))

      compileEach :: Def -> (Int, [ProgM C C]) -> (Int, [ProgM C C])
      compileEach p (i, ps) = 
        let (j, p') = compileM tops i p
        in (j,  p' : ps)

      -- Compiles all procedures independently, so 
      -- we don't get any inter-procedure optimization
      compileInd = snd . foldr compileEach (0, []) 

                     
  putStrLn "\n ========= Unoptimized ============"
  printResult progs (compileInd progs)
--  putStrLn "\n ========= Optimized Individually ============="
--  printResult (prepareExpr tops progs) (compileInd (opt6 . opt5 . opt4 . opt3 . opt2) progs)
  -- putStrLn "\n ========= Optimized Together ============="
  -- putStrLn (render (printProgM (compileAll (opt6 . opt5 . opt4 . opt3 . opt2) progs)))


hello = ("hello", bindE "v" 
                  (EApp mPrint (EVar "p")) $ \v -> mkUnit)

mPrint = EPrim "print" []
mkUnit = ECon "()" [] []

bindE :: String -> Expr -> (Expr -> Expr) -> Expr
bindE v body rest = 
  let var = EVar v
  in EBind v typ body (rest var)
              
typ = error "type"    
