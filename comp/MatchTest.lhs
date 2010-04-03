-----------------------------------------------------------------------
-- Simple Tests for our MatchLang compiler(s).
--
-- Load using:  hugs -98 MatchTest
--
-- Mark P Jones, March 2009

> module MatchTest where

> import Control.Monad
> import MatchLang

Uncomment one of the following imports to select between the
stack-based compiler and the register-based compiler.

> --import StackComp
> import RegComp

-- Quick Tests: -------------------------------------------------------

> main = foldM (\_ (t,p) -> putStr ("\n" ++ t ++ "\n") >> test p) () 
>         [("program", program)
>         , ("program2", program2)
>         , ("compTest", compTest)
>         , ("consDefn", consDefn)
>         , ("mapDefn", mapDefn)
>         , ("idDefn", idDefn)
>         , ("constDefn", constDefn)
>         , ("compDefn", compDefn)]
>                           
> test  :: Expr -> IO ()
> test   = putStr
>        . unlines
>        . concat
>        . map showBlock
>        . reverse
>        . codeGen

> showBlock :: Block -> [String]
> showBlock (Block l is e)
>        = [l ++ ":"] ++ map (indent . show) is ++ [indent (show e)]
>          where indent x = "  " ++ x

> program = ELet "map" mapDefn
>         $ ELet "id"  idDefn
>         $ ELet "comp" compDefn
>         $ (EVar "map" `EApp`
>            ((EVar "comp" `EApp` EVar "id") `EApp` EVar "id"))

> program2 = ELet "cons" consDefn
>          $ EApp (EApp (EVar "cons")
>                       (ELit 1))
>                 (ECon "Nil" [])

> compTest = ELet "comp" compDefn
>            $ ELet "id" idDefn
>            $ EApp (EApp (EApp (EVar "comp")
>                               (EVar "id"))
>                         (EVar "id"))
>                    (ELit 1)

> consDefn = EMat 
>            $ MPat (PVar "x")
>              $ MPat (PVar "xs")
>                $ MExp (ECon "Cons" [EVar "x", EVar "xs"])

> mapDefn = EMat (m1 `MAlt` m2)
>  where m1 = MPat (PVar "f")
>             $ MPat (PCon "nil" [])
>               $ MExp (ECon "nil" [])
>        m2 = MPat (PVar "f")
>             $ MPat (PCon "cons" [PVar "x", PVar "xs"])
>               $ MExp (ECon "cons"
>                   [EVar "f" `EApp` EVar "x",
>                    (EVar "map" `EApp` EVar "f") `EApp` EVar "xs"])

> idDefn = EMat (MPat (PVar "x") (MExp (EVar "x")))

> constDefn = EMat 
>             $ MPat (PVar "x") 
>               $ MPat (PVar "y")
>                 $ MExp (EVar "x")

> compDefn = EMat (MPat (PVar "f") $
>                  MPat (PVar "g") $
>                  MPat (PVar "x") $
>                  MExp (EVar "f" `EApp`
>                       (EVar "g" `EApp` EVar "x")))

-----------------------------------------------------------------------
