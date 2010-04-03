-- A simple (naive) compiler translating programs/expressions in
-- a small lambda calculus into code for an simple stack-based
-- abstract machine.
--
-- The code in this file requires some language extensions beyond
-- the Haskell 98 standard.  To load this file in Hugs, use the
-- following command:
--
--   hugs -98 LambdaComp.hs
--
-- Mark P Jones, January 2009

module LambdaComp where

import List(nub, (\\))
import Control.Monad.State
import Control.Monad.Writer

--- Source Language: a simple lambda calculus:

data Exp  = Var Var
          | App Exp Exp
          | Lam Var Exp
          | Con Int
type Var  = String

fv          :: Exp -> [Var]    -- free variables
fv (Var v)   = [v]
fv (App f x) = nub (fv f ++ fv x)
fv (Lam v e) = fv e \\ [v]
fv (Con n)   = []

--- Some sample expressions:

comp :: Exp --- composition
comp  = Lam f $ Lam g $ Lam x $ App (Var f) (App (Var g) (Var x))
 where f = "f"; g = "g"; x = "x"

idd  :: Exp --- identity
idd   = Lam x (Var x)
 where x = "x"

ex1  :: Exp -- comp idd idd 42
ex1   = App (App (App comp idd) idd) (Con 42)

ex2  :: Exp -- (\i -> comp i i 42) idd
ex2   = App (Lam i (App (App (App comp (Var i)) (Var i)) (Con 42))) idd
 where i = "i"

--- Target Language, a simple stack machine:

data Inst = Push Loc        -- Push contents of specified location onto stack
          | Enter           -- Enter closure on top of stack (with arg below)
          | Alloc Lab Int   -- Allocate closure on top of stack with n var slots
          | Store Int Loc   -- Store value in closure on top of stack
            deriving Show

data Loc  = Arg             -- argument to this function (on the stack)
          | Clo Int         -- value stored in closure for this function
          | Const Int       -- a constant value
            deriving Show
         
data Code = Code Lab [Inst] -- labelled code segment
type Lab  = String          -- label

-- Environments, mapping source variables to locations in the target machine

type Env  = [(Var, Loc)]

app         :: Env -> Var -> Loc  -- lookup, should not fail
app rho v    = head [ l | (w,l) <- rho, w==v ]

--- A monad for compilation (generate fresh labels, output auxiliary code):

type M   = StateT Int          -- for generating new labels
             (Writer [Code])   -- for accumulating auxiliary code fragments

compile :: Exp -> [Code]
compile e = Code "main" is : cs
 where (is, cs) = runWriter (codegen e [] `evalStateT` 0)

codegen     :: Exp -> Env -> M [Inst]
codegen e rho
  = case e of
      Var v   -> return [Push (app rho v)]
      Con c   -> return [Push (Const c)]
      App f x -> do is1 <- codegen x rho
                    is2 <- codegen f rho
                    return (is1 ++ is2 ++ [Enter])
      Lam v b -> do l <- newLabel
                    let vis  = fv e `zip` [1..]
                        rho1 = (v, Arg) : [ (v, Clo i) | (v, i) <- vis ]
                    codegen b rho1 >>= \is-> tell [Code l is]
                    return (Alloc l (length vis)
                              : [ Store i (app rho v) | (v, i) <- vis ])

newLabel :: M Lab
newLabel  = do l <- get
               put (l+1)
               return ("l" ++ show l)

test :: Exp -> IO ()
test  = putStr . unlines . concat . map showCode . compile
 where showCode (Code l is) = [ l ++ ":"]
                           ++ [ "   " ++ show i | i <- is ]
                           ++ [ "   Ret", "" ]

------------------------------------------------------------------------
{- -- version without a monad; probably a little outdated by other
   -- changes that I made when I switched to using a monad:

codegen     :: Exp -> Env -> Lab -> (Lab, [Inst], [Code])
codegen e rho l
  = case e of
      Var v   -> (l, [Push (app rho v)], [])
      Con c   -> (l, [Push (Const c)], [])
      App f x -> let (l1, is1, cs1) = codegen x rho l
                     (l2, is2, cs2) = codegen f rho l1
                 in (l2, is1 ++ is2 ++ [Enter], cs1 ++ cs2)
      Lam v e -> let vis  = fv e `zip` [1..]
                     is   = Alloc l (length vis)
                            : [ Store i (app rho v) | (v, i) <- vis ]
                     rho1 = (v, Arg) : [ (v, Clo i) | (v, i) <- vis ]
                     (l1, is1, cs) = codegen e rho1 (l+1)
                 in (l1, is, (Code l is1):cs)
-}

------------------------------------------------------------------------
