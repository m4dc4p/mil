-----------------------------------------------------------------------
-- Abstract syntax for a lambda calculus with matches.
--
-- Mark P Jones, March 2009

> module MatchLang where

> import List(union, (\\))

-- Source Language ----------------------------------------------------

> type Var   = String             -- variable

> data Expr  = EVar Var           -- var
>            | ECon CFun [Expr]   -- C e1 ... en
>            | EApp Expr Expr     -- f x
>            | ELet Var Expr Expr -- let v = e in e'
>            | EMat Match         -- { m }
>            | ELit Int           -- Literal value i

> type CFun  = String             -- constructor function

> data Match = MPat Pat Match     -- p -> m
>            | MGrd Guard Match   -- g; m
>            | MAlt Match Match   -- m OR m
>            | MExp Expr          -- ^ e

> data Pat   = PCon CFun [Pat]   -- C p1 ... pn
>            | PVar Var          -- v
>            | PGrd Pat Guard    -- (p | g)

> data Guard = GLet Var Expr     -- let v = e
>            | GGet Pat Expr     -- p <- e

-- Free Variables: ----------------------------------------------------

> freeExpr                :: Expr -> [Var]
> freeExpr (EVar v)        = [v]
> freeExpr (ECon c es)     = foldr union [] (map freeExpr es)
> freeExpr (EApp e1 e2)    = freeExpr e1 `union` freeExpr e2
> freeExpr (ELet v e e')   = freeExpr e `union` (freeExpr e' \\ [v])
> freeExpr (EMat m)        = freeMatch m
> freeExpr (ELit _)        = []

> freeMatch               :: Match ->[Var]
> freeMatch (MPat p m)     = freePat p (freeMatch m)
> freeMatch (MGrd g m)     = freeGuard g (freeMatch m)
> freeMatch (MAlt m1 m2)   = freeMatch m1 `union` freeMatch m2
> freeMatch (MExp e)       = freeExpr e

> freePat                 :: Pat -> [Var] -> [Var]
> freePat (PCon c ps)  fvs = foldr freePat fvs ps
> freePat (PVar v)     fvs = fvs \\ [v]
> freePat (PGrd p g)   fvs = freePat p (freeGuard g fvs)

> freeGuard               :: Guard -> [Var] -> [Var]
> freeGuard (GLet v e) fvs = freeExpr e `union` (fvs \\ [v])
> freeGuard (GGet p e) fvs = freeExpr e `union` freePat p fvs

-----------------------------------------------------------------------
