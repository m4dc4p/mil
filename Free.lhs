This module provides functions calculate the sets of variables that
are free/bound in various AST constructs.

> module Free(freeMatch, freeExpr, freePat, freeGuard, freeDecls) where

> import Data.List ((\\), union)
> import Habit.Syntax.AST
> import Habit.Syntax.Names (Name(..))

Matches and expressions can have free variables.  We will represent
sets of variables as lists of names without duplicates.  Functions
to calculate the set of free variables in any given instance of
these constructs can be defined as follows:

> freeMatch               :: Match ->[Name]
> freeMatch (MPat p m)     = freePat p (freeMatch m)
> freeMatch (MGrd g m)     = freeGuard g (freeMatch m)
> freeMatch (MAlt m1 m2)   = freeMatch m1 `union` freeMatch m2
> freeMatch (MFail _)      = []
> freeMatch (MExp e)       = freeExpr e

> freeExpr                :: Expr -> [Name]
> freeExpr (EVar name _ _) = [name]
> freeExpr (ELit l)        = []
> freeExpr (EApp e1 e2)    = freeExpr e1 `union` freeExpr e2
> freeExpr (ELet decls e)  = freeDecls decls (freeExpr e)
> freeExpr (EAbs m)        = freeMatch m
> freeExpr (ECase e m)     = freeExpr e `union` freeMatch m
> freeExpr (EInfix l n r)  = freeExpr l `union` (n : freeExpr r)
> freeExpr (EParens e)     = freeExpr e

Note that the case for EInfix is written in that way because union
allows (and removes) duplicate elements in the second list, which
could occur if n just happened to appear free in r.

Other constructs (specifically, patterns, guards, and declarations)
may include free variables, but they can also bind variables.  We
will describe the computation of free variables for these constructs
using functions that take the set of free variables in the program
fragment over which this construct scopes as an extra argument.
Again, we will not allow duplicates in these lists.  The free
variable functions for these cases can now be defined as follows:

> freePat                   :: Pat -> [Name] -> [Name]
> freePat (PVar n)       fvs = fvs \\ [n]
> freePat PWild          fvs = fvs
> freePat (PSig p _)     fvs = freePat p fvs
> freePat (PGrd p g)     fvs = freePat p (freeGuard g fvs)
> freePat (PCon n _ ps)  fvs = foldr ($) fvs (map freePat ps)

> freeGuard                 :: Guard -> [Name] -> [Name]
> freeGuard (GMatch p e) fvs = freeExpr e `union` freePat p fvs
> freeGuard (GLet decls) fvs = freeDecls decls fvs

> freeDecls                 :: Decls -> [Name] -> [Name]
> freeDecls decls fvs        = free \\ bound
>  where ds    = map decl (expl_decls decls) ++ impl_decls decls
>        bound = map decl_name ds
>        free  = foldr union fvs (map (freeMatch . decl_body) ds)

Note that the definition for freeDecls assumes letrec style
bindings, so none of the bound variables here can occur free in
the result.

-- Thanks to Mark for this one.
