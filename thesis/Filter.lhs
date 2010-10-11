What does it look like when we compile ``filter''
to our language of blocks and closure captures (MBC)? 

First, ``filter'' in Habit (I use case statements to reduce the number
of source expressions that need to be transformed):

> filter :: (a -> Bool) -> [a] -> [a]
> filter f xs = 
>   case xs of
>     Nil -> Nil
>     Cons x xs' -> case f x of
>       True -> Cons x (filter f xs')
>       _ -> filter f xs'


The first transformation turns the definition of ``filter''
into a series of ``closure'' and ``block'' 
definitions. 

The first closure definition, below, captures the predicate argument
(f). The notation ``{}'' indicates variables held in the closure when the
function is invoked. filter0 does not expect any variables in the
closure. The ``Alloc'' result type means memory might be allocated
when the value is computed. ``filter0'' constructs a closure for ``filter1'', 
which allocates memory (NB: what about regular data -- do we differentiate). 

> filter0 :: (a -> Bool) -> Alloc ([a] -> Alloc (((a -> Bool), [a]) -> Alloc [a]))
> filter0 {} f = filter1 {f}

``filter1'' finds one argument in its closure (``f'') and expects
a second argument ``xs''. It constructs a closure which points to
filter, the ``block'' that actually executes the function. Again,
``Alloc'' means memory will be allocated, due to the closure constructed.

> filter1 :: [a] -> Alloc (((a -> Bool), [a]) -> Alloc [a])
> filter1 {f} xs = filter(f,xs)

``filter'' now takes a tuple of arguments, instead of separate
arguments as in the original program. A ``block'' requires that all
arguments be present, and a tuple guarantees that. The recursive call
to filter makes the result type ``Alloc'' as well, since a closure
will be constructed when the call is made (NB: Will tail-recursive functions
NOT have the Alloc type? What about mutually recursive? Non-recursive?).

> filter :: ((a -> Bool), [a]) -> Alloc [a]
> filter(f, xs) = do
>   case xs of
>     Nil -> fb1
>     Cons x xs' -> fb2(f, x, xs')

Each case arm can only contain a call to another block, which explains
``fb1'' and ``fb2'' above. ``fb1'' doesn't do much:

> fb1 :: Alloc a
> fb1 = Nil

``fb2'', however, tests the element given:

> fb2 :: ((a -> Bool), a, [a]) -> Alloc [a]
> fb2(f, x, xs') = do
>   let v3 = f(x)
>   case v3 of
>     True -> fb3(v1, v2, xs')
>     _ -> fb4(v1, xs')

``fb3'' and ``fb4'' both handle the recursive call to ``filter''.  An
obvious optimization would be to call ``filter'' directly, instead of
going through the closure capture process again, but we'll leave that
to later:

> fb3 :: ((a -> Bool), a, [a]) -> Alloc [a]
> fb3(f, x, xs) = do
>   let xs' = (filter0 f) xs
>   Cons x xs'
>
> fb4 :: ((a -> Bool), [a]) -> Alloc [a]
> fb4(f, xs) = (filter0 f) xs

The entire program:

> filter(f, xs) = do
>   let v = xs
>   case v of
>     Nil -> fb1
>     Cons x xs' -> fb2(f, x, xs')
>
> fb1 = Nil
>
> fb2(f, x, xs') = 
>   let v1 = f 
>       v2 = x
>       v3 = v1(v2)
>   case v3 of
>     True -> fb3(v1, v2, xs')
>     _ -> fb4(v1, xs')
>
> fb3(f, x, xs) = 
>   let xs = filter(f, xs)
>   Cons x xs'
>
> fb4(f, xs) = filter(f, xs)


*****

Now let's try writing some compilation rules. Our lambda-like language
has top-level definitions, algebraic data-types (ADTs) with
constructors, case statements, applications, and let
statements. Static typing is assumed but not shown. Local, anonymous
functions and pattern-matching are missing.

A program is sequence of top-level definitions:

  program ::= def1 -- DEF
              def2
              ...
              defN

Each definition is a function or an ADT. Functions and constructors
can specify zero or more arguments. ``func'' is the function's name,
"C1", "C2", etc. are the constructors for ADT "C":

  def ::= func a1 ... aN = expr -- FUNC
       || data C = C1 a1 ... aN  -- DATA
                   | C2 a1 ... aN 
                   ... 
                   | CN a1 ... aN
          
Expressions:

  expr ::= let v = e1 in e2 -- LET
        || case e of  -- CASE
            C1 a1 ... aN -> e1
            ... 
            CN a1 ... aN -> eN
        || func1 e -- KNOWN-APP
        || e1 e2 -- APP
        || C e1 ... eN -- CONSTR

  
KNOWN-APP and APP distinguish between applying a known top-level
function and an unknown function. CONSTR creates a new value using the
constructor CN. LET computes the value ``v'' from ``e1'' for use in
the expression ``e2''. CASE matches the value of ``e'' against each
constructor given (C1, C2, etc.), binds the constructor's values to
the arguments (a1, a2, etc.)  and evaluates the appropriate ``eN''
value.

Now, let's write a compilation strategy from this language to Mark's
MBC language. 

Top-level functions with more than 1 argument get turned into a
series of ``closure capturing'' blocks, terminated by a ``basic
block'' that implements the function body:

[| func a1 a2 ... aN = e |] =>
   funcK1 {} a1 = funcK2 {a1}
   funcK2 {a1} a2 = funcK3 {a1, a2} 
   ...
   funcKN {a1, a2, ..., a(N-1)} aN = funcB(a1, a2, ..., aN)
   funcB(a1, a2, ..., aN) = [|e|]

Aside: Data-constructors get a similar treatment, but the ``body'' is
a primitive expression that creates a run-time value.

Compilation of expressions needs to ensure only values get used
in constructor arguments, case discriminators and let results.

[| let v = e1 in e2 |] => do
  let v = [|e1|]
  [|e2|]
[| case e of 
    C1 a1 ... aN -> e1
    ...
    CN a1 ... aN -> eN |] => do
  let v = [|e|]
  case v of 
   -- free1 - freeN represent variables not mentioned in the case expression 
   -- explicitly (i.e., "free" with respect to this expression).
   C1 a1 ... aN -> fe1(v, a1, ..., aN, free1, ..., freeN) 
   ...
   CN a1 ... aN -> feN(v, a1, ..., aN, free1, ..., freeN)
 
  -- New top-level definitions for each
  -- case arm
  fe1(v, a1, ..., aN, free1, ..., freeN) = [|e1|]
  ...
  feN(v, a1, ..., aN, free1, ..., freeN) = [|eN|]

Data constructors just get compiled to themselves, except we
need to ensure all arguments get evaluated first:

[| C a1 ... aN|] => do
  let v1 = [|a1|]
      ...
      vN = [|aN|]
  C v1 ... vN

Compiling application depends on two properties: the applied function
is a known top-level definition and, if so, that the function takes
more than 1 argument. For known functions which take 1 argument, we
can call their ``block'' directly:

[| func1 e |] => do
  let v = [|e|]
  funcB(v) -- call block for known function

For known functions with more than one argument, we start off by calling
the first closure capture block:

[| funcN e |] => do
  let v = [|e|]
  funcK1(v) -- call first closure capture for known function

For unknown functions, we call whatever function value gets returned
when ``e1'' is evaluated:

[| e1 e2 |] => do
  let v1 = [|e1|]
      v2 = [|e2|]
  v1(v2) -- call known function v1


