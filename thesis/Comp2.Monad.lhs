A function is represented as an environment, an argument type and 
a result type.

> data Fun env arg result = Fun (Env env) (Arg arg) (Result result)

Results and args do not have much meaning. They are present so we can 
control the values contained.

> data Result a = Res a
> data Arg a = Arg a

An environment will be a tuple, where each element represents the
type of the argument at that position in the environment.

> data Env a = Env a

A location is an address with an associated type. Addresses are integers for
now.

> data Loc a = Loc Int

A closure is the location of a function. Notice how phantom types
are used to control what it points to.

> data Closure env arg result = Clo (Loc (Fun env arg result))

Comp provides a monad for representing compilation. Right now, just the state
monad.

> data S = S
> type Comp a = State S a

I first define a closure type for functions with type |Int ->
Int|. The closure has one |Int| in the environment, expects an |Int|
argument, and returns an |Int| value:

> type IntF = Closure Int Int Int

I use these types to define the compose function as a sequence of
closures. For simplicity, compose is defined on functions of type |Int
-> Int|.

Please ignore the bodies of these definitions for now.

> compose :: Comp (Closure () IntF Lab1)
> compose = do
>   l1 <- mkLoc lab1
>   closure l1

compose is a location which holds a closure (|Closure ...|). The
function has an empty environment (|... () ...|) and expects an
argument which is a closure pointing to a function of type |Int ->
Int| (|... IntF ...|). When evaluated, the closure will return a value
of type |Lab1|.

> type Lab1 = Closure () IntF Lab0

> lab1 :: Comp (Closure () IntF Lab0)
> lab1 = block $ \_ arg -> do
>   l1 <- mkLoc lab0
>   reg6 <- closure l1 arg
>   return reg6

|lab1| is the first closure evaluated by compose. It has the same type
signature as compose. I don't quite understand how to avoid the
situation. It seems to occur because we need an initial location in
which to enter the compose function. |lab1| is the first function
which does any real work.

|lab1| epxects an environment with no elements and one argument 
giving the location a function with type |Int -> Int|. It returns a closure
with type |Lab0|. This closure holds the location of |lab0|.

> type Lab0 = Closure IntF IntF Lab2

> lab0 :: Comp (Closure IntF IntF Lab2)
> lab0 = block $ \clo arg -> do
>   reg7 <- load clo 0
>   l2 <- mkLoc lab2
>   reg8 <- closure l2 reg7 arg
>   return reg8

|lab0| expects an environment with one element, the location
of a function of type |Int -> Int|. It also expects the argument
to have be the location of a function with type |Int -> Int|. It
returns a closure with type |Lab2|. The closure holds the location of
|lab2|.

> type Lab2 = Closure (IntF, IntF) Int Int

> lab2 :: Comp (Closure (IntF, IntF) Int Int)
> lab2 = block $ \clo arg -> do
>   reg9 <- load clo 0
>   reg10 <- load clo 1
>   reg11 <- enter reg10 arg
>   reg12 <- enter reg9 reg11
>   let reg13 = undefined -- how to specify destination?
>   copy reg12 reg13
>   return reg13

|lab2| is the body of the |compose| function -- it does all the real work. It
expects an environment with two elements. Both are locations of functions with
type |Int -> Int|. |lab2| expects an |Int| argument and returns an |Int| result.

> comp = comp_k1 ()
> comp_k1 () f = comp_k2 f
> comp_k2 f g = comp_k3 (f, g)
> comp_k3 (f, g) x = do
>   y <- g x
>   f x

> main = do
>   u <- comp foo
>   w <- u bar
>   v <- w val

> comp = do
>   closure () comp_k1
> comp_k1 () f = do
>   closure comp_k2 f
> comp_k2 f g = do
>   closure comp_k3 (f, g)
> comp_k3 (f, g) x = do
>   y <- enter g x
>   v <- enter f y
>   return v
> main = do
>   u <- enter comp foo
>   w <- enter u bar
>   v <- w val
>   return v
[