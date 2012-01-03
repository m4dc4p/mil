\documentclass[12pt]{report}
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\input{preamble}
\begin{document}
\numbersoff
\input{document.preamble}

\chapter{Uncurrying}
\label{ref_chapter_uncurrying}
\intent{Overture: partial application, curried, uncurried.}  Many
functional languages encourage programmers to write definitions that
take advantage of \emph{partial application}. Partial application
means to give a function only some of its arguments, resulting in a
new function that takes the remaining arguments. A function definition
that supports partial application is said to be in \emph{curried}
style, after the mathematician Haskell Curry.\footnote{Curry used
  this style but did not invent it. That is due to a early $20^{th}$
  century mathematician named Moses Sch\"onfinkel.} In contrast, an
\emph{uncurried} function is defined such that it can only be applied
to all of its arguments at once.

\intent{Briefly motivate optimization.}  Partial
application can be very convenient for programmers, but it can also be
very inefficient. Conceptually, an uncurried function does real work
with each application --- that is, each application executes the body
of the function. A curried function does not do any real work until 
given all its arguments; each in-between application essentially creates
a new function. 

\intent{Introduce uncurrying optimization.} This chapter describes our
implementation of \emph{uncurrying}, an optimization that reduces the
number of partial applications in a program. Through dataflow
analysis, we find partial applications for a given function within a
block of MIL code. We replace those partial applications with
full applications to the function, or at least fewer partial
applications. 

\intent{Signposts.}  Section~\ref{uncurry_sec_papp} describes partial
application in more detail; Section~\ref{uncurry_sec_costs} discusses
drawbacks to supporting partial application.  We introduce several
examples that will be used to illustrate our optimization in
Section~\ref{uncurry_sec_examples} and discuss uncurrying as applied
to MIL in Section~\ref{uncurry_sec_mil}. We present our dataflow
equations for uncurrying in Section~\ref{uncurry_sec_df} and our
rewriting strategy in Section~\ref{uncurry_sec_rewriting}. We show our
implementation in Section~\ref{uncurry_sec_impl}. We describe
alternate (but unimplemented) strategies for our own approach in
Section~\ref{uncurry_sec_future}. We conclude with a discussion of our
experience in Section~\ref{uncurry_sec_refl}.

%% \emph{Describes our optimization for collapsing intermediate
%% closures. Our choice of representation is analyzed to
%% show how it facilitates this optimization. We should show one
%% closure can be eliminated from a program and how the optimization
%% is applied over and over until a fixed point is reached. The format
%% for this section will vary from the other two.}

\section{Partial Application}
\label{uncurry_sec_papp}
\intent{Motivate partial application --- what does it buy us?}  Partial
application in functional programming promotes reusability and
abstraction. It allows the programmer to define specialized functions
by fixing some of the arguments to a general function.

\begin{myfig}
> map1 :: (a -> b) -> [a] -> [b]
> map1 f xs = {-"\ldots"-}
>
> map2 :: ((a -> b), [a]) -> b
> map2 (f, xs) = {-"\ldots"-}
  \caption{Haskell definitions in curried and uncurried style. |map1|
    can be easily partially applied to produce specialized functions; |map2|
    cannot.}
  \label{uncurry_fig_partapp}
\end{myfig}

For example, the Haskell code in Figure~\ref{uncurry_fig_partapp}
defines |map1| in curried style and |map2| in uncurried
style.\footnote{The implementation of each function is not relevant
  here, so we elide them.} We can create specialized |maps| by
applying |map1| to a single argument. For example, we can create a
function to convert all its arguments to uppercase or one that squares
all integers in a list:

\begin{singlespace}\correctspaceskip
> upCase1 :: [Char] -> [Char]
> upCase1 = map1 toUpper
>
> square1 :: [Int] -> [Int]
> square1 = map2 (^ 2)
\end{singlespace}

\noindent We cannot do the same as easily with |map2|. At best we can define
a function that ignores one of its arguments:

\begin{singlespace}\correctspaceskip
> upCase2 :: ((a -> b), [Char]) -> [Char]
> upCase2 (_, xs) = map2 (toUpper, xs)
>
> square2 :: ((a -> b), [Int]) -> [Int]
> square2 (_, xs) = map2 ((^ 2), xs)
\end{singlespace}

\intent{Demonstrate that partial-application needs to be considered
  even when the language does not directly support it.}  Even if our
language did not support partial application, we can simulate it with
anonymous functions. For example, JavaScript does not explicitly
support partial application. Given the following definition of |map|,
we cannot define |upCase1| very easily:\footnote{Again, the
  implementation of map is not relevant here, so we elide it.}

\begin{singlespace}\correctspaceskip
  \begin{Verb}[gobble=4]
    function map (f, xs) { \ldots };
  \end{Verb}
\end{singlespace}

\noindent
However, the following definition of |curry| converts a
two-argument function to one that can be partially applied:

\begin{singlespace}\correctspaceskip
  \begin{Verb}[gobble=4]
    function curry(f) {
      return function (a) {
        return function(b) {
          return f(a,b);
        };
      }; 
    }
  \end{Verb}
\end{singlespace}

\noindent
And now we can define |upCase1|:

\begin{singlespace}\correctspaceskip
  \begin{Verb}[gobble=4]
    var upCase1 = curry(map)(function(c) { 
      return c.toUpper(); 
    });
  \end{Verb}
\end{singlespace}

\section{Cost of Partial Application}
\label{uncurry_sec_costs}
\intent{Demonstrates why partial application can be inefficient.}
Function application, regardless of whether partial application is
supported or not, almost always generates code that jumps from one
section of the program to another.\footnote{Inlining can remove some
  jumps, at the cost of increasing code size.} At the assembly
language level, function application is expensive because multiple
operations must take place to implement it: saving registers, loading
addresses, and finally jumping to the target location.

Partial application exagerates all these costs by essentially creating
a \emph{series} of functions, each of which gathers arguments and
returns a closure pointing to the next function in the chain. Only
when all the arguments are gathered does the function do ``real work''
--- that is, something besides allocating closures and gathering up
arguments.

Partial application also influences the code generated to implement
function application. Rather than generate specialized code for
partially versus fully-applied functions, it is simplest to generate
the same code for all applications, partial or otherwise. That means
every function application pays the price of partial application, even
if the function is ``obviously'' fully-applied.

\section{Partial Application in MIL}
\label{uncurry_sec_examples}
\intent{Remind reader about normal blocks.}
Recall that MIL defines two types of blocks: ``\cc'' and ``normal.''
Normal blocks act much like labeled locations in a program and are
written:

\block b(v_1, \dots, v_n): \ldots

\noindent  A normal block is
executed by writing \goto b(v_1, \dots, v_n) (``goto''). 

\intent{Remind reader about \cc blocks.}
\Cc blocks are also like labelled locations, except they expect to
recieve a closure and an argument when called. We write \cc blocks as:

\ccblock k(v_1, \dots, v_n)x: \ldots

\noindent A \cc block is always executed as the result of an
expression like \app f * x/, and expects to receive the argument \var
x/ and a closure containing captured variables $!+\{v_1, \dots,
v_n\}+!$. In the expression \app f * x/, \var f/ represents a closure
that points to some \cc block \lab k/ which expects a set of captured
variables and an argument. The \enter expression causes the block \lab
k/ to be executed using the captured variables in the closure
represented by \var f/ and with the argument \var x/.

\intent{Describe how \cc and normal blocks are generated.}  These two
definitions allow MIL to represent function application uniformly. For
a function with $n$ arguments, $n - 1$ \cc blocks and at least one
normal block will be generated. We name the \cc blocks \lab k$!+_i+!$/
and the normal block \lab b/. We define each \lab k$!+_i+!$/ block,
except the last, as:

\ccblock k$!+_i+!$(v_1, \dots, v_i)x: \mkclo[k$!+_{i+1}+!$:v_1, \dots, v_i, x]

\noindent This means the block \lab k$!+_i+!$/ returns a new closure
that points to the next block (\lab k$!+_{i+1}+!$/) and contains all
the values from the original closure as
well as the argument \var x/ ($\{!+v_1, \dots, v_i, x+!\}$).

The last block, \lab k$!+_{n-1}+!$/, does not return a new closure
immediately. Instead, it calls the normal block, \lab b/, with all
necessary arguments. In the general case, we write \lab k$!+_{n-1}+!$/ as:

  \ccblock k$!+_{n-1}+!$(v_1, \dots, v_{n-1})x: \goto b(v_1, \dots, v_{n-1}, x)

\noindent Of course, depending on the definition of the original
function, we may not pass all arguments to \lab b/, or pass them in
the same order as they appear in the closure. 

\intent{Show how partial application is
  implemented.}  For example, Figure~\ref{uncurry_fig_compose_a} shows
\lamC definitions for |compose| and |compose1|. We define |compose1|
to capture one argument, in order to illustrate how MIL implements
partial application. 

Figure~\ref{uncurry_fig_compose_b} shows the MIL code for the
definitions in Part~\subref{uncurry_fig_compose_a}. In particular, the
block \lab compose1/ acts as the top-level entry point for |compose1|,
returning a closure pointing to \lab absBodyL208/. When entered,
\lab absBodyL208/ will jump to the block \lab absBlockL209/ with \var f/,
the captured argument. 

\begin{myfig}\disableoverfull
  \begin{tabular}{l}
    \begin{minipage}{\hsize}
> compose1 f = compose f
> compose :: (a -> b) -> (b -> c) -> a -> c
> compose f g x = {-"\ldots"-}
    \end{minipage} \\
    \hss\scap{uncurry_fig_compose_a}\hss \\
    \begin{minipage}{\hsize}
      \begin{AVerb}[numbers=left]
\block compose1(): \mkclo[absBodyL208:]
\ccblock absBodyL208()f: \goto absBlockL209(f)
\block absBlockL209(f):
  \vbinds v210 <- \goto compose(); \label{absBlockL209_call}
  \app v210 * f/ \label{absBlockL209_enter}

\block compose(): \mkclo[absBodyL201:]
\ccblock absBodyL201()f: \mkclo[absBodyL202:f]
\ccblock absBodyL202(f)g: \mkclo[absBodyL203:f, g]
\ccblock absBodyL203(f, g)x: \goto absBlockL204(f, g, x)
\block absBlockL204(f, g, x):
  \vbinds v205 <- \app g * x/;
  \app f * v205/
      \end{AVerb}
    \end{minipage} \\
    \hss\scap{uncurry_fig_compose_b}\hss
  \end{tabular}
  \caption{The |compose| function. Part~\subref{uncurry_fig_compose_a}
    shows our \lamC definition. Part~\subref{uncurry_fig_compose_b}
    shows MIL code compiled from Part~\subref{uncurry_fig_compose_a}.}
  \label{uncurry_fig_compose}
\end{myfig}

Block~\lab absBlockL209/ actually implements partial application. On
Line~\ref{absBlockL209_call}, we call \lab compose/, resuling in a
closure that points to \lab absBodyL201/. On
line~\ref{absBlockL209_enter}, we apply that value to \var f/ and
return the result. The value returned by block~\lab absBlockL209/ is
a closure that points to \lab absBodyL202/, second in the chain of \cc
blocks that eventually result in executing |compose| with all its
arguments. In other words, the result of applying |compose1| is a
function that will take two more arguments and then execute |compose|
with them.

\section{Uncurrying MIL blocks}
\label{uncurry_sec_mil}
\intent{Show uncurrying by example, continuing discussion in previous
  section.}  Examination of \lab absBlockL209/ in
Figure~\ref{uncurry_fig_compose_b} reveals one opportunity for
optimization: the call \goto compose() assigns the closure
\mkclo[absBodyL208:] to \var v210/, which is immediately entered on
the next line with argument \var f/. We can eliminate the call by
using the closure directly:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block absBlockL209(f):
      \vbinds v210 <- \mkclo[absBodyL201:];
      \app v210 * f/
  \end{AVerb}
\end{singlespace}

\noindent Now we can see that \var v210/ holds the value
\clo[absBodyL201:{}], a closure referring to block~\lab absBodyL201/
and capturing no variables. Block~\lab absBodyL201/ also returns a
closure, this time capturing its argument and pointing to block~\lab
absBodyL202/. With this knowledge, we can eliminate the expression
\app v210 * f/ and instead create the closure directly, using the
expression \mkclo[absBodyL202:f]:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block absBlockL209(f):
      \vbinds v210 <- \mkclo[absBodyL201:];
      \mkclo[absBodyL202:f]
  \end{AVerb}
\end{singlespace}

\noindent At this point no uses of \var v210/ occur, allowing us to
rewrite \lab absBlockL209/ one more time:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block absBlockL209(f): \mkclo[absBodyL202:f]
  \end{AVerb}
\end{singlespace}

\noindent Thus, by uncurrying we eliminate one call (\goto compose()),
one enter operation (\app v210 * f/), and the creation of one closure
(\mkclo[absBodyL201:]).

\intent{Describe uncurrying in more general terms -- what do we do,
  what don't we do.}  Our uncurrying optimization transforms MIL
programs to eliminate \enter operations as we did by hand for the
program in Figure~\ref{uncurry_fig_compose_a}. In essence, we detemine
if an \enter operation results in a known closure, allowing us to
replace that expression with the closure returned.

Our optimization is applied to every ``normal'' block in the program,
not closure capturing blocks. We analyze closure allocations within
each block but do not propagate that information between blocks. We
discuss alternate strategies for performing uncurrying in
Section~\ref{uncurry_sec_future}; for now, we focus on our
optimization as currently implemented.

\section{Dataflow Equations}
\label{uncurry_sec_df}
\intent{Define dataflow equations for our uncurrying optimization.}
We implement uncurrying with a forwards dataflow analysis that
determines if a given statement allocates a closure. The analysis
creates a map of bound variables to closures. If a variable is
re-bound in the block, the analysis updates its map by removing any
facts that referred to that variable and adding a new fact associating
the variable with the new value.

\begin{myfig}
  \begin{minipage}{\hsize}
    \begin{math}
      %% Below used to measure & typeset the case where we don't
      %% see a binding.
      \newtoks\widest \widest={t (F, \binds v\ <-\ \ldots;)} %%
      \begin{array}{rlr}
        \multicolumn{3}{c}{\textit{Facts}} \\
        \setL{Labels} &= \text{Set of all program labels.} \\
        \setL{Vars} &= \text{Set of all variables.} \\
        \setL{Clo} &= \{\clo[l:v_1, \dots, v_n]\ ||\ \lab l/ \in \setL{Labels}, \var v_i/ \in \setL{Var}, n \geq 0\}.\\
        \setL{Fact} &= \setL{Vars} \times (\{\top\} \cup \setL{Clo}). \\\\

        \multicolumn{3}{c}{\textit{Meet}} \\
        
        p \lub q &= \begin{cases}
          p & \text{when}\ p = q \\
          \top & \text{when}\ p \neq q,
        \end{cases} \labeleq{uncurry_df_lub} & \eqref{uncurry_df_lub} \\
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } p, q \in \setL{Clo}.}\\\\
        
        F_1 \wedge F_2 &= \begin{array}{l}
          \{(\var v/, p \lub q)\ ||\ (\var v/, p) \in F_1, (\var v/, q) \in F_2\}\ \cup \\
          \{(\var v/, \top)\ ||\ \var v/ \in \dom(F_1), \var v/ \not\in \mfun{dom}(F_2)\ \text{or} \\
          \phantom{\{(v, \top)\ ||\ } \var v/ \not\in \dom(F_1), \var v/ \in \mfun{dom}(F_2)\},
        \end{array} \labeleq{uncurry_df_meet} & \eqref{uncurry_df_meet} \\ 
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } F_1, F_2 \in \setL{Fact}.}\\\\

        \multicolumn{3}{c}{\textit{Transfer Function}} \\
        t (F, \binds v\ <-\ \mkclo[l:v_1, \dots, v_n];) &= 
          \{(\var v/, \clo[l:v_1, \dots, v_n])\} \cup (F\ \backslash\ \mfun{uses}(F, \var v/)) 
          \labeleq{uncurry_df_transfer_closure} & \eqref{uncurry_df_transfer_closure} \\
        \the\widest &= \{(\var v/, \top)\} \cup (F\ \backslash\ \mfun{uses}(F, \var v/)) \labeleq{uncurry_df_transfer_other} & \eqref{uncurry_df_transfer_other} \\
        t (F, \_) &= F, \labeleq{uncurry_df_transfer_rest} & \eqref{uncurry_df_transfer_rest} \\
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } F \in \setL{Fact}.} \\\\

        \mfun{uses}(F, \var v/) &= \{(\var u/, p)\ ||\ (\var u/, p) \in F, p = \clo[l:\dots v \dots] \},
        \labeleq{uncurry_df_uses} & \eqref{uncurry_df_uses} \\
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } F \in \setL{Fact}, \var v/ \in \setL{Var}.}
      \end{array}
    \end{math}
  \end{minipage}
  \caption{Dataflow facts and equations for our uncurrying transformation.}
  \label{uncurry_fig_df}
\end{myfig}

\intent{Describe fundamental sets used by our dataflow equations:
  |Labels|, |Vars|, |Clo| and |Facts|.}  Figure~\ref{uncurry_fig_df}
shows the dataflow equations used for our analysis. The sets
\setL{Labels} and \setL{Vars} contain all labels and all variables in
the program, respectively.  The \setL{Clo} set associates some label
with a list of variables; the list may be empty. We use \setL{Clo}
values to represent the location a closure points to and the set of
variables it captures. The \setL{Fact} set defines the facts we can
compute. Each \setL{Fact} value is a pair, $(\var v/, p)$, associating a
bound variable $\var v/$ with a value $p$. If $p \in \setL{Clo}$, $\var v/$ refers
to a known location and some set of of captured variables. Otherwise,
when $p = \top$, $\var v/$ refers to some other value that we do not care
about.

\intent{Describe $\wedge$.}  We combine sets of \setL{Fact} values
using our meet operator, $\wedge$, as defined in
Equation~\eqref{uncurry_df_meet}. We define $\wedge$ over two sets of
facts, $F_1$ and $F_2$. When a variable \var v/ only appears in
$F_1$ or $F_2$, we assume we do not not know what value \var v/ may
represent, so we add $(\var v/, \top)$ to the result. When a variable
appears in both $F_1$ and $F_2$, we create a new pair by combining the
two associated \setL{Clo} values using the \lub operator defined in
Equation~\eqref{uncurry_df_lub}. The resulting pair has the same
variable but a (possibly) new \setL{Clo} value. Together, \setL{Fact}
and $\wedge$ form a lattice as described in
Chapter~\ref{ref_chapter_background}, Section~\ref{back_subsec_facts}.

\intent{Illustrate $\wedge$ with an example.}  For example, if $F_1 =
\{(\var v/, \clo[l:a]), (\var w/, \clo[l:b])\}$ and $F_2 = \{(\var u/,
\clo[l:a]),$ $(\var v/, \clo[l:a]),$ $(\var w/, \clo[l:a])\}$ then
$F_1 \wedge F_2$ would be $\{(\var u/, \top), (\var v/, \clo[l:a]),
(\var w/, \top)\}$. Because \var u/ only appears in one set, we cannot
assume it will always refer to \clo[l:a], so we add the pair $(\var
u/, \top)$ to the result. The variable \var v/ appears in both sets with the same
closure we add $(\var v/, \clo[l:a] \lub \clo[l:a])$, or $(\var v/,
\clo[l:a])$, to the result set. Finally, \var w/ appears in both
sets, but the closure associated with it in each differs: \clo[l:b] in
$F_1$ and \clo[l:a] in $F_2$. Therefore, we add $(\var w/, \top)$ to
the result set. 

\intent{Explain in detail how $t$ works.}  Our transfer function, $t$,
takes a statement and a set of \setL{Fact} values, $F$, as arguments.
It returns a \setL{Fact} set containing new facts based on the
statement given. We define $t$ by cases for each type of MIL statement.

Equation~\eqref{uncurry_df_transfer_closure} applies when the \rhs of
a \bind statement creates a closure, as in \binds v <- \mkclo[l: v_1,
  \dots, v_n];. Because \var v/ has been redefined, we must invalidate
any facts that refer to \var v/, as they do not refer to the new value
of \var v/. The \mfun{uses} function in
Equation~\eqref{uncurry_df_uses} finds the facts in $F$ that represent
a closure capturing the variable \var v/. We remove any facts in $F$
that refer to \var v/ by subtracting the results of the \mfun{uses}
function from $F$.  We combine this set with a new fact associating
\var v/ with the \setL{Clo} value \clo[l:v_1, \dots, v_n]. Our result
set shows that \var v/ now refers to the closure \clo[l:v_1, \dots,
  v_n], and does not include any previous facts that referred to \var
v/.

Equation~\eqref{uncurry_df_transfer_other} applies when the \rhs of a
\bind statement does not allocate a closure. We create a new fact
associating \var v/ with $\top$, indicating we know \var v/ does not
refer to a closure. We also remove any existing uses of \var v/ from
$F$. Our new fact and new set are combined to form our result.

In all other cases, Equation~\eqref{uncurry_df_transfer_rest}
applies, and $t$ acts like identity --- $F$ is returned unchanged.

\section{Rewriting}
\label{uncurry_sec_rewriting}
\intent{Explain how we rewrite |Enter| expressions.}  The facts
gathered by $t$ allow us to replace \enter expressions with closure
allocations if we know the value that the expression results in. For
example, let $F$ be the facts computed so far and \binds v <- \app f *
x/; the statement we are considering. If $(\var f/, p) \in F$ and $p =
\clo[l: v_1, \dots, v_n]$, then we know \var f/ represents the closure
\clo[l:v_1, \dots, v_n]. If \lab l/ is also a closure-capturing block
that returns \clo[m:c_1, \dots, c_m], we can then eliminate the \enter
operation and rewrite the statement to \binds v <- \mkclo[m: v_1,
  \dots, v_n, x];.  Notice we needed to add the \var x/ argument to
the resulting closure as the block \lab l/ would do the same if we had
entered it.

\intent{Point out we don't inline closures from |Goto| expressions.}
The example we discussed in Section~\ref{uncurry_sec_mil} does not
match with the optimization just discussed on one crucial point:
replacing calls to normal blocks on the \rhs of a \bind with
their closure result. Our implementation relies on another, more
general, optimization that inlines simple blocks into their
predecessor. We describe the optimization in detail in
Chapter~\ref{ref_chapter_monadic}, but in short that optimization will
inline calls to blocks such as \lab compose/, so a statement like \binds v <-
\goto compose(); becomes \binds v <- \mkclo[absBodyL201:];, where \lab absBodyL201/ is the
label in the closure returned by \goto compose().

\section{Implementation}
\label{uncurry_sec_impl}

\intent{Provide a bridge to the four subsections below.}  Originally,
we called this transformation ``closure-collapse,'' because it
``collapsed'' the construction of multiple closures into the
construction of a single closure. Later, we learned this optimization
is known as ``uncurrying,'' but at the point the code had already been
written. The ``collapse'' prefix in the code shown is merely an
artifact of our previous name for the analysis.

\intent{Explain why the code doesn't match the equations.}
In our presentation of dataflow equations in
Section~\ref{uncurry_sec_df}, we described this analysis by
statements. However, our implementation works on blocks of MIL
code. Fortunately, the net result is the same due to Hoopl's
interleaved analysis and rewriting. Our transfer and rewrite functions
work in tandem to rewrite \enter expressions within a block.

\intent{Introduce example used throughout this section.}
Figure~\ref{uncurry_fig_eg} gives an example program we will use
throughout this section to illustrate our implementation. The program
takes a string as input, converts it to an integer, doubles that
value, and returns the result. The program consists of five
blocks. Two of the blocks, \lab k0/ and \lab k1/, are \cc. Two others,
\lab add/ and \lab toInt/, are normal blocks that call runtime
primitives. The final block, \lab main/, is also a normal block but
is treated as the entry point for the program.

\intent{Signposts.}
We present our implementation in five sections, reflecting the
structure of our dataflow equations above. We first give the types
used, followed by the definition of our lattice, then our transfer
function, then our rewriting function, and finally we show the driver
that applies the optimization to a given program.

\begin{myfig}
  \begin{minipage}{\hsize}\singlespacing
    \begin{AVerb}[gobble=6]
      \block main(s):
        \vbinds n <- \goto toInt(s);
        \vbinds v0 <- \mkclo[k0:];
        \vbinds v1 <- \app v0 * n/;
        \vbinds v2 <- \app v1 * n/;
        \return v2/

      \ccblock k0()a: \mkclo[k1:a]
      \ccblock k1(a)b: \goto add(a, b)
      \block add(x, y): \prim plus(x, y)
      \block toInt(s): \prim atoi(s)
    \end{AVerb}
  \end{minipage} \\
  \caption{Example program.}
  \label{uncurry_fig_eg}
\end{myfig}

\subsection{Types}
\label{uncurry_impl_types}
\intent{Describe types used; give details on managing names; point out
  it other differences.}  Figure~\ref{uncurry_fig_types} shows the
types used by our implementation to represent the sets given in
Figure~\ref{uncurry_fig_df}. |CloDest| represents \setL{Clo} and
|CollapseFact| represents \setL{Fact}. |Dest| and |Name|, whose
definitions are not shown, correspond to \setL{Label} and \setL{Var},
respectively.

\begin{myfig}
  \begin{minipage}{\hsize}\disableoverfull
%let includeTypes = True
%include Uncurry.lhs
%let includeTypes = False
  \end{minipage}
  \caption{The types for our analysis. Referring to the sets defined
    in Figure~\ref{uncurry_fig_df}, |CloDest| represents \setL{Clo} and
    |CollapseFact| represents \setL{Fact}. |DestOf| is not represented
    in our dataflow equations; it describes the behavior of each MIL block that
    we may use while rewriting.}
  \label{uncurry_fig_types}
\end{myfig}

\intent{Explain |DestOf| values.}  When rewriting, we need to know the
result of every \cc block in the program. Specifically, we need to
know if a given block resturns a closure or if it jumps directly to
another block. The |DestOf| type, which does not appear in
Figure~\ref{uncurry_fig_df} but is defined in
Figure~\ref{uncurry_fig_types}, uses the |Capture| and |Jump|
constructors to represent the first and second case, respectively. The
|Dest| value in both is a destination: either the label stored in the
closure returned, or the block that the closure jumps to
immediately. 

\intent{Details on |Capture| value.}  A \cc block receives a closure
and an argument. The flag in the |Capture| constructor indicates how
the \cc block treats its argument. If |True|, the argument will be
included in the closure returned. Otherwise, the argument will be
ignored.

\intent{Details on |Jump| value.} A |Jump| block always has the form
``\ccblock k(v_1, \dots, v_n)x: \goto b(\ldots)'' where the arguments
to \lab b/ are not necessarily in the same order as in the closure
\clo[k:v_1, \dots, v_n] recieved by \lab k/. Each integer in the list
given to |Jump| indicates the position of a variable in the closure
received by the block \lab k/. The arguments to the block \lab b/ are
built by traversing the list, putting the variable indicated by each
index into the corresponding argument for the block. \footnote{This
  situation can also apply to |Capture| blocks and we would need to
  update our implementation our compiler's code generation strategy
  changed or if we began writing MIL programs directly.}

For example, in the following the variables in the closure received
by \lab c/ do not appear in the same order as expected by block \lab l/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \ccblock c(a, b)x: \goto l(x, a, b)
    \block l(x, a, b): \ldots
  \end{AVerb}
\end{singlespace}

\noindent 
We represent \lab c/ using |Jump {-"\lab
  l/\ "-} [2, 0, 1]|, because the variables from the closure \clo[:a,
  b] and the argument \var x/ must be given to \lab l/ in the order
$!+(x, a, b)+!$.

\intent{Details on |CloDest| values.}  We use |CloDest| to represent
all \setL{Clo} values. |CloDest| stores a |Dest| value, representing
the label the closure refers to, and a list of captured variables,
|[Name]|.

\intent{Explain how |WithTop CloDest| and |CollapseFact| represent
  \setL{Fact}.}  We use a finite map, aliased as |CollapseFact|, to
represent our \setL{Fact} set. Hoopl provides |WithTop|, a type that
adds a $\top$ value to any other type. |WithTop CloDest| then 
represents the set $\{\top\} \cup \{\setL{Clo}\}$. In turn, |CollapseFact| 
represents a finite map from variables to $\{\top\} \cup
\{\setL{Clo}\}$.

\subsection{Lattice \& Meet}
\label{uncurry_impl_lattice}
Figure~\ref{uncurry_fig_lattice} shows the |DataflowLattice| structure
defined for our analysis. We set |fact_bot| to an empty map, meaning
we start without any information. We define |lub| over |CloDests|, just
like \lub in Figure~\ref{uncurry_fig_df}. We use |joinMaps (toJoin
lub)| (Hoopl provides |joinMaps|) to transform |lub| into a function
that operates over finite maps.

\begin{myfig}
  \begin{minipage}{\hsize}\disableoverfull
%let includeLattice = True
%include Uncurry.lhs
%let includeLattice = False
  \end{minipage}
  \caption{The Hoopl |DataflowLattice| declaration representing the 
  lattice used by our analysis.}
  \label{uncurry_fig_lattice}
\end{myfig}

\subsection{Transfer}
\label{uncurry_impl_transfer}
The definition |t| in Figure~\ref{uncurry_fig_transfer} gives the
implementation of $t$ from Figure~\ref{uncurry_fig_df}. The top-level
definition, |collapseTransfer|, serves to turn |t|
into a |FwdTransfer| value.  As in all Hoopl-based forwards analysis,
the second argument to |t| is our facts so far. We define |t| for each
statement type in MIL.

The |BlockEntry| and |CloEntry| cases return the facts given
unchanged.\footnote{Note these will always be empty maps, because our
  analysis does not extend across blocks and |fact_bot| in our lattice
  is |Map.empty|.} Because we do not propagate facts between blocks,
the |CaseM| and |Done| cases pass an empty map to each successor,
using the Hoopl-provided |mkFactBase| function to create a |FactBase|
from empty facts.

\begin{myfig}
  \begin{minipage}{\hsize}\begin{withHsLabeled}{uncurry_fig_transfer}\disableoverfull
%let includeTransfer = True
%include Uncurry.lhs
%let includeTransfer = False
    \end{withHsLabeled}
  \end{minipage}
  \caption{The Haskell implementation of our transfer function $t$
    from Figure~\ref{uncurry_fig_df}.}
  \label{uncurry_fig_transfer}
\end{myfig}

|Bind| statments are handled based on the \rhs of the statement. In
both cases, we use the |kill| function to create a new set of facts
that does not contain any closures from the existing fact set which
refered to |v|, the variable bound. If the statement does not directly
create a closure (Line~\ref{uncurry_fig_transfer_rest}), we create a
fact associating |v| with |Top|, just as in
Equation~\eqref{uncurry_df_transfer_other}. If the expression creates
a closure (Line~\ref{uncurry_fig_transfer_rest}), we create a new fact
with the closure's destination and captured variables, corresponding
to Equation~\eqref{uncurry_df_transfer_closure}. We add the new fact
to the set returned by |kill| and return the result.

\begin{myfig}
  \begin{tabular}{lcccc}
    Statement & \var n/ & \var v0/ & \var v1/ & \var v2/ \\\cmidrule{2-2}\cmidrule{3-3}\cmidrule{4-4}\cmidrule{5-5}
    \binds n <- \goto toInt(s); & $\cdot$ & $\cdot$ & $\cdot$ & $\cdot$ \\
    \binds v0 <- \mkclo[k0:]; & $\top$ & $\cdot$ & $\cdot$ & $\cdot$ \\
    \binds v1 <- \app v0 * n/; & $\cdot$ & \clo[k0:] & $\cdot$ & $\cdot$ \\
    \binds v2 <- \app v1 * n/; & $\cdot$ & $\cdot$ & $\top$ & $\cdot$ \\
    \return v2/ & $\cdot$ & $\cdot$ & $\cdot$ & $\top$ \\
  \end{tabular}
  \caption{Facts about each variable in the \lab main/ block of
    our example program from Figure~\ref{uncurry_fig_eg}.}
  \label{uncurry_fig_impl_transfer}
\end{myfig}

Figure~\ref{uncurry_fig_impl_transfer} shows the facts gathered for
each variable in the \lab main/ block of our sample program. The
variables \var n/, \var v1/, and \var v2/ are assigned $\top$ because
the \rhs of the \bind statement for each does not directly create a
closure. Only \var v0/ is assigned a |CloDest| value (\clo[k0:])
because the \rhs of its \bind statement is in the right form. We will
see in the next section how these facts evolve as the program is
rewritten.

\subsection{Rewrite}
\label{uncurry_impl_rewrite}
\intent{Give an example demonstrating iterative rewriting.}
Figure~\ref{uncurry_fig_rewrite} shows the
top-level implementation of our rewrite function for the uncurrying
optimization. |collapseRewrite| creates the rewriter that can 
uncurry a MIL program. The |blocks| argument associates every \cc
block in our program with a |DestOf| value. |DestOf|, as explained in
Section~\ref{uncurry_impl_types}, indicates if the block returns a
closure or jumps immediately to another block.

\begin{myfig}
  \begin{minipage}{\hsize}\begin{withHsLabeled}{uncurry_fig_rewrite}\disableoverfull
%let includeRewrite = True
%include Uncurry.lhs
%let includeRewrite = False
  \end{withHsLabeled}\end{minipage} \\
  \caption{The top-level implementation of our uncurrying rewriter..}
  \label{uncurry_fig_rewrite}
\end{myfig}

On Line~\ref{uncurry_fig_rewrite_top}, |collapseRewrite| applies
Hoopl's |iterFwdRw| and |mkFRewrite| to create a |FwdRewrite|
value. The |iterFwdRw| combinator applies |rewriter| repeatedly, until
the |Graph| representing the program stops changing. Hoopl computes
new facts (using |collapseTransfer|) after each rewrite. This ensures
that a ``chain'' of closure allocations get collapsed into a single
allocation, if possible.

Figure~\ref{uncurry_fig_rewrite_iterations} demonstrates this
iterative process by showing how the \lab main/ block in our example
program changes over three iterations. The second column of each row
shows facts computed for the program text in the first column. The
value of |blocks| stays constant throughout, so we only show it
once. Rewrites occur between rows.

During the first iteration, |rewriter| transforms \binds v1 <- \app v0
* n/; to \binds v1 <- \mkclo[k1: n];, because \var v0/ holds the
closure \clo[k0:], and |blocks| tells us \lab k0/ returns a closure
pointing to \lab k1/.

\begin{myfig}
  \begin{tabular}{clll}
    Iteration & \lab main/ & Facts & |blocks| \\
    1 & \begin{minipage}[t]{\widthof{\binds n <- \goto toInt(s);}}    
      \begin{AVerb}[gobble=8]
        \vbinds n <- \goto toInt(s);
        \vbinds v0 <- \mkclo[k0:];
        \vbinds v1 <- \app v0 * n/;
        \vbinds v2 <- \app v1 * n/;
        \return v2/ 
      \end{AVerb} 
    \end{minipage} & \begin{minipage}[t]{\widthof{\ \phantom{\{}(\var v2/, \goto add(n,n))\}\ }}\raggedright
      (\var n/, $\top$),\break
      (\var v0/, \clo[k0:]),\break
      (\var v1/, $\top$),\break
      (\var v2/, $\top$)
    \end{minipage} & 
    \begin{minipage}[t]{\widthof{\phantom{\{}\lab k1/:\thinspace|Jump {-"\lab add/\ "-} [0, 1]|\}\ }}\raggedright
      \lab k0/:\thinspace|Capture {-"\lab k1/\ "-} True|,\break
      \lab k1/:\thinspace|Jump {-"\lab add/\ "-} [0, 1]|
    \end{minipage}
    \\\\
    2 & \begin{minipage}[t]{\widthof{\binds n <- \goto toInt(s);}}
      \begin{AVerb}[gobble=8]
        \vbinds n <- \goto toInt(s);
        \vbinds v0 <- \mkclo[k0:];
        \llap{\ensuremath{\rightarrow} }\vbinds v1 <- \mkclo[k1:n]; \ensuremath{\leftarrow}
        \vbinds v2 <- \app v1 * n/;
        \return v2/
      \end{AVerb} 
    \end{minipage} & \begin{minipage}[t]{\widthof{\ \phantom{\{}(\var v2/, \goto add(n,n))\}\ }}\raggedright
      (\var n/, $\top$),\break
      (\var v0/, \clo[k0:]),\break
      (\var v1/, \clo[k1:n]),\break
      (\var v2/, $\top$)
    \end{minipage} \\\\
    3 & \begin{minipage}[t]{\widthof{\binds v2 <- \goto add(n, n); \ensuremath{\leftarrow}}}
      \begin{AVerb}[gobble=8]
        \vbinds n <- \goto toInt(s);
        \vbinds v0 <- \mkclo[k0:];
        \vbinds v1 <- \mkclo[k1:n];
        \llap{\ensuremath{\rightarrow} }\vbinds v2 <- \goto add(n, n); \ensuremath{\leftarrow}
        \return v2/
      \end{AVerb}
    \end{minipage} & \begin{minipage}[t]{\widthof{\ \phantom{\{}(\var v2/, \goto add(n,n))\}\ }}\raggedright
      (\var n/, $\top$),\break
      (\var v0/, \clo[k0:]),\break
      (\var v1/, \clo[k1:n]),\break
      (\var v2/, \goto add(n,n))
    \end{minipage}
  \end{tabular}
  \caption{How |rewriter| transforms the \lab main/ block. Each
    row represents \lab main/ after the particular iteration. The
    first line shows the original program. The arrows 
    shows the line that changed during each iteration. After the second iteration,
    the program stops changing. }
  \label{uncurry_fig_rewrite_iterations}
\end{myfig}

The facts shown for the second iteration reflect the rewrite made,
associating \var v1/ with \clo[k1:n]. |rewriter| transforms \binds v2
 <- \app v1 * n/; to \binds v2 <- \goto add(n, n); after this iteration
because \var v1/ refers to \lab k1/ and |blocks| tells us that \lab
k1/ jumps immediately to \lab add/. No changes occur after the third
iteration because no statements remain that can be rewritten, and
Hoopl stops applying |rewriter|.

Figure~\ref{uncurry_fig_rewrite_impl} shows the functions that
implement our uncurrying optimization.\footnote{Note that these
  definition are local to |collapseRewrite|, so the |blocks| argument remains
  in scope.} Line
\ref{uncurry_fig_rewrite_impl_done} of |rewriter| rewrites \app f * x/
expressions when they occur in a \return/
statement. Line~\ref{uncurry_fig_rewrite_impl_bind} rewrites when \app
f * x/ appears on the \rhs of a \bind statement.  In
the first case, |done n l (collapse facts f x)| produces \return |e|/
when |collapse| returns |Just e| (i.e., a rewritten
expression). In the second case, |bind v (collapse facts f x)|
behaves similarly, producing \binds v <- |e|; when |collapse| returns
|Just e|.\footnote{Both |done| and |bind| are defined in a separate file, not shown.}

\begin{myfig}
  \begin{minipage}{\hsize}\begin{withHsLabeled}{uncurry_fig_rewrite_impl}\disableoverfull
%let includeRewriteImpl = True
%include Uncurry.lhs
%let includeRewriteImpl = False
  \end{withHsLabeled}\end{minipage} \\
  \caption{The implementation of our uncurrying rewriter.}
  \label{uncurry_fig_rewrite_impl}
\end{myfig}

The |collapse| function takes a set of facts and two names,
representing the left and \rhs of the expression \app f * x/. When
\var f/ is associated with a closure value, \clo[k:\dots], in the
|facts| map (Line~\ref{uncurry_fig_rewrite_impl_collapse_clo}),
|collapse| uses the |blocks| argument to look up the behavior of the
destination \lab
k/. Lines~\ref{uncurry_fig_rewrite_impl_collapse_jump} and
\ref{uncurry_fig_rewrite_impl_collapse_capt} test if \lab k/
returns a closure or jumps immediately to
another block. In the first case, |collapse| returns a new
closure-creating expression (\mkclo[|dest|:\dots]). In the
second case, |collapse| returns a new goto expression (\goto |dest|(\dots)).

If the destination immediately jumps to another block
(Line~\ref{uncurry_fig_rewrite_impl_collapse_jump}) then we will
rewrite \app f * x/ to call the block directly. The list of integers
associated with |Jump| specifies the order in which arguments were
taken from the closure and passed to the block. |collapse| uses the
|fromUses| function to re-order arguments appropriately.

{\tolerance=1000 In Figure~\ref{uncurry_fig_rewrite_iterations}, we showed that the
|DestOf| value associated with \lab k1/ is |Jump {-"\lab add/\ "-} [0,
  1]|. The list |[0, 1]| indicates that \lab add/ takes arguments in
the same order as the appear in the closure. However, if \lab add/
took arguments in opposite order, \lab k1/ and \lab add/ would look
like:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}
    \ccblock k1(a)b: \goto add(b, a)
    \block add(x, y): \ldots
  \end{AVerb}
\end{singlespace}

\noindent And the |DestOf| value associated with \lab k1/ would be |Jump
{-"\lab add/\ "-} [1, 0]|.}

If the destination returns a closure
(Line~\ref{uncurry_fig_rewrite_impl_collapse_capt}), we will rewrite
\app f * x/ to directly allocate the closure. The boolean argument to
|Capture| indicates if the closure ignores the argument passed, which
|collapse| uses to determine if it should place the \var x/ argument
in the closure that is allocated or not.

\subsection{Optimization Pass}

\intent{Describe how |collapse| creates initial values for uncurrying,
  applies the optimization, and cleans up.}
Figure~\ref{uncurry_fig_collapse} presents |collapse|, which applies
the uncurrying dataflow analysis and rewrite to the MIL program
represented by the argument
|program|. Line~\ref{uncurry_fig_collapse_analyze} analyzes and
transforms |program| by passing appropriate arguments to Hoopl's
|analyzeAndRewriteFwd| function. On Line~\ref{uncurry_fig_collapse_run} we evaluate Hoopl's
monadic program using |runSimple|. |runSimple| provides a monad with
infinite optimization fuel.

\begin{myfig}
  \begin{minipage}{\hsize}\begin{withHsLabeled}{uncurry_fig_collapse}\disableoverfull
%let includeCollapse = True
%include Uncurry.lhs
%let includeCollapse = False
  \end{withHsLabeled}\end{minipage}
  \caption{The function which puts together all definitions for our
    implementation of the uncurrying optimization.}
  \label{uncurry_fig_collapse}
\end{myfig}

Half of Figure~\ref{uncurry_fig_collapse} creates arguments for
|analyzeAndRewriteFwd|, which we will detail in order.

\begin{description}
\item[|fwd|] --- This argument packages the lattice, transfer and
  rewrite definitions we described in
  Sections~\ref{uncurry_impl_lattice}, \ref{uncurry_impl_transfer},
  and \ref{uncurry_impl_rewrite}.
\item[|JustC labels|] --- We must give Hoopl all entry points for the
  program analyzed. These labels tell Hoopl where to start
  traversing the program graph. Because our analysis does not extend
  across blocks we give all labels, so all blocks in |program| will be
  analyzed. This argument's type is |MaybeC C [Label]|, which requires
  us to use the |JustC| constructor. 
\item[|program|] --- This argument gives the program that will be 
  analyzed and (possibly) transformed.
\item[|initial|] --- The final argument gives initial facts for each
  label. Our analysis does not specify any prior knowledge at each
  label, so we set all initial facts to |Map.empty|. That is the value
  we gave |fact_bot| when defining our |Data{-"\-"-}flow{-"\-"-}Lattice| value
  (Figure~\ref{uncurry_fig_lattice}).
\end{description}

The other half of Figure~\ref{uncurry_fig_collapse} describes how we
create the |blocks| argument passed to |collapseRewrite|. The
|destinations| function enumerates all blocks in |program| to find all
\cc blocks. |destOf| determines the behavior of each \cc block and
creates the appropriate |Jump| or |Capture| value. The result of
|destinations| becomes the |blocks| argument for |collapseRewrite|.

\section{Future Work}
\label{uncurry_sec_future}
\intent{Discuss strategies for uncurrying: local only, across blocks,
  by duplication.}  The uncurrying optimization described in this
chapter only works within single blocks. We only apply the
optimization to closures. However, the optimization can be extended to
work across blocks and to work with monadic thunks. We discuss these
extensions in Sections~\ref{uncurry_sec_blocks} and
\ref{uncurry_sec_thunks}, respectively.

\subsection{Uncurrying Across Blocks}

\intent{Motivate multi-block uncurrying with example}
Uncurrying across blocks can further reduce the number of
\enter operations and closures created. For example, consider
a program that creates a partially applied function and passes
it through a case statement.

\begin{myfig}
  \caption{A MIL program that would benefit from uncurrying across
    blocks.}
  \label{uncurry_fig_blocks}
\end{myfig}

\intent{Discuss live variable analysis difficulty}

\intent{Discuss implications for separate compilation}

\subsection{Extending Uncurrying to Thunks}

\section{Reflection}
\label{uncurry_sec_refl}
\end{document}
