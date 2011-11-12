\documentclass[12pt]{report}
%include polycode.fmt
%include subst.fmt
\input{preamble}
\begin{document}
\def\rhs{right--hand side\xspace}
\def\lhs{left--hand side\xspace}
\def\bind{\texttt{<-}\xspace}
\def\var#1/{\texttt{#1}\xspace}
\def\clo[#1:#2]{\ensuremath{\ensurett{(#1, #2)}}\xspace}
\def\cc{closure--capturing\xspace}

\def\binds#1<-#2/{\ensuremath{\ensurett{#1\ \text{<-}\ #2}}\xspace}
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
implementation in Section~\ref{uncurry_sec_impl}. Previous approaches
to uncurrying are discussin in Section~\ref{uncurry_sec_prior}; we
describe alternate (but unimplemented) strategies for our own approach
in Section~\ref{uncurry_sec_future}. We conclude with a discussion of
our experience in Section~\ref{uncurry_sec_refl}.

%% \emph{Describes our optimization for collapsing intermediate
%% closures. Our choice of representation is analyzed to
%% show how it facilitates this optimization. We should show one
%% closure can be eliminated from a program and how the optimization
%% is applied over and over until a fixed point is reached. The format
%% for this section will vary from the other two.}

\section{Partial Application}
\label{uncurry_sec_papp}
\intent{Motivate partial application --- what does it buy us?}  Partial
application in functional programming promotes re-usability and
abstraction. It allows the programmer to define specialized functions
by fixing some of the arguments to a general function.

\begin{myfig}
> map1 :: (a -> b) -> [a] -> [b]
> map1 = {-"\ldots"-}
>
> map2 :: ((a -> b), [a]) -> b
> map2 = {-"\ldots"-}
  \caption{Haskell definitions in curried and uncurried style. |map|
    can be easily partially applied to produce specialized functions; |foldr|
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

> upCase1 :: [Char] -> [Char]
> upCase1 = map1 toUpper
>
> square1 :: [Int] -> [Int]
> square1 = map2 (^ 2)

We cannot do the same as easily with |map2|. At best we can define
a function that ignores one of its arguments:

> upCase2 :: ((a -> b), [Char]) -> [Char]
> upCase2 (_, xs) = map2 (toUpper, xs)
>
> square2 :: ((a -> b), [Int]) -> [Int]
> square2 (_, xs) = map2 ((^ 2), xs)

\intent{Demonstrate that partial-application needs to be considered
  even when the language does not directly support it.}  Even if our
language did not support partial application, we can simulate it with
anonymous functions. For example, JavaScript does not explicitly
support partial application. Given the following definition of |map|,
we cannot define |upCase1| very easily:\footnote{Again, the
  implementation of map is not relevant here, so we elide it.}

\singlespacing
\begin{minipage}{\hsize}
  \begin{MILVerb}[gobble=4]
    function map (f, xs) { 
      \ldots
    };
  \end{MILVerb}
\end{minipage}
\doublespacing

\noindent
However, the following definition of |curry| converts a
two-argument function to one that can be partially applied:

\begin{singlespace}
  \begin{MILVerb}[gobble=4]
    function curry(f) {
      return function (a) {
        return function(b) {
          return f(a,b);
        };
      }; 
    }
  \end{MILVerb}
\end{singlespace}

\noindent
And now we can define |upCase1|:

\begin{singlespace}
  \begin{MILVerb}[gobble=4]
    var upCase1 = curry(map)(function(c) { 
      return c.toUpper(); 
    });
  \end{MILVerb}
\end{singlespace}

\section{Cost of Partial Application}
\label{uncurry_sec_costs}
\intent{Demonstrates why partial application can be inefficient.}
Function application, regardless of whether partial application is
supported or not, almost always generates code that jumps from one
section of the program to another.\footnote{Inlining can remove the
  need for jumps, but of course increases code size. There is no
  perfect optimization --- only good enough.} At the assembly language
level, function application is expensive because multiple operations
must take place to implement it: saving registers, loading addresses,
and finally jumping to the target location. Partial application
exagerates all these costs.

Partial application essentially creates a \emph{series} of functions,
each of which gathers arguments and returns a closure pointing to the
next function in the chain. Only when all the arguments are gathered
does the function do ``real work'' --- that is, something besides
gathering up arguments and creating a closure. Each partial
application causes an allocation by creating and returning a
closure. Partial application also influences the code generated to
implement function application. Rather than generate specialized code
for partially versus fully-applied functions, it is simplest to
generate the same code for all applications, partial or
otherwise. That means every function application pays the price of
partial application, even if the function is ``obviously''
fully-applied.

\section{Partial Application in MIL}
\label{uncurry_sec_examples}
\intent{Remind reader how MIL \cc blocks are written
  and used.}  Recall that MIL defines two types of blocks:
``\cc'' and ``normal.'' Normal blocks act much like
labeled locations in a program and are written $!+b(v_1, \dots, v_n):
\dots+!$.  A \cc block is always executed as the result
of an !+@@+!  expression. That is, in the expression !+f @@ x+!, !+f+!
represents a closure that points to some block labeled !+k+!  and that
captures variables $!+\{v_1, \dots, v_n\}+!$. The !+@@+!  expression
causes the block !+k+! to be executed using the closure value
represented by !+f+! and with the argument !+x+!. We write
\cc blocks as $!+k\ \{v_1, \dots, v_n\}\ x: \dots
+!$. !+k+! names the block, $!+\{v_1, \dots, v_n\}+!$ gives the
variables expected in the closure, and !+x+! represents the argument
passed.

These two definitions allow MIL to represent function application
uniformly. For a function with $n$ arguments, $n - 1$ !+k+! blocks
will be generated. At least one !+b+! block will also be generated,
representing the body of the function. Each $!+k_i+!$ block, except
the $!+k_{n-1}+!$, returns a new closure pointing to the next
$!+k_{i+1}+!$ block. The closure created by block $!+k_i+!$ contains
all values found in the closure it was given, plus the argument
passed. The last block, $!+k_{n-1}+!$, does not return a new closure
immediately. Instead, it calls block !+b+!, unpacking all necessary
arguments. The value returned from block !+b+! is then returned by
block $!+k_{n-1}+!$.

\intent{Show how partial application is
  implemented.}  For example, Figure~\ref{uncurry_fig_compose_a} shows
\lamC definitions for |compose| and |compose1|. We define |compose1|
to capture one argument, in order to illustrate how MIL implements
partial application. 

Figure~\ref{uncurry_fig_compose_b} shows the MIL code for the
definitions in Part~\subref{uncurry_fig_compose_a}. In particular, the
block !+compose1+! acts as the top-level entry point for |compose1|,
returning a closure pointing to !+absBodyL208+!. When entered,
!+absBodyL208+! will jump to the block !+absBlockL209+! with !+f+!,
the captured argument. 

\begin{myfig}
  \begin{tabular}{l}
    \begin{minipage}{\hsize}
> compose1 f = compose f
> compose :: (a -> b) -> (b -> c) -> a -> c
> compose f g x = {-"\ldots"-}
    \end{minipage} \\
    \hss\scap{uncurry_fig_compose_a}\hss \\
    \begin{minipage}{\hsize}
      \begin{MILVerb}
compose1 (): closure absBodyL208 {}
absBodyL208 {} f: absBlockL209(f)
absBlockL209 (f):
  v210 <- compose()
  v210 @@ f

compose (): closure absBodyL201 {} 
absBodyL201 {} f: closure absBodyL202 {f}
absBodyL202 {f} g: closure absBodyL203 {f, g}
absBodyL203 {f, g} x: absBlockL204(f, g, x)
absBlockL204 (f, g, x):
  v205 <- g @@ x
  f @@ v205
      \end{MILVerb}
    \end{minipage} \\
    \hss\scap{uncurry_fig_compose_b}\hss
  \end{tabular}
  \caption{The |compose| function. Part~\subref{uncurry_fig_compose_a}
    shows our \lamC definition. Part~\subref{uncurry_fig_compose_b}
    shows MIL code compiled from Part~\subref{uncurry_fig_compose_a}.}
  \label{uncurry_fig_compose}
\end{myfig}

Block~!+absBlockL209+! actually implements partial application. It
evaluates the !+compose+! block, getting a closure that points to the
top-level entry point for |compose|. !+absBlockL209+! applies that
value to !+f+! and returns the result. The value returned by
block~!+absBlockL209+! is a closure that points to !+absBodyL202+!,
second in the chain of \cc blocks that eventually result
in executing |compose| with all its arguments. In other words, the
result of applying |compose1| is a function that will take two more
arguments and then execute |compose| with them.

\section{Uncurrying MIL blocks}
\label{uncurry_sec_mil}
\intent{Show uncurrying by example, continuing discussion in previous
  section.}  Examination of !+absBlockL209+! in
Figure~\ref{uncurry_fig_compose_b} reveals one opportunity for
optimization: the call to !+compose()+! results in a closure that is
entered on the next line with argument !+f+!. We could rewrite the
program to use the closure directly:
\begin{singlespace}
  \begin{MILVerb}[gobble=4]
    absBlockL209 (f):
      v210 <- closure absBodyL201 {} 
      v210 @@ f
  \end{MILVerb}
\end{singlespace}
\noindent Now we can see that !+v210+! refers to a closure pointing to
!+absBodyL201+! that captures no variables. Block~!+absBodyL201+! also
returns a closure, this time capturing its argument and pointing to 
block~!+absBodyL202+!. We can rewrite our program again to use
the value returned by !+absBodyL201+! directly:
\begin{singlespace}
  \begin{MILVerb}[gobble=4]
    absBlockL209 (f):
      v210 <- closure absBodyL201 {} 
      closure absBodyL202 {f}
  \end{MILVerb}
\end{singlespace}
\noindent The first value, !+v210+!, becomes irrelevant after our
second rewrite, allowing us to rewrite !+absBlockL209+! one more time,
producing:
\begin{singlespace}
  \begin{MILVerb}[gobble=4]
    absBlockL209 (f): closure absBodyL202 {f}
  \end{MILVerb}
\end{singlespace}
\noindent Thus, by uncurrying we have eliminated the creation of one
closure and the execution of at least one |Enter| instruction.

\intent{Describe uncurrying in more general terms-- what do we do,
  what don't we do.}  Our uncurrying optimization transforms MIL
programs to eliminate redundant closure allocations and |Enter|
instructions as we did by hand for the program in
Figure~\ref{uncurry_fig_compose_a}. We determine if a particular tail
evaluates to a closure and, if so, we replace the tail with the
closure directly. We can also detemine if an |Enter| instruction
results in a closure, allowing us to replace that |Enter| with the
closure returned.

Our optimization is applied to every ``normal'' block in the program,
not closure capturing blocks. We analyze closure allocations within
each block but do not propagate that information between blocks. We
discuss alternate strategies for performing uncurrying in
Section~\ref{uncurry_sec_future}; for now, we focus on our optimization
as currently implemented.

\section{Dataflow Equations}
\label{uncurry_sec_df}
\intent{Define dataflow equations for our uncurrying optimization.}
We implement uncurrying with a forwards dataflow analysis that
determines if a given statement allocates a closure. The
analysis creates a map of bound variables to closures. If a variable
is re--bound in the block, the analysis updates its map by removing any 
facts that referred to that variable and adding a new fact associating the 
variable with the new value. 

\begin{myfig}
  \begin{minipage}{\hsize}
    \begin{math}
      %% Below used to measure & typeset the case where we don't
      %% see a binding.
      \newtoks\widest \widest={t (F, !+v\ \texttt{<-}\ \ldots+!)} %%
      \begin{array}{rlr}
        \multicolumn{3}{c}{\textit{Facts}} \\
        \setL{Labels} &= \text{Set of all program labels.} \\
        \setL{Vars} &= \text{Set of all variables.} \\
        \setL{Clo} &= \{(l, v_1, \dots, v_n)\ ||\ l \in \setL{Labels}, v_i \in \setL{Var}, n \geq 0\}.\\
        \setL{Fact} &= \setL{Vars} \times (\{\top\} \cup \setL{Clo}). \\\\

        \multicolumn{3}{c}{\textit{Meet}} \\
        
        p \lub q &= \begin{cases}
          p & \text{when}\ p = q \\
          \top & \text{when}\ p \neq q,
        \end{cases} \labeleq{uncurry_df_lub} & \eqref{uncurry_df_lub} \\
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } p, q \in \setL{Clo}.}\\\\
        
        F_1 \wedge F_2 &= \begin{array}{l}
          \{(v, p \lub q)\ ||\ (v, p) \in F_1, (v, q) \in F_2\}\ \cup \\
          \{(v, \top)\ ||\ v \in \mfun{dom}(F_1), v \not\in \mfun{dom}(F_2)\ \text{or} \\
          \phantom{\{(v, \top)\ ||\ } v \not\in \mfun{dom}(F_1), v \in \mfun{dom}(F_2)\},
        \end{array} \labeleq{uncurry_df_meet} & \eqref{uncurry_df_meet} \\ 
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } F_1, F_2 \in \setL{Fact}.}\\\\

        \multicolumn{3}{c}{\textit{Transfer Function}} \\
        t (F, !+v\ \text{\bind}\ l\ \{v_1, \dots, v_n\}+!) &= 
          \{!+(v, (l, v_1, \dots, v_n))+!\} \cup (F\ \backslash\ \mfun{uses}(F, !+v+!)) 
          \labeleq{uncurry_df_transfer_closure} & \eqref{uncurry_df_transfer_closure} \\
        \the\widest &= \{!+(v, \top)+!\} \cup (F\ \backslash\ \mfun{uses}(F, !+v+!)) \labeleq{uncurry_df_transfer_other} & \eqref{uncurry_df_transfer_other} \\
        t (F, !+\_+!) &= F, \labeleq{uncurry_df_transfer_rest} & \eqref{uncurry_df_transfer_rest} \\
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } F \in \setL{Fact}.} \\\\

        \mfun{uses}(F, v) &= \{(u, p)\ ||\ (u, p) \in F, p = (l, \dots v \dots) \},
        \labeleq{uncurry_df_uses} & \eqref{uncurry_df_uses} \\
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } F \in \setL{Fact}, v \in \setL{Var}.}
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
compute. Each \setL{Fact} value is a pair, $(v, p)$, associating a
bound variable $v$ with a value $p$. If $p \in \setL{Clo}$, $v$ refers
to a known location and some set of of captured variables. Otherwise,
when $p = \top$, $v$ refers to some other value that we do not care
about.

\intent{Describe $\wedge$.}  We combine sets of \setL{Fact} values
using our meet operator, $\wedge$, as defined in
Equation~\eqref{uncurry_df_meet}. We define $\wedge$ over two sets of
facts, $F_1$ and $F_2$. When a variable $v$ only appears in $F_1$ or
$F_2$, we assume we do not not know what value $v$ may represent, so
we add $(v, \top)$ to the result. When a variable
appears in both $F_1$ and $F_2$, we create a new pair by combining
the two associated \setL{Clo} values using the \lub operator defined
in Equation~\eqref{uncurry_df_lub}. The resulting pair has the same
variable but a (possibly) new \setL{Clo} value. Together, \setL{Fact}
and $\wedge$ form a lattice as described in
Chapter~\ref{ref_chapter_background}, Section~\ref{back_subsec_facts}.

\intent{Illustrate $\wedge$ with an example.}  For example, if $F_1 =
\{(v, \{l\})\}$ and $F_2 = \{(u, \{l\}), (v, \{l\})\}$ then $F_1
\wedge F_2$ would be $\{(v, \{l\}), (u, \top)\}$. Because $u$ only
appears in one set, we cannot assume it will always refer to $\{l\}$,
so we add the pair $(u, \top)$ to the result. But $v$ appears in both
so we add $(v, \{l\} \lub \{l\})$, or $\{(v, \{l\})\}$, to the result
set.

\intent{Explain in detail how $t$ works.}  Our transfer function, $t$,
takes a statement and a set of \setL{Fact} values, $F$, as arguments.
It returns an updated \setL{Fact} set. We define $t$ by cases for each
type of MIL statement.

Equation~\eqref{uncurry_df_transfer_closure} applies when the
\rhs of a \bind statement creates a closure, as in
\binds v <- \clo[b: v_1, \dots, v_n]/. $t$ creates a \setL{Clo}
value with !+b+! (the label pointed to by the closure) and $!+v_1,
..., v_n+!$, the variables captured by the closure. A new fact
associating \var v/, the variable on the \lhs of the \bind
statement, is created. Because \var v/ has been redefined, any closure
that captured \var v/ does not refer to the new value for \var v/. The
\mfun{uses} function in Equation~\eqref{uncurry_df_uses} finds the
facts in $F$ that represent a closure capturing the variable \var v/. We
remove any facts in $F$ that refer to \var v/ by subtracting the results
of \mfun{uses} function from $F$.  We add our new fact to this set and
return. Our result set shows that \var v/ now refers to the closure
\clo[l: v_1, \dots, v_n], and does not include any previous facts
that referred to !+v+!.

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
gathered by $t$ allow us to replace |Enter| expressions with closure
allocations if we know the closure that the expression results
in. That is, we can rewrite tails like !+f @@ x+! when $!+(f, p) \in
\setL{Fact}+!$ and $!+p+! = (!+l, c_1, \dots, c_n+!)$ (i.e., $!+p+!
\neq \top$). We replace !+f @@ x+! with the closure constructed:
$!+k\ l\ \{c_1, \dots, c_n, x\}+!$. Notice we add the !+x+!  argument
to the closure as well.

\intent{Point out we don't inline closures from |Goto| expressions.}
The example we discussed in Section~\ref{uncurry_sec_mil} does not
match with the optimization just discussed on one crucial point:
replacing calls to normal blocks on the \rhs of a \bind with
their closure result. Our implementation relies on another, more
general, optimization that inlines simple blocks into their
predecessor. We describe the optimization in detail in
Chapter~\ref{ref_chapter_monadic}, but in short that optimization will
inline calls to blocks such as !+compose+!, so a statement like !+v <-
compose()+! becomes !+v <- k absBodyL201 \{\}+!, where !+absBodyL201+! is the
label in the closure returned by !+compose()+!.

\section{Implementation}
\label{uncurry_sec_impl}

\intent{Provide a bridge to the four subsections below.}  Originally,
we called this transformation ``closure--collapse,'' because it
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
work in tandem to rewrite !+@@+! expressions within a block.

\intent{Introduce example used throughout this section.}
Figure~\ref{uncurry_fig_eg} gives an example program we will use
throughout this section to illustrate our implementation. The program
takes a string as input, converts it to an integer, doubles that
value, and returns the result. The program consists of five
blocks. Two of the blocks, !+k0+! and !+k1+!, are
\cc. Two others, !+add+! and !+toInt+!, are normal
blocks whose implementation we ignore. The final block, !+main+!, is
also a normal block but is intended to be treated as the entry point
for the program.

\intent{Signposts.}
We present our implementation in five sections, reflecting the
structure of our dataflow equations above. We first give the types
used, followed by the definition of our lattice, then our transfer
function, then our rewriting function, and finally we show the driver
that applies the optimization to a given program.

\begin{myfig}
  \begin{minipage}{\hsize}\singlespacing
    \begin{MILVerb}[gobble=6]
      main(s):
        n <- toInt(s)
        v0 <- k0 {}
        v1 <- v0 @@ n
        v2 <- v1 @@ n
        return v2

      k0 {} a: k1 {a} 
      k1 {a} b: add(a, b)
      add(x, y): \ldots
      toInt(s): \ldots
    \end{MILVerb}
  \end{minipage} \\
  \caption{Example program.}
  \label{uncurry_fig_eg}
\end{myfig}

\subsection{Types}
\label{uncurry_impl_types}
\intent{Describe types used; give details on managing names; point out
  it other differences.}  Figure~\ref{uncurry_fig_types} shows the
types used by our implementation to represent the sets given in
Figure~\ref{uncurry_fig_df}. The |DestOf| type represents the
\setL{Dest} set, |CloVal| represents \setL{Clo}, and |CollapseFact|
represents \setL{Fact}. 

\begin{myfig}
  \begin{minipage}{\hsize}
%let includeTypes = True
%include Uncurry.lhs
%let includeTypes = False
  \end{minipage}
  \caption{The types for our analysis. Referring to the sets
    defined in Figure~\ref{uncurry_fig_df}, we use |DestOf| for the
    \setL{Dest} set, |CloVal| for \setL{Clo} and |CollapseFact| for
    \setL{Fact}.}
  \label{uncurry_fig_types}
\end{myfig}

\intent{Explain different |DestOf| values.}
|DestOf| actually carries more information than we specified for
\setL{Dest}. Recall that \cc blocks either return a
closure or jump directly to a block. The |Capture| constructor
represents the first case and |Jump| the second. The |Dest| value in
both is a destination: either the label stored in the closure
returned, or the block that the closure jumps to immediately.  

\intent{Details on |Capture| value.}
When a \cc block returns a closure, it copies all
captured variables from the old closure to the new. The argument can
be copied or ignored. The flag in the |Capture| constructor indicates
if the argument is used. 

\intent{Details on |Jump| value.}
Each integer in the list given to |Jump| represents the position of a
variable from the closure received. The arguments to the block are
built by traversing the list from beginning to end, putting the
variable indicated by the index into the corresponding argument for
the block. For example, the block !+c+!  in the following:
\begin{singlespace}
  \begin{MILVerb}[gobble=4]
    c {a, b, c}: l(c, a, b)
    l(c, a, b): \dots
  \end{MILVerb}
\end{singlespace}
would be represented by the value |Jump {-"!+l+!"-} [2, 0, 1]|, because the
variables from the closure $!+\{a, b, c\}+!$ must be given to !+l+! in
the order $!+(c, a, b)+!$.

\intent{Details on |CloVal| values.}  We use |CloDest| to represent
all \setL{Clo} values except $\top$. Recall that \setL{Clo} represents
a closure, holding a label and captured variables. |CloDest| stores a
|Dest| value, representing the label the closure refers to, and a list
of captured variables, |[Name]|. Hoopl provides |WithTop|, a type that adds a $\top$
element to any other type. We use |WithTop CloDest| to define the
alias |CloVal|, which completes our representation of \setL{Clo}.

\intent{Explain how |CollapseFact| represents \setL{Fact}.}  We use
the |CollapseFact| alias to represent our \setL{Fact}
set. |CollapseFact| aliases a finite map from variables (i.e., |Names|)
to |CloVals|.

\subsection{Lattice \& Meet}
Figure~\ref{uncurry_fig_lattice} shows the |DataflowLattice| structure
defined for our analysis. We set |fact_bot| to an empty map, meaning
we start without any information. We define |lub| over |CloVals|, just
like \lub in Figure~\ref{uncurry_fig_df}. Hoopl requires that
|fact_join| take particular arguments, so we use |toJoin| to transform
|lub| into the right type of function. The Hoopl--provided function
|joinMaps| transforms |toJoin lub| into a function that operates over
finite maps, giving |fact_join| the right signature.

\begin{myfig}
  \begin{minipage}{\hsize}
%let includeLattice = True
%include Uncurry.lhs
%let includeLattice = False
  \end{minipage}
  \caption{The Hoopl |DataflowLattice| declaration representing the 
  lattice used by our analysis.}
  \label{uncurry_fig_lattice}
\end{myfig}

\subsection{Transfer}
We give the implementation of $t$ (from Figure~\ref{uncurry_fig_df})
in Figure~\ref{uncurry_fig_transfer}. Due to Hoopl's use of GADTs, we
must specify a case for every |Stmt| constructor. As in all
Hoopl-based forwards analysis, the second argument to |t| is our facts
so far. |BlockEntry| and |CloEntry| just pass the facts given
along.\footnote{Note these will always be empty maps, because our
  analysis does not extend across blocks and |fact_bot| in our lattice
  is |Map.empty|.} Because we do not propagate facts between blocks,
|CaseM| and |Done| pass an empty map to each successor, using the
Hoopl--provided |mkFactBase| function to create a |FactBase| from 
empty facts. 

\begin{myfig}
  \begin{minipage}{\hsize}
%let includeTransfer = True
%include Uncurry.lhs
%let includeTransfer = False
  \end{minipage}
  \caption{The Haskell implementation of our transfer function $t$
    from Figure~\ref{uncurry_fig_df}.}
  \label{uncurry_fig_transfer}
\end{myfig}

|Bind| statments are handled based on the \rhs of the
statement. If the statement does not directly create a closure, we
create a fact associating the variable on the \lhs of the
bind with |Top|, just as in
Equation~\eqref{uncurry_df_transfer_other}. If the expression creates
a closure, we create a new fact using the closure's destination and
captured variables, corresponding to
Equation~\eqref{uncurry_df_transfer_closure}. We insert the new
fact into our |facts| finite map, using an appropriately transformed
|lub| function to combine the new fact with any existing facts. 

\begin{myfig}
  \begin{tabular}{lcccc}
    & !+n+! & !+v0+! & !+v1+! & !+v2+! \\\cmidrule{2-5}
    \begin{minipage}[c]{2in}\singlespacing
      \begin{MILVerb}[gobble=8]
        n <- toInt(s)
        v0 <- k0 {}
        v1 <- v0 @@ n
        v2 <- v1 @@ n
        return v2
      \end{MILVerb}
    \end{minipage}
    & |Top| & |CloDest {-"!+k0\ +!"-} []| & |Top| & |Top| \\
  \end{tabular}
  \caption{How facts evolve for the !+main+! block as our example program
    is iteratively rewritten.}
  \label{uncurry_fig_impl_transfer}
\end{myfig}

Figure~\ref{uncurry_fig_impl_transfer} shows the facts gathered for
each variable in the !+main+! block of our sample program from
Figure~\ref{uncurry_fig_eg}. The variables !+n+!, !+v1+!, and
!+v2+! are assigned |Top| becuase the \rhs of the \bind
statement for each does not directly create a closure. Only !+v0+!  is
assigned a |CloDest| value because the \rhs of its \bind
statement is in the right form. We will see in the next section how
these facts evolve as the program is rewritten.

\subsection{Rewrite}
\intent{Describe how |collapse| looks up closure information for an
  |Enter| expression.}  Figure~\ref{uncurry_fig_rewrite} shows the
implementation of our rewrite function for the uncurrying
optimization. We will describe it in pieces.

\begin{myfig}
  \begin{minipage}{\hsize}
%let includeRewrite = True
%include Uncurry.lhs
%let includeRewrite = False
  \end{minipage} \\
  \caption{Our rewrite function that replaces !+f @@ x+! expressions
    with closure allocations, if possible.}
  \label{uncurry_fig_rewrite}
\end{myfig}

|collapseRewrite| takes one argument and creates a rewriter that can
be applied to our MIL program. The |blocks| argument associates every
block in our program with a |DestOf| value. |DestOf|, as explained in
Section~\ref{uncurry_impl_types}, indicates if the block returns a
closure or  jumps immediately to another block. 

For example, Figure~\ref{fig_uncurry_destof} shows the |DestOf| values
in |blocks| for each block in the example program from
Figure~\ref{uncurry_fig_eg}. The $\bot$ value associated with blocks
!+toInt+!, !+add+! and !+main+! means they do not appear in |blocks|.

\begin{myfig}
    \begin{tabular}{ll}
      Block & |DestOf| \\\cmidrule{1-1} \cmidrule{2-2} 
      !+main+! & $\bot$ \\
      !+k0+! &  |Capture {-"!+k1+!"-} True| \\
      !+k1+! &  |Jump {-"!+add+!"-} [0, 1]| \\
      !+add+! & $\bot$ \\
      !+toInt+! & $\bot$ \\
    \end{tabular}
  \caption{|DestOf| values associated with each block in our example
program.}
  \label{fig_uncurry_destof}
\end{myfig}

|collapseRewrite| applies Hoopl's |iterFwdRw| and |mkFRewrite|
functions to our locally defined |rewriter| function, creating a
|FwdRewrite| value. The |iterFwdRw| combinator applies our function to
the program over and over, until |rewriter| stops changing the
program. This ensures that a ``chain'' of closure allocations get
collapsed into a single allocation, if possible.

Figure~\ref{uncurry_fig_rewrite_iterations} shows how the !+main+!
block in our example program changes as Hoopl iteratively applies
|rewriter|. During the first iteration, |rewriter| transforms the !+v1
{}<- v0 @@ n+! to !+v1 <- k1 {n}+!  (because !+v0+! holds a closure to
!+k0+!, and |blocks| tells us !+k0+! returns a closure pointing to
!+k1+!). During the second iteration, |rewriter| transforms the line,
!+v2 <- v1 @@ n+!, to !+v2 <- add(n, n)+!. No more iterations occur
after the second, as |rewriter| will not find any more \bind that can
be transformed.

\begin{myfig}
  \begin{tabular}{lcccc}
    Post-Iteration & !+main+! \\\midrule
    1 & \begin{minipage}[c]{2in}\singlespacing
      \begin{MILVerb}[gobble=8]
        n <- toInt(s)
        v0 <- k0 {}
        \textbf[v1 <- k1 {n}]
        v2 <- v1 @@ n
        return v2
      \end{MILVerb}
    \end{minipage}  \\
    2 & \begin{minipage}[c]{2in}\singlespacing
      \begin{MILVerb}[gobble=8]
        n <- toInt(s)
        v0 <- k0 {}
        v1 <- k1 {n}
        \textbf[v2 <- add(n, n)]
        return v2
      \end{MILVerb}
    \end{minipage} 
  \end{tabular}
  \caption{How facts evolve for the !+main+! block as our example program
    is iteratively rewritten.}
  \label{uncurry_fig_rewrite_iterations}
\end{myfig}

The |rewriter| function checks if it can rewrite |Enter| expressions
when they occur in a |Done| statement or on the \rhs of a
|Bind|. In the first case, |done n l (collapse col f x)| will produce
a new |Done| statement with the |TailM| expression returned by
|collapse|, if |collapse| returns a |Just| value. Otherwise, |done|
does not rewrite. Therefore, |done| rewrites an |Enter| only when
|collapse| indicates that rewriting can occur. In the second case,
|bind| behaves similarly, only rewriting if |collapse| returns a
|Just| value. In all other cases, |rewriter| does no rewriting.

The |collapse| function takes a set of facts and two names,
representing the left and \rhs of a !+@@+! expression,
respectively. If !+f+! is associated with a |CloDest| value (as
opposed to |Top|) in the |facts| map, then rewriting can possibly
occur, but only if the block indicated in the |CloDest| value returns
a closure or jumps immediately to another block. |collapse| uses the
|blocks| argument to look up the behavior of the destination in the
|CloDest| value.

If the destination immediately jumps to another block (as indicated by
a |Jump| value) then we will rewrite the !+f @@ x+! expression to call
the block directly. The list of integers associated with |Jump|
specifies the order in which arguments were taken from the closure and
passed to the block. |collapse| uses the |fromUses| function to
re-order arguments appropriately.

In Figure~\ref{fig_uncurry_destof}, we showed that the |DestOf| value
associated with !+k1+! is |Jump {-"!+add+!"-} [0, 1]|. The list |[0,
  1]| indicates that !+add+! takes arguments in the same order as the
appear in the closure. However, if !+add+! took arguments in
opposite order, !+k1+! and !+add+! would look like:
\begin{MILVerb}
  k1 {a} b: add(b, a)
  add(x, y): \ldots
\end{MILVerb}
And the |DestOf| value associated with !+k1+! would be |Jump
{-"!+add\ +!"-} [1, 0]|.

If the destination returns a closure, we will rewrite !+f @@ x+! to
directly allocate the closure. The boolean argument to |Capture|
indicates if the closure ignores the argument passed, which |collapse|
uses to determine if it should place the !+x+! argument in the closure
that is allocated or not.


\subsection{Optimization Pass}

\intent{Describe how we recognize when a closure is created} 

\intent{Describe how we re-write an Enter instruction to a closure or goto}

\intent{Describe how deep rewrite progressively captures closures.}

\section{Prior Work}
\label{uncurry_sec_prior}
\intent{Discuss other approaches to uncurrying.}

\section{Future Work}
\label{uncurry_sec_future}
\intent{Discuss strategies for uncurrying: local only, across blocks, by duplication.}

\section{Reflection}
\label{uncurry_sec_refl}
\end{document}
