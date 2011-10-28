\documentclass[12pt]{report}
%include polycode.fmt
%format . = "."
%format ^ = "\char`^"
\input{preamble}
\begin{document}
\input{document.preamble}

\chapter{Uncurrying}
\label{ref_chapter_uncurrying}
\intent{Overture: partial application, curried, uncurried.}  Many
functional languages encourage programmers to write definitions that
take advantage of \emph{partial application}. Partial application
means to give a function only some of its arguments, resulting in a
new function that takes the remaining arguments. A function definition
that supports partial application is said to be in \emph{curried}
style, after the mathematician Haskell Curry.\footnote{Historically,
  Curry used this style but did not invent it. That is due to a early
  $20^{th}$ century mathematician named Schrodenfinkel.} In contrast,
an \emph{uncurried} function is defined such that it can only be
applied to all of its arguments at once.

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

\intent{signposts.}  Section~\ref{uncurry_sec_papp} describes partial
application in more detail; Section~\ref{uncurry_sec_costs} discusses
drawbacks to supporting partial application.  We introduce several
examples that will illustrate our optimization and discuss uncurrying
as applied to MIL in Section~\ref{uncurry_sec_mil}. We present our
dataflow equations for uncurrying in Section~\ref{uncurry_sec_df}, and
describe our implementation in
Section~\ref{uncurry_sec_impl}. Alternate uncurrying strategies, which
we leave to future work, are shown in
Section~\ref{uncurry_sec_future}. We conclude with a discussion of our
experience in Section~\ref{uncurry_sec_conc}.

%% \emph{Describes our optimization for collapsing intermediate
%% closures. Our choice of representation is analyzed to
%% show how it facilitates this optimization. We should show one
%% closure can be eliminated from a program and how the optimization
%% is applied over and over until a fixed point is reached. The format
%% for this section will vary from the other two.}

\section{Partial Application}
\label{uncurry_sec_papp}
\intent{Motivate partial application -- what does it buy us?}  Partial
application in functional programming promotes re-usability and
abstraction. It allows the programmer to define specialized versions
of a function by providing only some fixed arguments to a general
function. 

\begin{myfig}
> map1 :: (a -> b) -> [a] -> [b]
> map1 = {-"\ldots"-}
>
> map2 :: ((a -> b), [a]) -> b
> map2 = {-"\ldots"-}
  \label{uncurry_fig_partapp}
  \caption{Haskell definitions in curried and uncurried style. |map|
    can be easily partially applied to produce specialized functions; |foldr|
    cannot.}
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
> square :: [Int] -> [Int]
> square = map2 (^ 2)

We cannot do the same as easily with |map2|. At best we can define
a function that ignores one of its arguments:

> upCase2 :: ((a -> b), [Char]) -> [Char]
> upcase2 (_, xs) = map2 (toUpper, xs)

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
level, function application is expensive because multilple operations
must take place to implement it: saving registers, loading addresses,
and finally jumping to the target location. Partial application
exagerates all these costs.

Partial application essentially creates a \emph{series} of functions,
each of which gathers arguments and returns a closure pointing to the
next function in the chain. Only when all the arguments are gathered
does the function do ``real work'' --- that is, something besides
gathering up arguments and creating a closure. Supporting partial
application also tends to influence the lowest-level of code
generation, where function appliation is implemented. Rather than
generate specialized code for partially versus fully-applied
functions, its simplest to generate the same code for all
applications, partial or otherwise. That means every function
appliation pays the price of partial applicatoin, even if the function
is ``obviously'' fully-applied.

\section{Partial Application and MIL}
\intent{Remind reader about different MIL blocks and how closures
  are created.}  Recall that MIL defines two types of blocks:
\emph{closure-capturing} and normal. A closure-capturing block takes
two arguments: a closure and a value. We write closure-capturing
blocks as !+k \{$v_1$, \ldots, $v_n$\} $v$+!, where $v_1$, \ldots, $v_n$
represent values in the closure given, and $v$ a new value. A normal
block takes some number of arguments, as specified by the \lamC
definition that it represents, and is written as !+b($v_1$, \ldots,
$v_n$)+!.

MIL also defines the \emph{enter} operator (written !+@@+!), which
applies a function to an argument. !+@@+! always expects a closure on
its left--hand side and some argument on the right. The closure always
refers to a closure-capturing block. A closure will never point to a
normal block.

These definitions allow MIL to represent function application
uniformly. For a function with $n$ arguments, $n - 1$ !+k+! blocks
will be generated. At least one !+b+! block will also be generated,
representing the body of the function. Each !+k+! block, except the
last, returns a new closure pointing to the next !+k+! block'; the new
closure contains all values found in the old closure plus the
new argument given. The last !+k+! block, block !+$k_{n-1}$+!, does 
not return a new closure. Instead, it calls block !+b+!, passing
all arguments needed from the closure given and the argument given. The
value returned from block !+$k_{n-1}$+! is the value returned from block !+b+!.

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

Block !+absBlockL209+! actually implements partial application. It
evaluates the !+compose+! block, getting a closure that points to the
top-level entry point for |compose|. !+absBlockL209+! applies that
value to !+f+! and returns the result. The value returned by
block~!+compose+! is a closure that points to !+absBodyL202+!, second
in the chain of closure-capturing blocks that eventually result in
executing |compose| with all its arguments. In other words, the result
of applying |compose1| is a function that will take two more arguments
and then execute |compose| with them. 

\section{Uncurrying MIL blocks}
\label{uncurry_sec_mil}
\intent{Show uncurrying by example, continuing discussion in previous
  section.}  Examination of !+absBlockL209+! in
Figure~\ref{uncurry_fig_compose_b} reveals one opportunity
for optimization: the call to !+compose()+! results in a closure that
is entered on the next line with argument !+f+!. We could rewrite the
program to use the closure directly:
\begin{singlespace}
  \begin{MILVerb}[gobble=4]
    absBlockL209 (f):
      v210 <- closure absBodyL201 {} 
      v210 @@ f
  \end{MILVerb}
\end{singlespace}

\noindent Now we can see that !+v210+! holds a closure pointing to
!+absBodyL201+! and holding no arguments. Block~!+absBodyL201+! also
returns a closure, this time holding one argument and pointing to 
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
Figure~\ref{uncurry_fig_compose}. We determine if a particular tail
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
\intent{Define dataflow equations for our uncurrying optimization.}
We implement uncurrying with a forwards dataflow-analysis that
attempts to determine if a given binding operation allocates a
closure. The analysis maintains a map of bound variables to
closures. If a given variable is re-bound, the analysis updates its
map. Our analysis only operates over single blocks so in general the
tracking is very straightforward. Our compiler will not generate new
names that collide, so in practice the map of bound variables only
grows.

\begin{myfig}
  \begin{minipage}{\hsize}
    \begin{math}
      %% Below used to measure & typeset the case where we don't
      %% see a binding.
      \newtoks\rest \rest={t (!+v\ \texttt{<-}\ \ldots+!)} %%
      \begin{array}{rl}
        \multicolumn{2}{c}{\textit{Facts}} \\
        \setL{Labels} &= \text{Set of all program labels.} \\
        \setL{Capt} &= \text{Set of all labels of closure-capturing blocks}; \setL{Capt} \subset \setL{Labels}. \\
        \setL{Vars} &= \text{Set of all variables.} \\
        \setL{Dest} &= \{(l, m)\ ||\ l \in \setL{Capt}, m \in \setL{Labels}\}. \\
        \setL{Clo} &= \top \cup \{(l, v_1, \dots, v_n)\ ||\ l \in \setL{Labels}, v_i \in \setL{Vars}\}. \\
        \setL{Fact} &= \{(v, p)\ ||\ v \in \setL{Vars}, p \in \setL{Clo}\}. \\\\

        \multicolumn{2}{c}{\textit{Meet}} \\
        %% Below aligns the meet operator on both rows.
        l \wedge \mathllap{l}\phantom{m} &= l. \\
        l \wedge m &= \top, \text{when}\ l \neq m. \\
        & \text{where\ } l, m \in \setL{Clo}.\\\\

        \multicolumn{2}{c}{\textit{Transfer Function}} \\
        \mathllap{t (!+v\ \text{!+<-+!}\ k\ b\ \{c_1, \dots, c_n\}+!)} &= %%
        \begin{cases}
          \{!+(v, (b, c_1, \dots, c_n) \wedge l)+!\} \cup (F \backslash \{!+(v, l)+!\}) & \text{when\ } !+(v, l)+! \in F. \\
          \{!+(v, (b, c_1, \dots, c_n))+!\} \cup F & \text{otherwise.}
        \end{cases} \label{uncurry_df_transfer_closure} \\
        \mathllap{\the\rest} &= \{!+(v, \top)+!\} \cup F.\\
        t (!+\_+!) &= F. \\
        & \text{where\ } F \subseteq \setL{Fact}.
      \end{array}
    \end{math}
  \end{minipage}
  \caption{Dataflow facts and equations for our uncurrying transformation.}
  \label{uncurry_fig_df}
\end{myfig}

\intent{Explain dataflow equations presented in the figure.}
Figure~\ref{uncurry_fig_df} shows the dataflow equations used for our
analysis. The sets \setL{Labels} and \setL{Vars} contain all labels
and all variables in the program, respectively. \setL{Capt} represents
the subset of labels that represent closure-capturing
blocks. \setL{Dest} associates each label in \setL{Capt} with the
destination label of the closure returned by that particular
closure-capturing block. 

The \setL{Clo} set associates some label with a list of variables; the
list may be empty. We use \setL{Clo} values to represent the location
a closure points to and the set of variables it captures. Our facts
are pairs associating a bound variable with either $\top$ or a
\setL{Clo} value. That is, a bound variable refers to a known location
and some set of captured variables or some other value that we do
not care about.

Our meet operator combines values in \setL{Fact}. When values are equal,
the result is the same value. Otherwise, the result is $\top$. 

\intent{Explain in detail how $t$ works.}
We define the transfer function, $t$, over MIL statements. $t$ takes a
statement and $F$, a set of \setL{Fact} values. For any statement
besides !+<-+!, $t$ does nothing --- it just returns $F$. 

Equation~\ref{uncurry_df_transfer_closure} applies when the
right--hand side of a !+<-+! statement creates a closure, as in 
$!+v\ \text{<-}\ k\ b\ \{c_1, \dots, c_n\}+!$. $t$ creates a \setL{Clo}
value with !+b+! (the label pointed to by the closure) and 
$!+c_1, ..., c_n+!$, the variables captured by the closure. Again, 
$t$ uses the meet operator to combine the new \setL{Clo} value with
any in $F$ already associated with !+v+!; otherwise, the new fact
is just added to $F$.

\section{Rewriting}

\intent{Explain how we rewrite based on facts.}  The facts gathered by
$t$ allow us to replace |Enter| operations when we know the left--hand
side refers to a closure. That is, we rewrite tails of the form !+f @@
x+! when $!+(f, p) \in \setL{Fact}+!$ and $!+p+! \neq \top$. We
know $!+p+! = (!+l, c_1, \dots, c_n+!)$, therefore we replace the
!+@@+!  operation with $!+k\ l\ \{c_1, \dots, c_n, x\}+!$, the closure
!+f @@ x+! would construct. Notice we add the !+x+! argument to the 
closure as well.

The example we discussed in Section~\ref{uncurry_sec_mil} does not
match with the optimization just discussed on one crucial point:
replacing blocks on the left-hand side of a !+<-+! with their closure
result. Our implementation relies on another, more general, that
inlines simple blocks into their predecessor. We describe the
optimization in detail in Chapter~\ref{ref_chapter_monadic}, but in short
that optimization will inline calls to blocks such as !+compose+!, so
a statement like !+v <- compose()+! becomes !+v <- k l \{\}+!, where !+l+!
refers to the label in the closure returned by !+compose()+!.

\section{Implementation}

\intent{Provide a bridge to the four subsections below.}
We present our implementation in four sections. 

\subsection{Types}
\label{uncurry_impl_types}
\intent{Describe |DestOf|; give details on managing names; point out
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

|DestOf| actually carries more informatino than we specified for
\setL{Dest}. Recall that closure-capturing blocks either return a
closure or jump directly to a block. The |Capture| constructor
represents the first case and |Jump| the second. The |Dest| value is a
destination: either the label stored in the closure returned, or the
block that the closure jumps to immedietely.  In any case, |Dest| is
just an alias for a |(Name, Label)| tuple, where |Name| is a string
and |Label| a Hoopl value.

When a closure-capturing block returns a closure, it always copies all
values from the old closure to the new. The argument can be copied or
ignored. The flag in the |Capture| constructor, |Maybe Int|, indicates
if the argument is used. When rewriting an expression like !+f @@ x+!
to $!+k\ b\ \{\dots\}+!$, we use this value to
determine if !+x+! should added to the variables captured in
the braces, $!+\{\dots\}+!$. For example, the following block
ignores its argument when returning a closure:
\begin{singlespace}
  \begin{MILVerb}[gobble=4]
    c {a, b} x: closure l {a, b}
    l {a, b} y: \ldots
  \end{MILVerb}
\end{singlespace}

We use the |Jump| constructor to capture when a closure-capturing
block jumps directly to another block.\footnote{This indicates that
  the function represented is now fully applied.} The |Dest| value
indicates which block we will jump to. However, the block receives
arguments in some order that does not necessarily represent the order
of variables in the captured closure. Each integer in the list given to
|Jump| represents the position of a variable from the closure
received. The arguments to the block are built by traversing the list
from beginning to end, putting the variable indicated by the index into
the corresponding argument for the block. For example, the block !+c+!
in the following:
\begin{singlespace}
  \begin{MILVerb}[gobble=4]
    c {a, b, c}: l(c, a, b)
    l(c, a, b): \dots
  \end{MILVerb}
\end{singlespace}
would be represented by the value |Jump l [2, 0, 1]|, because the
variables from the closure $!+\{a, b, c\}+!$ must be given to !+l+! in
the order $!+(c, a, b)+!$.

\subsection{Transfer}

\subsection{Rewrite}

\subsection{Optimization Pass}

\intent{Describe how we recognize when a closure is created} 

\intent{Describe how we re-write an Enter instruction to a closure or goto}

\intent{Describe how deep rewrite progressively captures closures.}

\section{Prior Work}

\section{Future Work}
\label{uncurry_sec_future}
\intent{Discuss strategies for uncurrying: local only, across blocks, by duplication.}

\section{Reflection}
\label{uncurry_sec_refl}
\end{document}
