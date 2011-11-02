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
\intent{Motivate partial application -- what does it buy us?}  Partial
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
\intent{Remind reader about different MIL blocks and how closures are
  created.}  Recall that MIL defines two types of blocks, one of which
we call \emph{closure-capturing}. MIL also defines the |Enter|
expression (written !+@@+!) that applies a function to an
argument. !+@@+! always expects a closure on its left--hand side and
some argument on the right. That is, in the expression !+f @@ x+!,
!+f+!  will be a closure value that points to a closure-capturing
block and !+x+! is the argument passed to that block.

\intent{Remind reader how MIL closure--capturing blocks are written
  and used.}  A closure--capturing block is always executed as the
result of an !+@@+! expression. That is, in the expression !+f @@ x+!,
!+f+!  represents a closure that points to some block labeled !+k+!
and that captures variables $!+\{v_1, \dots, v_n\}+!$. The !+@@+!
expression causes the block !+k+! to be executed using the closure
value represented by !+f+! and with the arguemnt !+x+!. We write
closure--capturing blocks as $!+k\ \{v_1, \dots, v_n\}\ x: \dots
+!$. !+k+! names the block, $!+\{v_1, \dots, v_n\}+!$ give the
variables expected in the closure, !+x+! represents the argument
passed, and the \ldots after the !+:+! represent the body of the block.

MIL also defines blocks that are not closure-capturing. A normal
blocks takes a list of arguments, as specified by the \lamC definition
that it represents, and is written as $!+b(v_1, \dots, v_n): \dots+!$.

These definitions allow MIL to represent function application
uniformly. For a function with $n$ arguments, $n - 1$ !+k+! blocks
will be generated. At least one !+b+! block will also be generated,
representing the body of the function. Each $!+k_i+!$ block, except
the $!+k_{n-1}+!$, returns a new closure pointing to the next
$!+k_{i+1}+!$ block. The closure created by block $!+k_i+!$ contains
all values found in the closure it was given, plus the new argument
given. The last block, $!+k_{n-1}+!$, does not return a new
closure. Instead, it calls block !+b+!, unpacking all necessary
arguments. The value returned from block !+$k_{n-1}$+! is the value
returned from block !+b+!.

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
second in the chain of closure-capturing blocks that eventually result
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
We implement uncurrying with a forwards dataflow-analysis that
attempts to determine if a given statement allocates a closure. The
analysis maintains a map of bound variables to closures. If a variable
is re-bound in the block, the analysis updates its map. Our analysis
only operates over single blocks so in general the tracking is very
straightforward. Our compiler will not generate new names that
collide, so in practice the map of bound variables only grows.

\begin{myfig}
  \begin{minipage}{\hsize}
    \begin{math}
      %% Below used to measure & typeset the case where we don't
      %% see a binding.
      \newtoks\rest \rest={t (F, !+v\ \texttt{<-}\ \ldots+!)} %%
      \begin{array}{rlr}
        \multicolumn{3}{c}{\textit{Facts}} \\
        \setL{Labels} &= \text{Set of all program labels.} \\
        \setL{Capt} &= \text{Set of all labels of closure-capturing blocks}; \setL{Capt} \subset \setL{Labels}. \\
        \setL{Vars} &= \text{Set of all variables.} \\
        \setL{Dest} &= \{(l, m)\ ||\ l \in \setL{Capt}, m \in \setL{Labels}\}. \\
        \setL{Clo} &= \top \cup \{(l, v_1, \dots, v_n)\ ||\ l \in \setL{Labels}, v_i \in \setL{Vars}\}. \\
        \setL{Fact} &= \{(v, p)\ ||\ v \in \setL{Vars}, p \in \setL{Clo}\}. \\\\

        \multicolumn{3}{c}{\textit{Meet}} \\
        
        l \lub m &= \begin{cases}
          l & \text{when}\ l = m. \\
          \top & \text{when}\ l \neq m.
        \end{cases} \labeleq{uncurry_df_lub} & \eqref{uncurry_df_lub} \\
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } l, m \in \setL{Clo}.}\\\\
        
        F_1 \wedge F_2 &= \begin{array}{l}
          \{(v, p \lub l)\ ||\ (v, p) \in F_1, (v, l) \in F_2\}\ \cup \\
          \{(v, p)\ ||\ (v, p) \in F_1, v \not\in \mfun{dom}(F_2)\}\ \cup \\
          \{(u, l)\ ||\ (u, l) \in F_2, u \not\in \mfun{dom}(F_1)\}.
        \end{array} \labeleq{uncurry_df_meet} & \eqref{uncurry_df_meet} \\ 
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } F_1, F_2 \in \setL{Fact}.}\\\\

        \multicolumn{3}{c}{\textit{Transfer Function}} \\
        \mathllap{t (F, !+v\ \text{!+<-+!}\ k\ b\ \{c_1, \dots, c_n\}+!)} &= 
          \{!+(v, (b, c_1, \dots, c_n))+!\} \wedge F. 
          \labeleq{uncurry_df_transfer_closure} & \eqref{uncurry_df_transfer_closure} \\
        \mathllap{\the\rest} &= \{!+(v, \top)+!\} \wedge F. \labeleq{uncurry_df_transfer_other} & \eqref{uncurry_df_transfer_other} \\
        t (F, !+\_+!) &= F. \labeleq{uncurry_df_transfer_rest} & \eqref{uncurry_df_transfer_rest} \\
        & \multicolumn{2}{l}{\phantom{=} \text{where\ } F \subseteq \setL{Fact}.}
      \end{array}
    \end{math}
  \end{minipage}
  \caption{Dataflow facts and equations for our uncurrying transformation.}
  \label{uncurry_fig_df}
\end{myfig}

\intent{Describe fundamental sets used by our dataflow equations.}
Figure~\ref{uncurry_fig_df} shows the dataflow equations used for our
analysis. The sets \setL{Labels} and \setL{Vars} contain all labels
and all variables in the program, respectively. \setL{Capt} represents
the subset of labels that represent closure-capturing
blocks. \setL{Dest} associates each label in \setL{Capt} with the
destination label of the closure returned by that particular
closure-capturing block. 

\intent{Describe |Clo| set.}  The \setL{Clo} set associates some label
with a list of variables; the list may be empty. We use \setL{Clo}
values to represent the location a closure points to and the set of
variables it captures. Our facts are pairs associating a bound
variable with either a \setL{Clo} value or $\top$. That is, a bound
variable refers to a known location and some set of captured variables
or some other value that we do not care about.

\intent{Describe |Fact| set} We use the \setL{Var} and \setL{Clo} sets
to describe \setL{Fact}, the set of facts that we will compute. Each
\setL{Fact} value associates a variable with the \setL{Clo} value computed
for that variable. 

\intent{Describe $\wedge$.}  We combine sets of \setL{Fact} values
using our meet operator, $\wedge$, as defined in
Equation~\eqref{uncurry_df_meet}. We define $\wedge$ over two sets of
facts, $F_1$ and $F_2$. When a given variable only appears in $F_1$ or
$F_2$, we add the pair directly to the result set. When a variable
appears in both $F_1$ and $F_2$, we create a new pair where we combine
the two associated \setL{Clo} values using the \lub operator defined
in Equation~\eqref{uncurry_df_lub}. The resulting pair has the same
variable but a (possibly) new \setL{Clo} value. Together, \setL{Fact}
and $\wedge$ form a lattice as described in
Chapter~\ref{ref_chapter_background}, Section~\ref{back_subsec_facts}.

\intent{Illustrate $\wedge$ with an example.}  For example, if $F_1 =
\{(v, \{l\})\}$ and $F_2 = \{(c, \{l\}), (v, \{m\})\}$ then $F_1
\wedge F_2$ would be $\{(v, \top), (c, \{l\})\}$. Because $c$ only
appears in one set, we add it directly to the result. But $v$ appears
in both so we add $(v, \{m\} \lub \{l\})$, or $\{(v, \top)\}$, to the
result set.

\intent{Explain in detail how $t$ works.}  We define the transfer
function, $t$, by cases for each MIL statement. $t$ takes a statement
and $F$, a set of \setL{Fact} values. $t$ returns a \setL{Fact}
set. For any statement besides !+<-+!, $t$ is the identity --- it just
returns $F$.

Equation~\ref{uncurry_df_transfer_closure} applies when the
right--hand side of a !+<-+! statement creates a closure, as in
$!+v\ \text{<-}\ k\ b\ \{c_1, \dots, c_n\}+!$. $t$ creates a
\setL{Clo} value with !+b+! (the label pointed to by the closure) and
$!+c_1, ..., c_n+!$, the variables captured by the closure. A new fact
associating !+v+!, the variable on the left--hand side of the !+<-+!
statement, is created. $t$ returns the result of combining $F$ and the
new fact using $\wedge$.

\section{Rewriting}
\label{uncurry_sec_rewriting}
\intent{Explain how we rewrite |Enter| expressions.}  The facts
gathered by $t$ allow us to replace |Enter| expressions with closure
allocations if we know the closure that the expression results
in. That is, we can rewrite tails like !+f @@ x+!  when $!+(f, p) \in
\setL{Fact}+!$ and $!+p+! \neq \top$. Because $!+p+! \neq \top$, we
know $!+p+! = (!+l, c_1, \dots, c_n+!)$; therefore we replace the
!+@@+! expression with the closure !+f @@ x+!  would construct:
$!+k\ l\ \{c_1, \dots, c_n, x\}+!$. Notice we add the !+x+!  argument
to the closure as well.

\intent{Point out we don't inline closures from |Goto| expressions.}
The example we discussed in Section~\ref{uncurry_sec_mil} does not
match with the optimization just discussed on one crucial point:
replacing calls to normal blocks on the right--hand side of a !+<-+! with
their closure result. Our implementation relies on another, more
general, optimization that inlines simple blocks into their
predecessor. We describe the optimization in detail in
Chapter~\ref{ref_chapter_monadic}, but in short that optimization will
inline calls to blocks such as !+compose+!, so a statement like !+v <-
compose()+! becomes !+v <- k l \{\}+!, where !+l+!  refers to the
label in the closure returned by !+compose()+!.

\section{Implementation}
\label{uncurry_sec_impl}

\intent{Provide a bridge to the four subsections below.}  Originally,
we called this transformation ``closure-collapse,'' because it
``collapsed'' the construction of multiple closures into the
construction of a single closure. Later, we learned this optimization
is known as ``uncurrying,'' but at the point the code had already been
written. The ``collapse'' prefix in the code shown is merely an
artifact of our previous name for the analysis.

In our presentation of dataflow equations in
Section~\ref{uncurry_sec_df}, we described this analysis by
statements. However, our implementation works on blocks of MIL
code. Fortunately, the net result is the same due to Hoopl's
interleaved analysis and rewriting. Our transfer and rewrite functions
work in tandem to rewrite !+@@+! expressions within a block.

We present our implementation in five sections, reflecting the
structure of our dataflow equations above. We first give the types
used, followed by the definition of our lattice, then our transfer
function, then our rewriting function, and finally we show the driver
that applies the optimization to a given program.

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
\setL{Dest}. Recall that closure-capturing blocks either return a
closure or jump directly to a block. The |Capture| constructor
represents the first case and |Jump| the second. The |Dest| value in
both is a destination: either the label stored in the closure
returned, or the block that the closure jumps to immediately.  In any
case, |Dest| is just an alias for a |(Name, Label)| tuple, where
|Name| is a string and |Label| a Hoopl value, representing a block of
MIL code.

\intent{Details on |Capture| value.}
When a closure-capturing block returns a closure, it copies all
caputred variables from the old closure to the new. The argument can
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
would be represented by the value |Jump l [2, 0, 1]|, because the
variables from the closure $!+\{a, b, c\}+!$ must be given to !+l+! in
the order $!+(c, a, b)+!$.

\intent{Details on |CloVal| values.}
We use |CloDest| to represent \setL{Clo} values, except the $\top$
value. Recall that \setL{Clo} represents a closure, holding a label
and captured variables. |CloDest| stores a |Dest| value, representing
the label the closure refers to, and a list of captured variables,
|[Name]|. 

\intent{Explain how we use |WithTop| to complete representation of
  \setL{Clo}.}  Hoopl provides |WithTop|, a type that adds a $\top$
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
like \lub in Figure~\ref{uncurry_fig_df}). Hoopl requires that
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

|Bind| statments are handled based on the right--hand side of the
statement. If the statement does not directly create a closure, we
create a fact associating the variable on the left--hand side of the
bind with |Top|, just as in
Equation~\eqref{uncurry_df_transfer_other}. If the expression creates
a closure, we create a new fact using the closure's destination and
captured variables, corresponding to
Equation~\eqref{uncurrying_df_transfer_closure}. We insert the new
fact into our |facts| finite map, using an appropriately transformed
|lub| function to combine the new fact with any existing facts. 

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

\subsection{Rewrite}
\intent{Describe how |collapse| looks up closure information for an
  |Enter| expression.}  Figure~\ref{uncurry_fig_rewrite} shows the
implementation of our rewrite function for the uncurrying
optimization. We will take the function apart in pieces.

\begin{myfig}
  \begin{minipage}{\hsize}
%let includeRewrite = True
%include Uncurry.lhs
%let includeRewrite = False
  \end{minipage}
  \caption{Our rewrite function that replaces !+f @@ x+! expressions
    with closure allocations.}
  \label{uncurry_fig_rewrite}
\end{myfig}

The |collapse| function takes a set of facts and two names,
representing the left and right--hand side of a !+@@+! expression,
respectively. If !+f+! is associated with a |CloDest| value (as
opposed to |Top|) in the |facts| map, then rewriting can possibly
occur. The |blocks| argument associates each label in the program with
one of three values: a closure value if the block immediately returns
one, a destination block if the block immediately jumps to another
block, or nothing if none of these cases hold. |collapse| uses
|blocks| to find the result of the block referred to by the |CloDest|
value associated with !+f+!. When the result is a closure or immediate
jump, |collapse| returns a |Just| value indicating such. In all other
cases, it returns |Nothing|, meaning no rewrite can occur.

The |rewriter| function checks if it can rewrite |Enter| expressions
when they occur in a |Done| statement or on the right--hand side of a
|Bind|. In the first case, |done n l (collapse col f x)| will produce
a new |Done| statement with the |TailM| expression returned by
|collapse|, if |collapse| returns a |Just| value. Otherwise, |done|
does not rewrite. Therefore, |done| rewrites an |Enter| only when
|collapse| indicates that rewriting can occur. In the second case,
|bind| behaves similarly, only rewriting if |collapse| returns a
|Just| value. In all cases, |rewriter| does no rewriting.

Finally, |collapseRewrite| defines its rewriting function so that all
possible rewrites occur. Hoopl provides the combinator |iterFwdRw|,
which applies iteratively applies the rewriter to the program until no
more graph rewrites occur. This iteration ensures that ``chains'' of 
closures get collapsed into a single allocation, if possible.

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
