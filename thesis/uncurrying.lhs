%&preamble
\input{nodocclass}\dodocclass
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\begin{document}
\numbersoff
\input{document.preamble}

\chapter{Uncurrying}
\label{ref_chapter_uncurrying}
\intent{Overture: partial application, curried, uncurried.}  Many
functional languages allow programmers to write definitions that take
advantage of \emph{partial application}. Partial application means to
give a function only some of its arguments, resulting in a new
function that takes the remaining arguments. A function definition
that supports partial application is said to be in \emph{curried}
style. In contrast, an \emph{uncurried} function is defined such that
it can only be applied to all of its arguments at once.

\intent{Briefly motivate optimization.}  Partial
application can be very convenient for programmers, but it can also be
very inefficient. Conceptually, an uncurried function can do real work
with each application --- that is, each application executes the body
of the function. A curried function does not do any real work until 
given all its arguments; each in-between application essentially creates
a new function. 

\intent{Introduce uncurrying optimization.} This chapter describes our
implementation of \emph{uncurrying}, an optimization that reduces the
number of partial applications in a program. Through dataflow
analysis, we find partial applications for a given function within a
block of \mil code. We replace those partial applications with
full applications to the function, or at least fewer partial
applications. 

\intent{Signposts.}  Section~\ref{uncurry_sec_papp} describes partial
application in more detail; Section~\ref{uncurry_sec_costs} discusses
drawbacks to supporting partial application.  We introduce several
examples that will be used to illustrate our optimization in
Section~\ref{uncurry_sec_examples} and discuss uncurrying as applied
to \mil in Section~\ref{uncurry_sec_mil}. We present our dataflow
equations for uncurrying in Section~\ref{uncurry_sec_df} and our
rewriting strategy in Section~\ref{uncurry_sec_rewriting}. We show our
implementation in Section~\ref{uncurry_sec_impl}. We give two extended
examples in Section~\ref{uncurry_sec_example}, demonstrating our
optimization's utility on more complicated \cfgs. Many other
implementations of uncurrying have been described elsewhere; we discuss
those in Section~\ref{uncurry_sec_related}. Section~\ref{uncurry_sec_refl}
summarizes our contribution.

\section{Partial Application}
\label{uncurry_sec_papp}
\intent{Motivate partial application --- what does it buy us?}  Partial
application in functional programming promotes reusability and
abstraction. It allows the programmer to define specialized functions
by fixing some of the arguments to a general function.

\begin{myfig}
> map1 :: (a -> b) -> [a] -> [b]
> map1 f xs = {-"\ldots"-}
  \caption{A Haskell definition in curried style. |map1|
    can be partially applied directly to produce specialized functions.}
  \label{uncurry_fig_partapp}
\end{myfig}

For example, the Haskell code in Figure~\ref{uncurry_fig_partapp}
defines |map1| in curried style. We can create specialized mapping
functions by applying |map1| to a single argument. The following
functions convert all their arguments to uppercase or square all
integers in a list, respectively:

\begin{singlespace}
> upCase1 :: [Char] -> [Char]
> upCase1 = map1 toUpper
>
> square1 :: [Int] -> [Int]
> square1 = map1 (^ 2)
\end{singlespace}

\section{Cost of Partial Application}
\label{uncurry_sec_costs}
\intent{Demonstrates why partial application can be inefficient.}  At
the assembly language level, function application is expensive because
multiple operations must take place to implement it: saving registers,
loading addresses, and finally jumping to the target location.
Partial application exaggerates all these costs by essentially creating
a \emph{series} of functions, each of which takes one argument and
returns a closure that points to the next function in the chain. Only
when all the arguments are gathered does the function do ``real work''
--- that is, something besides allocating closures and gathering up
arguments.

Partial application also influences the code generated to implement
function application. Rather than generate specialized code for
partially versus fully-applied functions, it is simplest to generate
the same code for all applications, partial or otherwise; meaning
every function application pays the price of partial application, even
if the function is ``obviously'' fully-applied.

\section{Partial Application in \mil}
\label{uncurry_sec_examples}
\intent{Remind reader about normal blocks.}
Recall that \mil defines two types of blocks: ``\cc'' and ``normal.''
Normal blocks act much like labeled locations in a program and are
written ``\block b(v_1, \dots, v_n): \ldots''  A normal block is
executed by writing ``\goto b(v_1, \dots, v_n).'' 

\intent{Remind reader about \cc blocks.}
\Cc blocks are also like labeled locations, except that they expect to
receive a closure and an argument when called. We write \cc blocks as ''\ccblock k(v_1, \dots, v_n)x: \ldots'' A \cc block is always executed as the result of an
expression like ``\app f * x/.''

\intent{Describe how \cc and normal blocks are generated.}  These two
definitions allow \mil to represent function application
uniformly. For a function with $n$ arguments, $n$ \cc blocks and at
least one basic block will be generated. The first $(n - 1)$ \cc
blocks are typically of the form:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \ccblock k$!+_i+!$(v_1, \dots, v_i)x: \mkclo[k$!+_{i+1}+!$:v_1, \dots, v_i, x]
  \end{AVerb}
\end{singlespace}

\noindent This means the block \lab k$!+_i+!$/ returns a new closure
that points to the next block (\lab k$!+_{i+1}+!$/) and contains all
the values from the original closure as
well as the argument \var x/ ($\{!+v_1, \dots, v_i, x+!\}$).

The last block, \lab k$!+_{n-1}+!$/, does not immediately return a new
closure, but instead calls a basic block, \lab b/, with all necessary
arguments. In the general case, we write \lab k$!+_{n-1}+!$/ as:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \ccblock k$!+_{n-1}+!$(v_1, \dots, v_{n-1})x: \goto b(v_1, \dots, v_{n-1}, x)
  \end{AVerb}
\end{singlespace}

\noindent Of course, depending on the definition of the original
function, we may not pass all arguments to \lab b/, or pass them in
the same order as they appear in the closure. 

\intent{Show how partial application is implemented.}  For example,
Figure~\ref{uncurry_fig_compose_a} shows the \lamC definition for
|compose| and its implementation in \mil.\footnote{This same program
  also appears in Figure~\ref{mil_fig2} on Page~\pageref{mil_fig2}.}
The basic block \lab k0/ acts as the top-level entry point to
|compose|. The other basic block, \lab compose/, implements the body
of |compose|. The two \cc blocks, \lab k1/ and \lab k2/ implement
\mil's support for partial application. The remaining \cc block only
executes when all of the arguments to |compose| are available.

\begin{myfig}\disableoverfull
  \begin{tabular}{l}
    \begin{minipage}{\hsize}
> compose f g x = f (g x)
    \end{minipage} \\
    \hss\scap{uncurry_fig_compose_a}\hss \\
    \begin{minipage}{\hsize}
      \begin{NVerb}[gobble=8]
        \block k0(): \mkclo[k1:] 
        \ccblock k1()f: \mkclo[k2:f] 
        \ccblock k2(f)g: \mkclo[k3:f, g] 
        \ccblock k3(f, g)x: \goto compose(f, g, x) 
        
        \block compose(f, g, x): {\rm\emph{\dots as in Figure \ref{mil_fig1b} on Page \pageref{mil_fig1b}}\dots} 
      \end{NVerb}
    \end{minipage} \\\\
    \hss\scap{uncurry_fig_compose_b}\hss
  \end{tabular}
  \caption{The |compose| function. Part~\subref{uncurry_fig_compose_a}
    shows our \lamC definition. Part~\subref{uncurry_fig_compose_b}
    shows \mil code implementing Part~\subref{uncurry_fig_compose_a}.}
  \label{uncurry_fig_compose}
\end{myfig}

Executing \lab k1/ results in a closure that captures the argument
\var f/ and points to \lab k2/. The closure returned is equivalent to
the expression \lcapp compose * a/, with |a| being the value held
by the closure. Executing \lab k2/ returns a closure that captures two
values, \var f/ and \var g/, and points to \lab k3/. The closure
returned is equivalent to the expression \lcapp compose * a * b/, with |a|
and |b| held by the closure. The values returned by these
two blocks represent partially applied functions. The remaining \cc
block, \lab k3/, does not return a value representing a partially
applied function, however.\footnote{Unless, of course, |compose a b c|
  results in a function value!} Instead, \lab k3/ immediately executes
the \lab compose/ block, and is the same as evaluating \lcapp compose
* a * b * c/.

\section{Uncurrying \mil blocks}
\label{uncurry_sec_mil}
\intent{Show uncurrying by example, continuing discussion in previous
  section.}  Using the definition of |compose| given in
Figure~\ref{uncurry_fig_compose_b}, we can give a \mil implementation
of a partially-applied |compose| function, \lcdef compose1(f)=\lcapp
compose * f/;:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block compose1(f):
      \vbinds t0<- \goto k0();
      \app t0 * f/
  \end{AVerb}
\end{singlespace}

Examination of this definition reveals one opportunity for
optimization: the call ``\goto k0()'' on the first line assigns the
closure \mkclo[k1:] to \var t0/, which we immediately enter on the
next line with argument \var f/. We can eliminate the call to \lab k0/
by allocating the closure directly:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block compose1(f):
      \vbinds t0<- \mkclo[k1:];
      \app t0 * f/
  \end{AVerb}
\end{singlespace}

Now we can see that \var t0/ holds the value
\mkclo[k1:], a closure referring to block~\lab k1/
and capturing no variables. Block~\lab k1/ also returns a
closure, this time capturing its argument and pointing to block~\lab
k2/. With this knowledge, we can eliminate the expression
\app t0 * f/ and instead create the closure directly, using the
expression \mkclo[k2:f]:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block compose1(f):
      \vbinds t0<- \mkclo[k1:];
      \mkclo[k2:f]
  \end{AVerb}
\end{singlespace}

Now we find that \var t0/ is no longer used, allowing us to
rewrite \lab compose1/ one more time:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block compose1(f): \mkclo[k2:f]
  \end{AVerb}
\end{singlespace}

\noindent Thus, by uncurrying, we eliminate one call (\goto k0()),
one enter operation (\app t0 * f/), and the creation of one closure
(\mkclo[k1:]).

\intent{Describe uncurrying in more general terms -- what do we do,
  what don't we do.}  Our uncurrying optimization transforms \mil
programs to eliminate \enter operations as we did by hand for
|compose1|. In essence, we determine if an \enter operation results in
a known closure, allowing us to replace that expression with the
closure returned.

\section{Dataflow Equations}
\label{uncurry_sec_df}
\intent{Define dataflow equations for our uncurrying optimization.}
We implement uncurrying with a forwards dataflow analysis. Our facts
indicate if a given variable refers to a known closure. Facts are
propagated to successor blocks when the block ends with a call or case
statement. We combine multiple input facts for a given block by
determining if all sets of facts agree on the value of a given
variable.

\begin{myfig}[tbp]
  \begin{minipage}{\hsize}
    \input{uncurrying_df}
  \end{minipage}
  \caption{Dataflow facts and equations for our uncurrying transformation.}
  \label{uncurry_fig_df}
\end{myfig}

\intent{Describe fundamental sets used by our dataflow equations:
  |Labels|, |Names|, |Clo| and |Facts|.}  Figure~\ref{uncurry_fig_df}
shows the dataflow equations used for our analysis. The sets
\setL{Labels} and \setL{Vars} contain all labels and all variables in
the program, respectively.  The \setL{Clo} set associates some label
with a (possibly empty) list of variables. We use \setL{Clo} values to
represent the location that a closure points to and the set of
variables that it captures. The \setL{Fact} set defines the facts that
we can compute, each of which is a pair, $(\var v/, p)$, associating a
bound variable $\var v/$ with a value $p$. If $p \in \setL{Clo}$, then
$\var v/$ refers to a known location and an associated set of captured
variables. Otherwise, if $p = \top$, then $\var v/$ refers to some
unknown value.

\intent{Describe $\wedge$.}  We combine sets of \setL{Fact} values
using a meet operator, $\wedge$, as defined in
Equation~\eqref{uncurry_df_meet}, over two sets of
facts, $F_1$ and $F_2$. When a variable \var v/ only appears in
$F_1$ or $F_2$, we assume we do not not know what value \var v/ may
represent, so we add $(\var v/, \top)$ to the result. When a variable
appears in both $F_1$ and $F_2$, we create a new pair by combining the
two associated \setL{Clo} values using the \lub operator defined in
Equation~\eqref{uncurry_df_lub}. The resulting pair has the same
variable but a (possibly) new \setL{Clo} value. Together, \setL{Fact}
and $\wedge$ form a lattice as described in
Section~\ref{back_subsec_facts} on Page~\pageref{back_subsec_facts}.

\intent{Illustrate $\wedge$ with an example.}  For example, if $F_1 =
\{(\var v/, \mkclo[l:a]), (\var w/, \mkclo[l:b])\}$ and $F_2 = \{(\var u/,
\mkclo[l:a]),$ $(\var v/, \mkclo[l:a]),$ $(\var w/, \mkclo[l:a])\}$ then
$F_1 \wedge F_2$ would be $\{(\var u/, \top), (\var v/, \mkclo[l:a]),
(\var w/, \top)\}$. Because \var u/ only appears in one set, we cannot
assume it will always refer to \mkclo[l:a], so we add the pair $(\var
u/, \top)$ to the result. The variable \var v/ appears in both sets with the same
closure, so we add $(\var v/, \mkclo[l:a] \lub \mkclo[l:a])$, or $(\var v/,
\mkclo[l:a])$, to the result set. Finally, \var w/ appears in both
sets, but the closure associated with it in each differs: \mkclo[l:b] in
$F_1$ and \mkclo[l:a] in $F_2$. Therefore, we add $(\var w/, \top)$ to
the result set. 

\intent{Explain in detail how $t$ works.}  Our transfer function, $t$,
takes a statement and a set of \setL{Fact} values as arguments.
It returns a \setL{Fact} set containing new facts based on the
statement given. We define $t$ by cases over \mil statements.


\begin{description}
\item[\emph{Equations~\eqref{uncurry_df_transfer_block} and
    \eqref{uncurry_df_transfer_ccblock} --- Block Entry}] These
  equations represent the entry points for normal and \cc blocks. We
  do not modify the facts received, but just pass them along to the
  next statement in the block.

\item[\emph{Equation~\eqref{uncurry_df_transfer_closure} --- Bind To
    Closure}] When the \rhs of a \mbind statement creates a closure,
  as in \binds v <- \mkclo[b: v_1, \dots, v_n];, we may or may not
  create a new fact. If \var v/ appears in $\{\var v_1/, \dots,
  \var v_n/\}$ (as in ``\binds v <- \mkclo[k1:];!+;+! \binds v <-
  \mkclo[k2: v];''), then we simply delete any facts mentioning \var v/
  and we do not create a new fact. Otherwise we create the fact $(\var
  v/, \mkclo[b: v_1, \dots, v_n])$.  Because \var v/ has been
  redefined, we must invalidate any previous facts that refer to \var
  v/, as they do not refer to the new value of \var v/. To ensure we
  remove all references to \var v/, we apply \mfun{uses} to the
  combined set $F \cup \{(\var v/, \mkclo[b:v_1, \dots, v_n])\}$. We
  subtract the result from $F$, thereby removing any facts that refer
  to $\var v/$.

\item[\emph{Equation~\eqref{uncurry_df_transfer_other} --- Any Other
    Bind}] Any other binding, \binds v <- \dots;, that does not create
  a closure invalidates any facts about \var v/. Therefore, we first
  remove all facts referring to \var v/ in $F$ with the \mfun{uses}
  function. We then create a new fact associating \var v/ with $\top$,
  indicating that we know \var v/ does not refer to a closure. Finally, we
  combine the new set and new fact and return the combined set.
\end{description}

\Mil blocks that end with a
\milres case/ statement can have multiple successors. Dataflow
analysis does not usually specify that different facts go to different
successors, but we do so here. The notation
\ensuremath{\{\hbox{\ensuremath{\lab b$!+_1+!$/:F_1}},
  \hbox{\ensuremath{\lab b$!+_2+!$/:F_2}}\}} used in
Equations~\eqref{uncurry_df_transfer_goto} and
\eqref{uncurry_df_transfer_case} means we transfer the set of facts
$F_1$ to the successor block \lab b$!+_1+!$/, and the set of facts
$F_2$ to the successor block \lab b$!+_2+!$/.

\Mil blocks also specify formal parameters, and the names of those
parameters usually differ from the actual variables used in a given
``goto'' expressions. Within a block, we collect facts using the names
local to that block. Those facts will have no meaning in successor
blocks (or worse, the wrong meaning) because the variable names will
differ. Equation~\ref{uncurry_df_rename} defines \mfun{rename}, which
takes a set of facts, $F$, and two variables, $\var u/$ and $\var
v/$. If a fact about $\var v/$ exists in $F$, we update it to be about
$\var u/$.  Combined with the \mfun{args} function, which retrieves
the list of formal parameters for a block, \mfun{rename} can update a
set of facts from one block so that it makes sense in a successor block.

The two equations,\eqref{uncurry_df_transfer_goto} and
\eqref{uncurry_df_transfer_case}, describe how we transfer facts
between blocks using the functions given above. In this presentation,
we only show one variable, but the equations can be easily extended to
a multiple variables. We also use a number of auxiliary definitions,
besides those mentioned above. The \mfun{trim} function applies the
\mfun{uses} and \mfun{delete} functions to remove all facts from $F$
that refer to or are about \var v/. The \mfun{delete} function removes
any facts about \var v/ from $F$. Conversely, the \mfun{restrict}
function filters all facts from $F$ except those about \var v/.

\begin{description}
\item[\emph{Equation~\eqref{uncurry_df_transfer_goto} --- Goto Block}]
  When a ``goto'' expression, such as \goto b(v), appears at the end
  of a block, we transfer the facts collected so far to the successor
  block. We use the \mfun{restrict} function to remove all facts from
  $F$ except those about \var v/. We then rename the facts to match
  the successor block \lab b/, and pass those facts along to \lab b/.

\item[\emph{Equation~\eqref{uncurry_df_transfer_case} --- Case
    Statement}] A case statement requires careful treatment. Recall
  that each alternative arm jumps immediately to another block (\lab
  b$!+_1+!$/, etc. in the equation). We pass separate sets of facts to
  each successor, tailored to the arguments that each block
  declares. Additionally, the alternative can bind new variables,
  shadowing previous bindings. Any of our existing facts that are
  about or that refer to shadowed variables must be removed from
  our facts before we pass them to successor blocks.
  
  For each successor block \lab b$!+_i+!$/, we first restrict our
  facts to include only those variables passed to the block (i.e., \var
  w_i/). From that restricted set, we trim any facts that mention a
  binding from the case alternative (i.e., \var v_i/). Finally, we
  rename those facts according the formal arguments of the successor
  block \lab b$!+_i+!$/.  We stress that, while these equations only
  mention one variable in the alternative and in the call to \lab
  b$!+_i+!$/, making an operation like \mfun{trim} trivial, they can
  easily be extended to multiple variables, allowing them to be used
  with real \mil programs.

\item[\emph{Equation~\eqref{uncurry_df_transfer_rest} --- All Other
    Statements}] Our final equation covers all other types of
  expression that can appear at the end of a block, such as a function
  application or allocation. None of these expressions specify a
  successor block, so in a sense it does not matter what they return
  as that value will be ignored. For completeness, however, we return
  the empty set in this final case.
\end{description}

\section{Rewriting}
\label{uncurry_sec_rewriting}
\intent{Explain how we rewrite |Enter| expressions.}  The facts
gathered by our dataflow analysis allow us to replace \enter expressions with closure
allocations if we know the value that the expression results in. For
example, let $F$ be the facts computed so far and \binds v <- \app f *
y/; the statement we are considering. If $(\var f/, \mkclo[k0: x]) \in
F$, then we know \var f/ represents the closure \mkclo[k0: x], and we
may be able to rewrite the expression. If \lab k0/ returns
\mkclo[k1:x, y], then we can rewrite the statement to \binds v <-
\mkclo[k1: x, y];.  Alternatively, if \lab k0/ immediately calls \goto b0(x, y), we can rewrite the statement to
\binds v <- \goto b0(x, y);. In both cases it is likely that the formal
arguments to \lab k2/ differ from those in either the closure
\mkclo[k0:x] or the expression \app f * y/, and we will need to rename
our facts. However, as explained previously when discussing $t$, that
is a straightforward operation.

\intent{Point out we don't inline closures from |Goto| expressions.}
The example we discussed in Section~\ref{uncurry_sec_mil} does not
match the optimization just discussed on one crucial point:
replacing calls to normal blocks on the \rhs of a \mbind with their
closure result. Our implementation relies on another, more general,
optimization that inlines simple blocks into their predecessor. We
discuss the optimization in Chapter~\ref{ref_chapter_conclusion},
Section~\ref{conc_inline_monadic} on
Page~\pageref{conc_inline_monadic}, but in short that optimization
will inline calls to blocks such as \lab compose/, so a statement like
\binds v <- \goto compose(); becomes \binds v <-
\mkclo[absBodyL201:];, where \lab absBodyL201/ is the label in the
closure returned by \goto compose().

\section{Implementation}
\label{uncurry_sec_impl}

\intent{Provide a bridge to the four subsections below.}  Originally,
we called this transformation ``closure-collapse'' because it
``collapses'' the construction of multiple closures into the
construction of a single closure. Later, we learned that this optimization
is known as ``uncurrying,'' but at the point the code had already been
written. The ``collapse'' prefix in the code shown is an
artifact of our previous name for the analysis.

\intent{Introduce example used throughout this section.}
Figure~\ref{uncurry_fig_eg} gives an example program that we will use
throughout this section to illustrate our implementation. The program
takes a string as input, converts it to an integer, doubles that
value, and returns the result. The program consists of five
blocks. Two of the blocks, \lab k0/ and \lab k1/, are \cc. Two others,
\lab add/ and \lab toInt/, are normal blocks that call runtime
primitives. The final block, \lab main/, is also a normal block but
is treated as the entry point for the program.

\begin{myfig}
  \begin{minipage}{\hsize}\singlespacing
    \begin{AVerb}[gobble=6]
      \block main(s):
        \vbinds n<-\goto toInt(s);
        \vbinds v0<-\mkclo[k0:];
        \vbinds v1<-\app v0 * n/;
        \vbinds v2<-\app v1 * n/;
        \return v2/

      \ccblock k0()a: \mkclo[k1:a]
      \ccblock k1(a)b: \goto add(a, b)
      \block add(x, y): \prim plus(x, y)
      \block toInt(s): \prim atoi(s)
    \end{AVerb}
  \end{minipage} \\
  \caption{A \mil program we will use to illustrate our implementation
  of uncurrying.}
  \label{uncurry_fig_eg}
\end{myfig}

\intent{Signposts.}
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
Figure~\ref{uncurry_fig_df}. The |Clo| type represents
\setL{Clo}. |Label| and |Var| correspond to \setL{Label} and
\setL{Var}, respectively. For documentation, the |Label| type pairs a
string with \hoopl's |Label| type. |Clo| stores a |Label| value,
giving the block that the closure refers to, and a list of captured
variables, |[Var]|, representing the environment captured by the
closure.

\begin{myfig}
  \begin{minipage}{\hsize}\disableoverfull
%let includeTypes = True
%include Uncurry.lhs
%let includeTypes = False
  \end{minipage}
  \caption{The types for our analysis. Referring to the sets defined
    in Figure~\ref{uncurry_fig_df}, |Clo| represents \setL{Clo} and
    |Fact| represents \setL{Fact}. |DestOf| is not represented in our
    dataflow equations; it describes the behavior of each \mil block
    that we may use while rewriting.}
  \label{uncurry_fig_types}
\end{myfig}

\intent{Explain |DestOf| values.}  The |DestOf| type captures the
behavior of a given \cc block. Recall that we limit \cc blocks to
containing a single \term tail/ expression. The |DestOf| type uses the
|Capture| and |Jump| constructors to indicate if the block returns a
closure or if it jumps to a normal block, respectively. The |Label|
value in both is a destination: either the label stored in the closure
returned, or the block that the closure jumps to. We use these values
to determine how we rewrite a given ``enter'' expression.

\intent{Details on |Capture| value.}  The |Capture| value represents a
block with the form ``\ccblock k0(v_1, \dots, v_n)x:
\mkclo[k1:\dots],'' The flag in the |Capture| constructor indicates if
\mkclo[k1:\dots] includes the \var x/ argument or not. If |True|, the
argument is included in the closure returned. Otherwise, the
argument is ignored.

\intent{Details on |Jump| value.} The |Jump| value represents a block
with the form ``\ccblock k(v_1, \dots, v_n)x: \goto b(\ldots)'' The
arguments to \lab b/ are not necessarily in the same order as the
parameters for the \cc block \lab k/. Each integer in the list given
to |Jump| corresponds to one of \lab k/'s parameters. The value of the
integer gives the position of that parameter in the call to \lab
b/. The arguments in the call to \lab b/ are built by traversing the
list, putting the variable indicated by each index into the
corresponding argument for the block.\footnote{This situation can
  also apply to |Capture| blocks and we would need to update our
  implementation our compiler's code generation strategy changed or if
  we began writing \mil programs directly.}

For example, in the following, the variables in the closure received
by \lab c/ do not appear in the same order as expected by block \lab l/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \ccblock c(a, b)x: \goto l(x, a, b)
    \block l(x, a, b): \ldots
  \end{AVerb}
\end{singlespace}

\noindent 
We represent \lab c/ using |Jump {-"\lab
  l/\ "-} [2, 0, 1]|, because the variables from the closure \mkclo[:a,
  b] and the argument \var x/ must be given to \lab l/ in the order
$!+(x, a, b)+!$.

\intent{Explain how |WithTop Clo| and |Fact| represent \setL{Fact}.}
|Fact| is a finite map, representing our \setL{Fact} set. \Hoopl's
|WithTop| type adds a $\top$ value to any other type. |WithTop Clo|
then represents the set $\{\top\} \cup \{\setL{Clo}\}$. |Fact|, then,
associates variables with values in the set  $\{\top\} \cup \{\setL{Clo}\}$.

\subsection{Lattice \& Meet Operator}
\label{uncurry_impl_lattice}
Figure~\ref{uncurry_fig_lattice} shows the |DataflowLattice| structure
defined for our analysis. We set |fact_bot| to an empty map, meaning
that we start without any information. We define |lub| over |Clos|, just
like \lub in Figure~\ref{uncurry_fig_df}. We use |joinMaps|, provided
by \hoopl, and |toJoin| to transform |lub| into a function
that operates over finite maps and that has the signature required by
\hoopl's |fact_join| definition.

\begin{myfig}
  \begin{minipage}{\hsize}\disableoverfull
%let includeLattice = True
%include Uncurry.lhs
%let includeLattice = False
  \end{minipage}
  \caption{The \hoopl |DataflowLattice| declaration representing the 
  lattice used by our analysis.}
  \label{uncurry_fig_lattice}
\end{myfig}

\subsection{Transfer Function}
\label{uncurry_impl_transfer}
The definition of |transfer| in Figure~\ref{uncurry_fig_transfer}
gives the implementation of $t$ from Figure~\ref{uncurry_fig_df}. The
top-level definition, |collapseTransfer|, packages |transfer| into the
|FwdTransfer| value that \hoopl uses to represent forwards transfer
functions.  The |blockParams| argument to |collapseTransfer| gives the
list of parameters for every ordinary block in the program, which we
use during renaming operations. The first argument to |transfer| is
the statement we are analyzing, and the second is our facts so
far. |transfer| depends on a number of auxiliary functions: |kill|,
|using|, etc. We will describe each function as it is first
encountered when describing |transfer|. The |Map| prefix on some of
the functions used by |transfer| and related definitions indicates
they are imported from Haskell's standard |Data.Map| library. We
define |transfer| by cases, analogous to the cases given in
Equations~\eqref{uncurry_df_transfer_block} through
\eqref{uncurry_df_transfer_rest}.

\begin{myfig}[p]
  \begin{minipage}{\hsize}\begin{withHsLabeled}{uncurry_fig_transfer}\disableoverfull
%let includeTransfer = True
%include Uncurry.lhs
%let includeTransfer = False
    \end{withHsLabeled}
  \end{minipage}
  \caption{Our implementation of the transfer function $t$
    from Figure~\ref{uncurry_fig_df}.}
  \label{uncurry_fig_transfer}
\end{myfig}

\begin{description}
  \item[|BlockEntry|, |CloEntry| ---] These cases apply to the entry point
    of each normal or \cc block, implementing
    Equations~\eqref{uncurry_df_transfer_block} and
    \eqref{uncurry_df_transfer_ccblock}. In both instances they
    just pass the facts received on to the rest of the block.

  \item[|Bind v (Closure dest args)| ---] This case corresponds to
    Equation~\ref{uncurry_df_transfer_closure}, representing a bind
    statement that allocates a closure on its \rhs. Binding a variable
    invalidates any facts previously collected about that
    variable. The local definition of |facts'| on
    Line~\ref{uncurry_fig_transfer_closure_kill} uses the |kill|
    function to remove all facts from |fact| that mention |v|. If |v|
    appears in |args| then the closure mentions the variable being
    bound. If that is the case, then we do not want to create a new
    fact, and we want to remove any existing facts about
    |v|. Line~\ref{uncurry_fig_transfer_closure1} accomplishes both
    tasks by first deleting any facts about |v| from |facts'| and then
    returning the updated map. Otherwise, on
    Line~\ref{uncurry_fig_transfer_closure2} we create a new fact
    describing the closure (using \hoopl's |PElem| constructor),
    insert it into |facts'|, and return the result.

  \item[|Bind v _| ---] This case implements
    Equation~\ref{uncurry_df_transfer_other}. It removes any facts
    mentioning |v| and inserts a new fact associating |v| with |Top|,
    indicating we do not know what value |v| may have. 
  
  \item[|Done _ _ (Goto (_, dest) args)| ---] On
    Line~\ref{uncurry_fig_transfer_goto1}, we implement
    Equation~\ref{uncurry_df_transfer_goto}. Recall that we must
    filter our facts to those about variables in |args|, and that we
    must rename those facts to match the parameters declared by the
    block represented by |dest|. The definition of |facts'|
    (Line~\ref{uncurry_fig_transfer_goto2}) uses the |restrict|
    function for filtering, and the |rename| function for renaming. We
    use \hoopl's |mapSingleton| function to create a set of facts
    associated with the block given by |dest|, analogous to the
    \hbox{$\{\lab b/:\dots\}$} notation used in
    Equation~\ref{uncurry_df_transfer_goto}.
    
  \item[|Case _ alts| ---] Recall that
    Equation~\ref{uncurry_df_transfer_case} produced a map associating
    each successor block with a set of facts. The list comprehension
    on
    Lines~\ref{uncurry_fig_transfer_case_start}--\ref{uncurry_fig_transfer_case_end}
    defines |facts'| as a list of |(Label, Fact)| pairs. Each pair
    represents the facts passed to a given successor block. On
    Line~\ref{uncurry_fig_transfer_case_result}, we apply \hoopl's
    |mkFactBase| function to |facts'|, returning a map associating each |Label|
    with a |Fact| set --- just as in
    Equation~\ref{uncurry_df_transfer_case}.

    Line~\ref{uncurry_fig_transfer_case_alts} extracts each
    alternative from |alts|, the list of alternatives associated with
    the \milres case/ statement. We defined \mil such that each
    alternative immediately jumps to a block; |dest| represents the
    destination block for the alternative, and |args| the variables
    passed to that block. Each alternative can introduce new bindings,
    represented here by the |binds| list. On
    Line~\ref{uncurry_fig_transfer_case_trimmed}, we use |restrict| to
    filter our set of facts to those about |args|. Because new
    bindings introduced by the alternative can invalidate existing
    facts, we use the |trim| function to remove any facts from the
    restricted set that are about or mention a variable in
    |binds|. Finally, we need to rename our facts to match the
    parameter names used by the successor block. On
    Line~\ref{uncurry_fig_transfer_case_end}, we retrieve the
    parameter list for the given
    block. Line~\ref{uncurry_fig_transfer_case_start} uses the
    |rename| function to rename all facts in |trimmed| that are about
    variables in |args| to match the names given in |params|.
    
  \item[|Done _ _ _| ---] A block that does not end in one of the cases
    above has no successors. Therefore, we just return an empty set of
    facts (as in Equation~\ref{uncurry_df_transfer_rest}.). We
    construct an empty set by passing |mkFactBase| an empty list.    

\end{description}

\begin{myfig}
  \begin{tabular}{lcccc}
    Statement & \var n/ & \var v0/ & \var v1/ & \var v2/ \\\cmidrule{2-2}\cmidrule{3-3}\cmidrule{4-4}\cmidrule{5-5}
    \binds n <- \goto toInt(s); & & & &  \\
    \binds v0 <- \mkclo[k0:]; & $\top$ & & & \\
    \binds v1 <- \app v0 * n/; & $\cdot$ & \mkclo[k0:] & & \\
    \binds v2 <- \app v1 * n/; & $\cdot$ & $\cdot$ & $\top$ &  \\
    \return v2/ & $\cdot$ & $\cdot$ & $\cdot$ & $\top$ \\
  \end{tabular}
  \caption{Facts about each variable in the \lab main/ block of
    our example program from Figure~\ref{uncurry_fig_eg}. A blank entry
    means the variable has no facts associated with it yet. A ``$\cdot$''
    entry means the fact remains unchanged.}
  \label{uncurry_fig_impl_transfer}
\end{myfig}

Figure~\ref{uncurry_fig_impl_transfer} shows the facts gathered for
each variable in the \lab main/ block of our sample program, after the
corresponding statement is analyzed. The variables \var n/, \var v1/,
and \var v2/ are assigned $\top$ because the \rhs of the \mbind
statement for each does not directly create a closure. Only \var v0/
is assigned a |Clo| value, \mkclo[k0:], because the \rhs of its \mbind
statement is in the correct form. We will see in the next section how
these facts evolve as the program is rewritten.

\subsection{Rewrite}
\label{uncurry_impl_rewrite}
\intent{Give an example demonstrating iterative rewriting.}
Figure~\ref{uncurry_fig_rewrite} shows the top-level implementation of
our rewrite function for the uncurrying
optimization. |collapseRewrite| creates the rewriter that can uncurry
a \mil program. The |blocks| argument associates every \cc block in
our program with a |DestOf| value. |DestOf|, as explained in
Section~\ref{uncurry_impl_types}, indicates if the block returns a
closure or jumps immediately to another block. The |rewrite| function
actually implements the uncurrying transformation; we will describe it
after discussing how we use \hoopl's iterative rewriting
function, |iterFwdRw|.

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
\hoopl's |iterFwdRw| and |mkFRewrite| functions to create a
|FwdRewrite| value. |iterFwdRw| applies |rewriter| repeatedly, until
the |Graph| representing the program stops changing. \Hoopl computes
new facts (using |collapseTransfer|) after each rewrite. This ensures
that a chain of closure allocations will be collapsed into a single
allocation, if possible.

Figure~\ref{uncurry_fig_rewrite_iterations} demonstrates this
iterative process by showing how the \lab main/ block in our example
program changes over three iterations. The second column of each row
shows facts computed for the program text in the first column. The
value of |blocks| stays constant throughout, so we only show it
once. 

During the first iteration, |rewriter| transforms \binds v1 <- \app v0
* n/; to \binds v1 <- \mkclo[k1: n];, because \var v0/ holds the
closure \mkclo[k0:], and |blocks| tells us that \lab k0/ returns a closure
pointing to \lab k1/.

\begin{myfig}
  \begin{tabular}{clll}
    Iteration & \lab main/ & Facts & |blocks| \\
    $1$ & \begin{minipage}[t]{\widthof{\binds n <- \goto toInt(s);}}    
      \begin{AVerb}[gobble=8]
        \vbinds n<- \goto toInt(s);
        \vbinds v0<- \mkclo[k0:];
        \vbinds v1<- \app v0*n/;
        \vbinds v2<- \app v1*n/;
        \return v2/ 
      \end{AVerb} 
    \end{minipage} & \begin{minipage}[t]{\widthof{\ \phantom{\{}(\var v2/, \goto add(n,n))\}\ }}\raggedright
      (\var n/, $\top$),\break
      (\var v0/, \mkclo[k0:]),\break
      (\var v1/, $\top$),\break
      (\var v2/, $\top$)
    \end{minipage} & 
    \begin{minipage}[t]{\widthof{\phantom{\{}\lab k1/:\thinspace|Jump {-"\lab add/\ "-} [0, 1]|\}\ }}\raggedright
      \lab k0/:\thinspace|Capture {-"\lab k1/\ "-} True|\break
      \lab k1/:\thinspace|Jump {-"\lab add/\ "-} [0, 1]|
    \end{minipage}
    \\\\
    $2$ & \begin{minipage}[t]{\widthof{\binds n <- \goto toInt(s);}}
      \begin{AVerb}[gobble=8]
        \vbinds n<- \goto toInt(s);
        \vbinds v0<- \mkclo[k0:];
        \llap{\ensuremath{\rightarrow} }\vbinds v1 <- \mkclo[k1:n];
        \vbinds v2 <- \app v1*n/;
        \return v2/
      \end{AVerb} 
    \end{minipage} & \begin{minipage}[t]{\widthof{\ \phantom{\{}(\var v2/, \goto add(n,n))\}\ }}\raggedright
      (\var n/, $\top$),\break
      (\var v0/, \mkclo[k0:]),\break
      (\var v1/, \mkclo[k1:n]),\break
      (\var v2/, $\top$)
    \end{minipage} \\\\
    $3$ & \begin{minipage}[t]{\widthof{\binds v2 <- \goto add(n, n); \ensuremath{\leftarrow}\ }}
      \begin{AVerb}[gobble=8]
        \vbinds n<- \goto toInt(s);
        \vbinds v0<- \mkclo[k0:];
        \vbinds v1<- \mkclo[k1:n];
        \llap{\ensuremath{\rightarrow} }\vbinds v2<- \goto add(n, n); 
        \return v2/
      \end{AVerb}
    \end{minipage} & \begin{minipage}[t]{\widthof{\ \phantom{\{}(\var v2/, \goto add(n,n))\}\ }}\raggedright
      (\var n/, $\top$),\break
      (\var v0/, \mkclo[k0:]),\break
      (\var v1/, \mkclo[k1:n]),\break
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
associating \var v1/ with \mkclo[k1:n]. |rewriter| transforms \binds v2
 <- \app v1 * n/; to \binds v2 <- \goto add(n, n); after this iteration
because \var v1/ refers to \lab k1/ and |blocks| tells us that \lab
k1/ jumps immediately to \lab add/. No changes occur after the third
iteration because no statements remain that can be rewritten, and
\hoopl stops applying |rewriter|. Note, however, that we could apply
dead-code elimination at this point to remove \var v0/ and \var v1/, because
they are no longer referenced.

Figure~\ref{uncurry_fig_rewrite_impl} shows the functions that
implement our uncurrying optimization.\footnote{Note that these
  definition are local to |collapseRewrite|, so the |blocks| argument
  remains in scope.} Line \ref{uncurry_fig_rewrite_impl_done} of
|rewriter| rewrites \app f * x/ expressions when they occur at the end
of a block. Line~\ref{uncurry_fig_rewrite_impl_bind} rewrites when
\app f * x/ appears on the \rhs of a \mbind statement.  In the first
case, |done n l (collapse facts f x)| produces \return |e|/ when
|collapse| returns |Just e| (i.e., a rewritten expression). In the
second case, |bind v (collapse facts f x)| behaves similarly,
producing \binds v <- |e|; when |collapse| returns |Just e|. Both
|done| and |bind| are defined in a separate file, not shown; they make
it easier to construct |Done| and |Bind| values based on the |Maybe Tail|
value returned by |collapse|. In all other cases, no rewriting occurs.

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
representing the left and right-hand arguments of the expression \app
f * x/. When \var f/ is associated with a closure value,
\mkclo[k:\dots], in the |facts| map
(Line~\ref{uncurry_fig_rewrite_impl_collapse_clo}), |collapse| uses
the |blocks| argument to look up the behavior of the destination \lab
k/. Lines~\ref{uncurry_fig_rewrite_impl_collapse_jump} and
\ref{uncurry_fig_rewrite_impl_collapse_capt} test if \lab k/ returns a
closure or jumps immediately to another block. In the first case,
|collapse| returns a new closure-creating expression
(\mkclo[|dest|:\dots]). In the second case, |collapse| returns a new
goto expression (\goto |dest|(\dots)).

If the destination immediately jumps to another block
(Line~\ref{uncurry_fig_rewrite_impl_collapse_jump}), then we will
rewrite \app f * x/ to call the block directly. The list of integers
associated with |Jump| specifies the order in which arguments were
taken from the closure and passed to the block. |collapse| uses the
|fromUses| function to re-order arguments appropriately.

{\tolerance=1000 In Figure~\ref{uncurry_fig_rewrite_iterations}, we showed that the
|DestOf| value associated with \lab k1/ is |Jump {-"\lab add/\ "-} [0,
  1]|. The list |[0, 1]| indicates that \lab add/ takes arguments in
the same order as they appear in the closure. However, if \lab add/
took arguments in the opposite order, \lab k1/ and \lab add/ would look
like the following code:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \ccblock k1(a)b: \goto add(b, a)
    \block add(x, y): \ldots
  \end{AVerb}
\end{singlespace}

\noindent and the |DestOf| value associated with \lab k1/ would be |Jump
{-"\lab add/\ "-} [1, 0]|.}

If the destination returns a closure
(Line~\ref{uncurry_fig_rewrite_impl_collapse_capt}), then we rewrite
\app f * x/ to allocate the closure directly. The Boolean value
|usesArg| indicates if the closure returned should capture the
argument |x| or not.

\subsection{Optimization Pass}

\intent{Describe how |collapse| creates initial values for uncurrying,
  applies the optimization, and cleans up.}
Figure~\ref{uncurry_fig_collapse} presents |collapse|, which applies
the uncurrying dataflow analysis and rewrite to the \mil program
represented by the argument
|program|. Line~\ref{uncurry_fig_collapse_analyze} analyzes and
transforms |program| by passing appropriate arguments to \hoopl's
|analyzeAndRewriteFwd| function. On Line~\ref{uncurry_fig_collapse_run}, we evaluate \hoopl's
monadic program using |runSimple|, which provides a monad with
infinite optimization fuel.

\begin{myfig}[p]
  \begin{minipage}{\hsize}\begin{withHsLabeled}{uncurry_fig_collapse}\disableoverfull
%let includeCollapse = True
%include Uncurry.lhs
%let includeCollapse = False
  \end{withHsLabeled}\end{minipage}
  \caption{The function that puts together all definitions for our
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
\item[|JustC labels|] --- We must give \hoopl all entry points for the
  program analyzed. These labels tell \hoopl where to start traversing
  the program graph. \Mil does not define any particular block as an
  entry point, so all blocks in |program| will be analyzed. This
  argument's type is |MaybeC C [Label]|, which requires us to use the
  |JustC| constructor.
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

\section{Example: Uncurrying Across Blocks}
\label{uncurry_sec_example}

The example shown in the previous section demonstrated that we can
eliminate unnecessary \enter expressions within a block. As we will
demonstrate with the next two examples, the dataflow algorithm enables
us to do the same across multiple blocks, even in the presence of loops.

\subsection*{Uncurrying |map|}
Figure~\ref{uncurry_global_a} shows a simple \lamC program that uses
|map| to turn a list into a list of lists.
Part~\subref{uncurry_global_b} shows the \mil translation of
Part~\subref{uncurry_global_a}. The listing is rather verbose as it
represents the output of our \lamC to \mil compiler.

\begin{myfig}
  \begin{tabular}{c}
    \begin{minipage}{\hsize}\begin{centering}
> main ns = map toList ns
> map f xs = case xs of
>   Cons x xs' -> Cons (f x) (map f xs')
>   Nil -> Nil 
> toList n = Cons n Nil
    \end{centering}\end{minipage} \\
    \scap{uncurry_global_a} \\
    \begin{tabular}{lr}\begin{minipage}[t]{.45\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block main(ns): 
        \vbinds v227<-\mkclo[k203:];
        \vbinds v228<-\mkclo[k219:];
        \vbinds v229<-\app v227*v228/;
        \app v229 * ns/ 
      \ccblock k219()x: \goto toList(x)
      \block toList(x):\label{uncurry_global_toList_body}
        \vbinds v221<-\mkclo[Consclo2:];
        \vbinds v222<-\app v221*x/;
        \vbinds v223<-Nil;
        \app v222 * v223/ \label{uncurry_global_toList_body_end}
      \ccblock Consclo2()a2: \mkclo[Consclo1:a2]
      \ccblock Consclo1(a2)a1: Cons a2 a1
    \end{AVerb}
  \end{minipage} &
  \begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left,firstnumber=last]
      \ccblock k203()f: \mkclo[k204:f]
      \ccblock k204(f)xs: \goto map(xs, f)
      \block map(xs, f): \label{uncurry_global_map_body}
        \case xs;
          \valt Nil()->\goto nil();
          \valt Cons(x xs)->\goto cons(f, x, xs);
      \block nil(): Nil \label{uncurry_global_map_nil}
      \block cons(f, x, xs): \label{uncurry_global_map_cons}
        v209 <- \mkclo[Consclo2:]
        \vbinds v210<-\app f*x/; \label{uncurry_global_map_cons_fx}
        \vbinds v211<-\app v209*v210/;
        \vbinds v212<-\mkclo[k203:]; \label{uncurry_global_map_cons_map_start}
        \vbinds v213<-\app v212*f/;
        \vbinds v214<-\app v213*xs/; \label{uncurry_global_map_cons_map_end}
        \app v211 * v214/ \label{uncurry_global_map_cons_end}
    \end{AVerb}
  \end{minipage}\end{tabular} \\
  \scap{uncurry_global_b} \\
  \end{tabular}
  \caption{A \lamC program that turns a list of elements into a list of lists and its unoptimized translation to \mil.}
  \label{uncurry_global}
\end{myfig}

In this program, |main| applies |toList| to each element in |ns| using
the |map| function. Per the definition of |map|, the |Cons| arm
applies |f| to an element |x|, and then recursively calls |map| to
apply |f| to the rest of the
list. Lines~\ref{uncurry_global_map_cons}--\ref{uncurry_global_map_cons_end}
in Part~\subref{uncurry_global_b} implement the |Cons| arm of
|map|. On Line~\ref{uncurry_global_map_cons_fx}, \var f/ is applied to
the element \var
x/. Lines~\ref{uncurry_global_map_cons_map_start}--\ref{uncurry_global_map_cons_map_end}
recursively call |map| with the remainder of the
list. Line~\ref{uncurry_global_map_cons_end} returns the updated list. 

In the body of \lab cons/, there are two opportunities to
eliminate \enter expressions. \var f/ always represents the |toList|
function, which is implemented by \lab toList/ on
Lines~\ref{uncurry_global_toList_body}--\ref{uncurry_global_toList_body_end}. We
should be able to replace \app f * x/ on
Line~\ref{uncurry_global_map_cons_fx} with \goto toList(f,
x). Similarly, the recursive call to |map| can be replaced by a direct
call to \lab map/, which implements the body of |map|. 

Though our analysis covers the entire program, we first concentrate on
the \lab main/ block. Figure~\ref{uncurry_global_main} shows how we
analyze and rewrite \lab main/. The figure shows consecutive
iterations of \hoopl's interleaved analysis and rewrite
process. Rewrites occur between the parts of the figure; we highlight
rewritten lines with a $\rightarrow$ symbol.

\begin{myfig}
  \begin{tabular*}{\textwidth}{l}\begin{minipage}[t]{\textwidth}
    \begin{NVerb}[gobble=6]
      \block main(ns):  \anchorF(nsa)
        \vbinds v227<-\mkclo[k203:];\anchorF(v227a) \label{main_v227a}
        \vbinds v228<-\mkclo[k219:];\anchorF(v228a)
        \vbinds v229<-\app v227*v228/;\anchorF(v229a) \label{main_v229a}
        \app v229 * ns/ 
    \end{NVerb}
  \end{minipage} \\\\
    \begin{tikzpicture}[overlay,remember picture]
      \node[fact, right=0.25in of nsa, anchor=west] (fvnsa) {$\{\var ns/\,:\,\top\}$};
      \node[fact, right=0.25in of v227a, anchor=west] (fv227a) {$\{\var v227/\,:\,\mkclo[k203:]\unskip\}$};
      \node[fact, right=0.25in of v228a, anchor=west] (fv228a) {$\{\var v228/\,:\,\mkclo[k219:]\unskip\}$};
      \node[fact, right=0.25in of v229a, anchor=west] (fv229a) {$\{\var v229/\,:\,\top\}$};
      \draw [->] (fvnsa) to (nsa);
      \draw [->] (fv227a) to (v227a);
      \draw [->] (fv228a) to (v228a);
      \draw [->] (fv229a) to (v229a);
    \end{tikzpicture}%%
  \hfil\scap{uncurry_global_main_a} \\
  \begin{minipage}[t]{\textwidth}
    \begin{NVerb}[gobble=6]
      \block main(ns): 
        \vbinds v227<-\mkclo[k203:];
        \vbinds v228<-\mkclo[k219:];
        \llap{\ensuremath{\rightarrow} }\vbinds v229<-\mkclo[k204:v228];\anchorF(v229b) \label{main_v229b}
        \app v229 * ns/\label{main_app_b}
    \end{NVerb}
  \end{minipage} \\\\
  \begin{tikzpicture}[overlay,remember picture]
    \node[fact, right=0.25in of v229b, anchor=west] (fv229b) {$\{\var v229/\,:\,\{\mkclo[k204:v228]\unskip\}$};
    \draw [->] (fv229b) to (v229b);
  \end{tikzpicture}%%
  \hfil\scap{uncurry_global_main_b} \\
  \begin{minipage}[t]{\textwidth}
    \begin{NVerb}[gobble=6]
      \block main(ns): 
        \xout{\vbinds v227<-\mkclo[k203:];}
        \vbinds v228<-\mkclo[k219:];
        \xout{\vbinds v229<-\mkclo[k204:v228];}
        \llap{\ensuremath{\rightarrow} }\goto map(ns, v228) \anchorF(gotoCaseEval216a)
    \end{NVerb}
  \end{minipage} \\
  \begin{tikzpicture}[overlay,remember picture]
    \node[fact, right=0.25in of gotoCaseEval216a, anchor=west] (fvGotoCaseEval216a) {$\{\var ns/\,:\,\top\}, \{\var v228/\,:\,\mkclo[k219:]\unskip\}$};
    \draw [->] (fvGotoCaseEval216a) to (gotoCaseEval216a);
  \end{tikzpicture}%%
  \hfil\scap{uncurry_global_main_c}
  \end{tabular*}
  \caption{Development of facts and rewrites applied to the \lab main/ block
    of our example program.}
  \label{uncurry_global_main}
\end{myfig}

Part~\subref{uncurry_global_main_a} shows the initial facts gathered
about each binding in \lab main/. On Line~\ref{main_v227a}, we
associate \var v227/ with the closure \mkclo[k203:]. We can use this
fact to rewrite the \enter expression on Line~\ref{main_v229a}.  In
Part~\subref{uncurry_global_main_b}, the rewritten line allows us to
create a new fact, associating \var v229/ with \mkclo[k204:v228]. The
\cc block \lab k204/ immediately jumps to \lab
map/. Therefore, on Line~\ref{main_app_b}, we can rewrite the
expression \app v229 * ns/ to \goto caseEval(ns,
v228). Part~\subref{uncurry_global_main_c} shows this rewrite and also
crosses out lines with now-dead bindings.

After the rewrite in Figure~\ref{uncurry_global_main_c}, the \cfg for
the program changes. \lab main/ did not originally end in a \milres
case/ statement or ``goto'' expression, so the block did not have any
successors; after our rewrite, \lab map/ becomes the successor
to \lab main/. Figure~\ref{uncurry_global_blocks_a} shows the \cfg for
our program before our rewrite; Figure~\ref{uncurry_global_blocks_b}
shows the \cfg afterwards. We also show the facts that flow between
each block (using the parameters for each block to name the facts).

\begin{myfig}
\input{uncurry_global_blocks}
\caption{Facts that flow between blocks in our example
  program. Part~\subref{uncurry_global_blocks_a} shows the \cfg before
  we rewrite \lab main/; Part~\subref{uncurry_global_blocks_b}
  shows the \cfg afterwards. The facts from \lab main/ only flow to
  the rest of the \cfg after rewriting.}
\label{uncurry_global_blocks}
\end{myfig}

As Figure~\ref{uncurry_global_blocks_b} shows, when \lab map/
becomes the successor of \lab main/, the fact $\{\var
f/\,:\,\mkclo[k219:]\unskip\}$ becomes available to \lab
cons/. Figure~\ref{uncurry_global_cons} shows how we iteratively
analyze and rewrite \lab cons/ using our new
fact. Part~\subref{uncurry_global_cons_a} shows the initial facts for
each binding. In Part~\subref{uncurry_global_cons_b}, we replace the
expression \app f * x/ on Line~\ref{ugb_v210b} with \goto toList(x),
because we know the \cc block \lab k219/ immediately jumps to \lab
toList/. On Line~\ref{ugb_v213b}, we rewrite \app v212 * f/ to
\mkclo[k204:f], due to the fact $\{\var
v212/\,:\,\mkclo[k203:]\unskip\}$ and that \lab k203/ returns
\mkclo[k204:f]. Originally, this line gathered the first argument for
|map|; now, we create the closure directly. This also generates a new
fact, $\{\var v213/\,:\,\mkclo[k204:f]\unskip\}$. We know that \lab
k204/ jumps to \lab map/ (i.e., the body of |map|). In
Part~\subref{uncurry_global_cons_c}, we use our knowledge of \var
v213/ to rewrite Line~\ref{ugb_v214c} from \app v213 * xs/ to \goto
map(xs, f). We also cross out dead bindings that could be
eliminated, after our rewrites. 

\begin{myfig}[tbp]
\input{uncurry_global_cons}
\caption{Development of facts and rewrites within \lab cons/, after 
  facts begin flowing from \lab main/.}
\label{uncurry_global_cons}
\end{myfig}

Figure~\ref{uncurry_global_opt} summarizes the result of applying our
uncurrying optimization (and dead-code elimination) to the program in
Figure~\ref{uncurry_global}. On Line~\ref{uncurry_global_opt_toList},
we replaced the expression \app f * x/ with \goto toList(x); our program
now directly calls |toList|, rather than repeatedly entering the
closure represented by \var f/. In Figure~\ref{uncurry_global},
Lines~\ref{uncurry_global_map_cons_map_start}--\ref{uncurry_global_map_cons_map_end}
implemented the recursive call to |map|. In Figure~\ref{uncurry_global_opt},
Line~\ref{uncurry_global_opt_map} replaces those three lines
with \goto map(xs, f), a direct recursive call. The first
change does not save a closure allocation (because \var f/ is still
passed in),\footnote{We could eliminate \var f/ through an analysis
  that finds unused parameters.} but the second change saves two
closure allocations and two \enter expressions.

\begin{myfig}[tbp]
  \begin{tabular}{lr}
  \begin{minipage}[t]{.45\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block main(ns):
        \vbinds v228<-\mkclo[k219:];
        \goto map(ns, v228)
      \ccblock k219()x: toList(x)
      \block toList(x):
        \vbinds v222<-\mkclo[Consclo1:x];
        \vbinds v223<-Nil;
        \app v222 * v223/
      \ccblock Consclo1(a2)a1: Cons a2 a1
    \end{AVerb}
  \end{minipage} &
  \begin{minipage}[t]{.45\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \ccblock k203()f: \mkclo[k204:f]
      \ccblock k204(f)xs: \goto map(xs, f)
      \block map(xs, f):
        \case xs;
          \valt Nil()->\goto nil();
          \valt Cons(x xs)->\goto cons(f, x, xs);
      \block nil(): Nil
      \block cons(f, x, xs):
        \vbinds v210<-\goto toList(x); \label{uncurry_global_opt_toList}
        \vbinds v211<-\mkclo[Consclo1:v210];
        \vbinds v214<-\goto map(xs, f); \label{uncurry_global_opt_map}
        \app v211 * v214/
    \end{AVerb}
  \end{minipage}
  \end{tabular}
  \caption{Our \mil program from Figure~\ref{uncurry_global} after
    applying our uncurrying optimization. We also removed unused
    blocks and unnecessary bindings within blocks.}
  \label{uncurry_global_opt}
\end{myfig}

\subsection*{Uncurrying Across Loops}
Our next example demonstrates uncurrying in the presence of
loops. Figure~\ref{uncurry_loop} gives our example \mil program and
its \cfg; the program itself does not do anything very interesting,
but we are concerned with its structure rather than its behavior. Note
that we only show the normal blocks (\lab b1/, \lab b2/, and \lab b3/)
in the \cfg, as the control-flow between each pair of \cc blocks is
not very relevant.

We annotated the \cfg in Figure~\ref{uncurry_loop_b} with the initial
facts between each block. Recall that in a forwards dataflow analysis,
the \inE facts for a block are computed using the meet of \out facts
from predecessor blocks. As \lab b2/ has two predecessors, we
explicitly show the \out facts for \lab b1/ and \lab b3/. Notice that
$\out(\lab b3)/$ does not contain a fact for \var f/; because no
binding to \var f/ occurs in \lab b3/, no fact will (yet) appear in
$\out(\lab b3)/$.  In turn, this means $\inE(\lab b2/)$ contains the
fact $\{\var f/\,:\,\mkclo[k1:]\unskip\}$ from $\out(\lab b1)/$. In
\lab b3/, the statement \binds w <- \mkclo[k4:v]; ultimately creates
the fact $\{\var g/\,:\,\mkclo[k3:]\unskip\}$ in $\out(\lab
b3/)$. However, $\out(\lab b1/)$ contains $\{\var
g/\,:\,\mkclo[k3:]\unskip\}$. Because these values differ, $\inE(\lab
b2/)$ contains the fact $\{\var g/\,:\,\top\}$.

\begin{myfig}
  \input{uncurry_loop}
  \caption{A \mil program with looping control-flow.}
  \label{uncurry_loop}
\end{myfig}

The initial facts in Figure~\ref{uncurry_loop} tell us that \var f/
refers to the \cc block \lab k1/, which lets us replace the expression
\app f * g/ on Line~\ref{uncurry_loop_fg} with
\mkclo[k2:g]. Similarly, the same fact propagates to \lab b3/,
allowing us to rewrite the expression \app f * t/ on
Line~\ref{uncurry_loop_ft} to \mkclo[k2:t].

\begin{myfig}
  \input{uncurry_loop_r1}
  \caption{Our rewritten \mil program, showing that we correctly uncurried
  \app f * g/ in \lab b2/; \app g * t/ remains unchanged.}
  \label{uncurry_loop_r1}
\end{myfig}

Figure~\ref{uncurry_loop_r1} shows the rewritten program and updated
facts. After these rewrites, the fact sets reach a fixed point and the
analysis stops. Applications of \var f/ are correctly replaced with
direct closure allocations, but applications of \var g/ remain as it
does not always hold the same closure.

\subsection{Soundness}
\label{uncurry_soundness}

Our implementation of uncurrying can produce incorrect results
under two circumstances. In the first case, we can introduce
free variables into a block. In the second case, our analysis
does not see facts that should be propagated to a block, leading to
unsound rewrites. We describe both cases, and possible solutions, below.

The first case occurs when a function application is replaced with a
closure that introduces variables not declared in the containing
block. When |collapseTransfer| sees a binding to a closure value, it
records not only the label that the closure refers to, but also all of
the variables captured in the closure. These facts are propagated to
successor blocks. If those blocks are subsequently rewritten to
allocate the closure directly, then the variables in the closure may
be ``unpacked'' into the block, introducing free variables that are
not properly bound.

For example, consider the \mil program in Figure~\ref{unc_fv}. In
Part~\subref{unc_fv_a}, the statement \binds v<-\mkclo[k1:x]; in \lab
b1/ binds \var v/ to \mkclo[k1:x]. The closure is then passed to \lab
b2/,  which applies the closure to \var y/ and returns the
result.

\begin{myfig}
  \begin{tabular}{cc}
  \begin{minipage}{\widthof{\ \ \ccblock k1(x)y: \goto p1(x, y)}}
    \begin{AVerb}[gobble=6]
      \block b1(x, y):
        \vbinds v<-\mkclo[k1:x];
        \goto b2(v, y)

      \block b2(v, y): 
        \vbinds t<-\app v*y/;
        \return t/
      \ccblock k1(x)y: \goto p1(x, y)
      \block p1(x,y): \dots
    \end{AVerb}
  \end{minipage} &
  \begin{minipage}{\widthof{\ \ \ccblock k1(x)y: \goto p1(x, y)}}
    \begin{AVerb}[gobble=6]
      \block b1(x, y):
        \vbinds v<-\mkclo[k1:x];
        \goto b2(v, y)

      \block b2(v, y): 
        \vbinds t<-\goto p1(x, y);
        \return t/
      \ccblock k1(x)y: \goto p1(x, y)
      \block p1(x,y): \dots
    \end{AVerb} 
  \end{minipage}\\\\
  \scap{unc_fv_a} & \scap{unc_fv_b}
  \end{tabular}
  \caption{A \mil program that demonstrates how free variables can
    be accidentally introduced by uncurrying. Part~\ref{unc_fv_a} shows
  the original program. In Part~\ref{unc_fv_b}, rewriting \lab b2/ 
  introduced the free variable \var x/.}
  \label{unc_fv}
\end{myfig}

Our analysis create the fact $\{\var v/, \mkclo[k1:x]\}$ when
analyzing \lab b1/, which then propagates to \lab b2/. In \lab b2/, we
would rewrite the expression \app v * y/ to \goto p1(x, y), as \lab
k1/ immediately jumps to \lab p1/, producing the program shown in
Part~\ref{unc_fv_b}. But this introduces a free variable, \var x/, in
\lab b2/.

This problem might be solved with another dataflow analysis. After
uncurrying, we would determine the free variables in each block (a
backwards dataflow analysis). Our uncurrying analysis could keep track
of where each variable in a given closure was declared.  We could use
that information to propagate free variables from the block in which
they are first bound to the blocks where they are used.

The second case occurs when a block is called on the \rhs of a bind
statement, such as \binds v <- \goto b(\dots);. Our analysis will not
propagate any facts to \lab b/ in such situations. If the values
passed to the block \lab b/ on the \rhs of a \mbind differ from those
passed at the end of a block, then our analysis may rewrite using
partial facts.

\begin{myfig}
  \begin{tabular}{cc}
  \begin{minipage}{\widthof{\qquad\ccblock k2()x: Right x}}
  \begin{AVerb}[gobble=6,numbers=left]
      \block b1 (x):
        \vbinds v<- \mkclo[k1:];
        \vbinds w<- \mkclo[k2:];
        \vbinds z<- \goto b2(w, y);\label{unc_goto_z}
        \goto b2(v, z) \label{unc_goto_callb2}
  
      \block b2 (v, y):
        \vbinds t<- \app v*y/;
        \return t/
      \ccblock k1()x: Left x
      \ccblock k2()x: Right x
  \end{AVerb}
  \end{minipage} &
  \begin{minipage}{\widthof{\qquad\ccblock k2()x: Right x}}
  \begin{AVerb}[gobble=6,numbers=left]
      \block b1 (x):
        \vbinds v<- \mkclo[k1:];
        \vbinds w<- \mkclo[k2:];
        \vbinds z<- \goto b2(w, y);
        \goto b2(v, z) 
  
      \block b2 (v, y):
        \vbinds t<- \mkclo[k1:];
        \return t/
      \ccblock k1()x: Left x
      \ccblock k2()x: Right x
  \end{AVerb}
  \end{minipage} \\\\
  \scap{unc_goto_ a} & \scap{unc_goto_b}
  \end{tabular}
  \caption{A \mil program demonstrating problems with ``call'' expressions on
  the \rhs of a bind. }
  \label{unc_goto}
\end{myfig}

Figure~\ref{unc_goto} demonstrates this issue. Block \lab b1/
allocates two closures, \var v/ to \mkclo[k1:] and \var w/ to
\mkclo[k2:]. On Line~\ref{unc_goto_z}, the program calls \lab b2/ with
\var w/; Line~\ref{unc_goto_callb2} calls \lab b2/ with \var v/. Our
analysis would only consider the second call to \lab b2/ and would
deduce that \var v/ is always \mkclo[k1:] in \lab
b2/. Figure~\ref{unc_goto_b} shows the rewritten program. In \lab b2/,
\binds t<- \app v*y/; has been incorrectly rewritten to \binds t<- \mkclo[k1:];,
which is incorrect.

A simple solution to this problem would first scan the entire program,
finding all blocks called on the \rhs of a bind; then those blocks
would be eliminated from further analysis. Our intuition is that
while this solution is not ideal, many programs can still be uncurried
even with this restriction.

\section{Related Work}
\label{uncurry_sec_related}
Appel \citeyearpar[Section~6.2]{Appel1992} describes uncurrying in the
context of a compiler that uses continuation-passing style, though
\cps conversion is not essential to the transformation. While we
described uncurrying in terms of one-argument functions, Appel allows
tuples of arguments. His approach looks for functions whose bodies only apply
a locally defined, non-recursive function. Using our \lamC notation with
tuples, this pattern looks like:

> f (x, c) = 
>   let g (y, k) = E
>   in c g

\noindent where |E| represents the non-recursive body of |g|. 

To uncurry |f|, Appel creates a new function, |f'|, that
takes all arguments to |f| and |g| at once. He then rewrites |f| to use |f'|:

> f' (x, c, g, y, k) = E 
> f (x, c) = 
>   let g (y, k) = f'(x, c, g, y, k)
>   in c g

\noindent This transformation preserves the original |f|, as not all
call sites of |f| may be known. Known call sites, however, can use
the more efficient version, |f'|. Appel describes what makes |f'|
efficient and how other optimizations can remove the unused
arguments in |f'| and |f|. 

Like our version of uncurrying, Appel relies on other optimizations to
clean up. Unlike our version, Appel's looks for a specific syntactic
form to transform. Our use of dataflow analysis allows us to rewrite
any function application that we can prove always uses the same
closure. Appel's version appears to only apply to a very specific form
of curried definitions, most of which are produced by the translation to
\cps.

Tarditi \citeyearpar{Tarditi96} describes an uncurrying optimization
that extends Appel's work. In fact, Tarditi points out that Appel's
description is only guaranteed to work for functions of two arguments;
for more arguments, Appel's transformation must be applied in a
specific order (which Appel did not describe). 

Tarditi's approach uses four passes to uncurry functions of the form
\lcapp (\lcabs x. \lcabs. y.\ \dots) * a * b/ into \lcapp (\lcabs (x,
y). \dots) * (a, b)/, where tuples represent a multi-argument
function.
The first pass of Tarditi's algorithm scans all definitions in the
program to find non-recursive, curried definitions, and records their
arity (i.e., the number of nested $\lambda$s). The second pass looks
for applications of curried functions to arguments. He again scans the
program, searching for specific declarations that partially apply a
curried function. He is also able to recognize subsequent applications
of previous partial applications, extending the number of
arguments associated with a given sequence of applications.  The third
pass of his algorithm creates new, uncurried definitions of the
curried functions found in the first pass. The fourth and final pass
of the algorithm converts those applications found in the second pass
that are fully applied to use the new, uncurried versions of the
curried function they originally referred to.

Tarditi's algorithm is not limited to finding curried functions of a
certain syntactic form, and it extends correctly to functions of
multiple arguments. His algorithm, however, only replaces fully-applied
functions. Our analysis can replace any candidate function
application, even if it does not result in a fully applied
function. 

Tolmach and Oliva \citeyearpar{Tolmach1998} do not specifically
describe an uncurrying optimization; rather, they describe how
``closure conversion,'' plus two other general optimizations, give
them uncurrying for free in their compiler for Standard
ML. Critically, their compiler uses closure-conversion to remove all
higher-order functions from the program and replace them with
functions that return a data structure representing the original
closure. Applications of curried functions are replaced with calls to
a dispatching function that uses case discrimination to distinguish
closures of the same arity, calling the uncurried version of each
curried function.

Tolmach and Oliva's compiler uses inlining and ``case
splitting'' to ensure the program does not trade the cost of a partial application
for the cost of a data allocation and a call to the dispatching function. Any
application of the curried function will be inlined into the call
site, as the body of the curried function just allocates a data
structure. The call to the dispatch function will now use the data
structure inlined from the curried function. The dispatch function
only contains a case statement that discriminates based on the data
structure representing each curried function. ``Case splitting''
replaces the entire call site with the relevant arm from the dispatch
function, thus turning an allocation, case discrimination and function
call into just a function call.

Tolmach and Oliva's approach does not depend on recognizing syntactic
patterns at all. It should recognize any known call site of a
partially applied function, and they claim it works for functions of
multiple arguments as well.  Our approach is similar, in that we look
for bindings known to refer to closure values. We even use a simple
form of inlining, meaning we inspect the \term tail/ found in the \cc
block referred to by a given closure and ``inline'' the tail when it
is a direct jump or closure allocation. Our use of dataflow analysis,
however, distinguishes our work, in that we do not depend on function
applications to take on a particular form. Once we determine that the
left-hand side of a given \enter expression always refers to the same
closure, we can transform the expression by a simple rewrite using the
body of the \cc block.

\section{Conclusion}
\label{uncurry_sec_refl}
In this chapter, we described an uncurrying optimization for \mil
programs in terms of the dataflow algorithm. We gave dataflow
equations detailing the optimization, setting our algorithm on a solid
theoretical foundation. We implemented our algorithm using the \hoopl
library, and gave a complete and detailed presentation of that
work. By example, we demonstrated the utility of our optimization. We
discussed challenges in our current implementation, and offered
suggestions for improving the algorithm in the future. Finally, we
compared our implementation to several other implementations of the
uncurrying optimization in the literature.


%% 1
%% (fset 'mil_block
%%   (lambda (&optional arg) "Keyboard macro." (interactive "p") (kmacro-exec-ring-item (quote ([92 98 108 111 99 107 32 C-right 4 1 down C-right C-left] 0 "%d")) arg)))

%% 2
%% (fset 'mil_ccblock
%%    (lambda (&optional arg) "Keyboard macro." (interactive "p") (kmacro-exec-ring-item (quote ([67108896 left right 92 98 backspace 99 99 98 108 111 99 107 32 C-right 4 19 41 right left 4 5 right C-right C-left] 0 "%d")) arg)))

%% 3
%% (fset 'mil_vbinds
%%    (lambda (&optional arg) "Keyboard macro." (interactive "p") (kmacro-exec-ring-item (quote ([92 118 98 105 110 100 115 32 C-right C-left 19 60 left backspace right right 4 5 59 right C-right C-left] 0 "%d")) arg)))

%% 4
%% (fset 'mil_mkclo
%%    (lambda (&optional arg) "Keyboard macro." (interactive "p") (kmacro-exec-ring-item (quote ([92 109 107 99 108 111 91 C-right 58 4 4 19 41 left right backspace 93 right C-right C-left] 0 "%d")) arg)))

%% 5
%% (fset 'mil_app
%%    (lambda (&optional arg) "Keyboard macro." (interactive "p") (kmacro-exec-ring-item (quote ([92 97 112 112 32 19 42 left backspace right 4 C-right 47 right C-right] 0 "%d")) arg)))

%% 6
%% (fset 'mil_goto
%%    (lambda (&optional arg) "Keyboard macro." (interactive "p") (kmacro-exec-ring-item (quote ([92 103 111 116 111 32 5 C-right C-left 1] 0 "%d")) arg)))

%% 7
%% (fset 'mil_valts
%%    (lambda (&optional arg) "Keyboard macro." (interactive "p") (kmacro-exec-ring-item (quote ([92 118 97 108 116 32 C-right 4 40 19 45 left left 41 4 19 62 left right 4 5 59 right C-right C-left] 0 "%d")) arg)))

\end{document}
