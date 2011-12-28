\documentclass[12pt]{report}
\usepackage{standalone}
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\input{tikz.preamble}
\input{preamble}
\begin{document}
\input{document.preamble}

\chapter{A Monadic Intermediate Language}
\label{ref_chapter_mil}

Most compilers do not generate executable machine code directly from a
program source file. Rather, the compiler typically implements of
pipeline of \emph{intermediate languages}. The compiler analyzes and
optionally transforms (e.g., for optimization) the program during each
stage of the pipeline. Typically, each intermediate language exposes
more details about the implementation of the program than the one
before.

A number of intermediate languages have been described for both
imperative and functional language compilers. Register transfer
languages (RTLs) makes data movement between memory and processor
registers explicit. RTLs aids in optimizing the use of registers,
typically a scarce resource on most processors. Single-static
assignment form (described in detail by \citet[pg.~252]{Muchnick1998})
appears similar to an RTL, but never re-uses a register assignment
(thus, ``single-static assignment''). It is particularly useful for
discovering constant values and for untangling register usage in the
presence of complex control-flow. Administrative-Normal Form, first
described by \citet{Flanagan1993}, is an intermediate form for
functional languages which makes all intermediate values explicit. It
is useful for showing the exact order of evaluation for expressions.

Our intermediate language, MIL (``monadic intermediate language''),
specifically supports functional language features, but also follows
the form of three-address code, an intermediate language more
associated with imperative languages. MIL directly supports function
application and abstraction. All intermediate values are named. MIL 
specifies evaluation order and separates stateful computation using a
monadic programming style. MIL's syntax enforces basic-block structure
on programs, making them ideal for dataflow analysis.

\intent{Signposts.}
% We first describe our source language, \lamC, in
% Section~\ref{mil_src}.  MIL syntax and
% examples follow in Section~\ref{mil_sec3}.  We
% then describe ``three-address code,'' the intermediate form from which
% MIL partly derives, in Section~\ref{mil_sec2}. Section~\ref{mil_sec4}
% shows our compiler for translating \lamC to MIL. We sketch how MIL
% programs can be evaluated in Section~\ref{mil_sec5}, using the same
% structural operational semantics (SOS) style as in
% Chapter~\ref{ref_chapter_languages}. Section \ref{mil_sec7} shows how
% Hoopl influenced the implementation the MIL language from Chapter
% \ref{ref_chapter_mil} and discusses the design choices we made.

\section{Source Language: \lamC}
\label{mil_src}

\intent{Introduce \lamC; where it came from, references, etc.}  We
call our source language ``$\lambda$-case'' and write its name as
\lamC. \lamC derives from the \lamA, with syntactic and semantic
elements borrowed from Haskell. In particular, \lamC uses Haskell's
\hsdo notation (and notion) for monadic programming. Jones and
colleagues developed \lamC as an intermediate representation for the
Habit programming language \citep{Habit2010}. The Habit ``Compilation
Strategy'' report \citep{HabitComp2010} gives full details on
\lamC.\footnote{For simplicity's sake, we ignore two features of \lamC
  in this work: patterns and guards. Details on those elements can be
  found in the aforementioned report.} The report describes several
different intermediate languages; \lamC corresponds to ``Normalized
MPEG.''

Figure~\ref{mil_fig_lam_syntax} gives the full syntax of \lamC. In the
figure, \term x/, \term x_1/, etc.\ represent simple variables, not
terms; however, \term t/, \term t_1/, etc.\ do represent arbitrary
terms. All \term def/ terms are global to the program in which
they are defined. Definitions can be recursive, but only functions can
be mutually-recursive. Simple variables are supported in definitions
and case alternatives --- pattern-matching outside the constructor
name in an alternative is not supported. The language is untyped and
does not support data declarations.

\begin{myfig}
  \begin{tabular}{r@@{}lr}
    \termrule def:|f x_1 {-"\dots\ "-} x_n = {-"\term term/"-}|, n \geq 0:Definition/ \\\\
    \termrule term:x, x_1, x_2, \ldots:Variables/ \\
    \termcase \lcabs x. \term t_1/:Abstraction/ \\
    \termcase \lcapp t_1 * t_2/:Application/ \\
    \termcase {\begin{minipage}[t]{\widthof{|case t of x|\quad}}
      |case t of|\endgraf%%
      \quad \term alt_1/\endgraf%%
      \quad $\ldots$\endgraf%%
      \quad \term alt_n/%%
      \end{minipage}}:Case Discimination/ \\
    \termcase |x <- t_1; t_2|:Monadic Bind/ \\
    \termcase {\begin{minipage}[t]{\widthof{$\mathbf{let}\ \term def_1/\quad$}}
        $\mathbf{let}\ \term def_1/$\endgraf%%
        $\phantom{\mathbf{let}}\ \ldots$\endgraf%%
        $\phantom{\mathbf{let}}\ \term def_n/$\endgraf
        $\mathbf{in}\ t$
    \end{minipage}}:Let/ \\
    \termcase \lcprim p*:Primitive/ \\
    \termcase \lccons C(x_1 \ldots x_n), n \geq 0:Allocate Data/ \\\\
    \termrule alt:{|C x_1 {-"\ldots\ "-} x_n -> t|}, n \geq 0:Alternative/
  \end{tabular}
  \caption{The syntax of \lamC. Variables are represented using \term
    x/, \term x_1/, etc. Terms are represented by \term t/, \term
    t_1/, etc. $C$ represents the name of a given constructor.}
  \label{mil_fig_lam_syntax}
\end{myfig}

While most elements should be recognizable
from Haskell or the \lamA, we will explain the the \emph{monadic
  bind}, \emph{let} and \emph{primitive} terms further.

\intent{Describe bind.}  The monadic binding term, |x <- t_1; t_2|,
states that the result of the monadic computation, |t_1|, will be
bound to |x| and that |t_2| will then be evaluated with |x| in
scope. |x| can only be a variable; \lamC does not support
pattern-matching on the \lhs of a bind. The monadic context in which
\term t_1/ is evaluated depends on the type of the expression (as
expressed in Habit).

\intent{Describe let.}  The term |let {-"\term def_1/, $\ldots$, \term
  def_n/"-} in t| brings the definitions \term def_1/, $\ldots$, \term
def_n/ into the scope of \term t/. The definitions are local and will
not be in scope outside of \term t/. Like top-level definitions,
\hslet definitions can be values or functions,\footnote{Technically,
  values are functions with zero arguments.} and they can be
recursive, but only functions can be mutually-recursive.

\intent{Describe primitives.}  The primitive expression \lcprim p*
treats \term p/ as it if were a definition, except the body of the 
primitive is not defined in \lamC. 

\section{MIL's Purpose}
\label{mil_sec3}

\intent{Remark on intermediate languages and MIL's focus.} An
intermediate language always seeks to highlight some specific
implementation detail while hiding others in order to support certain
analysis and transformation goals. Exposing intermediate values gives
us the chance to analyze and eliminate them. Hiding implementation
details makes the job of writing those analyses and transformations
simpler.

\intent{Relate MIL to three-address code.} MIL's syntax and design
borrow heavily from three-address code, an intermediate form normally
associated with imperative languages. Three-address code represents
programs such that all operations specify two operands and a
destination. Three-address code also hides details of memory
management by assuming that infinitely many storage locations can be
named and updated. For example, the expression:

\begin{singlespace}\correctspaceskip
  \begin{equation}
    \frac{(b * c + d)}{2},
  \end{equation}
\end{singlespace}

\noindent would be expressed in three-address code as:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \vbinds t_1 <- mul b c;
    \vbinds t_2 <- add t_1 d;
    \vbinds t_3 <- div t_2 2;
  \end{AVerb}
\end{singlespace}

\noindent where \var t_1/, \var t_2/ and \var t_3/ are new temporary storage
locations. 

\intent{Highlight focus of MIL (closure allocation).} Three-address
code emphasizes assignments and low-level operations, features
important to imperative languages. MIL emphasizes allocation and
side-effecting computations, features important to functional
languages.\footnote{Most importantly, features important to a pure
  functional language like Habit.} Though the operations supported by
MIL differ from traditional three-address code, the intention remains
the same: hide some details while exposing those we care about.

For example, the previously given expression can be written in Habit
as:

\begin{singlespace}
> div (plus (mul b c) d) 2
\end{singlespace}

\noindent and implemented in MIL as:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4, numbers=left]
    \vbinds t_1 <- \mkclo[mul:b]; \label{mil_arith_mul1}
    \vbinds t_2 <- \app t_1*c/; \label{mil_arith_mul2}
    \vbinds t_3 <- \mkclo[add:t_2];
    \vbinds t_4 <- \app t_3*d/;
    \vbinds t_5 <- \mkclo[div:t_5];
    \vbinds t_6 <- \app t_5*2/;
  \end{AVerb}
\end{singlespace}

\intent{Explain example, pointing out treatment of allocation.}
\noindent Line~\ref{mil_arith_mul1} shows MIL's emphasis on
allocation. \mkclo[mul:b] allocates a closure pointing to \lab mul/
and capturing the value of the variable \var b/. We make allocation of
closures a monadic, side-effecting operation by placing \mkclo[mul:b]
on the \rhs of the monadic binding operator (\bind). However, we do
not need to mention the actual address of the locaton \var t_1/, \var
b/ or even \lab mul/ --- those details are hidden. On
Line~\ref{mil_arith_mul2}, we represent function application with the
``enter'' operator, \enter. Line~\ref{mil_arith_mul2} executes the
multiplication and returns a result, which we store in \var
t_2/. Though MIL represents function application explicitly, we hide
implementation details such as stack operations or register spilling. The
rest of the program executes similarly.

%% Syntax of MIL
\section{MIL Syntax}

\intent{Introduce MIL syntax.}  Figure \ref{mil_fig3} gives the syntax
for MIL. Where the term \var v_1/, etc. appears, only simple variables
are allowed.  This includes most terms in the language, staying true
to the design of three-address code. Bold terms such as \lab b/, \lab
k/, and \lab m/ represent labeled locations in the MIL program. \var
C/ represents the name of a data constructor. Bold text such as
\milres case/ and \milres invoke/ represent MIL keywords. A MIL
program consists of a number of labeled blocks.

\input{mil_syntax}

\intent{Describe closure-capturing blocks} \Cc blocks specify an
environment $\left\{\parstrut\ensurett{v_1, \dots, v_n}\right\}$ and
an argument, \var v/. \Cc blocks only execute when initiated by the
\emph{enter} expression, \app f * x/. In \app f * x/, \var f/ refers
to a closure. The closure will point to a \cc block named \lab k/. The
environment declared for \lab k/ correspond to the environment
captured by the closure. The argument \var x/ becomes the argument
\var v/ declared in the \cc block. Though the syntax for \cc blocks
allows any \term tail/ in the body of the block, in practice they
always return a closure or jump to a basic block.

\intent{Describe basic blocks.} Basic blocks consist of a sequence of
statements that execute in order without any intra-block jumps or
conditional branches. Each basic block ends by evaluating a \term
tail/ or a conditional branch. A block body cannot end with a bind
statement. The arguments \ensuremath{\ensurett{(v_1, \dots, v_n)}} are
the only variables in scope while the block executes. The name of the
block (\lab b/) is global to the program but it cannot be captured in a
closure (as closures must always refer to \cc blocks). Basic blocks always
execute as the result of the goto tail expression, \goto b(v_1, \dots, v_n).

\intent{Describe bind.}
The bind statement can appear multiple
times in a block. Each binding assigns the result of the \emph{tail}
on the \rhs to a variable on the left. If a variable is
bound more than once, later bindings will shadow previous
bindings.

\intent{Describe \milres case/.}
The \milres case/ statement examines a
discriminant and selects one alternative based on the value found. The
discriminant is always a simple variable, not an expression. Each
alternative specifies a \emph{constructor} and
variables for each value held by the constructor. Alternatives always
jump immediately to a block --- they do not allow any other statement.

\intent{Introduce tail expressions.} \emph{Tail} expressions represent
effects and always appear on the \rhs of a \bind statement or at the
end of a basic block. \milres return/ takes a variable (\emph{not} an
expression) and makes its value monadic. The ``enter'' operator,
\enter, implements function application, ``entering'' the closure
represented by its \lhs with the argument on its \rhs. The \milres invoke/
operator executes the thunk referred to by its argument (thunks are
described in Section~\ref{mil_monadic_programs}).

\intent{Describe goto for blocks and primitives.}  The goto block and
goto primitive expressions implement labeled jumps with arguments. In
the first case, \lab b/ represents a labeled block elsewhere in the
program.  The primitive term, \lab p/\suptt*, is also bolded but does
not strictly represent a labeled location. Rather, it is treated as a
labeled location that is implemented outside of MIL. Otherwise,
primitives are treated like blocks.

\intent{Describe closure and thunk allocation.} Closure allocation
creates a closure pointing the block labelled \lab k/, capturing the
variables $!+v_1, \dots, v_n+!$. A thunk, details for which can be
found in Section~\ref{mil_monadic_programs}, is allocated
similarly. The constructor expression creates a data value with the
given tag, $!+C+!$, and the variables $!+v_1, \dots, v_n+!$ in the
corresponding fields.

\subsection{MIL Example: \lcname compose/}
\intent{Show an LC program and its translation in MIL.}  To give a
sense of MIL, consider the definition of \lcname compose/ given in
Figure~\ref{mil_fig1a}. Figure~\ref{mil_fig1b} shows a MIL program
implementing the definition. The three \cc blocks, \lab k1/, \lab k2/
and \lab k3/ progressivly capture the three arguments \term f/, \term
g/, and \term x/. \lab k3/ executes when all arguments are captured,
and immediately jumps to \lab compose/, the block implementing the
body of \term compose/.

The basic block defined on Line~\ref{mil_block_decl_fig1b} gives the
name of the block (\lab compose/) and arguments that will be passed in
(\var f/, \var g/, and \var x/). Line~\ref{mil_gofx_fig1b} applies
\var g/ to \var x/ and assigns the result to \var t1/. The ``enter''
operator (\enter), implements function application.
\footnote{So called because in the expression \app g * x/, we
  ``enter'' function \var g/ with the argument \var x/.}

The ``bind'' operator (\bind) assigns the result of
the operation on its right-hand side to the location on the left. All
expressions that could have a side-effect appear on the \rhs of a bind
operator in MIL; in this case, \app g * x/ may allocate memory when
evaluated. 

Line~\ref{mil_fofx_fig1b} applies \var f/ to \var
t1/ and assigns the result to \var t2/. The last line returns \var
t2/. Thus, the \lab compose/ block returns the value of \lcapp f * (g
* x)/, just as in our original \lamC expression.

\begin{myfig}
  \begin{tabular}{c@@{\hspace{2em}}c}
    \lcdef compose()=\lcapp \lcabs f. \lcabs g. \lcabs x. f * (g * x)/; & 
    \begin{minipage}[t]{\widthof{\block compose(f, g, x):}}
      \begin{AVerb}[numbers=left,gobble=8]
        \ccblock k1()f: \mkclo[k2:f]
        \ccblock k2(f)g: \mkclo[k3:f, g]
        \ccblock k3(f, g)x: \goto compose(f, g, x)

        \block compose(f, g, x): \label{mil_block_decl_fig1b}
          \vbinds t1 <- \app g*x/; \label{mil_gofx_fig1b}
          \vbinds t2 <- \app f*t1/; \label{mil_fofx_fig1b}
          \return t2/ \label{mil_result_fig1b}
      \end{AVerb}
    \end{minipage} \\\\
    \scap{mil_fig1a} & \scap{mil_fig1b}
  \end{tabular} 
  \caption{Part~\subref{mil_fig1a} gives a \lamC definition of the composition
    function; \subref{mil_fig1b} shows a fragment of the MIL program
    for |compose|.}
  \label{mil_fig1}
\end{myfig}

\section{Allocation as a Side-Effect} 

\intent{Motivate why we consider allocation impure.}
Functional languages normally treat data allocation as a pure operation, in
that the program cannot directly observe any effect from an allocation. Of
course, when implementing such operations, allocation is definitely impure:
the heap may be updated and a garbage collection might be triggered.

\intent{Illustrate allocation as in invisible effect in \lamA.} For
example, consider the operations that occur when calculating |compose
a b c| using call- by-value evaluation:

\begin{singlespace}\noindent
  \begin{math}\begin{array}{rl}
      \lcapp compose * a * b * c/ &= \lcapp (\lcabs f. \lcabs g. \lcabs x. {\lcapp f * (g * x)/}) * a * b * c/ \\
      &= \lcapp (\lcabs g. \lcabs x. {\lcapp a * (g * x)/}) * b * c/ \\
      &= \lcapp (\lcabs x. {\lcapp a * (b * x)/}) * c/ \\
      &= \lcapp a * (b * c)/ \\
    \end{array}\end{math}
\end{singlespace}

\intent{Introduce notation to make the environment and intermediate functions
explicit.}
This representation hides an important detail: each
application creates a closure representing a function and its
environment (or \emph{free variables}). We can make these values more
obvious by writing each $\lambda$-expression as a new function,
annotated with its free variables in braces:

\begin{singlespace}\noindent
  \begin{math}\begin{array}{rl}
      k_1 \left\{\strut \right\} f &= \lcabs g. \lcabs x. \lcapp f * (g * x)/ \\
      k_2 \left\{\strut f\right\} g & = \lcabs x. \lcapp f * (g * x)/ \\
      k_3 \left\{\strut f, g\right\} x &= \lcapp f * (g * x)/ \\
    \end{array}\end{math}
\end{singlespace}

\intent{Explain why the notation above is not sufficient to show
  allocation as an effect.}  This notation, however, is not quite
enough. Each time we return a $\lambda$ value in \lamC, we allocate a
closure to represent the result. \lcname k_1/ does not
return the result of executing \lcabs g. \lcabs x. \lcapp f * (g *
x)/; rather, \lcname k_1/ returns a closure that indirectly represents
the execution of \lcabs g. \lcabs x. \lcapp f * (g * x)/. These allocations
are not pure --- they affect the state of the machine and can
trigger observable effects. 

As described by Wadler \citeyearpar{Wadler1990}, \emph{monads}
can be used distinguish \emph{pure} and \emph{impure} functions. A
\emph{pure} function has no side-effects: it will not print to the
screen, throw an exception, write to disk, or in any other way change
the observable state of the machine.\footnote{We mean ``observable''
  from the program's standpoint. Even a pure computation will generate
  heat, if nothing else.} An \emph{impure} function may change the
machine's state in an observable way.

\intent{Explain our $k$ and \hsdo notation together.}  Therefore, we
rewrite the \rhs of \lcname k_1/ as $\hsdo\left\{\lcapp k_2 *
\left\{\parstrut f\right\}/;\right\}$, denoting two concepts. First,
\lcapp k_2 * \left\{\parstrut f\right\}/ indicates that we create a
closure pointing to \lcname k_2/ and holding an environment
containing \lcname f/. Second, because allocation has an observable
effect, we use $\mathbf{do}$ notation to show that \lcname k_1/ does
not represent a pure value --- it evaluates to a computation that must
be executed. We do the same for \lcname k_2/; \lcname k_3/ remains
unchanged as it does not evaluate to a $\lambda$ and therefore does
not directly have an observable effect:

\begin{singlespace}\noindent
  \begin{math}\begin{array}{rl}
      k_1 \left\{\strut \right\} f &= \hsdo \left\{\lcapp k_2 * \left\{\strut f\right\}/;\right\} \\
      k_2 \left\{\strut f\right\} g & = \hsdo \left\{\lcapp k_3 * \left\{\strut f, g\right\}/;\right\} \\
      k_3 \left\{\strut f, g\right\} x &= \lcapp f * (g * x)/ \\
    \end{array}\end{math}
\end{singlespace}

\intent{Show example with new notation and explain why it is important.}
With these definitions, we can rewrite the evaluation of \lcapp compose * a * b * c/
as a sequence of side-effecting monadic allocations:

\begin{singlespace}\noindent
  \begin{math}\begin{array}{rl}
      \lcapp compose * a * b * c/ &= \lcapp (\lcabs f. \lcabs g. \lcabs x. {\lcapp f * (g * x)/}) * a * b * c/\\
      &= \lcapp {\lcapp (k_1 \left\{\strut\right\} * a)/} * b * c/ \\
      &= \lcapp ({(\hsdo \left\{\lcapp k_2 * \left\{\strut a\right\}/;\right\})} * b) * c/ \\
      &= \lcapp {\lcapp (k_2 \left\{\strut a\right\} * b)/} * c/ \\
      &= \lcapp {(\hsdo \left\{\lcapp k_3 * \left\{\strut a, b\right\}/;\right\})} * c/ \\
      &= \lcapp k_3 \left\{\strut a, b\right\} * c/ \\
      &= \lcapp a * (b * c)/ \\
      \multicolumn{2}{l}{\vrule width.95\hsize height0pt depth0pt}
    \end{array}\end{math}
\end{singlespace}

\noindent In \lamC, the values created by \lcname k_1/ and \lcname
k_2/ are not explicitly represented. In the above, each \hsdo line
indicates that an allocation will occur. While this detail is hidden
from most high-level languages, MIL treats allocation as an impure
operation. Allocation affects the machine and MIL makes it explicit.

\begin{myfig}[t]
  \input{lst_mil2}
  \caption{The MIL program which computes $main =
    \lamApp{\lamApp{\lamApp{compose}{a}}{b}}{c}$. Note that $a$, $b$,
    and $c$ are assumed to be arguments given outside the program.}
  \label{mil_fig2}
\end{myfig}

\intent{Describe MIL program for |main = compose a b c|.}  Figure
\ref{mil_fig2} shows the complete MIL program for \lcdef main()=
\lcapp compose * a * b * c/;. The closure-capturing blocks \lab k1/,
\lab k2/ and \lab k3/ correspond to the \lcname k_1/, \lcname k_2,/
and \lcname k_3/ definitions above. The free variables annotated on each
definition correspond to the variables in braces next to \lab k1/, \lab k2/
and \lab k3/. \lab main/ corresponds to our
top-level expression |compose a b c|. 

\intent{Point out where intermediate values are created and captured.}
By examping \lab main/ in Figure \ref{mil_fig2} we can see how MIL
makes explicit the intermediate closures created while evaluating
\lcapp compose * a * b * c/. Line~\ref{mil_t0_fig2} executes the block
\lab k0/, allocating a closure pointing to \lab k1/ and assigning it
to \var t0/. On line \ref{mil_t1_fig2}, we apply \var t0/ to \var a/;
\lab k1/ executes and creates a closure which we write \mkclo[k2:f],
meaning the closure points to \lab k2/ and holds the value of \var
f/. We assign that closure to \var t1/. On Line~\ref{mil_t2_fig2} we
apply \var t1/ to the second argument, \var b/. This executes \lab
k2/, which expects to find one argument in its environment, just as we
stored in \var t1/. \lab k2/ creates another closure, \mkclo[k3:f, g],
which we assign to \var t2/. This closure points to \lab k3/ and holds
two variables in its environent. Finally, on line \ref{mil_t3_fig2},
we apply \var t2/ to the final argument, \var c/. \lab k3/ executes
and immediately jumps to \lab compose/ with our arguments. The result,
assigned to \var t3/, is returned on the last line of \lab main/.

\section{Monadic Thunks}
\label{mil_monadic_programs}

\intent{Introduce idea of monads as suspended computation.}
In another sense, also described in Wadler's \citeyear{Wadler1990} paper, a
monadic value represents a \emph{computation}. Where a pure function evaluates
to a ``pure'' value that is immediately available, a monadic function gives
back a suspended computation that we need to execute before we can get to the
value ``inside'' the computation.

\intent{Contrast pure and monadic values.}  Consider the \lamC
functions in Figure~\ref{mil_fig_monadic}.\footnote{Some syntactic
  liberties have been taken here. \lamC only supports monadic binding,
  so ``|print 0|'' really represents ``|_ <- print 0|.'' Integers are not
  directly part of the language, either.} Neither takes any arguments
and they ostensibly produce the same number. Of course, the value
produced by the pure function in
Part~\subref{mil_fig_monadic_pure} differs markedly from that produced
by the impure function in
Part~\subref{mil_fig_monadic_comp}. 

\begin{myfig}
  \begin{tabular}{cc}
    |f = 1| & 
    \begin{minipage}[t]{1in}
> m = do 
>   print 0
>   return 1
    \end{minipage} \\
    \scap{mil_fig_monadic_pure} & \scap{mil_fig_monadic_comp}
  \end{tabular}
  \caption{Part~\ref{mil_fig_monadic_pure} shows a \emph{pure}
    function with no side effects. Part~\ref{mil_fig_monadic_comp}
    shows an \emph{impure} function.}
  \label{mil_fig_monadic}
\end{myfig}

\intent{Introduce monadic thunks.}  Intuitively, |f| returns an
integer, but |m| returns a \emph{computation}. We call this
computation a \emph{monadic thunk}, as coined in the Habit Compiler
Report \citep{HabitComp2010}. Traditionally, thunks represent
\emph{suspended} computation. We use it in the same sense here, in
that |m| evaluates to a program that we can invoke; moreover,
evaluating |m| alone will \emph{not} invoke the computation --- |m|
must be evaluated and then invoked before the computation will produce
a result. 

\intent{Show how MIL thunks are used.}  To illustrate, consider the
\lamC functions in Figure~\ref{mil_fig_hello_a}.\footnote{Again, some
  syntactic liberties are taken.} Part~\subref{mil_fig_hello_b} shows
the corresponding MIL code for each. On
Line~\ref{mil_fig_thunk_hello}, \lab hello/ returns a thunk pointing to
\lab m/. \lab m/ represents the body of |hello|; it calls
primitives which we elide. The \lab main/ block, however, shows how we
invoke the thunk returned by \lab hello/. On
Line~\ref{mil_fig_get_hello1}, \lab hello/ is called, and the thunk
returned is bound to the variable \var t1/. On the next line, the
thunk is invoked. Lines~\ref{mil_fig_get_hello2} and
\ref{mil_fig_invoke_hello2} show the same operation again. In other
words, \lab main/ executes the \lab hello/ function twice, producing
an effect each time.

\begin{myfig}
  \begin{tabular}{cc}
    \begin{minipage}[t]{\widthof{|hello = print "hello"|}}
> hello = do
>   print 0
>
> main = do
>   hello
>   hello
    \end{minipage} &
    \begin{minipage}[t]{\widthof{\ \ \binds \_ <- \invoke v207/;}}
      \begin{AVerb}[gobble=8,numbers=left]
        \block hello(): \mkthunk[m:] \label{mil_fig_thunk_hello}
        \block m():
          \ldots

        \block main(): 
          \vbinds t1 <- \goto hello(); \label{mil_fig_get_hello1}
          \vbinds \_ <- \invoke t1/; \label{mil_fig_invoke_hello1}
          \vbinds t2 <- \goto hello(); \label{mil_fig_get_hello2}
          \vbinds \_ <- \invoke t2/; \label{mil_fig_invoke_hello2}
      \end{AVerb}
    \end{minipage} \\
    \scap{mil_fig_hello_a} & \scap{mil_fig_hello_b}
  \end{tabular}
  \caption{Part~\subref{mil_fig_hello_a} shows two monadic \lamC
    functions. The MIL blocks that create and use monadic thunks to
    execute |main| are shown in Part~\subref{mil_fig_hello_b}.}
  \label{mil_fig_hello}
\end{myfig}

\intent{Monadic thunks are like closures; but \cc blocks for thunks do
  not exist.}  Thunks can capture variables just like closures, but
unlike closures they are not progressively ``built up'' across
multiple blocks. Figure~\ref{mil_fig_kleisli} illustrates this
concept. Part~\subref{mil_fig_kleisli_a} shows the monadic, or
``Kleisli,'' \citep{KleisliXX} composition
function. Part~\subref{mil_fig_kleisli_b} shows the corresponding MIL
code. The blocks \lab k201/, \lab k202/, and \lab k203/ progressively
capture the arguments to |kleisli|. \lab b204/ constructs the thunk
for |kleisli|, but only after all arguments have been captured. The
block \lab m205/ implements the body of |kleisli| and is shown in 
Figure~\ref{mil_fig_kleisli_body} rather than here.

\begin{myfig}
  \begin{tabular}{cc}
    \begin{minipage}[t]{\widthof{|kleisli f g x = do|\quad}}
> kleisli f g x = do
>   v <- g x
>   f v
    \end{minipage} & \begin{minipage}[t]{\widthof{\ \ \block b204 (g, x, f): \mkthunk[m205:g, x, f]}}
      \begin{AVerb}[gobble=8,numbers=left]
        \block kleisli(): \mkclo[k201:]
        \ccblock k201()f: \mkclo[k202:f]
        \ccblock k202(f)g: \mkclo[k203:g, f]
        \ccblock k203(g, f)x: \goto b204(g, x, f)
        \block b204(g, x, f): \mkthunk[m205:g, x, f]
      \end{AVerb}
    \end{minipage} \\
    \scap{mil_fig_kleisli_a} & \scap{mil_fig_kleisli_b} \\
  \end{tabular}
  \caption{Part~\subref{mil_fig_kleisli_a} shows a monadic composition function 
    (also known as ``Kleisli'' composition). Part~\subref{mil_fig_kleisli_b} shows
  a MIL program representing the same function.}
  \label{mil_fig_kleisli}
\end{myfig}

\section{Compiling \lamC to MIL}
\label{mil_sec4}

\intent{Explain why we don't show the whole compiler.}  The compiler
we implemented followed the style used by Kennedy \citep{KennedyCont},
and in most cases it does not differ much from numerous other
compilers translating the \lamA to a given intermediate form. However,
we will highlight some nuances of our translation.

\intent{Show how $\lambda$-abstractions are translated.}  Consider
again the definition of |compose| in Figure~\ref{mil_fig1a} on
Page~\pageref{mil_fig1}. Our compiler translates each $\lambda$,
except the last, to a block that returns a closure. The final
$\lambda$ translates to a block that immediately jumps to the the
implementation of the function. This gives the sequence of blocks
shown in Figure~\ref{mil_fig2} on Page~\pageref{mil_fig2} (excepting
\lab main/, of course), and allows MIL to support partial application.

\intent{Point out how we rely on uncurrying to make this code
  performant.}  While general, this strategy produces code that does a
lot of repetitive work. When fully applied, a function of $n$
arguments will create $n - 1$ closures, perform $n - 1$ jumps between
blocks, and potentially copy arguments between closures numerous
times. Our uncurrying optimization
(Chapter~\ref{ref_chapter_uncurrying}) can collapse this work to one
closure, one jump and no argument copying in many cases. Therefore,
generating simple (and easy to analyze) code seemed a reasonable
tradeoff.

\intent{Explain how we know when to create a thunk versus executing
  monadic code.}  Monadic code presents other challenges. Monadic
expressions do not directly produce a value; they produce a thunk to
be evaluated later. Therefore, when the compiler first encounters a
monadic expression, it generates a block that returns a thunk. The
block pointed to by the thunk executes the monadic expression. 

\intent{Show where a thunk is created in |kleisli|.}  The code shown
for |kleisli| in Figure~\ref{mil_fig_kleisli_b} on
Page~\pageref{mil_fig_kleisli} illustrates this strategy. Block \lab
m205/ executes the body of |kleisli|. However, nothing calls \lab
m205/ directly. Instead, block \lab b204/ returns a thunk that points
to \lab m205/. \lab b204/ only executes after all arguments for
|kleisli| are collected; \lab m205/ can only execute by invoking the
thunk returned by \lab b204/.

\intent{Explain how compiler changes strategy when translating a
  monadic expression.}  While the compiler follows the strategy above
when it first encountes a monadic expresssion, it changes strategy
when compiling the body of that expression. The compiler assumes a
monadic expression consists of a sequence of ``monadic-valued''
statements.  In |x <- e|, |e| produces a monadic value. Any other
expression (such as ``|f g|'' or ``|case e of {-"\dots"-}|'') should
also evaluate to a monadic value.

\begin{myfig}
  \begin{tabular}{c}
    \begin{minipage}[t]{\widthof{\ \ \binds v1 <- \invoke v207/;}}
      \begin{AVerb}[gobble=8,numbers=left]
        \block m205(g, x, f):
          \vbinds v207 <- \app g*x/;
          \vbinds v1 <- \invoke v207/;
          \vbinds v206 <- \app f*v1/; \label{mil_fig_kleisli_f_app}
          \invoke v206/ \label{mil_fig_kleisli_result}
      \end{AVerb}
    \end{minipage}
  \end{tabular}
  \caption{The MIL implemention of the |kleisli| function from
    Figure~\ref{mil_fig_kleisli_a}. Here, we only show the main body
    of the function; the other blocks are shown in
    Figure~\ref{mil_fig_kleisli_b}.}
  \label{mil_fig_kleisli_body}
\end{myfig}

\intent{Show how the compiler translates a non-bind expression using
  |f v| in |kleisli|.}  The body of the |kleisli| fucntion shown in
Figure~\ref{mil_fig_kleisli_body} illustrates this principle. |kleisli|
ends with |f v|, an application that must produce a monadic result. We also
expect that result to be evaluated.\footnote{Imagine if |f| were
  |print| -- then ``|print x|'' should print!} The statements on
Lines~\ref{mil_fig_kleisli_f_app} and \ref{mil_fig_kleisli_result}
evaluate the application, assign the thunk returned to \var v206/, and
then execute that thunk. In essence, the compiler translates |kleisli|
as if it ended with a bind followed by a |return|:

\begin{singlespace}
> kleisli f g x = do
>   y <- g x
>   t <- f y
>   return t
\end{singlespace}

\section{Executing MIL Programs}
\label{mil_sec5}
\intent{MIL programs execute like assembly programs.}
\intent{Only variables mentioned in environments and arguments are in scope; however, definitions are global.}
\intent{Goto's are more like function calls than jumps.}

\section{MIL and Hoopl}
\label{mil_sec7}

\intent{Reminder about open/closed shapes.}  As described in
Section~\ref{hoopl_sec_cfg}, Hoopl characterizes control--flow between
nodes in a CFG by their entry and exit shape. Hoopl uses the |O| and
|C| types to express the shape of the entry and exit points for a
node. A node that is open on exit can only be followed a node that is
open on entry. A sequence of nodes can be characterized by the entry
shape of the first node and the exit shape of the last node.

\intent{Reminder about relationship between basic blocks and shape.}
In Hoopl terms, basic blocks (described in Section~\ref{sec_back3})
are closed on entry and closed on exit. Due to the constraints imposed
by the shape type, none of the nodes between the first and last will
jump or branch to other nodes. They can only execute one after
another.

%% \intent{Enumerate the various shape combinations and connect to basic
%%   blocks.}  An |O O| (``open/open'') node has exactly one predecessor
%% and one successor. An |O O| node must appear in the middle of a basic
%% block --- it cannot be the target of multiple predecessors, therefore
%% it cannot be the target of a jump or branch. A |C O| (``closed/open'')
%% node can have multiple predecessors but only one successor. A |C O|
%% node can start a basic block, but it must always be followed by at
%% least one node. An |O C| (``open/closed'') node can only have one
%% predecessor, but many successors. An |O C| node always ends a 
%% basic block. A |C C| (``closed/closed'') node is not very useful on
%% its own; however, a |C C| sequence of nodes forms a basic block.

\intent{Describe the five |Stmt| constructors.}
Figure~\ref{mil_fig_stmt_ast} shows |Stmt|, the data type defining the
\term block/ and \term stmt/ terms from Figure~\ref{mil_fig3}. The
|Stmt| type takes two type parameters, |e| and |x|, representing the
entry and exit shape of the statement. |BlockEntry| and |CloEntry|
represent the two types of blocks (basic and \cc, respectively). Their
shape, |C O|, shows that they can only be used to begin a MIL
block. The |Name| and |Label| arguments help Hoopl connect nodes
together in the CFG.  The |Bind| statement (with shape |O O|)
represents statements inside the block. The type ensures no block
begins or ends with a |Bind|. Blocks can end with either a |CaseM| or
|Done| statement. The |CaseM| value represents the \milres case/
statement. |Done| does not appear explicitly in Figure~\ref{mil_fig3},
but the AST uses it to end a block with a |Tail| expression. The
|Name| and |Label| arguments to |CaseM| and |Done| make it easier to
know the basic block being analyzed when traversing the CFG backwards.

\begin{myfig}
  \begin{minipage}{\linewidth}\begin{withHsLabeled}{mil_stmt_ast}\numbersoff
> data Stmt e x where
>   BlockEntry :: Name -> Label -> [Name] -> Stmt C O {-"\hslabel{block}"-}
>   CloEntry :: Name -> Label -> [Name] -> Name -> Stmt C O {-"\hslabel{ccblock}"-}
>   Bind :: Name -> Tail -> Stmt O O {-"\hslabel{bind}"-}
>   Case :: Name -> [Alt Tail] -> Stmt O C {-"\hslabel{case}"-}
>   Done :: Name -> Label -> Tail -> Stmt O C {-"\hslabel{done}"-}
  \end{withHsLabeled}\end{minipage}
  \caption{Haskell data type representing MIL \term stmt/ terms. The |C| and |O|
  types (from Hoopl) give the ``shape'' of each statement.}
  \label{mil_fig_stmt_ast}
\end{myfig}

\intent{Show how the AST mirrors the expected shape of a sample MIL
  block.}  Even without describing |Tail| values, we can show how
|Stmt| values give the correct shape to MIL blocks. Returning to our
example of Kleisli composition in Figure~\ref{mil_fig_kleisli_body} on Page~\pageref{mil_fig_kleisli_body}, we can
represent the block \lab m205/ with the following definition:

\begin{singlespace}
> m205 :: Label -> Graph Stmt C C
> m205 label = mkFirst (BlockEntry "m205" label ["g", "f", "x"]) <*>
>   mkMiddles [Bind "v207" ({-"\app g * x/"-})
>             , Bind "v1" ({-"\invoke v209/"-})
>             , Bind "v206" ({-"\app f * v1/"-})] <*>
>   mkLast (Done "m205" label ({-"\invoke v206/"-}))
\end{singlespace}

|m205| defines a basic block, as shown by its |C C| type. Hoopl
provides |mkFirst|, |mkMiddles| and |mkLast|
(Chapter~\ref{ref_chapter_hoopl}, Figure~\ref{hoopl_fig4}), for
lifting nodes into Hoopl's monadic graph representation. The operator
|<*>| connects pieces of the graph together. Hoopl uses the |label|
argument to connect this definition to other basic blocks in a larger
program.

Figure~\ref{mil_fig_tail_ast} shows the various |Tail| values
that implement the \term tail/ terms in Figure~\ref{mil_fig3}. Notice
the definition does not parameterize on shape. These expressions are not
used to construct CFGs and therefore did not need to be parameterized. 

\intent{Enumerate |Tail| constructors, call out |Run| and |Constr|
  because they have different names than in Figure~\ref{mil_fig3}.}
The constructors to |Tail| map directly to \term tail/
terms. |Return|, |Enter| |Goto|, |Prim|, |Closure|, and |Thunk|
represent the corresponding \term tail/ terms. |Run| represents
\milres invoke/ and |Constr| represents a
constructor.

\begin{myfig}[tb]
  \begin{minipage}{\linewidth}\begin{withHsLabeled}{mil_tail_ast}\numbersoff
> data Tail = Return Name {-"\hslabel{return}"-}
>   | Enter Name Name {-"\hslabel{enter}"-}
>   | Run Name {-"\hslabel{invoke}"-}
>   | Goto Dest [Name] {-"\hslabel{goto}"-}
>   | Prim Name [Name] {-"\hslabel{prim}"-}
>   | Closure Dest [Name] {-"\hslabel{clo}"-}
>   | Thunk Dest [Name] {-"\hslabel{thunk}"-}
>   | Constr Constructor [Name] {-"\hslabel{cons}"-}
  \end{withHsLabeled}\end{minipage}
  \caption{Haskell data type representing MIL \term tail/ expressions.}
  \label{mil_fig_tail_ast}
\end{myfig}

\intent{Show connection between MIL syntax and AST vis.\ arguments.}
All MIL \term tail/ terms that take arguments only allow variables,
not arbitrary expressions. The |Tail| constructors implement that
restriction by only taking |Name| arguments. Similarly, |Stmt|
constructors do not take any argument but |Names| or |Tails|.

\section{Summary}
\label{mil_sec6}

This chapter presented our Monadic Intermediate Language (MIL). Our
MIL resembles three-address code in several ways: infinitely many
registers can be named, nested expressions are not allowed, and
implementation details are made explicit. The MIL's unique features
include separate representations for \emph{closure-capturing} and
basic blocks, and the use of monadic \emph{tail} expressions. Later
chapters will be devoted to optimizing MIL programs using
dataflow techniques.

\standaloneBib

\end{document}

% LocalWords:  RTL Torczon Muchnick ANF MIL's dataflow Appel eq clo CompL invis
% LocalWords:  compclo stateful monad Monads Wadler monads eqn intra goto
