%&preamble
\input{nodocclass}\dodocclass
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\begin{document}
\input{document.preamble}
\chapter{A Monadic Intermediate Language}
\label{ref_chapter_mil}

Most compilers do not generate executable machine code directly from a
program source file. Rather, the compiler transforms the program into
a number of different \emph{intermediate languages}, where each
intermediate language exposes different details about the
implementation of the program. Each intermediate language provides
specialized support for aspect of the analysis and transformation of
the program performed by the compiler.

A number of intermediate languages have been described for both
imperative and functional languages. \emph{Three-address code}
(described in standard textbooks, such as \cite[Chap.~6,
  Sec.~6.2]{Aho2006}) is mostly associated with imperative languages
and emphasizes simplicity by requiring all operations to specify at
most two operands and one destination. Three-address code aids in
optimizing the use of registers, typically a scarce resource on most
processors. Administrative-Normal Form, first described by
\citet{Flanagan1993}, is an intermediate form for functional languages
which makes all intermediate values explicit. It is useful for showing
the exact order of evaluation for expressions. 

Our monadic intermediate language (\mil), specifically supports
functional language features, but also follows the form of
three-address code. \Mil directly supports function application and
abstraction. All intermediate values are named. \Mil specifies
evaluation order and separates stateful computation using a monadic
programming style. \Mil's syntax enforces basic-block structure on
programs, making them ideal for dataflow analysis.

\intent{Signposts.}  We first describe our source language, \lamC, in
Section~\ref{mil_src}.  The motivation and roots of \mil are given in
Section~\ref{mil_sec3}. \Mil's complete syntax follows in
Section~\ref{mil_syntax}.  Section~\ref{mil_monad} discusses \mil's
treatment of allocation as a side-effect.  Section~\ref{mil_thunks}
shows how \mil treats monadic programs as suspended
computations. Section~\ref{mil_sec4} highlights some of the subtler
points in our translation strategy from \lamC to \mil. We sketch how
\mil programs can be evaluated in Section~\ref{mil_sec5}. Section
\ref{mil_sec7} shows how \hoopl influenced the AST we used to
rerpresent \mil programs. We conclude in Section~\ref{mil_sec6}.

\section{Source Language: \lamC}
\label{mil_src}

\intent{Introduce \lamC; where it came from, references, etc.}  Our
source language, \lamC (pronounced ``lambda-case''), derives from the \lamA, with
elements borrowed from the Haskell languages's
use of \hsdo notation to represent monadic programs. Jones and
colleagues developed \lamC as an intermediate representation for the
Habit programming language \citep{Habit2010}. The Habit ``Compilation
Strategy'' report \citep{HabitComp2010} gives full details on
\lamC.\footnote{For simplicity's sake, we ignore two features of \lamC
  in this work: patterns and guards. Details on those elements can be
  found in the aforementioned report.} The report describes several
different intermediate languages; \lamC corresponds to ``Normalized
\textsc{mpeg}.''

Figure~\ref{mil_fig_lam_syntax} gives the full syntax of \lamC. In the
figure, \term x/, \term x_1/, etc.\ represent simple variables, while
\term t/, \term t_1/, etc.\ represent arbitrary terms. All \term def/
terms are global to the program in which they are defined. Definitions
with zero arguments are values and cannot be recursive; definitions
with more than one argument are functions and can be recursive. Only
variables can appear as arguments in definitions and case
alternatives --- the language does not support more sophisticated
pattern-matching. The language is untyped and does not support data
declarations. While most elements should be recognizable
from Haskell or the \lamA, we will explain the the \emph{monadic
  bind} and \emph{primitive} terms further.

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
    \termcase |do { x <- t_1; t_2 }|:Monadic Bind/ \\
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

\intent{Describe bind.}  \runin{Monadic Bind} The monadic binding
term, |do { x <- t_1; t_2 }|, states that the result of running the
monadic computation, |t_1|, will be bound to |x| and that |t_2| will
then be executed with |x| in scope. Note that |x| can only be a
variable; \lamC does not support pattern-matching on the \lhs of a
bind. When |t_2| is another monadic bind, we do not nest the \hsdo
keyword: for brevity, we write |do { x <- t_1; y <- t_2}| rather
than |do { x <- t_1; do { y <- t_2}}|.

\intent{Describe primitives.}  \runin{Primitives} The primitive expression \lcprim p*
refers to a primitive definition named $p$. Primitives refer to functionality
that is not implemented in \lamC itself. In all other respects the
primitive \lcprim p* is treated like any other function value. 

\section{\Mil's Purpose}
\label{mil_sec3}

\intent{Remark on intermediate languages and \mil's focus.} The design
of an intermediate language typically exposes some specific
implementation detail while hiding others in order to support certain
analysis and transformation goals. Exposing intermediate values gives
us the chance to analyze and eliminate them. Hiding implementation
details makes the job of writing those analyses and transformations
simpler.

\intent{Relate \mil to three-address code.} \Mil's syntax and design
borrow heavily from three-address code, an intermediate form normally
associated with imperative languages and described in standard
textbooks (e.g., \cite{Aho2006}). Three-address code represents
programs such that all operations specify at most two operands and a
single destination. Three-address code hides details of memory
management by assuming that infinitely many storage locations can be
named and updated. For example, the expression:
%
\begin{singlespace}
  \begin{equation*}
    \frac{(b * c + d)}{2},
  \end{equation*}
\end{singlespace}
%
\noindent could be expressed in three-address code as:
%
\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \vbinds t_1<-mul b c;
    \vbinds t_2<-add t_1 d;
    \vbinds t_3<-div t_2 2;
  \end{AVerb}
\end{singlespace}
%
\noindent where \var t_1/, \var t_2/ and \var t_3/ represent temporary
storage locations and \var mul/, \var add/, and \var div/ represent
the corresponding arithmetic operation.

\intent{Remark on Wadler \& MLj work.} \Mil seeks to expose certain
effects that are not normally represented in functional languages. As
described by Wadler \citeyearpar{Wadler1990}, \emph{monads} can be
used distinguish \emph{pure} and \emph{impure} functions. A
\emph{pure} function has no side-effects: it will not in any way
change the observable state of the machine. An \emph{impure} function
may change the machine's state in an observable way. Most functional
languages treat data and closure allocation as pure operations. \Mil
uses monads to treat those allocations as impure operations.

\intent{Highlight focus of \mil (closure allocation).} Three-address
code emphasizes assignments and low-level operations, features
important to imperative languages. \Mil emphasizes allocation and
side-effecting computations, features important to functional
languages. Though the operations supported by \mil differ from
traditional three-address code, the intention remains the same: hide
some details while exposing those we care about.

%% Syntax of MIL
\section{\Mil Syntax}
\label{mil_syntax}

\intent{Introduce \mil syntax.}  Figure \ref{mil_fig3} gives the syntax
for \mil. Where the term \var v_1/, etc. appears, only simple variables
are allowed. This includes most terms in the language, staying true
to the design of three-address code. Bold terms such as \lab b/, \lab
k/, and \lab m/ represent labeled locations in the \mil program. \var
C/ represents the name of a data constructor. Bold text such as
\milres case/ and \milres invoke/ represent \mil keywords. A \mil
program consists of a number of labeled blocks.

\input{mil_syntax}

\intent{Describe closure-capturing blocks} \Cc blocks specify an
environment $\left\{\parstrut\ensurett{v_1, \dots, v_n}\right\}$ and
an argument, \var v/. \Cc blocks only execute when initiated by an
\emph{enter} expression of the form \app f * x/. In \app f * x/, \var
f/ refers to a closure that will point to a \cc block named \lab
k/. The environment declared for \lab k/ corresponds to the
environment captured by the closure. The argument \var x/ becomes the
argument \var v/ declared in the \cc block. We chose to only allow a
single tail expression in the body of a \cc block in order to
simplify analysis of their behavior.

\intent{Describe basic blocks.} Basic blocks consist of a sequence of
statements that execute in order without any intra-block jumps or
conditional branches. Each basic block ends by evaluating a \term
tail/ or a conditional branch. A block body cannot end with a bind
statement. The arguments \ensuremath{\ensurett{(v_1, \dots, v_n)}} are
the only variables in scope at the start of the block. The name of the
block (\lab b/) is global to the program but it cannot be captured in
a closure (as closures must always refer to \cc blocks). Basic blocks
always execute as the result of a ``\emph{Goto Block}'' tail
expression of the form \goto b(v_1, \dots, v_n).

\intent{Describe bind.}  The bind statement can appear multiple times
in a block. Each binding assigns the result of the \emph{tail} on the
\rhs to a variable on the left. If a variable is bound more than once,
later bindings will shadow previous bindings.

\intent{Describe \milres case/.}  The \milres case/ statement examines
a discriminant and selects one alternative based on the value
found. The discriminant is always a simple variable, not an
expression. Each alternative specifies a \emph{constructor} and
variables for each value held by the constructor. No ``default''
alternative exists --- all possible constructors need to be
specified. Again, to simplify later analysis, we chose that
alternatives must always jump immediately to a block --- they do not
allow any other expression.

\intent{Introduce tail expressions.} \emph{Tail} expressions represent
effects and always appear on the \rhs of a bind statement, at the
end of a basic block, or as the body of a \cc block. \milres return/
takes a variable (\emph{not} an expression) and makes its value
monadic. The ``enter'' operator, \enter, implements function
application, ``entering'' the closure represented by its \lhs with the
argument on its \rhs. The \milres invoke/ operator executes the thunk
referred to by its argument (thunks are described in
Section~\ref{mil_thunks}).

\intent{Describe goto for blocks and primitives.}  The ``\emph{goto
  block}'' and ``\emph{goto primitive}'' expressions implement labeled
jumps with arguments. In the first case, \lab b/ represents a labeled
block elsewhere in the program.  The primitive term, \lab p/\suptt*,
is also bolded but does not strictly represent a labeled
location. Rather, it is treated as a labeled location that is
implemented outside of \mil. Otherwise, primitives are treated like
blocks.

\intent{Describe closure and thunk allocation.} Closure allocation,
written as \mkclo[k:v_1, \dots, v_n], creates a closure pointing to the
block labelled \lab k/, capturing the variables $\var v_1/, \dots,
\var v_n/$. A thunk, details for which can be found in
Section~\ref{mil_thunks}, is allocated similarly. The constructor
expression $\ensurett{C\ v_1\ \dots\ v_n}$ creates a data value with the
given tag, $!+C+!$, and the variables $\ensurett{v_1, \dots, v_n}$ in
the corresponding fields.

\subsection*{\Mil Example: \lcname compose/}
\intent{Show an LC program and its translation in \mil.}  Consider the
definition of \lcname compose/ given in Figure~\ref{mil_fig1a} and the
corresponding \mil program in Part~\subref{mil_fig1b}. The three \cc
blocks, \lab k1/, \lab k2/ and \lab k3/ correspond to the three
$\lambda$ values $(\lcabs f. \dots)$, $(\lcabs g. \dots)$, and
$(\lcabs x. \dots)$.  Each block, except \lab k3/, captures a single
argument and returns a new closure holding previously captured values
plus the new argument. \lab k3/ executes when all arguments are
captured, and immediately jumps to \lab compose/, the block
implementing the body of \term compose/.

The basic block defined on Line~\ref{mil_block_decl_fig1b} gives the
name of the block (\lab compose/) and arguments that will be passed in
(\var f/, \var g/, and \var x/). Line~\ref{mil_gofx_fig1b} applies
\var g/ to \var x/ and assigns the result to \var t1/. The ``enter''
operator (\enter), implements function application.
\footnote{So called because in the expression \app g * x/, we
  ``enter'' function \var g/ with the argument \var x/.}

The ``bind'' operator (\mbind) assigns the result of
the operation on its right-hand side to the location on the left. All
expressions that could have a side-effect appear on the \rhs of a bind
operator in \mil; in this case, \app g * x/ may allocate memory when
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
    function; \subref{mil_fig1b} shows a fragment of the \mil program
    for |compose|.}
  \label{mil_fig1}
\end{myfig}

\section{Allocation as a Side-Effect} 
\label{mil_monad}

\intent{Motivate why we consider allocation impure.}  Functional
languages normally treat data allocation as a hidden operation, in
that the program cannot directly observe any effect from an
allocation. Of course, allocation causes effects, such as updating the
heap or triggering a garbage collection.  For example, using the
definition of |compose| given in Figure~\ref{mil_fig1a}, consider the sequence of
reductions that occur when calculating |compose a b c| using
call-by-value evaluation:

\begin{singlespace}\begin{math}\begin{array}{rl}
      \lcapp compose * a * b * c/ &= \lcapp (\lcabs f. \lcabs g. \lcabs x. {\lcapp f * (g * x)/}) * a * b * c/ \\
      &= \lcapp (\lcabs g. \lcabs x. {\lcapp a * (g * x)/}) * b * c/ \\
      &= \lcapp (\lcabs x. {\lcapp a * (b * x)/}) * c/ \\
      &= \lcapp a * (b * c)/ \\
\end{array}\end{math}
\end{singlespace}\medskip

\intent{Make allocations in reductions really clear.}
This notation hides an important detail: in a
naive implementation of \lamC, each reduction of the form $\lcapp
(\lcabs x. \dots) * a/$ allocates a closure representing the
function $(\lcabs x. \dots)$ and its environment. 

\intent{Rewrite |compose| to show monadic effects.}
Figure~\ref{mil_fig_compose} shows |compose| rewritten in a monadic
style that makes closure allocations explicit. The |closure| operation
is a monadic function that allocates memory and stores its arguments
for retrieval later. The first argument is the function that the
closure points to. The second argument represents the environment that
will be used when that function is evaluated.

\begin{myfig}
  \begin{minipage}{2in}
> k_0 = do
>   t <- closure k_1 []
>   return t
> k_1 [] f = do
>   t <- closure k_2 [f]
>   return t
> k_2 [f] g = do
>   t <- closure compose [f, g]
>   return t
> compose [f, g] x = do 
>   t <- f (g x)
>   return t
  \end{minipage}
  \caption{A rewritten version of |compose| that makes closure
    allocation explicit. \lamC does not support pattern-matching on
    functin arguments, but use it for clarity here. }
  \label{mil_fig_compose}
\end{myfig}

Each $\lambda$ in Figure~\ref{mil_fig1a} becomes a |k_n| definition in
Figure~\ref{mil_fig_compose}. |k_0| corresponds to the expression
\lcapp \lcabs f. \lcabs g. \lcabs x. f * (g * x)/, allocating a
closure with an empty environment and pointing to |k_1|. |k_1| corresponds
to \lcapp \lcabs g. \lcabs x. f * (g * x)/, while |k_2| corresponds
to  \lcapp \lcabs x. f * (g * x)/. Each |k_n|
definition (except |k_0|) takes two arguments. The first is a list of
values representing the environment of the function, and the second a
new value representing the argument of the original $\lambda$
expression. |k_1| and |k_2| each allocate and return a new
closure. The closure stores a reference to the next $k_{n+1}$
definition and a list of values representing the current
environment. |compose| evaluates |f (g x)|; however, this expression
also becomes monadic, as |f (g x)| may cause an allocation.

\intent{Show how closures created by |compose| are used}
Figure~\ref{mil_fig_mon_compose} shows a program that evalutes
|compose a b c| using our rewritten, monadic |compose|. To evaluate
each closure, we define a monadic function |app| that takes a closure
and an argument. |app| evaluates the function referred to by the
closure, using the environment stored in the closure and passing the
additional argument supplied.

\begin{myfig}
  \begin{minipage}{2in}
> main a b c = do
>   t0 <- k_0
>   t1 <- app t0 a
>   t2 <- app t1 b
>   t3 <- app t2 c
>   return t3
  \end{minipage}
  \caption{A program that evaluates \lcapp compose * a * b * c/ using our
    rewritten, monadic form of |compose|.}
  \label{mil_fig_mon_compose}
\end{myfig}

The first line of the program in Figure~\ref{mil_fig_mon_compose} allocates an
initial closure that serves as the entry point for |compose|. Each
line after gathers an additional argument and ``adds'' it to the
closure represented. The final line returns the result of |compose a b
c|.  In our original expression, the allocation caused by each
$\lambda$ was not clear. In |main|, each line indicates that an
allocation will occur.

Of course, in \lamC we do not really define the |closure| or |app|
functions, and closure allocation is not directly visible. \Mil,
however, treats allocation as an impure operation and makes it
explicit. Figure \ref{mil_fig2} shows a complete \mil program for
\lcdef main()= \lcapp compose * a * b * c/;. \lab main/ corresponds to
the definition of |main| in Figure~\ref{mil_fig_mon_compose}. \lab k0/
corresponds to |k_0| and acts as the entry point for |compose|. Notice
that \lab k0/ is not a closure-capturing block; \lab k0/ just
allocates the initial closure that will be used to evaluate |compose a
b c|. The closure-capturing blocks \lab k1/ and \lab k2/ correspond to
|k_1| and |k_2|. The second argument to each |closure| operation
corresponds to the variables captured by the closures allocated in the
body of \lab k1/ and \lab k2/; the list of values passed as an
argument to |k_1| and |k_2| correspond to the environment defined for
the \lab k1/ and \lab k2/ closure-capturing blocks. In
Figure~\ref{mil_fig_compose}, |k_2| creates a closure pointing to
|compose|. However, in \mil a closure can only store the label of
another \cc block. Therefore, since we cannot create a closure
referring to \lab compose/, \lab k2/ returns a closure refering to
\lab k3/. Because the body of a \cc block must be a tail, \lab k3/
jumps immediately to \lab compose/ when executed.

\begin{myfig}[t]
  \input{lst_mil2}
  \caption{The \mil program which computes $main =
    \lamApp{\lamApp{\lamApp{compose}{a}}{b}}{c}$. Note that $a$, $b$,
    and $c$ are assumed to be arguments given outside the program.}
  \label{mil_fig2}
\end{myfig}

\intent{Point out where intermediate values are created and captured.}
By examining \lab main/ in Figure~\ref{mil_fig2} we can see how \mil
makes explicit the intermediate closures created while evaluating
\lcapp compose * a * b * c/. Line~\ref{mil_t0_fig2} executes the block
\lab k0/, allocating a closure pointing to \lab k1/ and assigning it
to \var t0/. On line \ref{mil_t1_fig2}, we apply \var t0/ to \var a/;
\lab k1/ executes and creates a closure  that points to \lab k2/ and
holds the value of \var a/. We assign \mkclo[k2: a] to \var t1/. On
Line~\ref{mil_t2_fig2} we apply \var t1/ to the second argument, \var
b/. This executes \lab k2/, which expects to find one argument in its
environment, just as we stored in \var t1/. \lab k2/ creates another
closure, \mkclo[k3:a, b], which we assign to \var t2/. This closure
points to \lab k3/ and holds two variables in its environent. Finally,
on line \ref{mil_t3_fig2}, we apply \var t2/ to the final argument,
\var c/. \lab k3/ executes and immediately jumps to \lab compose/ with
our arguments. The result, assigned to \var t3/, is returned on the
last line of \lab main/.

\section{Monadic Thunks}
\label{mil_thunks}

\intent{Introduce idea of monads as suspended computation.}  In
another sense, also described in Wadler's \citeyear{Wadler1990} paper,
a monadic value represents a \emph{computation}. Where a pure function
evaluates to a ``pure'' value that is immediately available, a monadic
function gives back a suspended computation that we need to execute
before we can get to the value ``inside'' the computation. We can also
execute the same computation multiple times, potentially producing a different
value each time.

\intent{Contrast pure and monadic values.}  Consider the \lamC
functions in Figure~\ref{mil_fig_monadic}.\footnote{Some syntactic
  liberties have been taken here. \lamC only supports monadic binding,
  so ``|print a|'' really represents ``|_ <- print 0|.''} Neither
takes any arguments and they ostensibly produce the same number. Of
course, the value produced by the pure function in
Part~\subref{mil_fig_monadic_pure} differs markedly from that produced
by the impure function in Part~\subref{mil_fig_monadic_comp}.

\begin{myfig}
  \begin{tabular}{cc}
    |id a = a| & 
    \begin{minipage}{1.5in}\disableoverfull
> printId a = do 
>   print a
>   return a
    \end{minipage} \\
    \scap{mil_fig_monadic_pure} & \scap{mil_fig_monadic_comp}
  \end{tabular}
  \caption{Part~\ref{mil_fig_monadic_pure} shows a \emph{pure}
    function with no side effects. Part~\ref{mil_fig_monadic_comp}
    shows an \emph{impure} function.}
  \label{mil_fig_monadic}
\end{myfig}

\intent{Introduce monadic thunks.}  Intuitively, |id| returns |a|, but
|printId| returns a \emph{computation}. We call this computation a
\emph{monadic thunk}. Traditionally, thunks represent \emph{suspended}
computation. We use it in the same sense here, in that |printId| evaluates
to a program that we can invoke; moreover, evaluating |printId| alone will
\emph{not} invoke the computation --- |printId| must be evaluated and then
invoked before the computation will produce a result.

\intent{Show how \mil thunks are used.}  To illustrate, consider the
\lamC functions in Figure~\ref{mil_fig_hello_a}.\footnote{Again, some
  syntactic liberties are taken.} The |echo| function prints its
argument to the screen. The \hsdo keyword shows that |echo| is a monadic
program. The |main| function uses a \hslet statment to assign |m| the value
|echo a|. Notice this does \emph{not} evaulate |echo a|; instead, |m| is a thunk
that points to the |echo| function and that captures the value of |x|. 

\begin{myfig}
  \begin{tabular}{cc}
    \begin{minipage}[t]{2in}\elimdisplayskip%
> echo a = do
>   print a
    \end{minipage} &
    \begin{minipage}[t]{2in}\elimdisplayskip
      \begin{AVerb}[gobble=8,numbers=left]
        \block echo(a): \prim print(a) \label{mil_fig_echo}
      \end{AVerb}
    \end{minipage} \\\\
    \begin{minipage}[t]{2in}\elimdisplayskip%
> main x = do
>   let m = echo x
>   m
>   m
    \end{minipage} &     
    \begin{minipage}[t]{2in}\elimdisplayskip
      \begin{AVerb}[gobble=8,numbers=left,firstnumber=last]
        \block main(x): 
          \vbinds m <- \mkthunk[echo:x]; \label{mil_fig_mkthunk}
          \vbinds \_ <- \invoke m/; \label{mil_fig_invoke1}
          \vbinds \_ <- \invoke /; \label{mil_fig_invoke2}
      \end{AVerb}
    \end{minipage} \\
    \scap{mil_fig_hello_a} & \scap{mil_fig_hello_b}
  \end{tabular}
  \caption{Part~\subref{mil_fig_hello_a} shows two monadic \lamC
    functions. The \mil blocks that create and use monadic thunks to
    execute |main| are shown in Part~\subref{mil_fig_hello_b}.}
  \label{mil_fig_hello}
\end{myfig}

Part~\subref{mil_fig_hello_b} shows the corresponding \mil code for
|echo| and |main|. The \lab echo/ block on Line~\ref{mil_fig_echo}
merely executes the primitive \primlab print/. The \lab main/ block,
however, shows how we allocate and invoke a
thunk. Line~\ref{mil_fig_mkthunk} allocates the thunk referring to
\lab echo/ and capturing \var x/. The thunk is bound to \var
m/. Lines~\ref{mil_fig_invoke1} and \ref{mil_fig_invoke2} invoke the
thunk causing \lab echo/ to execute twice. Notice we do not allocate
the thunk again --- only one allocation occurs, but we run the \app
\lab echo/ * x/ ``program'' twice.

\section{Compiling \lamC to \mil}
\label{mil_sec4}

\intent{Explain why we don't show the whole compiler.}  We implemented
a simple compiler from \lamC to \Mil in order to implement and test
the optimizations discussed later in this work. The compiler's implementation follows
the style used by Kennedy \citep{KennedyCont}, and in most cases it
does not differ much from numerous other compilers translating the
\lamA to a given intermediate form. However, we will highlight some
nuances of our translation.

\intent{Show how $\lambda$-abstractions are translated.}  Consider
again the definition of |compose| in Figure~\ref{mil_fig1a} on
Page~\pageref{mil_fig1}. Our compiler translates each $\lambda$,
except the innermost (\lcabs x.\dots/), to a block that returns a
closure. The innermost $\lambda$ translates to a block that immediately
jumps to an implementation of the body of |compose|. This gives the
sequence of blocks shown in Figure~\ref{mil_fig2} on
Page~\pageref{mil_fig2} (excepting \lab main/, of course), and allows
\mil to support partial application.

\intent{Point out how we rely on uncurrying to make this code
  performant.}  While general, this strategy produces code that does a
lot of repetitive work. When fully applied, a function of $n$
arguments will create $n - 1$ closures, perform $n - 1$ jumps between
blocks, and potentially copy arguments between closures numerous
times. Our uncurrying optimization
(Chapter~\ref{ref_chapter_uncurrying}) can collapse this work to one
closure, one jump and no argument copying in many cases. Therefore,
generating simple (and easy to analyze) code is a reasonable
tradeoff.

\intent{Explain how we know when to create a thunk versus executing
  monadic code.}  Monadic code presents other challenges. Monadic
expressions do not directly produce a value; they produce a thunk to
be evaluated later. Therefore, when the compiler first encounters a
monadic expression, it generates a block that returns a thunk. The
block pointed to by the thunk executes the monadic expression. 

\intent{Show where a thunk is created in |kleisli|.}  The code shown
for |kleisli| in Figure~\ref{mil_fig_kleisli} illustrates this
strategy. The |kleisli| function in Part~\ref{mil_fig_kleisli_a}
implements \emph{monadic} composition, where |f| and |g| produce
monadic results. Part~\ref{mil_fig_kleisli_a} shows a \mil
implementation of |kleisli|. Block \lab m205/ on
Line~\ref{mil_fig_kleisli_m205} executes the body of
|kleisli|. However, no blocks call \lab m205/ directly. Instead, block
\lab b204/ on Line~\ref{mil_fig_kleisli_b204} returns a thunk that
points to \lab m205/ and captures all the arguments to \lab m205/
(\var g/, \var f/, and \var x/). \lab b204/ only executes after all
arguments for |kleisli| are collected; \lab m205/ can only execute by
invoking the thunk returned by \lab b204/.

\begin{myfig}
  \begin{tabular}{cc}
    \begin{minipage}[t]{2in}\disableoverfull\elimdisplayskip
> kleisli f g x = do
>   v <- g x
>   f v
    \end{minipage} &
    \begin{minipage}[t]{2in}\disableoverfull\elimdisplayskip
      \begin{AVerb}[gobble=8,numbers=left]
       \block kleisli(): \mkclo[k201:]
       \ccblock k201()f: \mkclo[k202:f]
       \ccblock k202(f)g: \mkclo[k203:g, f]
       \ccblock k203(g, f)x: \goto b204(g, x, f)
       \block b204(g, x, f): \mkthunk[m205:g, x, f] \label{mil_fig_kleisli_b204}

       \block m205(g, x, f): \label{mil_fig_kleisli_m205}
          \vbinds v207 <- \app g*x/;
          \vbinds v1 <- \invoke v207/;
          \vbinds v206 <- \app f*v1/; \label{mil_fig_kleisli_f_app}
          \invoke v206/ \label{mil_fig_kleisli_result}
      \end{AVerb} 
    \end{minipage} \\
      \scap{mil_fig_kleisli_a} & \scap{mil_fig_kleisli_b}
  \end{tabular}
  \caption{Part~\subref{mil_fig_kleisli_a} shows a \lamC implementation
    of the monadic composition function (sometimes called ``Kleisli 
    composition''). Part~\subref{mil_fig_kleisli_b} shows a \mil 
    implementation of the same function.}
  \label{mil_fig_kleisli}
\end{myfig}

\intent{Explain how compiler changes strategy when translating a
  monadic expression.}  While the compiler follows the strategy above
when it first encountes a monadic expresssion, it changes strategy
when compiling binding statements that follow the initial monadic
expression. Instead of generating code that returns a suspended
computation, the compiler switches to generating code the invokes all
subsequent monadic values.

\intent{Show how the compiler translates a non-bind expression using
  |f v| in |kleisli|.}  The block \lab m205/ in
Figure~\ref{mil_fig_kleisli_b} (representing the body of the |kleisli|
function) illustrates this principle. Though |kleisli| ends with a
monadic expression (|f v|), it does not return a suspended computation
representing |f v|; it returns the result of executing |f v|. The
statement on Line~\ref{mil_fig_kleisli_f_app} evaluate \app f * v1/
and assigns the result to \var v206/. Crucially, the next line invokes
the thunk, immediately executing the program returned by \app f *
v1/. This is a case where the compiler generates code to execute a
sequence of monadic values, rather than code which returns a suspended
computation.

\section{Executing \mil Programs}
\label{mil_sec5}

\intent{Introduce \mil execution model.}  \Mil derives its syntax and
intention from three-address code, an intermediate form normally
associated with imperitave, procedural programming languages such as
C. Three-address code, like other register-transfer languages, closely
resembles assembly language code. The execution model for \mil draws on
its three-address code inspiration and executes like an
assembly-language for a simple register-based computer: execution
begins at a special designated point in the program and proceeds
sequentially. When the first block executed in the program
``returns,'' the program terminates.

\intent{Describe blocks as functions; argument scope; blocks always
  ``return.''}  Unlike assembly-language, \mil blocks also act like
functions. Each block declares arguments (\cc blocks have arguments in
their environment) and those names are only in scope over the
block. The value of the last statement in a given block is returned to
the block's caller. If that statement is a goto, enter (\enter),
\invoke/, or \milres case/ statement, then the return value of the
called block will become the return value of the current block.

\intent{Describe variable scope; storage locations are local.}  Within
each block, any number of storage locations may be named on the \lhs
of a bind (\mbind) statement. Those names are not global storage
locations: variables with the same name in differents blocks do not
affect each other. Values can only be passed from one block to another
as arguments, in a closure, or in a monadic thunk.

\intent{Describe control-flow on the \rhs of a bind.}  When an \enter,
\invoke/, or goto expression appears on the \rhs of a bind
statement, control-flow transfers to the appropriate block. For \enter
and \invoke/, the label stored in the closure or thunk determines the
block to execute. For goto, the block (or primitive) is named
directly. When the block returns a value, it will be assigned to the
storage location on the \lhs of the bind. The value returned must be
monadic, and in a type-correct program it always will be.

\intent{Describe our (lack of) error handling.}
\Mil's syntax does not mention error handling or exceptions at
all. However, errors can arise in a number of areas. For example, when
no case aleternatives match the inspected value, or if a block is
called with the wrong number of arguments. In these cases, and others,
an error would be generated by the \mil runtime or interpreter and the
program would terminate. We rely on the Habit compiler to avoid most
of these errors; the rest we ignore in the interest of simplicity.

\section{A \hoopl-friendly AST For \mil}
\label{mil_sec7}

\intent{Reminder about open/closed shapes.}  As described in
Section~\ref{hoopl_sec_cfg}, \hoopl characterizes control-flow between
nodes in a control-flow graph (\cfg) by their entry and exit
shape. \Hoopl uses the |O| and |C| types to express the shape of the
entry and exit points for a node. A node that is open on exit can only
be followed a node that is open on entry. A sequence of nodes can be
characterized by the entry shape of the first node and the exit shape
of the last node.

\intent{Reminder about relationship between basic blocks and shape.}
In \hoopl terms, basic blocks (described in Section~\ref{sec_back3})
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
shape, |C O|, shows that they can only be used to begin a \mil
block. The |Name| and |Label| arguments help \hoopl connect nodes
together in the \cfg.  The |Bind| statement (with shape |O O|)
represents statements inside the block. The type ensures no block
begins or ends with a |Bind|. Blocks can end with either a |CaseM| or
|Done| statement. The |CaseM| value represents the \milres case/
statement. |Done| does not appear explicitly in Figure~\ref{mil_fig3},
but the AST uses it to end a block with a |Tail| expression. The
|Name| and |Label| arguments to |CaseM| and |Done| make it easier to
know the basic block being analyzed when traversing the \cfg backwards.

\begin{myfig}
  \begin{minipage}{\linewidth}\begin{withHsLabeled}{mil_stmt_ast}\numbersoff
> data Stmt e x where
>   BlockEntry :: Name -> Label -> [Name] -> Stmt C O {-"\hslabel{block}"-}
>   CloEntry :: Name -> Label -> [Name] -> Name -> Stmt C O {-"\hslabel{ccblock}"-}
>   Bind :: Name -> Tail -> Stmt O O {-"\hslabel{bind}"-}
>   Case :: Name -> [Alt Tail] -> Stmt O C {-"\hslabel{case}"-}
>   Done :: Name -> Label -> Tail -> Stmt O C {-"\hslabel{done}"-}
  \end{withHsLabeled}\end{minipage}
  \caption{Haskell data type representing \mil \term stmt/ terms. The |C| and |O|
  types (from \hoopl) give the ``shape'' of each statement.}
  \label{mil_fig_stmt_ast}
\end{myfig}

\intent{Show how the AST mirrors the expected shape of a sample \mil
  block.}  Even without describing |Tail| values, we can show how
|Stmt| values give the correct shape to \mil blocks. Returning to our
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

|m205| defines a basic block, as shown by its |C C| type. \Hoopl
provides |mkFirst|, |mkMiddles| and |mkLast|
(Chapter~\ref{ref_chapter_hoopl}, Figure~\ref{hoopl_fig4}), for
lifting nodes into \hoopl's monadic graph representation. The operator
|<*>| connects pieces of the graph together. \Hoopl uses the |label|
argument to connect this definition to other basic blocks in a larger
program.

Figure~\ref{mil_fig_tail_ast} shows the various |Tail| values
that implement the \term tail/ terms in Figure~\ref{mil_fig3}. Notice
the definition does not parameterize on shape. These expressions are not
used to construct \cfgs and therefore did not need to be parameterized. 

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
  \caption{Haskell data type representing \mil \term tail/ expressions.}
  \label{mil_fig_tail_ast}
\end{myfig}

\intent{Show connection between \mil syntax and AST vis.\ arguments.}
All \mil \term tail/ terms that take arguments only allow variables,
not arbitrary expressions. The |Tail| constructors implement that
restriction by only taking |Name| arguments. Similarly, |Stmt|
constructors do not take any argument but |Names| or |Tails|.

\section{Related Work}

\subsection{Compiling with Continuations}

\intent{Describe criticisms by Kennedy against his \mil; compare to our \mil.}

\section{Summary}
\label{mil_sec6}

This chapter presented our Monadic Intermediate Language (\mil). Our
\mil resembles three-address code in several ways: infinitely many
registers can be named, nested expressions are not allowed, and
implementation details are made explicit. The \mil's unique features
include separate representations for \emph{closure-capturing} and
basic blocks, and the use of monadic \emph{tail} expressions. Later
chapters will be devoted to optimizing \mil programs using
dataflow techniques.

\standaloneBib

\end{document}

% LocalWords:  RTL Torczon Muchnick ANF MIL's dataflow Appel eq clo CompL invis
% LocalWords:  compclo stateful monad Monads Wadler monads eqn intra goto
