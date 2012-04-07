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

Our monadic intermediate language (\mil),
specifically supports functional language features, but also follows
the form of three-address code, an intermediate language more
associated with imperative languages. \Mil directly supports function
application and abstraction. All intermediate values are named. \Mil 
specifies evaluation order and separates stateful computation using a
monadic programming style. \Mil's syntax enforces basic-block structure
on programs, making them ideal for dataflow analysis.

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

\section{\Mil's Purpose}
\label{mil_sec3}

\intent{Remark on intermediate languages and \mil's focus.} An
intermediate language always seeks to highlight some specific
implementation detail while hiding others in order to support certain
analysis and transformation goals. Exposing intermediate values gives
us the chance to analyze and eliminate them. Hiding implementation
details makes the job of writing those analyses and transformations
simpler.

\intent{Relate \mil to three-address code.} \Mil's syntax and design
borrow heavily from three-address code, an intermediate form normally
associated with imperative languages. Three-address code represents
programs such that all operations specify two operands and a
destination. Three-address code also hides details of memory
management by assuming that infinitely many storage locations can be
named and updated. For example, the expression:

\begin{singlespace}\correctspaceskip
  \begin{equation*}
    \frac{(b * c + d)}{2},
  \end{equation*}
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

\intent{Highlight focus of \mil (closure allocation).} Three-address
code emphasizes assignments and low-level operations, features
important to imperative languages. \Mil emphasizes allocation and
side-effecting computations, features important to functional
languages.\footnote{Most importantly, features important to a pure
  functional language like Habit.} Though the operations supported by
\mil differ from traditional three-address code, the intention remains
the same: hide some details while exposing those we care about.

For example, the previously given expression can be written in Habit
as:

\begin{singlespace}
\begin{center}
> div (plus (mul b c) d) 2,
\end{center}
\end{singlespace}

\noindent and implemented in \mil as:

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
\noindent Line~\ref{mil_arith_mul1} shows \mil's emphasis on
allocation. \mkclo[mul:b] allocates a closure pointing to \lab mul/
and capturing the value of the variable \var b/. We make allocation of
closures a monadic, side-effecting operation by placing \mkclo[mul:b]
on the \rhs of the monadic binding operator (\mbind). However, we do
not need to mention the actual address of the locaton \var t_1/, \var
b/ or even \lab mul/ --- those details are hidden. On
Line~\ref{mil_arith_mul2}, we represent function application with the
``enter'' operator, \enter. Line~\ref{mil_arith_mul2} executes the
multiplication and returns a result, which we store in \var
t_2/. Though \mil represents function application explicitly, we hide
implementation details such as stack operations or register spilling. The
rest of the program executes similarly.

%% Syntax of MIL
\section{\Mil Syntax}
\label{mil_syntax}

\intent{Introduce \mil syntax.}  Figure \ref{mil_fig3} gives the syntax
for \mil. Where the term \var v_1/, etc. appears, only simple variables
are allowed.  This includes most terms in the language, staying true
to the design of three-address code. Bold terms such as \lab b/, \lab
k/, and \lab m/ represent labeled locations in the \mil program. \var
C/ represents the name of a data constructor. Bold text such as
\milres case/ and \milres invoke/ represent \mil keywords. A \mil
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
effects and always appear on the \rhs of a \mbind statement or at the
end of a basic block. \milres return/ takes a variable (\emph{not} an
expression) and makes its value monadic. The ``enter'' operator,
\enter, implements function application, ``entering'' the closure
represented by its \lhs with the argument on its \rhs. The \milres invoke/
operator executes the thunk referred to by its argument (thunks are
described in Section~\ref{mil_thunks}).

\intent{Describe goto for blocks and primitives.}  The goto block and
goto primitive expressions implement labeled jumps with arguments. In
the first case, \lab b/ represents a labeled block elsewhere in the
program.  The primitive term, \lab p/\suptt*, is also bolded but does
not strictly represent a labeled location. Rather, it is treated as a
labeled location that is implemented outside of \mil. Otherwise,
primitives are treated like blocks.

\intent{Describe closure and thunk allocation.} Closure allocation
creates a closure pointing the block labelled \lab k/, capturing the
variables $!+v_1, \dots, v_n+!$. A thunk, details for which can be
found in Section~\ref{mil_thunks}, is allocated
similarly. The constructor expression creates a data value with the
given tag, $!+C+!$, and the variables $!+v_1, \dots, v_n+!$ in the
corresponding fields.

\subsection{\Mil Example: \lcname compose/}
\intent{Show an LC program and its translation in \mil.}  To give a
sense of \mil, consider the definition of \lcname compose/ given in
Figure~\ref{mil_fig1a}. Figure~\ref{mil_fig1b} shows a \mil program
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

As described by Wadler \citeyearpar{Wadler1990}, \emph{monads}
can be used distinguish \emph{pure} and \emph{impure} functions. A
\emph{pure} function has no side-effects: it will not print to the
screen, throw an exception, write to disk, or in any other way change
the observable state of the machine.\footnote{We mean ``observable''
  from the program's standpoint. Even a pure computation will generate
  heat, if nothing else.} An \emph{impure} function may change the
machine's state in an observable way. We will use a monadic form
of |compose| to make closure allocation an impure, effectual operation.

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
|compose|. However, in \mil a closure-capturing block cannot do
anything but allocate another closure or jump to a block. Therefore,
in Figure~\ref{mil_fig2}, \lab k2/ refers to \lab k3/, which then
jumps to \lab compose/.

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
before we can get to the value ``inside'' the computation.

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
    \begin{minipage}{1.5in}\disableoverfull
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

\intent{Show how \mil thunks are used.}  To illustrate, consider the
\lamC functions in Figure~\ref{mil_fig_hello_a}.\footnote{Again, some
  syntactic liberties are taken.} Part~\subref{mil_fig_hello_b} shows
the corresponding \mil code for each. On
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
    \end{minipage} &     
    \begin{minipage}[t]{\widthof{\ \ \binds \_ <- \invoke v207/;}}
      \begin{AVerb}[gobble=8,numbers=left]
        \block hello(): \mkthunk[m:] \label{mil_fig_thunk_hello}
        \block m():
          \ldots
      \end{AVerb} 
    \end{minipage} \\
    \begin{minipage}[t]{\widthof{|hello = print "hello"|}}
> main = do
>   hello
>   hello
    \end{minipage} &
    \begin{minipage}[t]{\widthof{\ \ \binds \_ <- \invoke v207/;}}
      \begin{AVerb}[gobble=8,numbers=left]
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
    functions. The \mil blocks that create and use monadic thunks to
    execute |main| are shown in Part~\subref{mil_fig_hello_b}.}
  \label{mil_fig_hello}
\end{myfig}

\intent{Monadic thunks are like closures; but \cc blocks for thunks do
  not exist.}  Thunks can capture variables just like closures, but
unlike closures they are not progressively ``built up'' across
multiple blocks. Figure~\ref{mil_fig_kleisli} illustrates this
concept. Part~\subref{mil_fig_kleisli_a} shows the monadic, or
``Kleisli,'' composition function. Part~\subref{mil_fig_kleisli_b}
shows the corresponding \mil code. The blocks \lab k201/, \lab k202/,
and \lab k203/ progressively capture the arguments to |kleisli|. \lab
b204/ constructs the thunk for |kleisli|, but only after all arguments
have been captured. The block \lab m205/ implements the body of
|kleisli| and is shown in Figure~\ref{mil_fig_kleisli_body} rather
than here.

\begin{myfig}
  \begin{tabular}{cc}
    \begin{minipage}[t]{2in}\disableoverfull
> kleisli f g x = do
>   v <- g x
>   f v
    \end{minipage} & \begin{minipage}[t]{\widthof{\ \ \block b204 (g, x, f): \mkthunk[m205:g, x, f]}}\disableoverfull
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
  a \mil program representing the same function.}
  \label{mil_fig_kleisli}
\end{myfig}

\section{Compiling \lamC to \mil}
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
\lab main/, of course), and allows \mil to support partial application.

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
  \caption{The \mil implemention of the |kleisli| function from
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
