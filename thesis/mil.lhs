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

\section{Source Language}
\label{mil_src}

\intent{Introduce \lamC; where it came from, references, etc.}  We
call our source language ``MPEG'' and write its name as
\lamC. ``MPEG'' derives from ``Matches, Patterns, Expressions and
Guards,'' all features of \lamC. \lamC derives from the \lamA, with
syntactic (and semantic) elements borrowed from Haskell. In
particular, \lamC uses Haskell's notation for monadic bind (|<-|) and
|case| expressions. \lamC is itself one of the proposed intermediate
languages for the Habit programming language \citep{Habit2010}.

\intent{Excuse why we don't give semantics, etc. for \lamC.}
Our work focused on MIL, rather than \lamC, so we do not describe it
in detail here. The Habit ``Compilation Strategy''
\citep{HabitCompiler2010} report gives full details on
\lamC.\footnote{For simplicity's sake, we ignore two features of \lamC
  in this work: patterns and guards. Details on those elements can be
  found in the aforementioned report.} The report describes several
variations on MPEG: the language we describe corresponds to
``Normalized'' MPEG.

Figure~\ref{mil_fig_lam_syntax} gives the full syntax of \lamC. In the
figure, \term a/, \term b/, $\ldots$, \term v_1/, etc.\ represent simple
variables, not terms; however, \term t/, \term t_1/, etc.\ do represent
arbitrary terms. While most elements should be recognizable from
Haskell or the \lamA, the \emph{monadic bind} \eqref{lam_syntax_bind},
\emph{let} \eqref{lam_syntax_let} and \emph{primitive}
\eqref{lam_syntax_prim} terms bear further explanation.

\begin{myfig}
  \begin{tabular}{r@@{}lrl}
    \termrule def:|f v_1 {-"\dots"-} v_n = {-"\term term/"-}|:Definition/& \labeleq{lam_syntax_def}\eqref{lam_syntax_def} \\\\
    \termrule term:a, b, \ldots:Variables/ & \labeleq{lam_syntax_var}\eqref{lam_syntax_var} \\
    \termcase \lcabs x. \term t_1/:Abstraction/ & \labeleq{lam_syntax_abs}\eqref{lam_syntax_abs} \\
    \termcase \lcapp t_1 * t_2/:Application/ & \labeleq{lam_syntax_app}\eqref{lam_syntax_app} \\
    \termcase {\begin{minipage}[t]{\widthof{|case t_1 of x|}}
      |case t_1 of|\endgraf%%
      \quad \term alt_1/\endgraf%%
      \quad $\ldots$\endgraf%%
      \quad \term alt_n/%%
      \end{minipage}}:Case Discimination/ & \labeleq{lam_syntax_case}\eqref{lam_syntax_case} \\
    \termcase |v <- t_1; t_2|:Monadic Bind/ & \labeleq{lam_syntax_bind}\eqref{lam_syntax_bind} \\
    \termcase {\begin{minipage}[t]{\widthof{|let f_1 v_1 {-"\ldots"-} v_n = t_1|}}
        $\mathbf{let} \term def_1/$\endgraf%%
        $\phantom{\mathbf{let}}\ \ldots$\endgraf%%
        $\phantom{\mathbf{let}} \term def_n/$\endgraf
        $\mathbf{in}\ t$
    \end{minipage}}:Let/ & \labeleq{lam_syntax_let}\eqref{lam_syntax_let} \\
    \termcase \lcprim p*:Primitive/ & \labeleq{lam_syntax_prim}\eqref{lam_syntax_prim} \\
    \termcase \lccons C(v_1 \ldots v_n):Allocate Data/ & \labeleq{lam_syntax_cons}\eqref{lam_syntax_cons} \\\\
    \termrule alt:{|C v_1 {-"\ldots"-} v_n -> t|}:Alternative/& \labeleq{lam_syntax_alt}\eqref{lam_syntax_alt} 
  \end{tabular}
  \caption{The syntax of \lamC.}
  \label{mil_fig_lam_syntax}
\end{myfig}

\intent{Describe bind.}
A monadic bind expression, |v <- t_1; t_2|, states that the result of
the monadic computation, |t_1|, will be bound to |v|; |t_2| will then
be evaluated with |v| in scope. In this case, |v| can only be a
variable; \lamC does not support pattern-matching on the \lhs of a
bind. As we describe later in Section~\ref{mil_subsec_monad}, the
monadic context in which \term t_1/ is evaluated depends on the type
of the expression in Habit.

\intent{Describe let.}
The |let {-"\term def_1/, $\ldots$, \term def_n/"-} in t| term brings
the definitions given into the scope of \term t/. The definitions can
be values or functions\footnote{Technically, values are functions with
  zero arguments.}, and they can be recursive. However, Habit only
allows functions to be mutually-recursive.

\intent{Describe primitives.}
The primitive expression \lcprim p* treats \term p/ as if it were a
function. When the term appears alone, \lcprim p* acts as a function
with no arguments. Primitives can be pure or impure, but our syntax
does not distinguish them --- we rely on the Habit compiler to sort
out the difference.

\section{MIL's Purpose}
\label{mil_sec3}

An intermediate language always seeks to highlight some specific
implementation detail while hiding others in order to support certain
analysis, transformations or other goals such as portability or code
verification. We designed MIL such that intermediate values specific to
functional languages would be explicitly represented. We also designed MIL to
hide details about memory locations, stack management, and register
allocation. Exposing intermediate values gives us the chance to analyze and
eliminate them. Hiding implementation details makes the job of writing those
analysis and transformation programs simpler.

MIL's syntax and design borrow heavily from three-address code, an
intermediate form normally associated with imperative languages. Three-address
code represents programs such that all operations specify two operands and a
destination. Three-address code also hides details of memory management by
assuming infinitely many storage locations can be named and updated. For
example, the expression:

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

Three-address code emphasizes assignments and low-level operations, features
important to imperative languages. MIL emphasizes closures and side-effecting
computations, features important to functional languages.\footnote{Most
importantly, features important to a pure functional language like Habit.}
Though the operations supported by MIL differ from traditional three-address
code, the intention remains the same. For example, the previously given
expression can be written in Habit as:

\begin{singlespace}\correctspaceskip
> div (plus (mul b c) d) 2
\end{singlespace}

which can be implemented in MIL as:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4, linenumbers=left]
    \vbinds t_1 <- \mkclo[mul:b] \label{mil_arith_mul1}
    \vbinds t_2 <- \app t_1 * c/; \label{mil_arith_mul2}
    \vbinds t_3 <- \mkclo[add:t2]
    \vbinds t_4 <- \app t_3 * d/;
    \vbinds t_5 <- \mkclo[div:t5]
    \vbinds t_6 <- \app t_5 * 2/
  \end{AVerb}
\end{singlespace}

\noindent On Line~\ref{mil_arith_mul1}, \mkclo[mul:b] allocates a closure
pointing to \lab mul/ and capturing the value of the variable \var b/. On
Line~\ref{mil_arith_mul2}, we ``enter'' the closure represented by \var t1/
with  argument \var c/. This executes the multiplication and returns a result,
which we store  in \var t2/. These two lines show how MIL makes closure
allocation explicit. The monadic syntax (\bind) also hints at MIL treatments
of allocation as side-effect.

%% Syntax of MIL
\section{MIL Syntax}

Figure \ref{mil_fig3} gives the syntax for MIL.  A MIL program
consists of a number of \emph{blocks}. Blocks come in two types:
\emph{\cc} blocks \eqref{mil_syntax_cc} and basic blocks
\eqref{mil_syntax_block}. Though the syntax for closure blocks allows
any \term tail/, in practice they either return a closure
(\mkclo[k:v_1, \dots, v_n]) or jump to a block (\goto b(v_1, \dots,
v_n)). 

\input{mil_syntax}

Basic block bodies \eqref{mil_syntax_body} consist of a sequence of
statements that execute in order without any intra-block jumps or
conditional branches. Each basic block ends by evaluating a \term
tail/ or a conditional branch. A block body cannot end with a 
bind statement.

The bind statement \eqref{mil_syntax_body} can appear multiple
times in a block. Each binding assigns the result of the \emph{tail}
on the \rhs to a variable on the left. If a variable is
bound more than once, later bindings will shadow previous
bindings.

The \milres case/ statement \eqref{mil_syntax_case} examines a
discriminant and selects one alternative based on the value found. The
discriminant is always a simple variable, not an expresssion. Each
alternative \eqref{mil_syntax_alt} specifies a \emph{constructor} and
variables for each value held by the constructor. Alternatives always
jump immediately to a block --- they do not allow any other statement.

\emph{Tail} expressions represent effects -- they create monadic
values. \milres return/ \eqref{mil_syntax_return} takes a variable
(\emph{not} an expression) and makes its value monadic. The ``enter''
operator \eqref{mil_syntax_enter}, \enter, implements function
application, ``entering'' the closure represented by its \lhs with the
argument on its \rhs. The invoke operator \eqref{mil_syntax_invoke}
executes the thunk referred to by its argument.

The goto block \eqref{mil_syntax_goto} and goto primitive
\eqref{mil_syntax_prim} expressions implement labeled jumps with
arguments. In the first case, \lab b/ represents a labeled block
elsewhere in the program.  In the second, \lab p/\suptt* refers to
code that is implemented outside of MIL. Otherwise, primitives are
treated like blocks.

Closures and thunks are allocated similarly. Closure allocation
\eqref{mil_syntax_clo} creates a closure pointing the block labelled
\lab k/, capturing the variables $!+v_1, \dots, v_n+!$. Thunk
allocation \eqref{mil_syntax_thunk} behaves analogously.  The
constructor expression \eqref{mil_syntax_cons} creates a data value
with the given tag, $!+C+!$, and the variables $!+v_1, \dots, v_n+!$
in the corresponding fields.

\subsection{MIL Example: \lcname compose/}
To give a sense of MIL, consider the definition of \lcname compose/
given in Figure~\ref{mil_fig1a}. Figure~\ref{mil_fig1b} shows a
fragment of this expression in MIL. The \emph{block declaration} on
Line~\ref{mil_block_decl_fig1b} gives the name of the block (\lab
 compose/) and arguments that will be passed in (\var f/, \var g/, and
\var x/). Line~\ref{mil_gofx_fig1b} applies \var g/ to \var x/ and
assigns the result to \var t1/. The ``enter'' operator (\enter),
represents function application.
\footnote{So called because in the expression \app g * x/, we
  ``enter'' function \var g/ with the argument \var x/.}  We assume
\var g/ refers to a function (or, more precisely, a
\emph{closure}). The ``bind'' operator (\bind) assigns the result of
the operation on its right-hand side to the location on the left. In
turn, Line~\ref{mil_fofx_fig1b} applies \var f/ to \var t1/ and
assigns the result to \var t2/. The last line returns \var t2/. Thus,
the \lab compose/ block returns the value of
\lcapp f * (g * x)/, just as in our original \lamC expression.

\begin{myfig}[t]
  \begin{tabular}{c@@{\hspace{2em}}c}
    \lcdef compose()=\lcapp \lcabs f. \lcabs g. \lcabs x. f * (g * x)/; & 
    \input{lst_mil1} \\\\
    \scap{mil_fig1a} & \scap{mil_fig1b}
  \end{tabular} 
  \caption{Part~\subref{mil_fig1a} gives a \lamC definition of the composition
    function; \subref{mil_fig1b} shows a fragment of the MIL program
    for |compose|.}
  \label{mil_fig1}
\end{myfig}

\section{Monads \& MIL} 

\intent{Briefly describe what we mean by ``monad'' or ``monadic.'' Introduce
the idea of monadic values as computation.} As described by Wadler
\citeyearpar{Wadler1990}, \emph{monads} can be used distinguish \emph{pure}
and \emph{impure} functions. A \emph{pure} function has no side-effects: it
will not print to the screen, throw an exception, write to disk, or in any
other way change the observable state of the machine.\footnote{We mean
``observable'' from the program's standpoint. Even a pure  computation will
generate heat, if nothing else.} An \emph{impure} function may change the
machine's state in an observable way. In another sense, also described in the
same paper, a monadic value represents a \emph{computation}. Where a pure
function evaluates to a ``pure'' value that is immediately availabe, a monadic
function gives back a suspended computation that we need to execute before we
can get to the value ``inside'' the computation.


% All MIL programs execute in a monadic context. For example, we
% consider allocation impure, because it affects the machine's
% memory. Some runtime primitives have observable effects (like printing
% to the screen), making them impure. Dividing by zero typically causes
% a program to abort or throw an exception, making division an impure
% operation. Even addition can cause exceptions, due to overflow. 

% Pure operations include inspecting data values (i.e., with the |case|
% statement) or jumping to another location in the program (using
% application). 

% We designed MIL to support the Habit programming language; in
% particular, we rely on Habit to give meaning to the monadic context
% for each MIL operation. We further assume that the interpreter (or
% compiler) for MIL will implement underlying monadic primitives (e.g.,
% allocation, arithmetic, etc.).

%% \subsection{MIL \& Closures}
%% Closures

\intent{Illustrate allocation as a monadic effect in MIL. Contrast with
allocation as in invisible effect in \lamA.} Using Habit's call-by-value
evaluation strategy, we can compute the value of the expression \lcapp compose
* a * b * c/:

\begin{singlespace}\noindent
  \begin{math}\begin{array}{rlr}
      main &= \lcapp compose * a * b * c/ & \\
      &= \lcapp (\lcabs f. \lcabs g. \lcabs x. f * (g * x)) * a * b * c/ & \text{\emph{Definition of |compose|.}} \\
      &= \lcapp (\lcabs g. \lcabs x. a * (g * x)) * b * c/ & \text{\emph{E-App.}} \\
      &= \lcapp (\lcabs x. a * (b * x)) * c/ & \text{\emph{E-App.}} \\
      &= \lcapp a * (b * c)/ & \text{\emph{E-App.}} \\[-\baselineskip]
      \multicolumn{3}{l}{\hbox to .95\hsize{}}
    \end{array}\end{math}
\end{singlespace}

\noindent According to the rules in Figure~\ref{lang_fig6}, every
evaluation that results in a $\lambda$-function creates a new
value. Evaluating \lcapp compose * a * b * c/ creates two intermediate
values: \lcapp (\lcabs g. \lcabs x. a * (g * x))/ and \lcapp (\lcabs
x. a * (b * x))/. We can make intermediate values explicit by
assigning each to a new variable during evaluation:

\begin{singlespace}\noindent
  \begin{math}\begin{array}{rllr}
    \lcname main/ &= \lcapp compose * a * b * c/ \\
    &= \rlap{\lcapp (\lcabs f. \lcabs g. \lcabs x. f * (g * x)) * a * b * c/} & & \hfil\text{\emph{Definition of |compose|.}} \\
    &= \lcapp t_1 * b * c/ & \text{where\ } t_1 = \lcapp \lcabs g. \lcabs x. a * (g * x)/  & \hfil\text{\emph{E-App.}}\\
    &= \lcapp t_2 * c/ & \text{where\ } t_2 = \lcapp \lcabs x. a * (b * x)/ & \hfil\text{\emph{E-App.}}\\
    &= \lcapp a * (b * c)/ & & \hfil\text{\emph{E-App.}} \\[-\baselineskip]
    \multicolumn{4}{l}{\hbox to .95\hsize{}}
  \end{array}\end{math}
\end{singlespace}

Notice that we consumed one argument each to create \lcname t_1/ and
\lcname t_2/. That is, \lcname t_1/ results from applying \lcapp
(\lcabs f. \lcabs g. \lcabs x. f * (g * x))/ to \lcname a/, giving
\lcapp \lcabs g. \lcabs x. a * (g * x)/. Similarly, \lcname t_2/
results from applying \lcapp (\lcabs g. \lcabs x. a * (g * x))/ (i.e., \lcname
t_1/) to \lcname b/, giving \lcapp \lcabs x. a * (b * x)/.

Both \lcname t_1/ and \lcname t_2/ represent \emph{closures}. As
detailed in Section \ref{mil_subsec2}, a closure holds a pointer to a
body of code and any free variables. In this case, \lcname t_1/ holds
\lcname a/ and points to code that executes \lcapp \lcabs
g. \lcabs x. a * (g * x)/. In turn, \lcname t_2/ holds \lcname a/ and \lcname
b/, and it points to code that executes \lcapp \lcabs x. a * (b * x)/.

In \lamC, these intermediate closures are not explicitly represented
--- they are really a consequence of implementing function application. 
MIL, on the other hand, represents all of these values (and code fragements)
explicitly.

\begin{myfig}[t]
  \input{lst_mil2}
  \caption{The MIL program which computes $main =
    \lamApp{\lamApp{\lamApp{compose}{a}}{b}}{c}$. Note that $a$, $b$,
    and $c$ are assumed to be arguments given outside the program.}
  \label{mil_fig2}
\end{myfig}

Figure \ref{mil_fig2} shows the complete MIL program for \lcdef
main()= \lcapp compose * a * b * c/;. We call the blocks labeled \lab
k1/, \lab k2/ and \lab k3/ (lines \ref{mil_k1_fig2} --
\ref{mil_k3_fig2}) \emph{closure-capturing} blocks.\footnote{So called
  because they \emph{capture} arguments in a closure.}  As opposed to
\lab main/, these blocks create new closures. In the definition
\ccblock k1()f: \mkclo[k2:f], the braces on the left-hand side
represent variables expected in the closure given to this function. In
this case, \lab k1/ does not expect to find any variables. \var f/
names the argument given to \lab k1/. The right-hand side,
\mkclo[k2:f], shows the creation of a new closure. The closure points
to block \lab k2/ and captures the value of \var f/.  Evaluating \lab
k1/ returns a closure which can be used to execute \lab k2/. \lab k2/
expects an argument, \var g/, and a closure with one value (\var
f/). \lab k2/ returns a closure that points to \lab k3/ and contains
the variables \var f/ and \var g/: \clo[k3:f, g]. \lab k3/, however,
does something new. Instead of returning a closure, it executes the
\lab compose/ block (defined in Figure \ref{mil_fig1b}) with three
arguments: \var f/, \var g/, and \var x/. The value returned by \lab
k3/ will be the value computed by \lab compose/ with the arguments
given.

Returning to the \lab main/ block in Figure \ref{mil_fig2}, we can now
see how MIL makes explicit the intermediate closures created while
evaluating \lcapp compose * a * b * c/. On line \ref{mil_t1_fig2}, we
enter \lab k1/ with the first argument, \var a/ (remember, \app \lab
k1/ * a/ represents function application). The result on the \lhs of
the \bind, \var t1/, holds the closure returned. On the next line, we
enter \var t1/ (which will point to \lab k2/) with the second
argument, \var b/. \var t2/ then holds the closure returned. Finally,
on line \ref{mil_t3_fig2}, we enter \var t2/ (which will point to \lab
k3/) with the final argument, \var c/. \lab k3/ will directly execute
\lab compose/ with our arguments. \var t3/ holds the result returned
by \lab compose/. On the last line of \lab main/ we return the value
computed, \var t3/.

\subsection{Monadic Programs}

\intent{Contrast pure and monadic values.}  Consider the \lamC
functions in Figure~\ref{mil_fig_monadic}.\footnote{Some syntactic
  liberties have been taken here. \lamC only supports monadic binding,
  so ``|print 0|'' really represents ``|_ <- print 0|.'' Integers are not
  directly part of the language, either.} Neither takes any arguments
and they ostensibly produce the same number. Of course, the value
produced by the \emph{pure} function in
Part~\subref{mil_fig_monadic_pure} differs markedly from that produced
by the \emph{impure} function in
Part~\subref{mil_fig_monadic_comp}. 

\begin{myfig}
  \begin{tabular}{cc}
    |f = 1| & 
    \begin{minipage}{\widthof{|do {print "hello";}|}}
> m = do 
>   print 0
>   return 1
    \end{minipage} \\
    \scap{mil_fig_monadic_pure} & \scap{mil_fig_monadic_comp}
  \end{tabular}
  \caption{}
  \label{mil_fig_monadic}
\end{myfig}

\intent{Introduce monadic thunks.}  Intuitively, |f| returns an
integer, but |m| returns a \emph{computation}. We call this
computation a \emph{monadic thunk}, as coined in the Habit Compiler
Report \citep{HabitComp2010}. Traditionally, thunks have represented
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
\lab m201/. \lab m201/ represents the body of |hello|; it calls
primitives which we elide. The \lab main/ block, however, shows how we
invoke the thunk returned by \lab hello/. On
Line~\ref{mil_fig_get_hello1}, \lab hello/ is called, and the thunk
returned is bound to the variable \var v207/. On the next line, the
thunk is invoked. Lines~\ref{mil_fig_get_hello2} and
\ref{mil_fig_invoke_hello2} show the same operation again. In other
words, \lab main/ executes the \lab hello/ function twice, producing
an effect each time.

\begin{myfig}
  \begin{tabular}{cc}
    \begin{minipage}{\widthof{|hello = print "hello"|}}
> hello = do
>   print 0
>
> main = do
>   hello
>   hello
    \end{minipage} &
    \begin{minipage}{\widthof{\ \ \binds \_ <- \invoke v207/;}}
      \begin{AVerb}[gobble=8,numbers=left]
        \block hello(): \mkthunk[m201:] \label{mil_fig_thunk_hello}
        \block m201():
          \ldots

        \block main(): 
          \vbinds v207 <- \goto hello(); \label{mil_fig_get_hello1}
          \vbinds \_ <- \invoke v207/; \label{mil_fig_invoke_hello1}
          \vbinds v206 <- \goto hello(); \label{mil_fig_get_hello2}
          \vbinds \_ <- \invoke v206/; \label{mil_fig_invoke_hello2}
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
``Kleisli,'' \citep{KleisliXX} composition function. Part~\subref{mil_fig_kleisli_b}
shows the corresponding MIL code. The blocks \lab k201/, \lab k202/, and \lab k203/
progressively capture the arguments to |kleisli|. \lab b204/ constructs
the thunk for |kleisli|, but only after all arguments have been captured. 

\begin{myfig}
  \begin{tabular}{c}
    \begin{minipage}{\widthof{|kleisli f g x = do|}}
> kleisli f g x = do
>   v <- g x
>   f v
    \end{minipage} \\
    \scap{mil_fig_kleisli_a} \\
    \begin{minipage}{\widthof{\ \ \block b204 (g, x, f): \mkthunk[m205:g, x, f]}}
      \begin{AVerb}[gobble=8,numbers=left]
        \block kleisli(): \mkclo[k201:]
        \ccblock k201()f: \mkclo[k202:f]
        \ccblock k202(f)g: \mkclo[k203:g, f]
        \ccblock k203(g, f)x: \goto b204(g, x, f)
        \block b204(g, x, f): \mkthunk[m205:g, x, f]

        \block m205(g, x, f):
          \vbinds v207 <- \app g * x/;
          \vbinds v1 <- \invoke v207/;
          \vbinds v206 <- \app f * v1/; \label{mil_fig_kleisli_f_app}
          \invoke v206/ \label{mil_fig_kleisli_result}
      \end{AVerb}
    \end{minipage} \\\\
    \scap{mil_fig_kleisli_b} \\
  \end{tabular}
  \caption{Part~\subref{mil_fig_kleisli_a} shows a monadic composition function 
    (also known as ``Kliesli'' composition). Part~\subref{mil_fig_kleisli_b} shows
  a MIL program representing the same function.}
  \label{mil_fig_kleisli}
\end{myfig}

\section{Evaluating MIL Programs}
\label{mil_sec5}

\section{Compiling \lamC to MIL}
\label{mil_sec4}

\intent{Explain why we don't show the whole compiler.}
Compilers translating the \lamA to executable (or intermediate) forms
have existed for decades, and our work did not seek to advance
knowledge in this area. However, some nuances of our translation should be
highlighted, especially concering $\lambda$-abstractions.

\intent{Show how $\lambda$-abstractions are translated.}  Consider
again the definition of |compose| in Figure~\ref{mil_fig1a} on
Page~\pageref{mil_fig1}. Our compiler translates each $\lambda$,
except the last, to a block that returns a closure. The final
$\lambda$ translates to a block that immediately jumps to the the
implementation of the function. This gives the sequence of blocks
shown in Figure~\ref{mil_fig2} on Page~\pageref{mil_fig2} (excepting
\lab main/, of course).

\intent{Point out how we rely on uncurrying to make this code performant.}
This strategy produces code that does a lot of repetitive work. When
fully applied, a function of $n$ arguments will create $n - 1$
closures, perform $n - 1$ jumps between blocks, and copy arguments
between closures numerous times. Our uncurrying optimization
(Chapter~\ref{ref_chapter_uncurrying}) can collapse this work to 1
closure, 1 jump and no argument copying in many cases. Therefore,
generating simple (and easy to analyze code) seems reasonable.

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

\intent{Show how the compiler translates a non-bind expression using
  |f v| in |kleisli|.}  The translation of |kleisli| in
Figure~\ref{mil_fig_kleisli_b} illustrates this principle. |kleisli|
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

\intent{Enumerate the various shape combinations and connect to basic
  blocks.}  An |O O| (``open/open'') node has exactly one predecessor
and one successor. An |O O| node must appear in the middle of a basic
block --- it cannot be the target of multiple predecessors, therefore
it cannot be the target of a jump or branch. A |C O| (``closed/open'')
node can have multiple predecessors but only one successor. A |C O|
node can start a basic block, but it must always be followed by at
least one node. An |O C| (``open/closed'') node can only have one
predecessor, but many successors. An |O C| node always ends a 
basic block. A |C C| (``closed/closed'') node is not very useful on
its own; however, a |C C| sequence of nodes forms a basic block.

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
  \begin{minipage}{\linewidth}\begin{withHsLabeled}{mil_stmt_ast}
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
example of Kleisli composition in Figure~\ref{mil_fig_kleisli} on Page~\pageref{mil_fig_kleisli}, we can
represent the block \lab m205/ with the following definition:

\begin{singlespace}\correctspaceskip
  \begin{minipage}{\widthof{|BlockEntry "m205" "m205" ["g", "f", "x"] <*>|\quad}}
> m205 :: Label -> Graph Stmt C C
> m205 label = mkFirst (BlockEntry "m205" label ["g", "f", "x"]) <*>
>   mkMiddles [Bind "v207" ({-"\app g * x/"-})
>             , Bind "v1" ({-"\invoke v209/"-})
>             , Bind "v206" ({-"\app f * v1/"-})] <*>
>   mkLast (Done "m205" label ({-"\invoke v206/"-}))
  \end{minipage}
\end{singlespace}

|m205| defines as basic block, as shown by its |C C| type. Hoopl
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
\milres invoke/ \eqref{mil_syntax_invoke} and |Constr| represents a
constructor \eqref{mil_syntax_cons}.

\begin{myfig}[tb]
  \begin{minipage}{\linewidth}\begin{withHsLabeled}{mil_tail_ast}
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
not arbitrary expressions. The |Tail| constructors implement taht
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
