\documentclass[12pt]{report}
%include polycode.fmt
\input{preamble}
\begin{document}
\input{document.preamble}

\chapter{Compiling to a Monadic Intermediate Language}
\label{ref_chapter_mil}

%% Compiling the lambda calculus - fundamentals

%% MIL and Three Address Code

%% * Motivate intermediate languages; motivate MIL thorugh three-address
%%     code.
%%    a. Describe details specific to functional languages

%% What makes MIL cool and interesting? How is it unique? Why did
%% we pick the features it has?
%%
%%  * Make curried function application explicit.
%%  * Make allocation explicit.
%%  * Make basic-blocks the default.
%%

%% Syntax/Examples of MIL

%% Compiling LC to MIL
%% Compiling lambda-c to MIL. 
%%    a. Closures, environments.

%% Evaluating MIL (?)  

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

Section~\ref{mil_sec1} describes closures, a fundamental data
structure used to implement functional languages. We then describe
``three-address code,'' the intermediate form from which MIL partly
derives, in Section~\ref{mil_sec2}.  MIL syntax and examples follow in
Section~\ref{mil_sec3}. Section~\ref{mil_sec4} shows our compiler for
translating \lamC to MIL. We sketch how MIL programs can be evaluated
in Section~\ref{mil_sec5}, using the same structural operational
semantics (SOS) style as in
Chapter~\ref{ref_chapter_languages}. Section \ref{mil_sec7} shows
how Hoopl influenced the implementation the MIL language from Chapter
\ref{ref_chapter_mil} and discusses the design choices we made.

%% Examples of intermediate forms: SSA, RTL, a-normal, bytecode

%% MIL overture

%% Plan of the chapter

%% This chapter describes our intermediate language, MIL

%% Our intermediate language, MIL (``monadic intermediate language''),
%% directly supports several concepts fundamental to functional language
%% compilers. 

%% We describe our intermediate language, MIL (``monadic intermediate language''). Before
%% introducing MIL, however, we first discuss  

\section{Closures}
\label{mil_sec1}

Closures are the fundamental data structures used to implement
functional languages. A closure always results when a function value is
created. They may not have the exact form described here but they
always have the same purpose: they pair a location with a list of
values. The location tells where to find the code implementing the
body of the function. The list of values defines the environment in
which the code will execute. 
\footnote{The values are not necessarily stored in the immediate
  environment. For example, static links (described by
  \citet[pg.~125]{Appel2003}) might be used to implement a chain of
  environments. In any case the environment is always used to find
  values for arguments, so we say they ``can be located'' in the
  environment.} 

For example, consider the value created when we apply the |compose|
function to two arguments:
\begin{equation}
  \begin{split}
    t_1 &= \lamApp{compose}{\lamApp{a}{b}} \\
    &= \lamAPp{\lamCompose}{\lamApp{a}{b}} \\
    & \dots \\
    t_1 &= \lamAbs{x}{\lamApP{\lamSubst{a}{f}}{\lamApp{\lamSubst{b}{g}}{x}}}.
  \end{split}\label{mil_eq1}
\end{equation}
The result of Expression~\eqref{mil_eq1}, $t_1$, is itself a
function. We say $x$ is \emph{bound},
because it is given as an argument, and that $f$ and $g$ are
\emph{free} because they are not arguments (i.e., no
$\lambda$-abstraction mentions them). The notation \lamSubst{a}{f} in
$t_1$ means we substitute the value $a$ for the argument $f$. This
lets us keep track of the original name of the argument as well as the
value given for it.

\begin{myfig}
  \begin{tabular}{m{1in}m{4in}}
    \scap{mil_fig4a} & \begin{minipage}{4in}\vbox to .75in {\vss\hbox to \textwidth{\hss
      \begin{tikzpicture}[remember picture, overlay]
        \newbox\clobox
        \tikzstyle{clo}=[draw]
        \begin{pgfinterruptpicture}
          \global\setbox\clobox=\hbox{\normalfont\sc CompL}
        \end{pgfinterruptpicture}

        \node[clo,minimum height=3\ht\clobox] (compclo_l) {\sc CompL}; 
        \node[clo,minimum height=3\ht\clobox, right=0.2in of compclo_l] (compclo_f) {$a$}; 
        \node[clo,minimum height=3\ht\clobox, right=0.0in of compclo_f] (compclo_g) {$b$};
        \draw (compclo_l.east) -- (compclo_f.west);

      \end{tikzpicture}\hss}\vss}
    \end{minipage} \\
      \scap{mil_fig4b} & \tikz[remember picture,overlay]{\node[invis] (comp_l) {}; \draw[->] (compclo_l.west) -|| (comp_l.north) ;}\text{\sc CompL}:\ %%
      \lamAbs{f}{\lamAbs{g}{\lamAbs{x}{%%
            \lamApp{\tikz[remember picture,overlay]{\node[invis] (comp_f) {\phantom{\fbox{f}}}; \draw[->] (comp_f.north) -- (compclo_f.south);}\fbox{f}}%%
                   {(\lamApp{\tikz[remember picture,overlay]{\node[invis] (comp_g) {\phantom{\fbox{g}}}; \draw[->] (comp_g.north) -- (compclo_g.south);}\fbox{g}}%%
                     {x})}}}}.
  \end{tabular}
  \caption{\subref{mil_fig4a}
    shows the closure representing function value
    \lamAbs{x}{\lamApP{\lamSubst{a}{f}}{\lamApp{\lamSubst{b}{g}}{x}}}. The
    definition of |compose| is given in \subref{mil_fig4b}. Arrows
    from variables to their position in the closure show how argument
    values are accessed when the function is evaluated.}
  \label{mil_fig4}
\end{myfig}

The value referred to by $t_1$ will be a
closure. Figure~\ref{mil_fig4} shows this closure and the original
definition of |compose|. Figure~\ref{mil_fig4b} attaches the label
\textsc{CompL} to the body of |compose|, suggesting that |compose|
appears at fixed location in our program. The closure refers to the
body of the |compose| function using \textsc{CompL}. The closure also
holds values for the free variables $f$ and $g$. The arrows from $f$
and $g$ show how the body of the function refers to fixed locations in
the closure. In this case, the $x$ argument does not have an arrow
since only $f$ and $g$ are free in $t_1$. When $t_1$ is applied to an
argument, the implementation of |compose| will be able to refer to
fixed locations within the closure to find the arguments originally
supplied (i.e., $a$ and $b$).

Closures are the ``value'' created by $\lambda$-abstractions. That is,
when a function evaluates to a $\lambda$, a closure results. The
closure refers to the location of the body of the $\lambda$ using a
label, address or symbolic name. The closure also holds the current
values for all free variables in the body of the $\lambda$. The code
implementing the body of the $\lambda$ refers to fixed locations
within the closure to find the values of free variables when that
code executes.

%% When the compiler generates code that implements the |compose| function,
%% it ensures that the closure is constructed such that the function
%% can execute with the correct arguments. One strategy the compiler can
%% use is to put the function's arguments in the same location within the
%% closure, simplifying the code in the function's body for locating
%% arguments.

%% can use is to put the function's arguments
%% in the same location within the closure, simplifying the code in the
%% function's body for locating arguments.  

%% \subsection{Variables}
%% \label{mil_subsec1}

%% A variable names a value -- in essence, it associates some storage
%% location with a name, allowing our program to use a consistent label
%% for some location. Our compiler must be able to associate names with
%% locations. For example, consider this function (a fragment of the
%% |compose| function given in Expression~\ref{lang_eq_const1}):
%% \begin{equation}
%%   \lamAbs{x}{\lamApP{f}{\lamApp{g}{x}}}.  \label{mil_eq1}
%% \end{equation}
%% We see three variables: $f$, $g$, and $x$. We say $x$ is \emph{bound},
%% because it is given as an argument, and that $f$ and $g$ are
%% \emph{free} because, in this context, they are not arguments in a 
%% $\lambda$-abstraction. To evaluate this expression, though, we need
%% a way to find the values of these terms.  

%% We can describe where to find $f, g$ and $x$ in terms of memory
%% locations. We can say that $x$ will appear in a special location,
%% |arg|, because it is the argument to the function and we will always
%% put arguments in the same place. We can further say that another
%% special location, |clo|, will have two
%% slots. The first will contain $g$ and the second will contain
%% $f$. Conceptually, then, our expression can be represented as:
%% \begin{center}
%%   \begin{tabular}{c}
%%     \begin{math}\begin{aligned}[b]
%%       |arg| &= x, \\
%%       |clo|[0] &= g, \\
%%       |clo|[1] &= f 
%%     \end{aligned}\text{\ in}\end{math} \\
%%     \lamAbs{|arg|}{\lamApp{|clo|[1]}{\lamPApp{|clo|[0]}{arg}}}.
%%   \end{tabular}
%% \end{center}

%% \par
%% In general, the $|clo|$ location holds the \emph{environment} for our
%% expression. For any given expression, we will be able to find all the
%% free variables (i.e., all those except the argument) in the
%% environment. The compiler will be responsible for ensuring the correct
%% environment is available whenever a given expression is evaluated.

%% Our machine, then, must have instructions for storing and retrieving
%% values. #Store# and #Load# (from Table \ref{tbl_mil1}) serve this
%% purpose. 

%% \subsection{Function Application}
%% \label{mil_subsec2}

%% Associating locations with names is not enough, however. Looking again
%% at expression \ref{mil_eq1}, $g$ clearly represents a function to
%% which we pass the argument $x$. To compute the value of
%% $\lamPApp{g}{x}$, we must be able to execute the code representing
%% $g$. We already assigned a storage location for $g$ ($|clo|[0]$) -- now
%% we just say that the value in $|clo|[0]$ is a \emph{label} that tells
%% us where to find the code representing $g$. However, $g$ will need
%% an environment of its own, to hold any free variables for $g$. Therefore,
%% we pair the label indicating where to find $g$ with a list of free
%% variables. We call this structure a \emph{closure}.

%% Closures are the fundamental data structures used to compile
%% functional languages. They may not have the exact form described here
%% but they always have the same purpose: they pair a label with the free
%% variables used in the function represented. 

%% \subsection{Abstraction}
%% \label{mil_subsec3}
%% The \lamA lets us define functions which return new functions. We have
%% seen how to access variables in the environment and how to execute
%% unknown functions using closures. Now we come to the final element
%% needed to compile the \lamA\ -- creating closures.

%% Consider the following expression, where we apply the $|const|$ function (expression 
%% \ref{mil_eq4}) to an argument:
%% \begin{equation}
%%   \begin{split}
%%     |main| &= \lamApp{|const|}{s} \\
%%          &= \lamAppP{\lamAbs{a}{\lamAbs{b}{a}}}{s}.
%%   \end{split}
%% \end{equation}
%% In order to evaluate $|main|$, we need to apply the $|const|$ function
%% to $s$. From the previous section we know that a closure is required to
%% implement function application. It follows that
%% \lamAbs{a}{\lamAbs{b}{a}} must create a closure which will
%% then be used to execute the body of the $\lambda$-abstraction with the
%% argument $s$. In fact, the ``value'' created by a
%% $\lambda$-abstraction is always a closure. The closure will point to
%% the body of the $\lambda$-abstraction and will hold the free variables
%% necessary to evaluate it.

\section{Three-address Code}
\label{mil_sec2}

Three-address code represents programs in a form similar to assembly
language, where named registers represent storage locations. Each
instruction in the translated program has two operand registers and
one destination register, thus the name ``three-address.'' Infinitely
many registers are available, making them more like memory locations
than registers in real hardware.

Three-address code makes all intermediate expression values explicit, 
by reducing complicated expressions to a series of assignments. 
For example, the expression:
\begin{equation}
  a = \frac{(b * c + d)}{2},
\end{equation}
would be expressed in three-address code as:
\begin{AVerb}
  s = b * c;
  t = s + d;
  a = t / 2;
\end{AVerb}
where !+s+! and !+t+! are new temporaries created by the compiler. This 
representation makes it easier for the compiler to re-order expressions,
unravel complex control-flow, and manipulate intermediate values. 

Three-address code intends to simplify the analysis of programs while
not revealing all details of the underlying hardware. Three-address
code accomplishes these goals by reducing the all expressions to a
uniform representation, exposing the intermediate values (and thus,
memory operations) created while expressions are evaluated. It hides
some details by deferring decisions about the actual location of
values to some later stage of compilation. Finally, three-address code
programs are easy to represent as basic blocks, which makes
control-flow analysis much simpler.

\section{Monadic Intermediate Language}
\label{mil_sec3}

Our intermediate language, MIL, serves the same purpose as any
intermediate language: it simplifies the analysis of programs (for
certain characteristics), while hiding details of the underlying
hardware. MIL shares some of the same goals as three-address code, and
accomplishes them in similar ways: programs are organized into basic
blocks; all intermediate values are named; precise details of
registers and memory locations used are deferred. In contrast to
three-address code, however, our language supports features unique to
functional languages: the ability to treat functions as first-class
values, and the representation of stateful computations in a monad.

\subsection*{Monads \& Functional Programming}
As described by \citet{Wadler1990}, \emph{monads} can be used
distinguish \emph{pure} and \emph{impure} functions. A \emph{pure}
function has no side-effects: it will not print to the screen, throw
an exception, write to disk, or in any other way change the observable
state of the machine. An \emph{impure} function may change the
machine's state.

%% Presentation drawn from http://en.wikipedia.org/wiki/Monad_%28functional_programming%29, 
%% accessed April 6 2010.
A \emph{monad} provides the abstraction that separates pure and impure
functions. Impure (or ``monadic'') functions execute ``inside'' the
monad. Values returned from a monadic function are not directly
accessible -- they are ``wrapped'' in the monad. The only way
to ``unwrap'' a monadic value is to execute the computation -- inside
the monad! 

\subsection*{The Monad in MIL}

When designing MIL we wished to make all memory allocation
explicit. Besides the obvious effect of reducing free memory
available, allocation can also cause two other effects: the allocation
may fail, or a garbage-collection may occur. A monad allows us to
separate computations which (potentially) allocate memory from those
that do not.

\subsection*{MIL Example: $compose$}

To give a sense of MIL, consider the definition of $compose$ given in
Figure~\ref{mil_fig1a}. Figure~\ref{mil_fig1b} shows a fragment of this 
expression in MIL. The \emph{block declaration}
on Line~\ref{mil_block_decl_fig1b} gives the name of
the block (!+compose+!) and arguments that will be passed in (!+f+!, !+g+!,
and !+x+!). Line~\ref{mil_gofx_fig1b} applies !+g+! to !+x+! and assigns
the result to !+t1+!. The ``enter'' operator (!+@@+!), represents function application.
\footnote{So called because in the expression !+g @@ x+!, we ``enter''
  function !+g+! with the argument !+x+!.}  We assume !+g+! refers to a
function (or, more precisely, a \emph{closure}). The ``bind'' operator
(!+<-+!) assigns the result of the operation on its right-hand side to
the location on the left. In turn, Line~\ref{mil_fofx_fig1b} applies
!+f+! to !+t1+! and assigns the result to !+t2+!. The last line returns
!+t2+!. Thus, the !+compose+! block returns the value of
\lamApPp{f}{\lamApp{g}{x}}, just as in our original \lamA expression.

\begin{myfig}[t]
  \begin{tabular}{cc}
    $compose = \lamCompose$ & 
    \input{lst_mil1} \\
    \scap{mil_fig1a} & \scap{mil_fig1b}
  \end{tabular} 
  \caption{\subref{mil_fig1a} gives a \lamA definition of the composition
    function; \subref{mil_fig1b} shows a fragment of the MIL program
    for $compose$.}
  \label{mil_fig1}
\end{myfig}

%% Closures

However, according to rules in Figure~\ref{lang_fig6},
Chapter~\ref{ref_chapter_languages} on page~\pageref{lang_fig6},
evaluating an expression which applies $compose$ actually involves the
creation of several intermediate values. Consider the expression
\begin{equation}
  main = \lamApp{\lamApp{\lamApp{compose}{a}}{b}}{c}, \label{mil_eqn4}
\end{equation}
where $a$, $b$ and $c$ are given values elsewhere. Using the
rules for call-by-value evaluation order from Figure~\ref{lang_fig6} in 
Chapter \ref{ref_chapter_languages}, we can compute the value of the expression
as follows:
\begin{align*}
  main &= \lamApp{\lamApp{\lamApp{compose}{a}}{b}}{c} \\
  &= \lamApp{\lamApp{\lamAPp{\lamCompose}{a}}{b}}{c} & \text{\emph{Definition of |compose|.}} \\
  &= \lamApp{\lamAPp{\lamAbs{g}{\lamAbs{x}{\lamApP{a}{\lamApp{g}{x}}}}}{b}}{c} & \text{\emph{E-App.}} \\
  &= \lamAPp{\lamAbs{x}{\lamApP{a}{\lamApp{b}{x}}}}{c} & \text{\emph{E-App.}} \\
  &= \lamApP{a}{\lamApp{b}{c}}. & \text{\emph{E-App.}} 
\end{align*}

We can capture each intermediate value created when evaluating this
expression by assigning each result to a new variable. 

\begin{align*}
  main &= \lamApp{\lamApp{\lamApp{compose}{a}}{b}}{c} \\
  &= \lamApp{\lamApp{\lamAPp{\lamCompose}{a}}{b}}{c} & \text{\emph{Definition of |compose|.}} \\
  t_1 &\leftarrow \lamAbs{g}{\lamAbs{x}{\lamApP{a}{\lamApp{g}{x}}}} & \text{\emph{Result of E-App.}}\\
  &= \lamApp{t_1}{\lamApp{b}{c}} \\
  t_2 &\leftarrow \lamAbs{x}{\lamApP{a}{\lamApp{b}{x}}} & \text{\emph{Result of E-App.}} \\
  &= \lamApp{t_2}{c} \\
  t_3 &\leftarrow \lamApP{a}{\lamApp{b}{c}} & \text{\emph{Result of E-App.}} \\
  &= t_3.
\end{align*}

We apply $t_1$ to $b$ to create our next intermediate value, $t_2$:
\begin{equation}
  t_2 = \lamApp{t_1}{b} = \lamAbs{x}{\lamApp{a}{\lamApp{b}{x}}}. \label{mil_eqn2}
\end{equation}
Finally, we compute our final value, $main$, by applying $t_2$ to $c$:
\begin{equation}
  main = \lamApp{t_2}{c} = \lamApp{a}{\lamApp{b}{c}}. \label{mil_eqn3}  
\end{equation}

Both $t_1$ and $t_2$ will hold \emph{closures} when evaluating
expression \eqref{mil_eqn4}. As detailed in Section \ref{mil_subsec2}, a closure
holds a pointer to a body of code and any \emph{free variables}. In this case,
$t_1$ holds $a$ and points to the code that evaluates to $t_2$. In turn, $t_2$
holds $a$ and $b$, and points to the code which evaluates to $main$. The
\lamA does not make this explicit, but our MIL does. 

\begin{myfig}[t]
  \input{lst_mil2}
  \caption{The MIL program which computes $main =
    \lamApp{\lamApp{\lamApp{compose}{a}}{b}}{c}$. Note that $a$, $b$,
    and $c$ are assumed to be arguments given outside the program.}
  \label{mil_fig2}
\end{myfig}

Figure \ref{mil_fig2} shows the complete MIL program for $main =
\lamApp{\lamApp{\lamApp{compose}{a}}{b}}{c}$. !+k1+!, !+k2+! and !+k3+!
(lines \ref{mil_k1_fig2} -- \ref{mil_fig2_k3}) represent
\emph{closure-capturing} blocks. As opposed to !+main+!, these blocks
create new closures. In the definition !+k1 \{\} f = k2 \{f\}+!, the braces
on the left-hand side represent variables expected in the closure
given to this function. In this case, !+k1+! does not expect to find any
variables. !+f+! names the argument given to !+k1+!. The right-hand side,
!+k2 \{f\}+!, shows the creation of a new closure. The closure points to
!+k2+! and captures the value of !+f+!. In other words, evaluating !+k1+!
returns a closure which can be used to execute !+k2+!. !+k2+! behaves
similarly. It expects to find one value in its closure (!+\{f\}+!) and
returns a closure pointing to !+k3+! that copies the value !+f+! from the
existing closure and adds the argument, !+g+! (!+k3 \{f, g\}+!). !+k3+!,
however, does something new. Instead of returning a closure, it
executes the !+compose+! block (defined in Figure \ref{mil_fig1b}) with
three arguments: !+f+!, !+g+!, and !+x+!. This does \emph{not} return a
closure or ``enter'' a function. Instead, we jump directly to the
block. The value returned by !+k3+! will be the value computed by
!+compose+! with the arguments given.

Returning to !+main+! on line \ref{mil_main_fig2} in Figure
\ref{mil_fig2}, we can now see how MIL makes explicit the intermediate
closures created while evaluating
\lamApp{\lamApp{\lamApp{compose}{a}}{b}}{c}. On line
\ref{mil_t1_fig2}, we enter !+k1+! with the first argument, !+a+!. !+t1+!
holds the closure returned. On the next line, we enter !+t1+! (which
will point to !+k2+!) with the second argument, !+b+!. !+t2+! then holds the
closure returned. Finally, on line \ref{mil_t3_fig2}, we enter !+t2+!
(which will point to !+k3+!) with the final argument, !+c+!. !+k3+! will directly
execute !+compose+! with our specific arguments. !+t3+! holds the result returned
by !+compose+!. On the last line of !+main+! we return the value computed, !+t3+!.

%% Syntax of MIL
\subsection*{MIL Syntax}

Figure \ref{mil_fig3} gives the syntax for MIL.  A MIL program
consists of a number of \emph{blocks}: \emph{closure} blocks (line
\ref{mil_k1_fig3}), basic blocks (line \ref{mil_b_fig3}) and top-level
blocks (line \ref{mil_t_fig3}). Though the syntax for closure blocks
seems to allow any tail, in practice they can only do one of two
things: either return a closure (\texttt{k \{\dots\}}) or jump to a
basic block (\texttt{b(\dots)}). Top-level blocks (line
\ref{mil_t_fig3}) provide an entry point for top-level functions --
they provide a closure which can be used to initially ``enter'' the
function.

\afterpage{\clearpage{\input{mil_syntax}}\clearpage}

Basic blocks (line \ref{mil_body_fig3}) consist of a sequence of statements that
execute in order without any intra-block jumps or conditional
branches. Each basic block ends with a branch: either they return a
value (!+done+!) or take conditional branch (!+case+!). Conditional
branches can specify multiple destinations, though at any given time
only one will be taken.

The !+case+! statement (line \ref{mil_case_fig3}) specifies a list of
\emph{alternatives}, each of which matches a \emph{constructor} and
binds new variables to the values held by the constructor. !+case+!
examines the variable given (note, this cannot be an expression) and
selects the alternative that matches the constructor
found. Alternatives always branch immediately to some block -- they do
not allow any other statement. The result of block called becomes the
result of the !+case+!, which in turn becomes the result of the calling
block.

Only the binding statement (line \ref{mil_bind_fig3}) can appear multiple
times in a block. Each binding assigns the result of the \emph{tail}
on the right-hand side to a variable on the left. If a variable is
bound more than once, later bindings will ``shadow'' previous
bindings.

The !+done+! statement (line \ref{mil_done_fig3}) ends a block and returns
the value of tail expression specified.

\emph{Tail} expressions represent effects -- they create monadic
values. !+return+! (line \ref{mil_return_fig3}) takes a variable and
makes its value monadic. Notice it can only take a variable, not an
expression.  The ``enter'' operator, !+@@+!, expects a closure on its
left and some value on the right. It will enter the function pointed
to by the closure, with the argument given, and will evaluate to the
result of that function. !+k+!, the ``capture'' operator, creates a
closure from a block name and a list of variables. The name given is
not an arbitrary code pointer -- it is a location determined during
compilation. The ``goto'' expression, \texttt{b(\dots)}, jumps to the
particular block with the arguments given. Again, this is not a
computed value -- !+b+! represents a known location for the block. The
variables mentioned in the !+goto+! do not have to have the same names
as those given in the block's declaration. The constructor expression,
``C'', will create a data value with the given tag (``C'') and
variables. Primitives, which are not implemented in MIL, have the form
!+p*+! and are treated the same as ``goto'' expressions. They are not 
implemented in MIL, however. 

\section{Compiling \lamA to MIL}
\label{mil_sec4}

\input{lamCComp}

\section{Evaluating MIL Programs}
\label{mil_sec5}

\emph{\dots Lots of text \dots}

%% \section{Intermediate Languages, MIL, and Three-Address Code}


\section{MIL and Hoopl}
\label{mil_sec7}

\subsection{MIL Statements, Tails, \& Shapes}

\section{Summary}
\label{mil_sec6}

This chapter presented our Monadic Intermediate Language (MIL). Our
MIL resembles three-address code in several ways: infinitely many
registers can be named, nested expressions are not allowed, and
implementation details are made explicit. The MIL's unique features
include separate representations for \emph{closure-capturing} and
basic blocks, and the use of monadic \emph{tail} expressions. We 
presented a simple scheme for compiling the \lamA given in
Chapter \ref{ref_chapter_languages} to our MIL. Later will be devoted
to optimizing those MIL programs using dataflow techniques.

%% Compiling the lambda-calculus to MIL

%% \section{Monadic Intermediate Language}

%% %% What does the language support?

%% Our monadic language takes its inspiration from Haskell's @do@
%% notation. It is a pure functional language, making allocation of data
%% structures and closures explicit via monadic syntax. Functions in MIL
%% define computations which, when run, can affect heap memory. Figure
%% \ref{figMILDef} gives the syntax of the language.

%% %% TODO: Mention that v restricts the term to variables
%% %% only.

%% MIL programs consist of a series of definitions (@defM@). Each
%% definition can be any of the following.

%% \begin{description}
%%   \item[Closure-capturing] (@k {v1, ..., vN} v = k1 {v1, ..., vN, v}@) -- This function
%%     expects to find the variables @v1, ..., vN@ in its own closure. It constructs
%%     a new closure containing the existing variables plus the newly captured variable
%%     @v@. The new closure refers to @k1@, another closure-capturing function.
%%   \item[Block-calling] (@k {v1, ..., vN} v = b(v1, ..., vN, v)@) -- This function immediately
%%     jumps to block @b@ with arguments @v1, ..., vN@ and @v@. No closure value needs to
%%     be constructed. 
%%   \item[Function block] (@b(v1, ..., vN) = bodyM@) -- This function executes the statements
%%     in the body. 
%%   \item[Top-level] (@t <- k {}@) -- This special case ensures top-level definitions in the program
%%     can be accessed like any other function. The notation indicates that @t@ holds a closure
%%     structure, referring to the definition @k@. 
%% \end{description}

%% Notice that we can distinguish syntatically between functions that
%% merely create a closure (@k { ... }@) and those that do actual work
%% (@b(...)@). The body of a @k@ functin can only allocate another
%% closure or jump to a block. A block, on the other hand, can do other
%% work, but it cannot directly return a closure. As will be described in
%% chapter \ref{ref_chapter_uncurrying} this makes it much easier to
%% recognize and elminate intermediate closures.

%% The body of each block consists of statements followed by a
%% \emph{tail}. Tails can only
%% appear as the last statement in a block or on the right-hand side of
%% the monadic arrow (``@<-@''). Tail instructions, in other words, cause 
%% effects. The three tail statements follow:

%% \begin{description}
%% \item[Return a computation] (@return v@) -- Returns the result of a computation
%%   to the caller.

%% \item[Create a closure] (@k {v1, ..., vN}@) -- Creates a closure pointing to
%%   function @k@, capturing variables @v1@ through @vN@.

%% \item[Enter a function] (@v1 @@ v2@) -- Enter the closure referred to by @v1@, with
%%   argument @v2@. In other words, function application. Note that @v1@ represents an
%%   \emph{unknown} function -- one for which we compute the address at run-time.

%% \item[Call a block] (@f(v1, ..., vN)@) -- Jump to the block labeled @f@ with the arguments
%%   given. In this case we know the function @f@ refers to and do not need to examine
%%   a closure in order to execute it.
%% \item[Create a value] (@C v1 ... vN@) -- Create a data value with tag @C@, holding
%%   the values found in variables @v1 ... vN@.
%% \end{description}

%% %% TODO: Describe alt syntax.

%% Statements in a block either bind the result of a tail statement 
%% (@v <- tailM@) or branch conditionally (@case v of ... @). Binding ``runs''
%% a computation and ``dereferences'' the result, placing
%% the value in a variable (e.g., @v@). That same variable can be bound
%% again later, but that does not affect previous uses of @v@. In essence, the old
%% name becomes hidden and its value inaccessible.

%% Though the syntax allows multiple @case@ statements in a function
%% body, only one can appear and it must be the last statement in the
%% body. The arms of the @case@ statement can only match on constructor
%% tags (@C@) and can only bind the constructor arguments to variables
%% (@v1 ... vN@). Each arm then jumps to a known block with those
%% variables as arguments. This choice makes compilation simpler.


%% %% \emph{Defines our monadic language and explains the terms in
%% %%   it. Example programs are given which illustrate closure construction
%% %%   and data allocation. The use of ``tail'' vs. statements is motivated
%% %%   and described. }

%% \emph{Need to talk about the monad we work in as well - what 
%% do bind and return mean?}

%% \section{Compiling to Our MIL}
%% \emph{A compilation scheme which uses Hoopls ``shapes'' is
%% described. This scheme will give use our initial, unoptimized
%% MIL program. An example (possibly |compose|, or |const3|) illustrates 
%% our scheme.}

\standaloneBib

\end{document}

% LocalWords:  RTL Torczon Muchnick ANF MIL's dataflow Appel eq clo CompL invis
% LocalWords:  compclo stateful monad Monads Wadler monads eqn intra goto
