\documentclass[12pt]{report}
\usepackage{standalone}
%include polycode.fmt
\input{tikz.preamble}
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

We first describe our source language, \lamC, in
Section~\ref{mil_src}.  Section~\ref{mil_sec1} describes closures, a
fundamental data structure used to implement functional languages. We
then describe ``three-address code,'' the intermediate form from which
MIL partly derives, in Section~\ref{mil_sec2}.  MIL syntax and
examples follow in Section~\ref{mil_sec3}. Section~\ref{mil_sec4}
shows our compiler for translating \lamC to MIL. We sketch how MIL
programs can be evaluated in Section~\ref{mil_sec5}, using the same
structural operational semantics (SOS) style as in
Chapter~\ref{ref_chapter_languages}. Section \ref{mil_sec7} shows how
Hoopl influenced the implementation the MIL language from Chapter
\ref{ref_chapter_mil} and discusses the design choices we made.

\section{Our Source Language}
\label{mil_src}

\intent{Introduce \lamC as extension to \lamA. Motivate \lamC as used by Habit; 
something to write a compiler for.}

\intent{Brief tour of \lamC's features except bind: constructors, case, primitives and let.}

\intent{Description of \lamC's bind feature.}

\intent{Present syntax of \lamC.}

Section~\ref{lang_sec1} should make it clear that the \lamA is capable
of general-purpose programming, but also quite cumbersome. In
particular, representing conditional statements and values in purely
``functional'' form is extremely verbose. Therefore we extend the
\lamA in our work by adding two new terms: \emph{algebraic data
  types}\ and \emph{case discrimination}.

\emph{Algebraic data types} (ADTs) are a new type of value, alongside
$\lambda$-abstractions.  They consist of a \emph{constructor} tag and
zero or more fields. For example, we can create boolean values by
defining two constructors:

> Boolean = True | False

Here, |Boolean| is the name of the data we will create, while |True| and
|False| represent the different possible values for |Boolean| data. Our syntax
does not actually support naming data types like |Boolean|; we only are able
to name the constructors |True| and |False|. For presentation, however, this
shorthand is convenient and will be used as needed.

Constructors can take also take arguments. This allows us to build
composite data values from simpler pieces. For example, lists
typically have one constructor taking no arguments that represents the
empty list, and another taking two arguments, one of which holds an
element of the list and other which holds the ``rest'' of the list:

> List = Nil | Cons x xs

Here, |Nil| represents the empty list. |Cons| holds an element of the
list (|x|) and the rest of the list (|xs|). While the |x| argument can
hold any value, the |xs| argument must be another |Cons| or |Nil|
value. If |xs| is some other value, we do not have a valid list. For
example, the list |[True, False, True]| translates to the following
sequence of |List| constructors:

> Cons True (Cons False (Cons True Nil))) 

However, for convenience, we will write lists using brackets. The
empty list, |Nil|, is written as empty brackets: |[]|.

Natural numbers can be represented as successors to zero, otherwise
known as \emph{Peano} numbers. We define two constructors, |Z| for
zero and |S| for successor:

> Natural = Z | S n

The |n| argument to |S| will be either another |S| or a
|Z|.\footnote{At least, if we want our program to execute properly.} We
then represent each natural as some number of |S| constructors,
terminated by a |Z|:

> 0 = Z
> 1 = S Z
> 2 = S (S Z)
> 3 = S (S (S Z))
> {-"\ldots"-}

Constructors are just like functions, except for one crucial
difference: we do not write their ``body.'' Instead, the body of the
constructor creates new data, in some way that we cannot explicitly express
in \lamC. 

We use ADTs to construct values; we take them apart using \emph{case
  expressions} (or \emph{case discrimination}). Case expressions are a
generalized form of the \emph{if} or \emph{switch} statements found in
languages such as C, Java, and JavaScript. The case expression
inspects a value (the \emph{discriminant}) and selects one of many
\emph{case alternatives} (or \emph{arms}) based on the value
found. The value of the alternative becomes the value of the case
expression.

For example, we can implement \emph{if} over booleans using \emph{case}:

> case b of
>   True -> {-"\ldots"-}
>   False -> {-"\ldots"-}

Each alternative specifies a constructor to the left of the arrow. The
right-hand side gives the body that will be evaluated if the
discriminant matches the constructor. 

When the constructor used in the case alternatives takes arguments,
then those values become available in the arm associated with the
alternative.  Looking at lists, we can write \emph{takeOne}, which
will take 1 element from a list and return a list. If the list
given has no elements, an empty list is returned:

> takeOne = {-"\lamAbs{l}{}"-} case l of
>               Cons a as -> Cons a Nil
>               Nil -> Nil   

We use |a| and |as| to emphasize that these bindings are new and based on
the value of |l|.

It is possible to write a case expression with undefined behavior, if
the discriminant contains a value that does not match one of the arms. For
example, this expression would have undefined behavior:

> case (Cons True Nil) of
>   Nil -> Nil

Figure~\ref{lang_fig5} shows the syntax for ADTs and case
discrimination. An ADT consists of a constructor name, |C|, and zero
or more arguments ($t_1$, $t_2$, \ldots). Each argument can be a
term. The ADT term itself can only appear where our syntax allows
terms. Specifically, they cannot be used as the parameter variable in
an abstraction. That is, we do not support ``pattern-matching,'' as
found in many functional languages. Case discrimination consists of
the determinant term, $t$, and one or more alternatives (or
``arms''). Each arm consists of a constructor ($C_1$, $C_2$, \ldots)
and a ``binding'' for each argument that the constructor was defined
with ($a_1$, $b_1$, \ldots). The number of bindings must exactly match
the number of arguments defined for the constructor. Each binding is
also a \emph{variable} -- we do \emph{not} allow terms. Each arm
defines a body ($t_1$, $t_2$, \ldots). Both the new bindings from the
arm \emph{and} the discriminant are in scope in the arm.\footnote{Any
  other variables bound by enclosing $\lambda$'s are in scope as well,
  of course.}  Bindings in the arm will ``shadow'' any bindings with
the same name that are already in scope.

\begin{myfig}[tbh]
  \begin{minipage}{3in}
  \begin{align*}
    term &= \mathit{C}\ t_1\ t_2\ \ldots\ t_n, n \ge 0 & \hfil\text{\emph{(ADTs)}} \\ \\
      &= |case|\ t\ |of| & \hfil\text{\emph{(Case Discrimination)}} \\
      & \qquad\mathit{C}_1\ a_1\ a_2\ \ldots\ a_n \rightarrow t_1, n \ge 0 \\
      & \qquad\mathit{C}_2\ b_1\ b_2\ \ldots\ b_n \rightarrow t_2, n \ge 0 
  \end{align*}
  \end{minipage}
  \caption{The syntax of \lamC, which extends \lamA from
    Figure~\ref{lang_fig3} with \emph{algebraic data types} (ADTs) and
    \emph{case discrimination}. $t$ again represents an arbitrary
    term. $C$ stands for a constructor name. $a$ and $b$ represent
    variables, not terms.}
  \label{lang_fig5}
\end{myfig}

Figure~\ref{lang_fig6} shows how we evaluate our new terms. In {\sc
  Case1}, the discriminant must evaluate to a constructor. Otherwise,
the behavior is undefined. If we allowed evaluation to an arbitrary
value, that would imply a $\lambda$ could appear as a discriminant,
which does not make sense. {\sc Case2} shows two important
actions. First, the discriminate value is matched to an alternative
with the same constructor \emph{and} number of arguments.\footnote{The
  behavior is undefined if a single match is not found.}  Second, the
alternative's body will be evaluated with new bindings, where $v_1$
maps to $a_1$, $v_2$ maps to $a_2$, etc. The {\sc Value} rule shows
that constructors will evaluate all of their arguments to
values.\footnote{Note that order of evaluation for arguments is
  \emph{not} specified.}

\begin{myfig}[tbh]
  \begin{minipage}{5in}
    \centering
    \begin{math}
      \begin{array}{lclr}
        \begin{minipage}{1in}
          \begin{math}
            \begin{array}{l}
              |case|\ t\ |of| \\
              \;\ldots \\
            \end{array}
          \end{math}
        \end{minipage} & %%
        \rightarrow & %%
        \begin{minipage}{1in}
          \begin{math}
            \begin{array}{l}
              |case|\ |C|\ v_1\ \ldots\ v_n\ |of| \\
              \;\ldots
            \end{array}
          \end{math}
        \end{minipage} & \text{({\sc Case1})} \\ \\

        \begin{minipage}{2in}
          \begin{math}
            \begin{array}{l}
              |case|\ |C|\ v_1\ \ldots\ v_n\ |of| \\
              \;\ldots \\
              \; |C|\ a_1\ \ldots\ a_n \rightarrow\ t \\
              \;\ldots
            \end{array}
          \end{math}
        \end{minipage} & %% 
        \rightarrow & [v_1 \mapsto a_1, \ldots, v_n \mapsto a_n]\ t & \text{({\sc Case2})} \\ \\

        \;|C|\ t_1\ \ldots\ t_n& %%
        \rightarrow & |C|\ v_1 \ldots\ v_n & \text{({\sc Value})}

      \end{array}
    \end{math}
  \end{minipage}
  \caption{Evaluation rules for the new elements in \lamC. Constructors
    require that their arguments be values. Case discrimination evaluates
    its argument, but does \emph{not} evaluate every arm -- only the one
    which matches.}
  \label{lang_fig6}
\end{myfig}

With our new terms, we can more easily define functions from
Section~\ref{lang_sec1}. Rather than the Church numerals,
we can define \emph{plus} in terms of Peano numbers:

> plus = {-"\lamAbs{m}{\lamAbs{n}{}}"-} case m of
>   S m' -> S (plus m' n)
>   Z -> n

Multiplication can be defined in terms of |plus|:

> mult = {-"\lamAbs{m}{\lamAbs{n}{}}"-} case m of
>   S m' -> plus n (mult m' n)
>   Z -> Z

This allows us to define our |multiplier| and |mag| function from
Section~\ref{lang_sec2}:\footnote{We use ``2'' here to represent the
  Peano number |S (S Z)|.}

> multiplier = {-"\lamAbs{multiple}{\lamAbs{a}{}}"-} mult multiple a
> mag = multiplier 2

Figure~\ref{lang_fig7} collects the syntax and evaluation rules for
\lamC into one place. Part~\subref{lang_fig7_syntax} gives the full
syntax for \lamC, and Part~\subref{lang_fig7_eval} gives our
evaluation rules. We extend the syntax for convenience in two ways. We
have added the ability to define top-level definitions, so that a
program is formed of multiple definitions, each of which is available
to all top-level functions. We have also allowed arguments to be
written to the left of the equals when defining a function.  We also
updated the abstraction notation from ``$\lamAbs{x}{t}$'' to ``|\x ->
t|.''

\afterpage{\clearpage\input{lang_fig7}\clearpage}


\section{Closures}
\label{mil_sec1}

Closures are the fundamental data structures used to implement
functional languages. A closure always results when a function value
is created. They may not have the exact form described here but they
always have the same purpose: they pair a location with a list of
values. The location tells where to find the code implementing the
body of the function. The list of values defines the environment in
which the code will execute.\footnote{The values are not necessarily
  stored in the immediate environment. For example, static links
  (described by \citet[pg.~125]{Appel2003}) might be used to implement
  a chain of environments. In any case the environment is always used
  to find values for arguments, so we say they ``can be located'' in
  the environment.}

For example, consider the value created when we apply the |compose|
function to two arguments:

\begin{singlespace}\correctspaceskip
  \begin{equation}
    \begin{split}
      t_1 &= \lamApp{compose}{\lamApp{a}{b}} \\
      &= \lamAPp{\lamCompose}{\lamApp{a}{b}} \\
      & \dots \\
      t_1 &= \lamAbs{x}{\lamApP{\lamSubst{a}{f}}{\lamApp{\lamSubst{b}{g}}{x}}}.
    \end{split}\label{mil_eq1}
  \end{equation}
\end{singlespace}

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
  \caption{Part~\subref{mil_fig4a}
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

\begin{singlespace}\correctspaceskip
  \begin{equation}
    a = \frac{(b * c + d)}{2},
  \end{equation}
\end{singlespace}

\noindent would be expressed in three-address code as:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=2]
    s = b * c;
    t = s + d;
    a = t / 2;
  \end{AVerb}
\end{singlespace}

\noindent where \var s/ and \var t/ are new temporaries created by the
compiler. This representation makes it easier for the compiler to
re-order expressions, unravel complex control-flow, and manipulate
intermediate values.

Three-address code intends to simplify the analysis of programs while
not revealing all details of the underlying hardware. Three-address
code accomplishes these goals by reducing all expressions to a
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
We can divide functions into two types: \emph{pure} and
\emph{impure}. A \emph{pure} function has no side-effects: it will not
print to the screen, throw an exception, write to disk, or in any
other way change the observable state of the
machine.\footnote{We mean ``observable'' from the program's standpoint. Even a pure
  computation will generate heat, if nothing else.} An
\emph{impure} function may change the machine's state in an observable
way.

As described by Wadler \citeyearpar{Wadler1990}, \emph{monads} can be
used distinguish \emph{pure} and \emph{impure} functions. Impure (or
``monadic'') functions execute ``inside'' the monad. Values returned
from a monadic function are not directly accessible --- they are
``wrapped'' in the monad. The only way to ``unwrap'' a monadic value
is to execute the computation --- inside the monad!

\subsection*{The Monad in MIL}

All MIL programs execute in a monadic context. For example, we
consider allocation impure, because it affects the machine's
memory. Some runtime primitives have observable effects (like printing
to the screen), making them impure. Dividing by zero typically causes
a program to abort or throw an exception, making division an impure
operation. Even addition can cause exceptions, due to overflow. 

Pure operations include inspecting data values (i.e., with the |case|
statement) or jumping to another location in the program (using
application). 

We designed MIL to support the Habit programming language
\citep{Habit2010}; in particular, we rely on Habit to give meaning to
the monadic context for each MIL operation. We further assume that the
interpreter (or compiler) for MIL will implement underlying monadic
primitives (e.g., allocation, arithmetic, etc.).  

\subsection*{MIL Example: \lcname compose/}

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
    for $compose$.}
  \label{mil_fig1}
\end{myfig}

%% Closures

Using the evaluation rules from Figure~\ref{lang_fig6}, we can compute
the value of the expression \lcapp compose * a * b * c/:

\begin{singlespace}\noindent
  \begin{math}\begin{array}{rlr}
      main &= \lcapp compose * a * b * c/ & \\
      &= \lcapp (\lcabs f. \lcabs g. \lcabs x. f * (g * x)) * a * b * c/ & \text{\emph{Definition of |compose|.}} \\
      &= \lcapp (\lcabs g. \lcabs x. a * (g * x)) * b * c/ & \text{\emph{E-App.}} \\
      &= \lcapp (\lcabs x. a * (b * x)) * c/ & \text{\emph{E-App.}} \\
      &= \lcapp a * (b * c)/ & \text{\emph{E-App.}} \\[-\baselineskip]
      \multicolumn{3}{l}{\hbox to \hsize{}}
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
    \multicolumn{4}{l}{\hbox to \hsize{}}
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

\input{mil_syntax}

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
