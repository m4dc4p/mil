\documentclass[12pt]{report}
%include lineno.fmt
\input{preamble}
\begin{document}
\numbersoff
\input{document.preamble}

\chapter{The \LamA \& Functional Languages}
\label{ref_chapter_languages}

%% Overall: Justify why the lambda-calculus matters
%%   * Give syntax and evaluation rules for pure lambda calculus 
%%   * Extend for ADTs and case statements
%%   * Set the foundation for LC-to-MIL later

John McCarthy created LISP, the first ``functional'' language, in 196X
\citep{McCarthy}. Other functional languages created since then
include Scheme, ML, Haskell, and many more. While syntax, semantics
and capabilities differ widely between all these languages, they share
a common characteristic: \emph{functions are values}.  This chapter
explains what that means and introduces the language we will use to
write our programs. Section~\ref{lang_sec2} introduces the basic idea
of treating functions as values through examples in four different
functional languages: Haskell, Scheme, ML and
JavaScript. Section~\ref{lang_sec1} introduces the syntax and
semantics of the \lamA\ -- in some ways the simplest possible
functional programming language. We then describe \lamC in
Section~\ref{lang_sec4}, a variant of the \lamA that we will be using
throughout the remainder of this thesis. We summarize our chapter in
Section~\ref{lang_sec5}.

\section{Introductory Example}
\label{lang_sec2}
A function that returns a function can be hard to get used to, so we
first look at a function that just computes a value -- it does not
return a function or anything fancy.  Figure~\ref{lang_fig1} shows
``#mag#,'' a function that doubles its value, written in four
different functional languages.

\begin{myfig}[bth]
  \begin{tabular}{cc}%%
    \begin{minipage}{2in}\begin{withHsNum}%%
> mag :: Float -> Float {-"\label{lang_fig1_haskell_sig}"-}
> mag a = 2 * a {-"\label{lang_fig1_haskell_impl}"-}
    \end{withHsNum}\end{minipage} & %%
  \input{lang_fig1_ml} \\

  \lscap{lang_fig1_haskell}{Haskell.} & \lscap{lang_fig1_ml}{ML.} \\

  \input{lang_fig1_scheme} & %%
  \input{lang_fig1_js} \\

  \lscap{lang_fig1_scheme}{Scheme.} & \lscap{lang_fig1_js}{JavaScript.}
  \end{tabular}
  \caption{Definitions of a function that doubles its argument in
    \subref{lang_fig1_haskell} Haskell, \subref{lang_fig1_ml} ML, 
    \subref{lang_fig1_scheme} Scheme, and \subref{lang_fig1_js} JavaScript.}
  \label{lang_fig1}
\end{myfig}

Part \subref{lang_fig1_haskell} gives the Haskell version. Haskell is
a statically typed language, so we begin with a type signature on
Line~\ref{lang_fig1_haskell_sig}: |Float -> Float|. This
signature indicates that |mag| takes an argument of type |Float| and
returns a result, also of type
|Float|. Line~\ref{lang_fig1_haskell_impl} implements |mag|. The
function name comes first, followed by the argument, |a|. The
right-hand side of the equals sign defines the \emph{body} of the
function: |2 * a|. The body is evaluated when the function is applied
to an argument and a result must be computed.\footnote{Haskell is a
  \emph{lazy} language, meaning no computations are performed until
  demanded. Therefore, we say the body is evaluated only when a
  ``result must be computed.''}

Figure~\ref{lang_fig1}, Part~\subref{lang_fig1_ml}, gives the ML
implementation. ML is also statically typed, so we start with the type
signature on Line~\ref{lang_fig1_ml_sig}: #float -> float#. This
signature has much the same meaning as the Haskell
version. Line~\ref{lang_fig1_ml_impl} gives the implementation of
#mag#. The ``#*.#'' operator represents floating-point
multiplication. Otherwise, the implementation is much the same as the
Haskell version.

Figure~\ref{lang_fig1}, Part \subref{lang_fig1_scheme}, gives the
Scheme definition. Scheme is a dynamically typed language, so no
signature can be given -- just the implementation. The expression
\texttt{define mag (lambda (a) \ldots)}\ associates the value created by
the #lambda# expresion with the name #mag#. \texttt{(lambda (a)
  \ldots)} creates a new function that takes one argument, #a#.  The
body of the function, #(* 2 a)#, shows that the argument will be
doubled when the function is applied.

%% ``#define#'' keyword
%% associates a name with a value. The
%% ``#lambda#'' keyword indicates that a function will be created. The
%% funciton defined takes only one argument, designated ``#a#.'' The
%% postfix expression, ``#(* 2 a)#,'' defines the body of the function
%% and will be evaluated when the function is applied.

Figure~\ref{lang_fig1}, Part \subref{lang_fig1_js}, shows the
JavaScript version. Line~\ref{lang_fig1_js_def} gives the
\emph{signature} of the function -- the name of the function and any
named arguments.\footnote{We say ``named'' here because JavaScript
  functions can take more arguments than declared.}  JavaScript is
also a dynamically typed language, so this is \emph{not} a type
signature, but rather a specification of how to call the
function. Function definitions always start with the #function#
keyword, followed by the function name, any named arguments in
parentheses, and the body in braces: \texttt{function mag (a) \{
  \ldots\ \}}. The body of the function, on
Line~\ref{fig_lang1_js_impl}, uses the #return# keyword to
indicate the function doubles its argument and returns the resulting
value: #return 2 * a#.

The functions defined in Figure~\ref{lang_fig1} all have one thing in
common: they are limited to doubling their argument. If we want to
triple our argument, halve it, zero it or perform any other
multiplication, then we need to write a new function.

Of course, we can write a function that takes two arguments, the
multiplier and the argument. For example, in JavaScript:
\begin{AVerb}
function magBy(multiple, a) \{
  return multiple * a;
\}
\end{AVerb}
But this limits us from re-using #magBy# in certain ways. 

Imagine a function that wants to apply #magBy# to all items in a
list:\footnote{In this fragment, #items# is an array of values,
  accessed by index. We enumerate it using a #for# loop much like the
  that found in the C language.}
\begin{AVerb}
function magAll(items, multiple) \{
  for(var i = 0; i < items.length(); i++)
    items[i] = magBy(multiple, items[i]);
\}
\end{AVerb}
This definition creates two problems:
\begin{enumerate}
\item Every call to #magAll# requires us to specify a value for
  #multiple#.
\item Our function is limited to using #magBy#. If #magBy#
  is not appropriate for some situation, we need to write a new
  #magAll# that uses a different version.
\end{enumerate}
We solve these two problems by making #magBy# a \emph{parameter}
to #magAll#. It is something like creating a ``hole'' in the
definition of #magAll#, where we can put code that is passed in as
an argument:
\begin{AVerb}
function magAll(items, \emph{<code>}) \{
  for(var i = 0; i < items.length(); i++)
    items[i] = \emph{<code>};
\}
\end{AVerb}
The ``\emph{<code>}'' argument illustrates how functional languages
treat ``functions as values.''

Figure~\ref{lang_fig2} shows the definition of |mag| in terms of a
new function, |multiplier|.  When |multiplier| is evaluated, it
produces a value like any function; that value just happens to be a
function itself! The function returned takes an argument and
multiplies it by the original multiple given to |multiplier|.

\begin{myfig}
  \begin{tabular}{cc}
    \begin{minipage}{3.5in}\begin{withHsNum} %%
> multiplier :: Float -> (Float -> Float)
> multiplier multiple = 
>   \a -> multiple * a {-"\label{lang_fig2_hs_fun}"-}
>
> mag :: Float -> Float
> mag = multiplier 2 {-"\label{lang_fig2_hs_mag}"-}
        \end{withHsNum}
      \end{minipage} & %%
    \input{lang_fig2_ml} \\

    \lscap{lang_fig2_hs}{Haskell.} & \lscap{lang_fig2_ml}{ML.} \\

    \input{lang_fig2_scheme} & %%
    \input{lang_fig2_js} \\

    \lscap{lang_fig2_scheme}{Scheme.} & \lscap{lang_fig2_js}{JavaScript.} \\

  \end{tabular}
  \caption{The |multiplier| function and how it can be used to define
    |mag|. When evaluated, |multiplier| returns a function that
    will multiply its argument by |multiple|. We give
    \subref{lang_fig2_hs} Haskell, \subref{lang_fig2_ml} ML,
    \subref{lang_fig2_scheme} Scheme, and \subref{lang_fig2_js}
    JavaScript versions.}
  \label{lang_fig2}
\end{myfig}

Figure~\ref{lang_fig2}, Part~\subref{lang_fig2_hs} gives the Haskell
version of |multiplier|. The signature, |Float -> (Float -> Float)|,
shows that |multiplier| takes one argument, a |Float| value, and
returns a function (|Float -> Float)|. The implementation on
Line~\ref{lang_fig2_hs_fun} uses an \emph{anonymous} function:

> \a -> multiple * a

The anonymous function is introduced with the |\| (``lambda'') symbol,
followed by the function's argument, |a|. The body of the function
follows the arrow.  Notice that |multiple| is \emph{not} an
argument to this function. Instead, it is an argument to
|multiplier|. We say |multiple| is \emph{captured} by the anonymous
function. The anonymous function is the value returned by
|multiplier|. When that value is itself applied to an argument, it
will use the value of |multiple| originally given to |multiplier|.

On Line~\ref{lang_fig2_hs_mag} we use |multiplier| to define the
|mag| function from Figure~\ref{lang_fig2_hs}. The function has
the same signature, |Float -> Float|, but no argument:

> mag :: Float -> Float
> mag = multiplier 2

If we substitute the definition of
|multiplier| in |mag|, we can see the function |mag| represents:

\begin{math}
  \begin{array}{cc}
    |mag| &= |multiplier 2| \\
    &= |\a -> 2 * a | 
  \end{array}
\end{math}

Notice that the argument |a| appears on the right-hand
side here, for which reason |mag| does not specify an argument
in Figure~\ref{lang_fig2_hs}.

Figure~\ref{lang_fig2}, Part \subref{lang_fig2_ml}, shows the ML
definition for #multiplier# and #mag#. \texttt{multiplier} returns
the value #f#, which is again a function. Line~\ref{lang_fig2_ml_fun}
defines #f# as a local, named function:

\begin{AVerb}
  let f a = a *. multiple
  in f
\end{AVerb}

Again, we capture the value of #multiple# when defining #f#. When #f#
is evaluated, it will multiply its argument by the #multiple#
given. The definition of #mag# on Line~\ref{lang_fig2_ml_mag} in terms
of #multiplier# looks almost exactly the same as the Haskell version.

In Figure~\ref{lang_fig2}, Part \subref{lang_fig2_scheme}, we give the
Scheme version of #multiplier# and #mag#. As in
Figure~\ref{lang_fig1_scheme}, the body of #multiplier# is a function,
defined using #lambda#. However, this function returns a function,
again defined with #lambda#:

\begin{AVerb}
  (lambda (a) (* multiple a))))
\end{AVerb}

As in the Haskell and ML versions, the inner function captures the
value of #multiple# given to the outer function. On
Line~\ref{lang_fig2_scheme_mag} we evaluate the expression
\texttt{({multiplier} 2)} and assign the result to #mag#:
\begin{AVerb}
  (define mag 
    (multiplier 2))
\end{AVerb}

Figure~\ref{lang_fig2}, Part \subref{lang_fig2_js} shows the JavaScript
version of #multiplier#. The body of #multiplier# returns an anonymous
function, defined by using the #function# keyword without a name:
\begin{AVerb}
  return function(a) \{ 
    return multiple * a;
  \};
\end{AVerb}

Once again, the #multiple# argument is captured and used by the
returned function. Line~\ref{lang_fig2_js_mag} shows how #mag#
is defined in terms of #multiplier#:

\begin{AVerb}
  var mag = multiplier(2);
\end{AVerb}

The #var# keyword introduces an identifier, to which we assign the
function returned by #multiplier(2)#. In some ways this syntax makes
it most obvious that we are treating functions as values.

Returning to #magAll#, we can redefine it to take a function argument:
\begin{AVerb}
function magAll(items, magnifier) \{
  for(var i = 0; i < items.length(); i++)
    items[i] = magnifier(i);
\}
\end{AVerb}
Here, #magnifier# is a function, passed as an argument. If 
we wish to double the items in the array, we just pass #double#
to #magAll#:
\begin{AVerb}
  magAll(items, double);
\end{AVerb}
To multiply items by different amounts, we create appropriate
\emph{function values} and pass them to #magAll#:
\begin{AVerb}
  var halve = multiplier(0.5);
  var quadruple = multiplier(4);
  magAll(items, quadruple);
  magAll(items, halve);
\end{AVerb}
We can even pass an \emph{anonymous function} directly to 
#magAll#, as here where we halve the values again:
\begin{AVerb}
  magAll(items, function (i) \{ return i * 0.5; \});
\end{AVerb}

Functional languages vary widely, but they all share the ability
illustrated in our examples: \emph{functions are values}. Creating a
function, passing a function as an argument, and parameterizing
functions by creating ``holes'' to fill with code that is passed in
are all defining characteristics of functional languages.  Having
demonstrated the idea behind ``functional languages'', we now move to
the \lamA, the ``lowest common denominator'' for all functional
languages. Its simplicity makes it impractical for writing ``real''
programs, but at the same time ideal for exploring singular concepts
and techniques.


\section{The \LamA}
\label{lang_sec1}
%%\emph{Why is it important}

%%\emph{What is the \lamA}

Alonzo Church defined his \lamA (``lambda calculus'') in 19XX
\citep{ChurchXX} to study systems of recursive equations. Being
Turing-complete, it can be used to model the behavior of any
computational system. Like Turing machines, the \lamA is \emph{not}
a ``programming language'' in any practical sense, but it has proved
incredibly useful when modeling the behavior of other functional
programming languages.

\subsection{Syntax of the \LamA}
\label{lang_sec1_syntax}

Figure~\ref{lang_fig3} shows the three types of terms used in the
\lamA: \emph{variables}, \emph{abstractions} and
\emph{applications}. \emph{Variables} have no further structure --
they are just names. An \emph{abstraction} defines a function that has
one parameter, $x$, and a body given by the term $t$. The parameter
$x$ does not stand for a term -- it can only be used as a variable in
the body of $t$.  An \emph{application} applies the term $t_2$ to the
term $t_1$.

\begin{myfig}[tbh]
  \begin{minipage}{5in}
    \begin{align*}
      \mathit{term} &= a, b, \ldots & \hfill\text{\emph{(Variables)}} \\
      &= \lamAbs{x}{t} & \hfill\text{\emph{(Abstraction)}} \\ 
      &= \lamApp{t_1}{t_2} & \hfill\text{\emph{(Application)}}
    \end{align*}
  \end{minipage}
  \caption{The \lamA' syntax.}
  \label{lang_fig3}
\end{myfig}

Using this syntax, we can define some basic functions. |Identity|
returns its argument:
\begin{align}
  |identity| &= \lamAbs{x}{x}. \label{lang_eq1} \\
  \intertext{|Compose| takes two functions and an argument. The result of
    applying the second function to the argument is passed to the first:}
  |compose| &= \lamCompose. \label{lang_eq_compose1} \\
  \intertext{|Const| takes two arguments but always returns the first:}
  |const| &= \lamAbs{a}{\lamAbs{b}{a}}. \label{lang_eq_const1} 
\end{align}
Note that application is left-associative, meaning
\lamApp{const}{\lamApp{a}{b}} is the same as \lamAppP{\lamApp{const}{a}}{b}
but \emph{not} the same as \lamApp{const}{(\lamApp{a}{b})}. Abstractions
also extend as far right as possible, unless parentheses are used to
delimit scope. That is, \lamAbs{x}{\lamApp{x}{\lamAbs{y}{y}}} is the
same as $(\lamAbs{x}{\lamApp{x}{(\lamAbs{y}{y})}})$, but not the
same as $\lamApp{(\lamAbs{x}{x})}{(\lamAbs{y}{y})}$.

\subsection{Evaluating \LamA Terms}
\label{lang_sec1_eval}

When an abstraction, \lamAbs{x}{t_1}, is applied to a term, $t_2$, we
can \emph{substitute} $t_2$ for each occurrence of $x$ in $t_1$. We say
that $t_2$ ``maps to'' or ``substitutes for'' each $x$ in $t_1$. Using
Pierce's notation \citep{PierceXX}, we write this as:
\begin{equation}
  \lamAppP{\lamAbs{x}{t_1}}{t_2} = [t_2 \mapsto x]\ t_1.
\end{equation}
Though substitution may appear simple, it is surprisingly hard to get
right. When $t_2$ mentions variables that are bound by $t_1$, we can
unintentionally capture values that we did not expect. For example,
consider the following substitution, where we replace $x$ with $y$
blindly:
\begin{equation}
  \begin{split}
    & \lamAppP{\lamAbs{x}{\lamAbs{y}{\lamApp{x}{y}}}}{y} \\
    & \quad = [y \mapsto x]\ \lamAbs{y}{\lamApp{x}{y}} \\
    & \quad = \lamAbs{y}{\lamApp{y}{y}}
  \end{split}
\label{lang_eq_capt1}
\end{equation}
Clearly, ``doubling'' the $y$ term in the last abstraction is not what
we mean here -- we are really referring to two different
$y$'s. Solving this issue algorithmically is very tricky -- but we can
avoid it altogether by assuming we can \emph{rename} variables
correctly and at any time, to avoid unintentional capture. That is, we
imagine we can rewrite Equation~\ref{lang_eq_capt1} using new
variables as needed:
\begin{equation}
  \begin{split}
    & \lamAppP{\lamAbs{x}{\lamAbs{y}{\lamApp{x}{y}}}}{y} \\
    & \qquad = [y \mapsto x]\ \lamAbs{w}{\lamApp{x}{w}} \\
    & \qquad = \lamAbs{w}{\lamApp{y}{w}}
  \end{split}
\label{lang_eq_capt2}
\end{equation}
For a full treatment of this issue, see Pierce \citep{PierceXX},
Chapter X, Section Y.

Following Church
\citep{ChurchXX}, we call any term where we can use substitution
(i.e., a term applied to an abstraction) a \emph{reducible expression}
or \emph{redex}. We call the act of reducing
\emph{beta-reduction}. Evaluating (or ``executing'') a \lamA
expression means finding these redexes and \emph{beta-reducing} them.

For example, consider the following term:
\begin{equation}
  \lamAppP{\lamAbs{y}{\lamAppP{\lamAbs{x}{y}}{y}}} %%
         {\lamAbs{z}{\lamAppP{\lamAbs{x}{x}}{z}}}
\end{equation}
There are three possible redexes (i.e., substitutions) we can make in 
this program:

\begin{center}
  \begin{tabular}{lccc}
    & \emph{term} & \emph{substitutes for} & \emph{in} \\
    \cmidrule(r){2-2} \cmidrule(r){3-3} \cmidrule(r){4-4}
    1. & $y$ & $x$ & $(\lamAbs{x}{y})$ \\
    2. & $z$ & $x$ & $(\lamAbs{x}{x})$ \\
    3. & $(\lamAbs{z}{\lamAppP{\lamAbs{x}{x}}{z}})$ & $y$ & $(\lamAbs{y}{\lamApp{\lamAbs{x}{y}}{y}})$
  \end{tabular}
\end{center}
The means by which we choose what redex to beta-reduce is called our
\emph{evaluation strategy}.

There are a number of possible strategies we can use. \emph{Full
  beta-reduction} lets us choose any of the possible redexes, in any
order we wish, until no more redexes remain. \emph{Normal-order}
requires us to choose the leftmost, outermost redex, again until none
remain. \emph{Call-by-name} also requires us to choose the leftmost,
outermost redex first, but we cannot reduce any redexes inside, or
``under,'' $\lambda$'s (i.e., abstractions). \emph{Call-by-value}, has
the same restrictions as call-by-name and also requires that we reduce
the right side (i.e., the argument) of each application to a value
before applying it to the left.

The phrase ``no more redexes'' really means we have reduced the term
to a \emph{value}. In the \lamA, \emph{values} are abstractions. That
is, \emph{literally} functions \emph{are} values! The evaluation
strategies differ on when to stop reducing: full-beta reduction and
normal-order will reduce ``under'' an abstraction, while call-by-need
and call-by-value will not. In all cases though, evaluation terminates
(if at all), when only an abstraction remains. In the call-by-value
and call-by-name case, we can have redexes \emph{inside} the
abstraction when we terminate. That is not the case for full and
normal-order evaluation.

In our work, we chose to use the call-by-value strategy over other
alternatives for three reasons:
\begin{itemize}
\item The memory behavior of call-by-need
  can be hard to predict (i.e., ``space leaks'' are easy to create and
  hard to spot). 
\item Call-by-value is the norm among popular high-level
  languages (Scheme, ML, and JavaScript, to name a few). 
\item Our research
  language, Habit \citep{HabitXX}, designed for systems and device
  programming, also uses the call-by-value strategy, motivating our
  choice.
\end{itemize}

Figure~\ref{lang_fig4} uses Plotkin's \emph{structural operational
  semantics} \citep{PlotkinXX} to formalize our evaluation strategy as
a set of \emph{rewrite rules}. That is, we treat evaluation of
lambda-terms as a sequence of \emph{rewrites}. Each step of evaluation
matches a redex to the left-hand side of one of the rules. The redex
is rewritten according to the right-hand side. If no more redexes
remain, evaluation terminates.\footnote{Of course, it is possible to
  write expressions that will rewrite forever, failing to terminate.}
Each rewrite is called a \emph{transition}, and the strategy as a
whole a \emph{transition function}.

\begin{myfig}[tbh]
\begin{minipage}{2.5in}
  \begin{math}
    \begin{array}{lclr}
      \lamApp{t_1}{t_2} & \rightarrow & \lamApp{t_1}{v} & (\text{\sc App1}) \\
      \lamApp{t_1}{v_2} & \rightarrow & \lamApp{v_1}{v_2} & (\text{\sc App2}) \\
      \lamAppP{\lamAbs{x}{t}}{v} & \rightarrow & [v \mapsto x]\ t & (\text{\sc Abs})
    \end{array}
  \end{math}
\end{minipage}
  \caption{Rewrite rules for the \emph{call-by-value} evaluation
    strategy. Redexes are evaluated finding a matching left-hand side
    left and rewriting according to the right-hand side. The $t$'s
    represent arbitrary terms, while the $v$'s represent values.}
  \label{lang_fig4}
\end{myfig}

Notice how the rules for application implement call-by-value. {\sc
  App1} requires that the argument, $t_2$, be reduced to a value, $v$,
before we can evaluate the function term, $t_1$. {\sc App2} reduces
the function term, $t_1$, to a value, $v_1$. Because values are
abstractions, {\sc Abs} will only be applied after {\sc App1} and {\sc
  App2} have done their work.


%%\emph{What does it look like?}
We now show how natural numbers and some common arithmetic operations
can be expressed using just the \lamA. We start with the \emph{Church
  numerals}, which represent natural numbers (0, 1, 2, etc.) as functions
of two variables, $s$ and $z$:
\begin{equation}
  \begin{split}
    0 &= \lamAbs{s}{\lamAbs{z}{z}} \\
    1 &= \lamAbs{s}{\lamAbs{z}{\lamApp{s}{z}}} \\
    2 &= \lamAbs{s}{\lamAbs{z}{\lamApp{s}{\lamApp{s}{z}}}} \\
    \ldots
  \end{split}
  \label{lang_eq_nats}
\end{equation}
In other words, the number of applications of $s$ gives the natural
number represented by the term. 

Using this representation, we can define the \emph{successor}
function, which always adds 1 to its argument:
\begin{equation}
  \mathit{succ} = \lamAbs{n}{\lamAbs{s}{\lamAbs{z}{\lamApPp{s}{\lamApp{n}{\lamApp{s}{z}}}}}}
\end{equation}
Using the rewrite rules from Figure~\ref{lang_fig4}, we show how
evaluating $\lamApp{\mathit{succ}}{0}$ results in 1.\footnote{``0''
  and ``1'' stand for the lambda-terms in
  Equation~\ref{lang_eq_nats}.} At each step we give the rule used to
rewrite the redex:
\begin{equation*}
  \begin{array}{rlr}
    \lamApp{\mathit{succ}}{0} &= \\ 
    &= \lamAppP{\lamAbs{n}{\lamAbs{s}{\lamAbs{z}{\lamApPp{s}{\lamApp{n}{\lamApp{s}{z}}}}}}}{0} & \text{\emph{Definition of} succ.} \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApPp{s}{\lamApp{0}{\lamApp{s}{z}}}}} & \text{\sc Abs} \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApPp{s}{\lamAppP{\lamAbs{s}{\lamAbs{z}{z}}}{\lamApp{s}{z}}}}} & \text{\emph{Definition of}\ 0 \emph{from Equation~\ref{lang_eq_nats}}} \\ \\
    \multicolumn{3}{l}{\parbox[c]{\linewidth}{\emph{For illustration, we reduce the $\lambda$'s introduced by 0, though call-by-value does not technically allow it.}}} \\ \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApPp{s}{\lamAppP{\lamAbs{z}{z}}{z}}}}  & \text{\sc Abs} \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApp{s}{z}}}  & \text{\sc Abs} \\
    &= 1 & \text{\emph{Definition of}\ 1.}
  \end{array}
\end{equation*}

Addition can be represented by applying one numeral to the other:
\begin{equation}
  \mathit{plus} = \lamPlus
\end{equation}
In fact, $\mathit{plus}$ generalizes $\mathit{succ}$ by adding $s$ to
$n$ $m$ times, rather than just once. To illustrate, we add
$1$ and $1$:
\begin{equation*}
  \begin{array}{llr}
    \lamApp{\mathit{plus}}{\lamApp{1}{1}} &= \\
    &= \lamAppP{\lamPlus}{\lamApp{1}{1}} & \text{\emph{Definition of} plus}. \\
    &= \lamAppP{\lamAbs{n}{\lamAbs{s}{\lamAbs{z}{\lamApp{1}{\lamApPp{s}{\lamApp{n}{\lamApp{s}{z}}}}}}}}{1} & \text{\sc Abs} \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApp{1}{\lamApPp{s}{\lamApp{1}{\lamApp{s}{z}}}}}} & \text{Abs} \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApp{(\lamAbs{s}{\lamAbs{z}{\lamApp{s}{z}}})}{\lamApPp{s}{\lamApp{1}{\lamApp{s}{z}}}}}} & \text{\emph{Definition of}\ 1 \emph{from Equation~\ref{lang_eq_nats}}.} \\ \\
    \multicolumn{3}{l}{\emph{Again, we reduce under the $\lambda$ here, for illustration.}} \\ \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApp{(\lamAbs{z}{\lamApp{s}{z}})}{(\lamApp{1}{\lamApp{s}{z}})}}} & \text{\sc abs} \\

    &= \lamAbs{s}{\lamAbs{z}{\lamApp{s}{(\lamApp{1}{\lamApp{s}{z}})}}} & \text{\sc abs} \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApp{s}{(\lamApp{(\lamAbs{s}{\lamAbs{z}{\lamApp{s}{z}}})}{\lamApp{s}{z}})}}} & \text{\emph{Definition of}\ 1.} \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApp{s}{(\lamApp{(\lamAbs{z}{\lamApp{s}{z}})}{z})}}} & \text{\sc Abs} \\
    &= \lamAbs{s}{\lamAbs{z}{\lamApp{s}{\lamApp{s}{z}}}} & \text{\sc Abs} \\
    &= 2. & \text{\emph{Definition of}\ 2.}
  \end{array}
\end{equation*}

\section{Summary}
\label{lang_sec5}

In this chapter we described the basic proposition of functional
languages: \emph{functions are values}. Section~\ref{lang_sec2} showed
how to create a code ``hole'' in a function definition, which is later
filled with ``code'' passed as an argument. We introduced the \lamA in
Section~\ref{lang_sec1}, describing its syntax and our chosen
evaluation strategy, \emph{call-by-value}. In Section~\ref{lang_sec4}
we extended the \lamA to \lamC, the language we will be using for the
rest of this thesis. For reference, Figure~\ref{lang_fig7} shows the
complete syntax and evaluation rules.

\end{document}
