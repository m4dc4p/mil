\documentclass[12pt]{report}
%include polycode.fmt
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

%%  However, that value is itself a 
%% function. |multilp
%% evaluated, creates a new function. in our four languages

%% We will be demonstrating a number of dataflow optimizations over
%% our intermediate language programs, but all of our source programs will
%% be written in a variant of the \lamA. Any variante

%% A compilation technique demonstrated for
%% some variant of the \lamA can be translated into any other functional
%% programming language. Making the translation work well with the syntax
%% and semantics of the target language is still hard work, but
%% absolutely possible -- a result developed for the \lamA really is
%% universal (as far as you want to make use of that result, of course). 

%% It is these three reasons that make the \lamA such a popular
%% language for showing theoretic (or practical) results

%% This chapter introduces the \lamA calcus, giving its 

%% Most importantly, results obtained
%% using the \lamA are guaranteed to translate to other Turing-complete
%% languages -- and usually with better syntax! 

%% Being Turing-complete, the \lamA is capable of exeucting any program
%% you could write on a modern computer.  

%%  . What it does mean is that anything possible in the \lamA Being
%% Turing-complete, it can be

%% \emph{\ldots transition
%%   \ldots}. Most importantly, the \lamA serves as the \emph{lingua
%%   franca} for functional programmers. It provides a way to translate
%% between functional programming languages, and a way to carry
%% developments from one language to another. 

%% so its capabilities are
%% as powerful as any other Turing-complete programming language. 

%% Being Turing-complete, it can emulate any other
%% Turing-complete language. Its direct support for manipulating
%% functions-as-values makes it a good choice for emulating higher-level
%% functional languages.

%% It is not a language that you want to write many 
%% programs in, 

%% Its sparse syntax
%% and straightforward evaluation rules means their is less to worry about
%% when trying out new design ideas or theories.  . Most importantly, though, 


%% Figure~\ref{lang_fig1} defines
%% a function for adding two numbers in Scheme, ML, Haskell and JavaScript,
%% some of the more prominent functional languages in use today. 




 
%% 1. Relate lambda-calculus to functional langauges in general
%% 2. Define the lambda-calculus
%%    * syntax, semantics, evaluation rules
%% 3. Compliling - or better to move that to MIL chapter?

%% Informally, a \emph{function} is a mathematical definition that takes
%% arguments and computes some result. For example, \emph{plus1} just adds 1 
%% to its argument, using the normal rules of arithmetic:
%% \begin{equation}
%%   |plus1|\ x = x + 1.
%% \end{equation}
%% We are not limited to defining functions that add 1. Functions can
%% also be \emph{values} -- just as 1 or $x$ are in the expression
%% above. Here, we define a function, that returns a function, that always
%% adds 1:
%% \begin{equation}
%%   |adder1| = \lambda\ x = x + 1.
%% \end{equation}
%% In |adder1|, ``$\lambda\ x$'' indicates we return a function that takes one
%% argument. We can go further and define a function that, given an
%% argument, returns a function which always adds that amount:
%% \begin{equation}
%%   |adder|\ n = \lambda\ x = x + n.
%% \end{equation}
%% Notice how the outer argument $n$ gets ``captured'' by the body $x +
%% n$. Using $|adder|$, we can now re-define $|adder1|$ above:
%% \begin{equation}
%%   |adder1| = |adder|\ 1.
%% \end{equation}

%% Other functional languages created since then include 
%% Scheme, ML, Haskell, and many more. While syntax, semantics and capabilities
%% differ widely between all these languages, they all share the characteristic
%% shown above: \emph{the ability to manipulate functions as first-class values}.

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

%% as \emph{rewrite} rules. 
%% Interestingly, these strategies are not strictly equivalent: some will
%% fail to terminate where others do not. The SuchAndSuch theorem states that,
%% if a term can 
%% The call-by-value strategy is used by many 
%% programming languages today: Java, C, PHP, and more. Call-by-name 
%% (under the variant call-by-need) is not very widely used -- the Haskell
%% programming language is one of the most prominent to employ it. 



%% using
%%   a variety Part \subref{lang_fig4_eval} shows to evaluate \lamA
%%   terms. Each rule should be read top-to-bottom. When a term matches
%%   the top of the rule, we rewrite according to the bottom
%%   portion. Each \texttt{\emph{t}} stands for an arbitrarily large term
%%   -- meaning we can ``match'' the portions in typewriter font, while
%%   ``parameterizing'' over \texttt{\emph{t}}. These rules show
%%   ``call-by-value'' style, where arguments are evaluated before
%%   functions. Other styles include ``call-by-need'' and
%%   ``call-by-name,'' where arguments are only evaluated as needed, but
%%   we do not address them here.

%% The {\sc E-App1} and {\sc E-App2} rules show that terms must be
%% reduced to values before application can be applied. {\sc E-App1}
%% ensures that the argument ($t_2$) is reduce to a value before the
%% function ($t_1$) is applied.  Each $v$ represents a value -- a term
%% that cannot be reduced any further. {\sc E-Abs} shows how arguments
%% are substituted in the body of an abstraction: the notation $[v/x] t$
%% means we replace all occurrences of $x$ in $t$ with $v$. There are
%% many subtle issues that arise when arguments have the same names as
%% parameters, but we do not need to worry about them here. {\sc E-Val}
%% lets us continue to reduce any terms found inside a $\lambda$ if
%% needed.  Notice, however, that no rule will match $\lambda$ terms
%% (i.e., abstractions) except when applied to an argument or when their
%% body is not fully evaulated: $\lambda$ terms are our values.


%% Every abstraction, \lamAbs{x}{t}, \emph{binds} its argument, $x$, in
%% the context of its body, $t$. Alternatively, we can say $x$ is
%% \emph{bound} by the abstraction. Our syntax allows us to write terms
%% containing \emph{free} variables -- variables not bound by any
%% enclosing abstraction. For example, $b$ is free in \lamAbs{a}{\lamApp{a}{b}},
%% but bound in \lamAbs{b}{\lamApp{a}{b}}. A term containing free variables
%% is \emph{open}; otherwise, it is \emph{closed}.


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

%% Nothing is built-in,
%% not even the natural numbers. There is almost nothing to get in the
%% way of studying your particular domain, rather than fiddling with the
%% programming language. However, the \lamA is inherently functional --
%% it can only define functions, and all values computed are really
%% functions. Translating from the \lamA to another functional language
%% is usually straightforward.\footnote{And, if not, maybe your target
%%   language isn't very functional.}

%% Its power, simplicity, and functional nature of the \lamA motivates
%% our own choice in using it. We do not show how to compile a
%% ``real-world'' functional language to our intermediate language, but
%% by showing how to compile the \lamA to our language, we show our
%% technique could be used by ``real'' functional languages (with some
%% adaptions, of course).

%% Using this syntax, we can define some common functions. |Identity|
%% returns its argument:
%% \begin{align}
%%   |identity| &= \lamAbs{x}{x}. \label{eq_lang2} \\
%%   \intertext{|Const| takes two arguments but always returns the first:}
%%   |const| &= \lamAbs{a}{\lamAbs{b}{a}}. \label{eq_lang4} \\
%%   \intertext{|Compose| takes two functions and an argument. The result of
%%     applying the second function to the argument is passed to the first:}
%%   |compose| &= \lamCompose. \label{eq_lang3} 
%% \end{align}
%% Note that function application is right-associative, meaning
%% \lamPApp{f}{\lamPApp{g}{x}} is the same as \lamApp{\lamApp{f}{g}}{x},
%% but \emph{not} the same as \lamPApp{\lamPApp{f}{g}}{x}.

%% \begin{myfig}[bt]
%% \begin{minipage}{2in}
%% \begin{Verbatim}
%%                 ##  
%%                  #  
%%  ##  ## ## ###   #  
%% ####  # ## ###   #  
%% #     ###  # #   #  
%%  ###   #   ## # ### 
%% \end{Verbatim}
%% \end{minipage}
%%   \caption{Evaluation rules for \lamA. These rules show 
%%     \emph{call-by-value}, where arguments are evaluated
%%     before functions.}
%%   \label{fig_lang2}
%% \end{myfig}

%% A \lamA term executes by rewriting the expression according to the
%% rules in Figure \ref{fig_lang2}. We match our term to each of the
%% patterns above the line. If we have a match, we rewrite according to
%% the pattern below the line. When no more matches can be made, we say
%% the term is in \emph{normal form}: we have finished executing.

%% The rules given implement \emph{call-by-value} evaluation order,
%% meaning arguments to a function are evaluated before the function
%% itself. Other variants include \emph{call-by-need} and
%% \emph{call-by-name}, where arguments are not evaluated until
%% needed. We do not considers those variants further, however.

\section{\lamC\ -- Extending the \lamA}
\label{lang_sec4}
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

%% \section{Why \LamA?}
%% \label{lang_sec1}

%% \section{Compiling the \LamA}
%% \label{sec_lang1}

%% %% Define which steps in compilation we're going to worry about
%% Compiling even a language as simple as the \lamA involves a number of
%% steps, such as defining a concrete syntax, parsing source programs
%% into an abstract syntax tree (AST), and producing an executable
%% program from the AST. For our purposes, however, we just focus on the
%% \lamA' three fundamental operations:

%% \begin{itemize}
%% \item Naming values (\emph{variables}).
%% \item Apply a function to an argument (\emph{application}).
%% \item Create a new function (\emph{abstraction}). 
%% \end{itemize}

%% Any compiler for the \lamA must be able to produce executable programs
%% which implement these operations. 

%% \subsection{The Target Machine}
%% We begin by defining a \emph{target machine}, |M|, for our compiler. To
%% reduce complexity we do not target an actual computer, but one of our
%% own design. Our machine will have an infinite number of
%% \emph{registers} (i.e., storage locations) that we can refer to by
%% name. It will have an unlimited supply of memory (called the
%% \emph{heap}) in which we can allocate structured values. However, we
%% will not refer to memory locations directly. Instead, we will always
%% store references to heap values in registers. Finally, the machine
%% will execute a list of instructions (our \emph{program}), starting at
%% the beginning and proceeding in sequential order (unless otherwise
%% instructed), until reaching the end of the list. Each instruction will
%% have a definite location, but we will only refer to certain special
%% locations using named labels.

%% \subsection{M's Language: \machLam}
%% Table \ref{tbl_lang1} gives the language that our machine will
%% execute, \machLam. A benefit of defining our own machine is that we
%% can also define the language it executes -- and the language we need
%% to compile to! We cannot make it too dissimilar from a ``real''
%% machine, but at this stage it helps to keep things simple. 

%% \begin{table}[th]
%%   \centering
%%   \begin{tabular}{lp{3.5in}}
%%     \emph{Instruction} & \emph{Description} \\
%%     \cmidrule(r){1-1}\cmidrule(r){2-2}
%%     \texttt{Store \emph{R} (\emph{F}, \emph{M})} & Store the value found in register #R# to field %%
%%     #F# of the value in register #M#. \\
%%     \texttt{Load (\emph{F}, \emph{M}) \emph{R}} & Load field #F# of the value in register #M# to register #R#. \\
%%     \texttt{Set \emph{v} \emph{R}} & Sets the register #R# to name of the variable $v$. \\
%%     \texttt{Copy \emph{R} \emph{M}} & Copies the contents of register #R# to register #M#. \\
%%     #Enter# & Jump to the location indicated by the closure in
%%     register #clo#, assuming an argument in register #arg#. The next #Return# executed
%%     will return to this location, with a result in register #res#.\\
%%     #Return# & Jump to the instruction following the most recently 
%%     executed #Enter# instruction and begin executing.  \\
%%     \texttt{MkClo \emph{L} [\emph{R}, \emph{S}, \dots]} &  Create a closure pointing to the 
%%     label #L# and holding the values in registers #R#, #S#, etc. The closure will be stored in 
%%     the #res# register.
%%   \end{tabular}
%%   \caption{\machLam, the ``machine language'' executed by our machine |M|.}
%%   \label{tbl_lang1}
%%   \figend
%% \end{table}

%% Each instruction supports an some aspect of the \lamA. In brief:
%% \begin{description}
%% \item[Variables] -- #Store# and #Load# help access variables and
%%   function arguments.
%% \item[Function Application] -- #Enter# and #Return# allow us to execute a function with arguments.
%% \item[Abstraction] -- #MkClo# lets us create functions as values.
%% \end{description}
%% The following sections describe each aspect in detail.

%% \subsection{Variables}
%% \label{subsec_lang1}

%% Free variables and environment
%% Consider how to find a value by its name. For example, consider
%% the |compose| function (expression \ref{eq_lang3}):
%% \begin{equation}
%%   \lamCompose.  \label{eq_lang1}
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
%% values. #Store# and #Load# (from Table \ref{tbl_lang1}) serve this
%% purpose. 

%% \subsection{Function Application}
%% \label{subsec_lang2}

%% Application & closures
%% Associating locations with names is not enough, however. Looking again
%% at expression \ref{eq_lang1}, $g$ clearly represents a function to
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
%% \label{subsec_lang3}
%% The \lamA lets us define functions which return new functions. We have
%% seen how to access variables in the environment and how to execute
%% unknown functions using closures. Now we come to the final element
%% needed to compile the \lamA\ -- creating closures.

%% Consider the following expression, where we apply the $|const|$ function (expression 
%% \ref{eq_lang4}) to an argument:
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

%% \subsection{Compiling from \lamA to \machLam}

%% Table \ref{tbl_lang2} gives our algorithm to compile from \lamA to
%% \machLam. We present it in in three parts, \emph{a} - \emph{c},
%% corresponding to the syntax of \lamA terms given in Figure
%% \ref{lang_fig2}. The ``fat brackets,'' \compMach{t}, represent our
%% compiler, with the term being compiled given as the argument, $t$.
%% Each term compiles to a given sequence of instructions. We also assume
%% a function $\rho$, maintained by the compiler, that knows which
%% register holds a given variable.

%% %% Compilation rules ...
%% \afterpage{\clearpage{\input{machLamComp}}\clearpage}

%% Table \ref{tbl_lang2}, part \emph{a}, shows the compilation
%% scheme for variables. Variable refrences that are not used
%% in function application can only be the body of an expression, so we
%% just copy the variable's name to the #res#
%% register and return.

%% Function application, \lamPApp{f}{g}, is shown in part
%% \emph{b}. To apply a function, we must save the current #clo#
%% and #arg# registers. The compiler creates \emph{fresh} registers,
%% guaranteed to be unused anywhere else in the program, to store #clo#
%% and #arg#. We then use $\rho$ to find the registers holding $f$ and
%% $g$. Remember that $f$ will be a closure, while $g$ will be some
%% value. We copy those values into #clo# and #arg#. The #Enter#
%% instruction will execute the code pointed to by #clo#. When that
%% function returns, we restore #clo# and #arg# from the fresh registers
%% created earlier.

%% Abstractions, such as \lamAbs{x}{t}, return a closure pointing to the
%% code implementing $t$. Therefore, our compiler needs to generate code
%% that returns a closure, which in turn points to the code generated for
%% the body of the abstraction. To accomplish this, our compiler
%% recursively calls itself on the body. We get a label back, which is the
%% location of the just compiled code. In parts \emph{c} and \emph{d}
%% the expression $l = \compMach{\lamAbs{y}{t}}$ shows this
%% recursive call, and the label that results. That label can then be used in the 
%% closure returned by the abstraction.

%% We separate compilation of abstractions into two cases, depending if
%% the body is an abstraction or not. In the first case, as shown in part
%% \emph{c}, we begin by marking the location of this code with a new label,
%% #m#. We prepare to create a new closure by copying all values out of
%% the current closure into fresh registers. We then create a closure that
%% points to the body of our abstraction, contains all the values found
%% in the current closure, and ``captures'' our argument in the new
%% closure. 

%% For example, consider compiling this expression:

%% \begin{equation}
%%   \lamAbs{x}{\lamAbs{y}{\lamApp{f}{\lamPApp{y}{x}}}}. 
%% \end{equation}

%% $f$ and $x$ must be available when the body
%% \lamPApp{f}{\lamPApp{y}{x}} executes. Therefore, the closure returned
%% by \lamAbs{x}{(\dots)} must copy all values in the existing
%% closure as well as add the argument, $x$.

%% Part \emph{d} shows the code generated when the body of an abstraction
%% is \emph{not} another abstraction. We first mark the location of the
%% start of the body with a new label, #m#.  We then find the free
%% variables in the body, calling them $v_1, \dots, v_n$. This is a
%% compile-time operation, not something the program will do when
%% executing.  We assume that value of each free variables can be found
%% in the corresponding closure slot. For example, $v_0$ will be found in
%% $clo[0]$, $v_1$ in $clo[1]$, and so on. We also copy the $arg$
%% register to the corresponding register for our argument, as determined
%% by the $\rho$ function. Now that we have placed all variables in the
%% registers expected by our function, we generate the code for our body
%% and place it inline.

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

%% Nothing is built-in,
%% not even the natural numbers. There is almost nothing to get in the
%% way of studying your particular domain, rather than fiddling with the
%% programming language. However, the \lamA is inherently functional --
%% it can only define functions, and all values computed are really
%% functions. Translating from the \lamA to another functional language
%% is usually straightforward.\footnote{And, if not, maybe your target
%%   language isn't very functional.}

%% Its power, simplicity, and functional nature of the \lamA motivates
%% our own choice in using it. We do not show how to compile a
%% ``real-world'' functional language to our intermediate language, but
%% by showing how to compile the \lamA to our language, we show our
%% technique could be used by ``real'' functional languages (with some
%% adaptions, of course).

%% Functional languages distinguish themselves by their ability to treat
%% \emph{functions} as \emph{first-class values}. The \lamA, invented
%% some time before the first functional language, turned out to be a
%% simple but effective way to model (and experiment with) the behavior
%% of functional languages. Therefore, understanding how to compile the
%% \lamA can effectively show us how to compile functional languages in
%% general.

%% This chapter gave the basic mechanisms needed to understand the \lamA:
%% \emph{variables}, \emph{application}, and
%% \emph{abstraction}. Understanding how to compile the \lamA means
%% understanding how to compile these three mechanisms. Variables become
%% \emph{locations}. Application means evaluating a function with a given
%% \emph{environment} for any \emph{free variables}. Abstractions create
%% \emph{closures} that carry two pieces of information: the location of
%% the compiled function body and the value of free variables to be used
%% when evaluating the function.

\end{document}
