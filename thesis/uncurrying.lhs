\documentclass[12pt]{report}
 %include polycode.fmt
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
style, after the mathematician Haskell Curry.\footnote{Historically,
  Curry used this style but did not invent it. That is due to a early
  $20^{th}$--century mathematician named Schrodenfinkel.} In contrast,
an \emph{uncurried} function is defined such that it can only be
applied to all of its arguments at once.

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

\intent{signposts.}
Section~\ref{uncurry_sec_papp} describes partial application in 
more detail and introduces several examples that we will use
to demonstrate our optimization. We will discuss uncurrying
as applied to MIL in Section~\ref{uncurry_sec_mil}. We present
our dataflow equations for uncurrying in Section~\re{uncurry_sec_df},
and describe our implementation in Section~\ref{uncurry_sec_impl}. Alternate
uncurrying strategies, which we leave to future work, are shown in
Section~\ref{uncurry_sec_future}. We conclude with a discussion of our
experience in Section~\ref{uncurry_sec_conc}.

%% \emph{Describes our optimization for collapsing intermediate
%% closures. Our choice of representation is analyzed to
%% show how it facilitates this optimization. We should show one
%% closure can be eliminated from a program and how the optimization
%% is applied over and over until a fixed point is reached. The format
%% for this section will vary from the other two.}

\section{Partial Application}
\label{uncurry_sec_papp}
\intent{Motivate partial application -- what does it buy us? Introduce example too.}

\section{Uncurrying MIL blocks}
\label{uncurry_sec_mil}
\intent{Describe uncurrying in terms of MIL -- what do we do, what don't we do.}

\section{Dataflow Equations}
\intent{Define dataflow equations for our uncurrying optimization.}

\begin{myfig}
\begin{math}
%% Below used to measure & typeset the case where we don't
%% see a binding.
\newtoks\rest \rest={f (!+v\ \texttt{<-}\ \dots+!)} %%
  \begin{array}{rl}
    \multicolumn{2}{l}{\textit{Facts}} \\
    \setL{Labels} &= \text{Set of all program labels.} \\
    \setL{Vars} &= \text{Set of all variables.} \\
    \setL{Dest} &= \{\top\} \cup \setL{Labels}. \\
    \setL{Fact} &= \{(v, b)\ ||\ v \in \setL{Vars}, b \in \setL{Dest}\}. \\

    \multicolumn{2}{l}{\textit{Meet}} \\
    b \wedge b &= b. \\
    b \wedge c &= \top, b \neq c. \\
    & \text{where\ } b, c \in \setL{Dest}. \\\\

    \multicolumn{2}{l}{\textit{Transfer Function}} \\
    \phantom{\the\rest} \mathllap{f (!+v\ \texttt{<-}\ k\ b\ \{\dots\}+!)} &= %%
    \begin{cases}
      \{!+(v, b \wedge c)+!\} \cup (F \backslash \{!+(v, c)+!\}) & \text{when\ } !+(v, c)+! \in F. \\
      \{!+(v, b)+!\} \cup F & \text{otherwise.}\\
    \end{cases} \\
    \the\rest &= \{!+(v, \top)+!\} \cup F.\\
    f (!+\_+!) &= F. \\
    & \text{where\ } F \subseteq \setL{Fact}.
  \end{array}
\end{math}
\caption{Dataflow facts and equations for our uncurrying transformation.}
\label{uncurry_df_fig}
\end{myfig}

\section{Implementation}

\intent{Define curried and uncurried.}
Functional languages permit definitions in two styles: \emph{curried}
and \emph{uncurried}. A curried function can be \emph{partially
  applied} --- it does not need to be given all of its arguments at
once. An \emph{uncurried} function, however, must be given
all of its arguments at once. It cannot be partially applied. 

\intent{Illustrate curried vs. uncurried.}  For example, the following
Haskell code defines |adder| in curried style and |multiplier| in
uncurried style:

\begin{code}
adder :: Int -> Int -> Int
adder a b = a + b

multiplier :: (Float, Float) -> Float
multiplier (a,b) = a * b
\end{code}

\noindent
When applied to a single argument, |adder| returns a function that we
can re-use over and over. Now we can use |adder| to defined specialized 
functions such as |add1|:

\begin{code}
add1 :: Int -> Int
add1 = adder 1
\end{code}

We cannot do the same with |multiplier|. At best we can define
a function that ignores one of its arguments:

> mult1 :: (Float, Float) -> Float
> mult1 (a, _) = multiplier (a, 1)

%% Why is this a problem? Need more motivation
The implementation of partial application, however, does come at a
cost. Each partial application requires that we construct a closure
over the arguments captured so far. That closure represents a function
specialized to the arguments given so far. In general, we don't know
the address of the function it contains when compiling -- only at
run-time. Therefore, when the closure is applied to the rest of the
arguments, we cannot generate code that jumps to a known
address. Instead, we must look at the address in the closure at
run-time and then jump.

Because each function application |f x| may result in another
function, the most general implementation strategy makes \emph{every}
application result in a closure. The compiler need only generate code
that inspects the closure constructed and jumps to the address
indicated. When a curried function is applied to all of its arguments
at once (e.g., |adder 1 2|), we get a chain of function calls where
most construct a closure and immediately return. It would be more
efficient to collect all arguments at once and immediately jump to the
function body. \emph{Uncurrying} is the transformation we use to turn 
fully-applied curried functions into direct calls to the function body.

%% TODO: Talk about how we can look for fully-applied forms
%% as a special case, but that is sub-optimal

%% TODO: What is an example of a fully-applied function that we cannot
%% recognize syntatically (very easily)?

\section{Example of Desired Optimization}

Suppose we define the functions |main| and |compose| as follows:

\begin{code}
compose f g x = f (g x)
main a b x = compose a b x
\end{code}

Our compiler generates the following code, before optimization:
\begin{singlespace}\begin{MILVerb}[gobble=2]
  main (compose, a, b, x):
    v201 <- compose @@ a
    v202 <- v201 @@ b
    v202 @@ x

  compose (): closure absBody201 {}
  absBody201 {} f: closure absBody203 {f}
  absBody203 {f} g: closure absBody205 {f, g}
  absBody205 {f, g} x: absBlock207(f, g, x)
  absBlock207 (f, g, x):
    v209 <- g @@ x
    f @@ v209
\end{MILVerb}
\end{singlespace}

We wish to transform our program in order to remove the intermediate
closures created by calling !+compose+!:
\begin{singlespace}\begin{MILVerb}
main (a, b, x): absBlock208(a, b, x)
absBlock208 (f, g, x):
  v210 <- g @@ x
  f @@ v210
\end{MILVerb}
\end{singlespace}

\section{Implementation}

\intent{Describe how we recognize when a closure is created} Our
transfer function analyzes each statement in each block. The function
inspects the right-hand side of each |Bind| statement in the
block. When the right-hand side creates a closure, the function
associates the binding with the destination label and captured
arguments used by the closure. Any other |TailM| value is represented
as $\top$.

At the end of each block, the transfer function passes the facts
collected to each successor. 


\intent{Describe how we re-write an Enter instruction to a closure or goto}

\intent{Describe how deep rewrite progressively captures closures.}

\section{Prior Work}

\section{Future Work}
\lable{uncurry_sec_future}
\intent{Discuss strategies for uncurrying: local only, across blocks, by duplication.}

\section{Reflection}
\label{uncurry_sec_refl}
\end{document}
