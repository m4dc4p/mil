\documentclass[12pt]{report}
 %include polycode.fmt
\input{preamble}
\begin{document}
\input{document.preamble}

\chapter{Uncurrying}
\label{ref_chapter_uncurrying}
\intent{Introduce curried and uncurried terms; describe uncurrying}

%% \emph{Describes our optimization for collapsing intermediate
%% closures. Our choice of representation is analyzed to
%% show how it facilitates this optimization. We should show one
%% closure can be eliminated from a program and how the optimization
%% is applied over and over until a fixed point is reached. The format
%% for this section will vary from the other two.}

\section{Partial Application}
\intent{Motivate partial application -- what does it buy us? Introduce example too.}

\section{Uncurrying MIL blocks}
\intent{Describe uncurrying in terms of MIL -- what do we do, what don't we do.}

\section{Dataflow Equations}
\intent{Define dataflow equations for the uncurrying optimization}

\begin{math}
\newtoks\rest \rest={f (\mathtt{v\ \texttt{<-}\ \dots}, F)} %%
  \begin{array}{rl}
    \multicolumn{2}{l}{\textit{Facts}} \\
    \setL{Labels} &= \text{Set of all program labels.} \\
    \setL{Vars} &= \text{Set of all variables.} \\
    \setL{Dest} &= \{\top\} \cup \setL{Labels}. \\
    \setL{Fact} &= \{(v, x)\ ||\ v \in \setL{Vars}, x \in \setL{Dest}\} \\

    \multicolumn{2}{l}{\textit{Meet}} \\
    x \wedge \top &= \top, x \in \setL{Dest}. \\
    \top \wedge x &= \top, x \in \setL{Dest}. \\
    x \wedge y &= \top, x, y \in \setL{Dest}, x \neq y. \\\\

    \multicolumn{2}{l}{\textit{Transfer Function}} \\
    
    \phantom{\the\rest} \mathllap{f (\mathtt{v\ \texttt{<-}\ k\ b\ \{\dots\}}, F)} &= \{(\mathtt{v, b})\} \cup F \\
    \the\rest &= \{(\mathtt{v}, \top)\} \cup F\\
    f (\_, F) &= F \\
    \multicolumn{2}{c}{F \dots \subseteq \setL{Fact}.}\\\\
  \end{array}
\end{math}

\section{Implementation}

\intent{Define curried and uncurried.}
Functional languages permit definitions in two styles: \emph{curried}
and \emph{uncurried}. A curried function can be \emph{partially
  applied} --- it does not need to be given all of its arguments at
once. A function that takes the remaining arguments results from such
an application. An \emph{uncurried} function, however, must be given
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

Recall from Section \ref{ref_foo} our definition of |foldr|:

\begin{code}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr f b (a:as) = foldr f (f a b) as
foldr f b []     = b
\end{code}

which compiles to the following blocks in our MIL:

\begin{code}

\end{code}

\section{Implementation}
\section{Reflection}
\subsection{Prior Work}
\emph{...}

\end{document}
