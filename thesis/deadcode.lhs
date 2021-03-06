\documentclass[12pt]{report}
%include polycode.fmt
\input{preamble}
\begin{document}
\input{document.preamble}

\chapter{Dead-code elimination}

Dead-code elimination seeks to remove program statements that will not
be executed or which have no visible effect. It can be applied at
multiple points during compilation, as other transformations
frequently introduce dead code. Without dead-code elimination, many
other optimizations have minimal effect, since they leave behind code
which still executes even if it is no longer needed.

For our MIL, we want to eliminate two types of dead code: bindings and
blocks. Dead bindings represent allocations we do not need to
make. Dead blocks increase the size of our program without providing
any benefit. To illustrate these two types of dead code, consider
the following program:

\begin{code}
main = do
  a <- 1 + 2
  b <- block1(a)
  c <- a + a
  return c

block1 (a) = {-"\dots \emph{elided} \dots"-}
\end{code}

In |main2|, |a| and |c| will be used, but |b| will not. The binding to
|b| is therefore dead and can be eliminated.\footnote{If |block1| had
  a side effect this would not be the case, but we assume it is does
  not for now.} With |b| gone, our program becomes:

\begin{code}
main = do
  a <- 1 + 2
  c <- a + a
  return c

block1 (a) = {-"\dots \emph{elided} \dots"-}
\end{code}

In the new program, |block1| is not called and can be eliminated. This
not only demonstrates how dead-code can be removed, it also shows that
iteratively applying the optimization can result in multiple
eliminations.

\section{Eliminating Bindings}
\label{dead_sub_elim_bindings}

A binding can be eliminated if no references to the bound variable
occur after the initial binding. Within each block, we find all the
variables which are ``live'' (i.e., used after being bound) and then
eliminate any binding which is not in the live set. 
Hoopl traverses each block backwards, applying the transfer function in turn to each statement. 
Variables used are collected in the set of live
variables, while new bindings remove variables from the set. 

After gathering facts for a statement, Hoopl then applies the rewrite
function to the next statement. If the statement binds a variable that
is not in the live set, the statement can be eliminated. Otherwise the
statement is unchanged and Hoopl applies the transfer function to it,
gathering new facts.

% Tempoarily change comment style for this example.
%if style == poly
%subst comment a = "\texttt{\emph{" a "}}"
%endif

\begin{figure}[b]
  \begin{code}
    --  1. live: [c] 
    a <- block1(c) -- -- C
    --  2. live: [c, a]
    b <- block2(a) -- -- B
    --  3. live: [c]
    a <- block3(c) -- -- A
    --  4. live: [a] 
    return a 
    --  5. live: []
  \end{code}
  \caption{A program fragment with the ``live'' variable set annotated between each fragment.}
  \label{fig_dead1}
\end{figure}

To illustrate, consider the program fragment in Figure
\ref{fig_dead1}, where the live set is annotated between each
statement. For illustration, we do not rewrite any statements.
At the end of the block (where analysis begins), no
variables are live (\#5). After |return a|, |a| is in live set
(\#4). However, the next statement, |a <- block3(c)|, removes
|a| from the live set and adds |c| (\#3). At point \#2, a new |a| (different than
the one at \#4) is added. That |a| is removed by the next statement, leaving 
only |c| in the live set (\#1). 

With rewriting, the program changes as Hoopl interleaves analysis and
rewriting. At statement #A# (the first to bind a variable),|a| is
bound and also appears in the live set (\#4). Therefore, we do not
elminate it. At #B#, |b| is bound but it does appear \emph{not} in the
live set (\#3), so we eliminate it. 

Hoopl's ability to analyze the \emph{updated} program works to our
advantage now. With line #B# eliminated, we also update the live
set. Figure \ref{fig_dead2} shows our updated program with new live
sets. 

\begin{figure}[h]
  \begin{code}
    --  1. live: [c] 
    a <- block1(c) -- -- C
    --  2. live: [c]
    a <- block3(c) -- -- A
    --  4. live: [a] 
    return a 
    --  5. live: []
  \end{code}
  \caption{Our program fragment from Figure \ref{fig_dead1} with line B removed.}
  \label{fig_dead2}
\end{figure}

Notice that the live set at \#2 no longer contains |a|. Our rewrite
function now considers line #C# with the update live sets and
eliminates it. Figure \ref{fig_dead3} shows the final program.

\begin{figure}[h]
  \begin{code}
    a <- block3(c)
    return a 
  \end{code}
  \caption{The final program with all dead bindings eliminated.}
  \label{fig_dead3}
\end{figure}

% Restore poly-style comments
%if style == poly
%subst comment a = "\mbox{\onelinecomment " a "}"
%endif

\subsection*{Safe Bindings}

As eluded to in this chapter's introduction, we can only eliminate
bindings that do not have any side-effects (except
allocation). Fortunately, all bindings with side-effects in MIL will
use the |Invoke| statement. As long as a binding does not takes its value
from a |Invoke| statement, it can be eliminated.

\subsection*{Implementation}

%let deadcode = True
%include Live.lhs

\section{Eliminating Blocks}

%% TODO - talk about direction of analysis, and more about
%% dataflow analysis.

We eliminate blocks that will never execute in order to decrease code
size and memory footprint. ``Dead'' blocks are found in much the same
way as dead variables, except we consider the whole program. Since MIL
does not have computed labels, we know that if a block is never
referenced in a |Goto| or |Closure| statement then it will never be
called. Any block which is referenced will be considered ``live''; all
other will be eliminated.

Our algorithm uses Hoopl to find all the blocks referenced within a
given block. From this set , we create a map of blocks to their
predecessors -- that is, for each block, we determine who calls that
block. This map allows us to determine which blocks have no
predecessors -- that is, they are not referernced. We eliminate those
blocks and repeat the analysis until no more blocks can be eliminated.

\subsection*{Implementation}

%include DeadBlocks.lhs

\section{Reflection}
%% \emph{What was good, what didn't work so well, and how Hoopl helped
%% or hindered the implementation}

The Hoopl library made the implementation of dead-code elimination
straightforward. Because it interleaves analysis and rewriting,
removing one useless binding can make other bindings useless, which
will in turn be removed.

%{

%% This ensures the "." in the forall statement does not
%% format as composition.

%format . = ".\ "

Unfortunately, the same cannot be said for dead block
elimination. Hoopl's interface does not allow a block to be removed
during rewrite. This is a consequence of the type our rewriting
function must have: |(FuelMonad m) => (forall e x. StatM e x -> Fact x
f -> m (Maybe (Graph StatM e x)))|.  The result type of this function
can be |Nothing| or |Just g|, where |g| is a new graph, with one or
more statements. |Nothing| means the statement is unchanged. |Just g|
does not let us express that the statement should be deleted in all
cases. When the type is |O O|, we can return |emptyGraph|. But when
the type is |C O| or |O C|, there is no constructor that lets us
delete the node. At best, we can replace statements with no-ops or
special-purpose ``markers'', but we cannot truly eliminate the block
during rewrite.

%}

Consequently, we have to implement our own iterative process to
eliminate all dead blocks (as shown in |deadBlocks| above), including
those which become dead when another block is eliminated.

\end{document}
