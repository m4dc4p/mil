\documentclass[12pt]{report}
%include polycode.fmt
\input{preamble}
\begin{document}
\input{document.preamble}
\chapter{The Hoopl Library}
\label{ref_chapter_hoopl}

%% Introduction ...

The Hoopl library \citep{Hoopl-3.8.7.0}, written in Haskell, provides
a framework for implementing optimizations using the dataflow
algorithm. It does not target a particular programming language or
provide specific optimizations; rather, it enables the user to
implement their own optimizations for their own language. A
thorough description of the implementation of the library can be found
in the authors' paper \citep{Ramsey2010}; here, we discuss the
abstractions they provide and how to use Hoopl when implementing
dataflow-based optimizations.

%% Broad description of how Hoopl abstracts the dataflow algorithm

Hoopl applies a given optimization to a control-flow graph (CFG),
iteratively collecting facts (either forward or backward) until
reaching a fixed point. The library implements the generic portions of
the dataflow algorithm: iterative analysis, traversing the CFG, and
combining facts between blocks. The \emph{client program}, a term
Hoopl uses to mean a program implementing some optimization, provides
data structures and functions for that specific optimization: the
representation of facts, a transfer function, a meet operator such
that the facts can be placed in a lattice, and a rewriting function
that transforms the CFG.

%% Discuss Hoopl's implementation of the iterative analyze/rewrite
%% technique discussed in Lerner's paper.

%% TODO: Read the paper.
%% Hoopl diverges from standard dataflow analysis by implementing the
%% interleaved analysis and rewriting technique described in
%% \cite{Lerner2002}.

%% Introduce example

Throughout this chapter we will explain Hoopl concepts by implementing
a client program that performs \emph{dead-code elimination} for a very
small subset of the C language. Dead-code elimination removes
``useless'' statements from a program. The definition of ``useless''
varies according to programming language, hardware, and user intent,
but in all cases it implies that the semantics of the program do not
change.

Figure \ref{hoopl_fig1} defines a function in C. The assignments to
|a| on Lines \ref{hoopl_lst1_assign_a} and \ref{hoopl_lst1_add} do
not affect the behavior of the function and can be safely
eliminated. We will develop a client program that can 
analyze this function and transform it as described.


\begin{myfig}
\begin{tabular}{cc}
  \begin{minipage}[b]{2in}
    \begin{AVerb}[numbers=left]
void f() {
  int c = 4; \label{hoopl_lst1_assign_c}
  int a = c + 1;  \label{hoopl_lst1_assign_a}
  print(c); \label{hoopl_lst1_print}
  a = c + 1; \label{hoopl_lst1_add};
}
    \end{AVerb}
  \end{minipage} & 
  \begin{minipage}[b]{2in}
    \begin{AVerb}[numbers=left]
void f() {
  int c = 4; \label{hoopl_lst2_assign_c}
  print(c); \label{hoopl_lst2_print}
}
    \end{AVerb}
  \end{minipage} \\
  \scap{hoopl_fig1_a} & \scap{hoopl_fig1_b} 
\end{tabular}
\caption{Part \subref{hoopl_fig1_a} defines function defined in
  C. Part \subref{hoopl_fig1_b} shows the program after perfomring
  dead-code elimination.}
\label{hoopl_fig1}
\end{myfig}

%% Provides signposts for chapter.

In Section \ref{hoopl_sec1}, we describe Hoopl's abstractions, showing
the Haskell types, data structures, and function signatures provided
by the library. Throughout, we develop our client program to implement
dead-code elimination and show how it optimizes the program in Figure
\ref{hoopl_fig1}. Section \ref{hoopl_sec2} shows how Hoopl influenced
the implementation the MIL language from Chapter \ref{ref_chapter_mil}
and discusses the design choices we made. We conclude with a summary
and brief discussion of our experience with Hoopl in Section
\ref{hoopl_sec3}.

\section{Hoopl's Representation of the Dataflow Algorithm}
\label{hoopl_sec1}

%% Hoopl parameters: Hoopl-defined structures

In order to implement dataflow analysis generically, Hoopl defines
several core data structures which client programs must use. These
include: the representation of CFGs, the type of transfer and rewrite
functions, and the represention of the meet operator. Hoopl controls
the CFG representation so it can traverse, rewrite, and propagate
facts around the CFG. Hoopl specifies the type of the transfer and
rewrite function such that they produce useable information (and
rewrites). Finally, Hoopl specifies the meet operator (but not its
implementation) so that the library can find fixpoints.

%% Hoopl parameters: User-defined structures

Hoopl requires that client programs specify those items related to
their specific optimization: the abstract syntax tree (AST) of the
language, the representation of facts, and the implementation of the
transfer and rewrite functions. Each node in the CFG typically
contains an expression or statement from the client programs
AST. While Hoopl controls the edges between nodes in the CFG, it does
not specify the contents of those nodes. Similarly, while Hoopl
determines when the analysis reaches a fixpoint, it requires that the
client specify when one set of facts equals another. Finally, Hoopl
applies the transfer and rewrite functions to the CFG but requires
that the client program implement them for their specific AST and
optimization.

\subsection*{Control-Flow Graphs}

Hoopl defines CFGs in terms of \emph{successors} and
\emph{predecessors}. Additionally, Hoopl parameterizes blocks as
\emph{open} or \emph{closed} on entry and exit. Roughly, ``open''
means control-flow enters the block. ``Closed'' means control-flow
branches from the block. As open and closed apply to both entry and
exit, we write them as ``open/open'', ``open/closed'',
``closed/open,'' and ``closed/closed.''

> type Graph = Graph' Block
> data Block n e x where
>   {-"\ellipsis"-}
>
> data Graph' block n e x where
>   GNil  :: Graph' block n O O
>   GUnit :: block n O O -> Graph' block n O O
>   GMany :: MaybeO e (block n O C) 
>         -> LabelMap (block n C C)
>         -> MaybeO x (block n C O)
>         -> Graph' block n e x

An ``open/open'' block can be
the successor of another block (i.e., it can be the target of a jump
or normal straight-line execution).  There may not be any predecessor,
of course. However, the same block must be the predecessor of another
block.

A closed on entry
block block can be the target of a jump; i.e., an open block can be
the successor of another block. A closed block cannot be the target of
a jump, but it can jump to one of many blocks; for example, a |switch|
statement in C can be represented as a closed block that could branch
to any of the case labels.

\subsection*{Facts and Lattices}

\subsection*{Transfer Functions}

\subsection*{Iteration \& Fixed Points}

\subsection*{Interleaved Analysis \& Rewriting}

\section{MIL and Hoopl}
\label{hoopl_sec2}

\subsection{MIL Statements, Tails, \& Shapes}

\section{Summary}
\label{hoopl_sec3}

\standaloneBib

\end{document}
