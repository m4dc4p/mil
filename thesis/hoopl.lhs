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

Hoopl defines CFGs in terms of basic blocks. The library parameterizes
blocks by \emph{content} and \emph{shape}. Content means statements or
expressions from the client's AST. Shape can be either \emph{open} or
\emph{closed} and applies to both the entry and exit of the block. 
Roughly, ``open'' allows control-flow to fall through the block; ``closed''
means control-flow branches from the block. 

Hoopl provides types representing open and closed, |O| and
|C|. Neither needs constructors as we only use them to parameterize
later types. As open and closed apply to both entry and exit, we write
them as |O O| (``open/open''), |O C| (``open/closed''), etc., where the
first describes the block's entry shape and the latter its exit shape.

> data O 
> data C

Hoopl defines the |Block| type to represent blocks:

> data Block n e x = {-"\dots"-}

The parameters |e| and |x| (``entry'' and ``exit'') describe the shape
of the block and must be |O| or |C|. The |n| (for ``node'') parameter
specifies the contents of the each block and will be the type of the
AST used by the client program. |Block| defines a number of
constructors but they do not relate to our presentation and we ignore
them. In practice, they are rarely used.

The |O| and |C| types, with the |e| and |x| parameters, constrain the
edges between blocks. An |O C| block allows one predecessor block but
many successors (i.e., control-flow branches on exit). An |O O| block
permits exactly one predecessor and one successor (i.e., control-flow
falls through on exit). |C O| blocks allow many predecessors but only
a single successor (i.e., the block can be the target of many
jumps). Table \ref{hoopl_tbl1} summarizes the meaning of the different
block shapes.

\begin{myfig}[tb]
  \begin{tabular}{cccr}
    Shape & Predecessors & Successors & Example Statement \\\midrule
    \texttt{O C} & One & Many & Conditionals, jumps. \\
    \texttt{C O} & Many & One & Function entry points, branch labels. \\
    \texttt{O O} & One & One & Assignments, statements. \\
    \texttt{C C} & Many & Many & Function bodies. \\
  \end{tabular}
  \caption{This table shows the four entry and exit shapes that Hoopl
    defines for blocks. It also shows the number of predecessors and
    successors allowed by each shape, as well as example
    statements.}
  \label{hoopl_tbl1}
\end{myfig}

Hoopl's forms blocks into graphs using the |Graph'| type. |Graph'|
allows the block type to vary, but in practice the alias |Graph| works
well. |Graph'| exports several constructors but we rarely use them and
omit them here:

> type Graph = Graph' Block
> data Graph' block n e x {-"\dots"-}

Client programs construct graphs from blocks using functions from
the class |GraphRep|. The class parameterizes
each method by the shape of blocks it accepts and the shape of
the graph produced:

> class GraphRep g where
>   mkFirst  :: n C O -> g n C O
>   mkMiddle :: n O O -> g n O O
>   mkLast   :: n O C -> g n O C

While |GraphRep| allows the client to implement their
own graph representation, but we do not use that here. Instead, we use
Hoopl's instances defined for |Graph|. |mkFirst| creates an 
entry point in the graph; |mkMiddle| concatenates blocks together such
that control-flow falls through each; |mkLast| creates a branching
block. 

A closed on entry
block block can be the target of a jump; i.e., an open block can be
the successor of another block. A closed block cannot be the target of
a jump, but it can jump to one of many blocks; for example, a |switch|
statement in C can be represented as a closed block that could branch
to any of the case labels.

\subsection*{Blocks and the Client AST}

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
