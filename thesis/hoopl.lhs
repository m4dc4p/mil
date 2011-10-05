\documentclass[12pt]{report}
%include polycode.fmt
\input{preamble}
\begin{document}
\input{document.preamble}
\chapter{The Hoopl Library}
\label{ref_chapter_hoopl}

%% Introduction ...

The Hoopl library \citep{Hoopl-3.8.7.0}, written in Haskell, provides
a framework for implementing dataflow-based program analyses and
transformations (which we refer to together as ``optimizations''). The
library does not target a particular langauge or provide any built-in
optimizations; rather, Hoopl enables the user to implement their own
optimizations for their own language. A thorough description of the
library's implementation can be found in the authors' paper
\citep{Ramsey2010}; here, we discuss the abstractions they provide and
how to use Hoopl when implementing dataflow-based optimizations.

%% Broad description of how Hoopl abstracts the dataflow algorithm

Hoopl implements the generic portions of the dataflow algorithm:
iterative analysis, traversing the control-flow graph (CFG), and combining
facts. The \emph{client program}, a term Hoopl uses to mean the
program using the library for some optimization, provides data
structures and functions specific to that optimization: the
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

We will illustrate Hoopl concepts through a running example motivated
by the C function, #foo#, defined in Figure \ref{hoopl_fig1_a}. The
assignments on Lines \ref{hoopl_lst1_assign_a} and
\ref{hoopl_lst1_add} do not affect the output, or observable behavior,
of #foo#. Eliminating them will not change the program's meaning and
may improve its performance. However, we could not eliminate the
assignment to #c# on Line \ref{hoopl_lst1_assign_c} because that would
change the value printed on Line \ref{hoopl_lst1_print}. In general, a
\emph{live} variable might be used in an observable way; a \emph{dead}
variable will definitely not. 

\begin{myfig}
\begin{tabular}{cc}
  \input{hoopl_lst1} & \input{hoopl_lst2} \\
  \scap{hoopl_fig1_a} & \scap{hoopl_fig1_b}
\end{tabular}
\caption{Part \subref{hoopl_fig1_a} defines function defined in
  C. Part \subref{hoopl_fig1_b} shows the program after perfomring
  dead-code elimination.}
\label{hoopl_fig1}
\end{myfig}

\emph{Dead-code elimination} refers to the process described above:
determing variable ``liveness'' and removing statements only using dead
variables. Our running example will implement a client program that
performs dead-code elimination for enough of the C language to apply
it to Figure \ref{hoopl_fig1_a}. Our example will be able to
analyze and rewrite #foo# into the form show in Figure
\ref{hoopl_fig1_b}.

%% Provides signposts for chapter.

In Section \ref{hoopl_sec1}, we describe Hoopl's abstractions, showing
the Haskell types, data structures, and function signatures provided
by the library. Throughout, we develop our client program to implement
dead-code elimination and show how it optimizes the program in Figure
\ref{hoopl_fig1_a}. Section \ref{hoopl_sec2} shows how Hoopl influenced
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

%% Introduce parameterization of blocks by AST and shape.

Hoopl defines CFGs in terms of basic blocks, parameterized by
\emph{content} and \emph{shape}. Content means statements or
expressions from the client's AST. Shape can be either \emph{open} or
\emph{closed} and applies to both the entry and exit of the block.
Roughly, ``open'' allows control-flow to fall through the block;
``closed'' means control-flow branches from the block.

%% Introduce meaning and definition of O and C types.

Hoopl provides types named |O| and |C|, representing open and
closed. Neither needs constructors as we only use them to parameterize
other types:

> data O 
> data C

Hoopl uses the |O| and |C| types to constrain the edges between blocks
in the CFG. As open and closed describe both the entry and exit point
of the block, we write them as |O O| (``open/open''), |O C|
(``open/closed''), etc., where the first describes the block's entry
shape and the latter its exit shape. An |O C| block allows one
predecessor block but many successors (i.e., control-flow branches on
exit). An |O O| block permits exactly one predecessor and one
successor (i.e., control-flow falls through on exit). Table
\ref{hoopl_tbl1} summarizes the meaning of the different block shapes.

\begin{myfig}[tb]
  \begin{tabular}{cccr}
    Shape & Predecessors & Successors & Example Statement \\\midrule
    |O C| & One & Many & Conditionals, jumps. \\
    |C O| & Many & One & Function entry points, branch labels. \\
    |O O| & One & One & Assignments, statements. \\
    |C C| & Many & Many & Function bodies. \\
  \end{tabular}
  \caption{This table shows the four entry and exit shapes that Hoopl
    defines for blocks. It also shows the number of predecessors and
    successors allowed by each shape, as well as example
    statements.}
  \label{hoopl_tbl1}
\end{myfig}

Using |O| and |C|, we can define an AST for our subset of C as 
follows:

%let includeAst = True
%include DeadCodeC.lhs
%let includeAst = False

%% Introduce types necessary to construct graphs; use of O and C
%% types in graphs.

Hoopl represents blocks with the |Block| type and graphs with the
|Graph'| type. |Graph'| is parameterized by block type; however, Hoopl
also provides an alias, |Graph|, which specifies |Block| and that
works well in practice:\footnote{|Block| and |Graph'| define a number
  of constructors but they do not relate to our presentation and so we
  elide them.}

> data Block n e x = {-"\dots"-}
> data Graph' block n e x {-"\dots"-}
> type Graph = Graph' Block

The parameters |e| and |x| (``entry'' and ``exit'') describe the shape
of the block (or graph) and must be |O| or |C|. The |n| (for ``node'')
parameter specifies the contents of each block (or graph) and will be
the type of the AST used by the client program.

%% 

Client programs construct graphs using methods specified by the
|GraphRep| class. While |GraphRep| allows the client to implement
their own graph representation, but we do not use that here. Instead,
we use Hoopl's instances defined for |Graph| and give those signatures
instead of the more general method definitions:

>   mkFirst  :: n C O -> Graph n C O
>   mkMiddle :: n O O -> Graph n O O
>   mkLast   :: n O C -> Graph n O C
>   (<*>)    :: NonLocal n => Graph n e O -> Graph n O x -> Graph n e x

|mkFirst|, |mkMiddle| and |mkLast| all turn a single block into a
graph of one node with the same shape.  Notice that the
resulting |Graph| has the same shape as the argument.

The graph concatenation operator, |(<*>)|, connects graphs
together. Ignoring the |NonLocal| constraint for the time being, its
signature specifies that the predecessor graph must be open on exit
and the successor must be open on entry. The resulting graph's shape
will depend on the two arguments: |O C|, |C O|, |C C|, or |O O|. This
method concatenates graphs such that control-flow falls through
each. |e C| predecessors and |C x| successors do not fall through: the
former branches to multiple successors, while the latter may have
multiple predecessors. In both cases, the type of |(<*>)| prevents
such graphs.



The |n| parameter on each method in |GraphRep| represents the AST of
the language that the client program targets. Notice that the
statement must be parameterized with the correct |O| and |C|
type. 


|mkFirst| creates an 
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
