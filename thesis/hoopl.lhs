\documentclass[12pt]{report}
%include polycode.fmt
\input{preamble}
\begin{document}
\input{document.preamble}
\chapter{The Hoopl Library}
\label{ref_chapter_hoopl}

\section{Introduction}
\label{hoopl_sec4}

\intent{Introduction}
The Hoopl library \citep{Hoopl-3.8.7.0}, written in Haskell, provides
a framework for implementing program analyses and transformations,
which we call ``optimizations,'' using dataflow analysis. The library
does not target a particular language or provide any built-in
optimizations; rather, Hoopl enables the user to implement their own
optimizations for their own language. A thorough description of the
library's implementation can be found in the authors' paper
\citep{Ramsey2010}; here, we discuss the abstractions they provide and
how to use them.

\intent{Broad description of how Hoopl abstracts dataflow optimization}

Hoopl implements the generic portions of dataflow analysis:
iterative computation, traversing the control-flow graph (CFG), and
combining facts. The \emph{client program}, a term Hoopl uses to mean
the program using the library for some optimization, provides data
structures and functions specific to that optimization: the
representation of facts, a transfer function, a meet operator, and a
rewriting function that transforms the CFG.

%% Discuss Hoopl's implementation of the iterative analyze/rewrite
%% technique discussed in Lerner's paper.

%% TODO: Read the paper.
%% Hoopl diverges from standard dataflow analysis by implementing the
%% interleaved analysis and rewriting technique described in
%% \cite{Lerner2002}.

\intent{Introduce example}

We will illustrate Hoopl concepts through a running example motivated
by the function defined in Figure~\ref{hoopl_fig1_a}. The assignments
to \texttt{a} on Lines~\ref{hoopl_lst1_assign_a} and
\ref{hoopl_lst1_add} do not affect the output (i.e., observable
behavior)of !+foo+!. Eliminating them will not change the program's
meaning and may improve its performance. However, we could not
eliminate the assignment to !+c+! on Line~\ref{hoopl_lst1_assign_c}
because that may change the value printed on
Line~\ref{hoopl_lst1_print}. We call variables that may affect
observable behavior \emph{live}; a \emph{dead} variable is not
live. Figure~\ref{hoopl_fig1_b} shows one way we could optimize this
program by eliminating the ``dead'' statements in
Figure~\ref{hoopl_fig1_a}.

\begin{myfig}
\begin{tabular}{cc}
  \input{hoopl_lst1} & \input{hoopl_lst2} \\
  \scap{hoopl_fig1_a} & \scap{hoopl_fig1_b}
\end{tabular}
\caption{Part~\subref{hoopl_fig1_a} defines function defined in
  C. Part~\subref{hoopl_fig1_b} shows the program after performing
  dead-code elimination.}
\label{hoopl_fig1}
\end{myfig}

\emph{Dead-code elimination} refers to the optimization that first
determines ``liveness'' and then removes dead statements (i.e., those
only using dead variables). Our running example will implement a
client program that can apply dead-code elimination to the program in
Figure~\ref{hoopl_fig1_a}, transforming it to resemble
Figure~\ref{hoopl_fig1_b}.

\intent{Provides signposts for chapter.}

In Section~\ref{hoopl_sec1}, we describe the the Haskell types, data
structures, and functions Hoopl provides for implementing
dataflow-analysis based optimizations. Throughout, we develop our
client program to implement dead-code elimination. We conclude with a
summary and brief discussion of our experience with Hoopl in
Section~\ref{hoopl_sec3}.

\section{Hoopl's API}
\label{hoopl_sec1}

\intent{Introduce Hoopl-managed structures}

In order to implement dataflow analysis generically, Hoopl defines
several core data structures which client programs must use. These
include the representation of CFGs, the type of transfer and rewrite
functions, and the represention of the meet operator. Hoopl controls
the CFG representation so it can traverse, propagate facts around, and
rewrite the CFG. Hoopl specifies the type of the transfer and rewrite
function such that they produce useable information (and
rewrites). Finally, Hoopl specifies the meet operator (but not its
implementation) so that the library can recognize fixpoints.

\intent{Introduce client-managed structures}

Hoopl requires that client programs specify those items related to
their specific optimization: the abstract syntax tree (AST) of
  the language, the representation of facts, and the implementation of
  the transfer and rewrite functions. Each node in the CFG
typically contains an expression or statement from the client
program's AST. While Hoopl controls the edges between nodes in the
CFG, it does not specify the contents of those nodes. Similarly, while
Hoopl determines when the analysis reaches a fixpoint, it requires
that the client specify when one set of facts equals another. Finally,
Hoopl applies the transfer and rewrite functions to the CFG but
requires that the client program implement them for their specific AST
and optimization.

\section{Control-Flow Graphs}

\intent{Introduce parameterization of blocks by AST and shape.}

Hoopl defines CFGs in terms of basic blocks, parameterized by
\emph{content} and \emph{shape}. Content means statements or
expressions from the client's AST. Shape can be either \emph{open} or
\emph{closed} and applies to both the entry and exit of the block.
Roughly, ``open'' allows control-flow to fall through the block;
``closed'' means control-flow branches.

\intent{Introduce meaning and definition of O and C types.}

Hoopl provides types named |O| and |C|, representing open and closed,
which Hoopl uses to constrain the edges between blocks in the CFG. As
open and closed describe both the entry and exit point of the block,
we write them as |O O| (``open/open''), |O C| (``open/closed''), etc.,
where the first describes the block's entry shape and the latter its
exit shape. An |O C| block allows one predecessor block but many
successors (i.e., control-flow can branch to one of many locations on
exit). An |O O| block permits exactly one predecessor and one
successor (i.e., control-flow falls through on
exit). Figure~\ref{hoopl_tbl1} summarizes the meaning of the different
block shapes.

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

\intent{Show example with O and C types applied.}

Figure~\ref{hoopl_fig3} gives Haskell declarations that can represent
the AST for !+foo+!. We use the GHC Haskell compiler's GADT syntax
\citep{GHC-7.2.1} to succinctly specify the actual type of the |e|
(``entry'') and |x| (``exit'') type parameters for each
constructor. The entry and exit type (i.e., either |O| or |C|) given
for each constructor reflects the control-flow of the represented
statement. The |CExpr| and |Var| types do not affect control flow in
our subset, so we do not annotate them like |CStmt|. Hoopl defines the
|Label| type and uses it to connect basic blocks together.

\begin{myfig}
  \begin{minipage}{\hsize}
%let includeAst = True
%include DeadCodeC.lhs
%let includeAst = False
  \end{minipage}
  \caption{Haskell datatypes capable of representing the AST of \texttt{foo}.}
\label{hoopl_fig3}
\end{myfig}

For example, the |Return| constructor creates a value with the type
|CStmt O C| --- an ``open/closed'' statement. A statement with a
``closed'' exit type does not allow control-flow to fall through,
which reflects the behavior of the !+return+! statement. The |Assign|
constructor's type, |CStmt O O|, indicates that control-flow
\emph{can} fall through, again reflecting the behavior of the
assignment statement.

\begin{myfig}
  \begin{tabular}{cc}
    \input{hoopl_lst3} &  \input{hoopl_lst4} \\
    \scap{hoopl_fig2_a} & \scap{hoopl_fig2_b}
  \end{tabular}
  \caption{Our example function as a control-flow
    graph. Part~\ref{hoopl_fig1_a} uses C syntax for each
    statement. Part~\ref{hoopl_fig1_b} uses the AST given in
    Figure~\ref{hoopl_fig3}.}
  \label{hoopl_fig2}
\end{myfig}

\intent{Make connection between CFG using program text and CFG using
  AST.}  Figure~\ref{hoopl_fig2} shows !+foo+! as a
CFG. Part~\subref{hoopl_fig2_a} shows the program with C
syntax. Part~\subref{hoopl_fig2_b} uses the AST just given.  Each
block in Part~\subref{hoopl_fig2_a} corresponds with the adjacent
block in Part~\subref{hoopl_fig2_b}. For example,
Block~\refNode{hoopl_lst3_assignc} (``\verb_c = 4_'') corresponds with
Block~\refNode{hoopl_lst4_assignc} (``|Assign "c" (Const 4)|''). Also
notice that the entry and exit points ($E$ and $X$, respectively) in
Part~\subref{hoopl_fig2_a} do not explicitly appear in our program
text, but they must be represented in the CFG. Our AST makes entry and
exit points explicit using the |Entry| and |Return| constructors.

\intent{Show how types mirror control flow.}
Each block in Figure~\subref{hoopl_fig2_b} shows the type
associated with its value. The type for
Block~\refNode{hoopl_lst4_assignc}, |CStmt O O|, shows that
control-flow falls through the statement. However, the type on
\refNode{hoopl_lst4_start}, |CStmt C O|, shows that the function's
entry point allows many predecessors --- that is, the function can be
called from multiple locations. The type |CStmt O C| on
\refNode{hoopl_lst4_return} (i.e., the exit point
for the function) shows the opposite --- the function can have many
successors (i.e., since it can be called from many locations, it can
return to those same locations) but control-flow exits the function
from only one location -- namely, that preceding the implicit return.

\intent{Introduce types and classes Hoopl uses to build graphs; use of
  O and C types in graphs.}  
Hoopl builds CFGs like that in
Figure~\ref{hoopl_fig2_b} using the |Block| and |Graph'|
types. |Graph'| is parameterized by block type; however, Hoopl also
provides an alias, |Graph|, which suffices for our
needs:\footnote{|Block| and |Graph'| define a number of constructors
  but they do not relate to our presentation and so we elide them.}

> data Block n e x = {-"\dots"-}
> data Graph' block n e x = {-"\dots"-}
> type Graph = Graph' Block

The parameters |e| and |x| (``entry'' and ``exit'') describe the shape
of the block (or graph) and must be |O| or |C|. The |n| (``node'')
parameter specifies the contents of each block (or graph) and will be
the type of the AST used by the client program.

\intent{Describe how to build CFGs with Hoopl}
Client programs construct graphs using methods specified by the
|GraphRep| class. |GraphRep| allows the client to implement their own
graph representation, but we do not use that here. Instead,
Figure~\ref{hoopl_fig4} shows Hoopl's instances for |Graph| instead of
the more general class definitions.\footnote{These instances show why
  we let Hoopl create |Block| and |Graph'| values. The |Graph| alias
  expands to |Graph' Block|; Hoopl provides a |GraphRep| instance for
  the |Graph| type that constructs the actual |Graph'| and |Block|
  values.}

\begin{myfig}
\begin{minipage}{\hsize}
> instance GraphRep Graph where
>   mkFirst  :: n C O -> Graph n C O
>   mkMiddle :: n O O -> Graph n O O
>   mkLast   :: n O C -> Graph n O C
>   (<*>)    :: NonLocal n => Graph n e O -> Graph n O x -> Graph n e x
>   (|*><*|) :: NonLocal n => Graph n e C -> Graph n C x -> Graph n e x
>   {-"\dots"-}
\end{minipage}
\caption{Hoopl's definition of the |Graph| instance for the |GraphRep| class.}
\label{hoopl_fig4}
\end{myfig}

\intent{Show how to build single-node graphs and how to compose them into 
basic blocks. Continue illustrating use of |O| and |C| types.}
|mkFirst|, |mkMiddle| and |mkLast| all turn a single block
(represented by the type parameter |n|) into a graph of one block with
the same shape. The |(<*>)| operator, said ``concat'' , concatenates
compatible graphs. By compatible, we mean the shapes of each argument
must fit together. Ignoring the |NonLocal| constraint for the time
being, the |(<*>)| operator's signature specifies that the first
argument must be open on exit (i.e., |n e O|) and the second must be
open on entry (i.e., |n O x|). The resulting graph's shape combines
the exit shape of the predecessor with the entry shape of the
successor (i.e., |n e x|). For example, arguments with type |CStmt C
O| and |CStmt O O| will have a result with type |CStmt C O|. The types
|CStmt O O| and |CStmt O C| will result in |CStmt O C|. Necessarily,
in the resulting graph the first argument will be a predecessor to the
second. In other words, |(<*>)| creates basic blocks.

\begin{myfig}
\begin{minipage}{\hsize}
%let buildFoo = True
%include DeadCodeC.lhs
%let buildFoo = False
\end{minipage}
\caption{A representation of our example function, built using the |GraphRep| methods in
Figure~\ref{hoopl_fig4} and the AST
from Figure~\ref{hoopl_fig3}.}
\label{hoopl_fig5}
\end{myfig}

\intent{Illustrate use of |(<*>)|.}  Returning to our example, we can
construct the CFG from Figure~\ref{hoopl_fig2_b} using code in
Figure~\ref{hoopl_fig5}.  The |l| parameter (with type |Label|)
defines the entry point for this block and will be supplied
externally. Each individual statement turns into a graph through
|mkFirst|, |mkMiddle| and |mkLast|. |(<*>)| concatenates those graphs
together, forming one large graph with type |CStmt C C|. This
construction exactly represents the CFG in Figure~\ref{hoopl_fig2_b}.

\intent{Show how Hoopl manages control-flow between blocks.}
Hoopl connects basic blocks into larger graphs
using the |(||*><*||)| operator.\footnote{Sorry, I don't know how to
  pronounce this one. Call it ``funny.''} This operator does not imply any 
control-flow between its arguments, unlike |(<*>)|. Instead, the |NonLocal|
class defines control-flow between blocks with its two members, |entryLabel| and
|successors|:

> class NonLocal n where 
>   entryLabel :: n C x -> Label 
>   successors :: n e C -> [Label]

The |entryLabel| method returns the entry point (as a |Label|) for a
given node, block or graph. The |C| type on the first argument (i.e.,
|n C x|) ensures only ``closed on entry'' graphs can be given to
|entryLabel|. |successors| gives the |Labels| that a given node, block
or graph may branch to. Again, the |C| type on the first argument
(i.e., |n e C|) ensures only ``closed on exit'' graphs can be given to
|successors|. Hoopl uses these methods to determine how basic blocks
connect. The |NonLocal| constraint on |(<*>)| and |(||*><*||)| ensures
Hoopl can traverse the CFG built by the client program.

\intent{Illustrate use of |NonLocal| in our example.}
Now we can give the |NonLocal| instance for |CStmt|:

%let nonLocalInst = True
%include DeadCodeC.lhs
%let nonLocalInst = False

We only define |entryLabel| for the |Entry| constructor,
  because only it is ``open on entry'' (i.e., due to its type |C O|).
  We do not define any cases for |successors| even though |Return| is
  ``closed on exit'' (i.e., due to its type |O C|), because our AST
  does not represent the destination of a return (implicit or
  explicit). If our AST supported branching (such as \texttt{if}
  statements), then |successors| would be more interesting.

\intent{Summarize CFGs in Hoopl} 

Hoopl ensures that client programs build correct CFGs using the |O|
and |C| types. The library controls graph creation through the
|GraphRep| class --- and that class ensures graphs are built from
basic blocks, connected by |Labels|. Hoopl recovers control-flow
information using the |NonLocal| class, through its |entryLabel| and
|successors| methods. This section introduced our example function,
!+foo+!, in Figure~\ref{hoopl_fig1}, defined an AST in
Figure~\ref{hoopl_fig2} that represents the subset of the C
language used by !+foo+!, and showed how to build a representation of
!+foo+! in Figure~\ref{hoopl_fig5}.

\section{Facts, Meet Operators and Lattices}
\intent{Reminder about what facts and lattices are; How Hoopl
  represents them.  Emphasize facts are defined by the client; meet
  operator defined by the client; Hoopl manages combining facts and
  determining when a fixed point has been reached.}  

Recall that dataflow analysis computes \emph{facts} for each block in
the control-flow graph, using a \emph{meet operator} to combine facts
when a block has multiple successors or predecessors (depdening on the
direction of the analysis). \margin{The analysis will always terminate
  if the meet operator forms the facts into a finite-height
  lattice.}{Awkward.}

\intent{Introduce |DataflowLattice| type and show connection to facts and 
the meet operator.}

Hoopl provides the type |DataflowLattice| (shown with several
associated definitions in Figure~\ref{hoopl_fig7}) so clients can
define the facts and meet operator for their specific analysis. The
field |fact_name| exists only for documentation. Hoopl uses the value
in the |fact_empty| field to create initial facts for each block in
the CFG when analysis starts. The |fact_join| field will hold the
client's implementation of their meet operator.

The meet operator, |fact_join|, takes two arguments (one of type
|OldFact| and the other of type |NewFact|) and returns a pair
consisting of a value and a |ChangeFlag|. |OldFact| and |NewFact|
represent two, possibly different, facts. \margin{The facts may differ
  for two reasons: |OldFact| and |NewFact| could be from different
  iterations of the analysis, or they could be from multiple
  predecessors or successors\footnote{Facts come from multiple
    predecessors when doing forwards analysis, multiple successors
    when going backwards.} of the current block.}{Is |fact_join| used
  to combine facts from nodes, or does th transfer function implicitly
  do that when the |Fact| argument is a |FactBase|?} The client
determines if the facts differ and returns |SomeChange|, plus the new
facts, if so. Otherwise, the client returns |NoChange|, indicating the
the |OldFact| and |NewFact| values are equal. Hoopl choose this
implementation for efficiency: the client can determine if facts
change during each join, rather than the library comparing all facts
on every iteration.

\begin{myfig}
  \begin{minipage}{\hsize}
> data DataflowLattice a = DataflowLattice { fact_name :: String,
>   fact_bot :: a,
>   fact_join :: JoinFun a }
>
> type JoinFun a = Label -> OldFact a -> NewFact a -> (ChangeFlag, a)
>
> newtype OldFact a = {-"\dots"-}
> newtype NewFact a = {-"\dots"-}
>
> data ChangeFlag = NoChange | SomeChange 
>
  \end{minipage}
  \caption{|DataflowLattice| and associated types defined by Hoopl for
    representing and combining facts.}
  \label{hoopl_fig7}
\end{myfig}

\intent{Show fact and meet operator for example as Haskell code and as 
  dataflow equations.}

As stated in Section~\ref{hoopl_sec4}, dead-code uses \emph{liveness}
analysis to find dead code. A variable is live if it is used after
declaration; otherwise, it is dead. Therefore, we call our facts the
set of live variables for each block. Our transfer function, given in
Section~\ref{hoopl_sec5}, will show that we compute this information
by traversing the CFG backward. When a block has multiple successors,
we must take the union of the successors' \inE facts to compute the
\out set for the current block. 

Consider Figure~\ref{hoopl_fig8}, which shows a fragment of C code
and its associated CFG. 

\begin{myfig}
  \begin{tabular}{cc}
    \input{hoopl_lst5} & \input{hoopl_lst6} \\
    \scap{hoopl_fig8_a} & \scap{hoopl_fig8_b}
  \end{tabular}
  \caption{A fragment of C code and its associated CFG.}
  \label{hoopl_fig8}
\end{myfig}

\intent{Aside: |WithTop|/|WithBottom| types.}

\section{Direction \& Transfer Functions}
\label{hoopl_sec5}

\intent{Reminder about what transfer functions do \& that they can go forwards or
backwards;}

\intent{Introduce |FwdTransfer| and |BwdTransfer| types; show how to construct them
with |mkFTransfer3| and |mkBTransfer3|. }

\intent{Show how |mkFTransfer| and |mkBTransfer| with existential
  types and type families are used in general.}

\intent{Give definition for example's transfer function.}

\section{Iteration \& Fixed Points}

\intent{Describe how Hoopl iterates on facts; how Hoopl determines when
a fixed point has been reached.}

\section{Rewriting}

\intent{Briefly describe rewriting as transformation.}
\intent{Introduce |FwdRewrite| and |BwdRewrite| types; show
  how to construct them with |mkFRewrite3| and |mkBRewrite3|.}

\intent{Segue to |mkFRewrite|, |mkBRewrite|, existentials and type families.}

\intent{Give definition of examples transfer functino.}

\section{Interleaved Analysis \& Rewriting}

\intent{Discuss how Hoopl manages to interleave both.}

\section{Dead-Code Elimination}

\intent{Apply the optimization developed to the example program with 
lots of illustratin.}

\section{The Rest of Hoopl}

\intent{Items that don't fit in elsewhere: combinators for rewriting,
  the |CheckPoint| monad, optimization fuel, |liftFuel|,
  |runInfinite|, |runChecked|, etc. }

\section{Summary}
\label{hoopl_sec3}
\intent{Discuss experience with Hoopl; summarize features, move on.}

\begin{myfig}
\begin{minipage}{\hsize}
%let includeAll = True
%include DeadCodeC.lhs
%let includeAll = False
\end{minipage}
\caption{Complete listing of our dead-code elimination optimization.}
\label{hoopl_fig6}
\end{myfig}

\standaloneBib

\end{document}

