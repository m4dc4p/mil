%&preamble
\input{nodocclass}\dodocclass
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\begin{document}
\numbersoff
\input{document.preamble}
\chapter[The \textnormal{\Hoopl\unskip} Library]{The \Hoopl Library}
\label{ref_chapter_hoopl}

\intent{Introduction} The dataflow algorithm describes a 
method for analyzing programs based on the computation of facts
between nodes in the program's control-flow graph. The \hoopl library
\citep{Hoopl-3.8.7.0}, written in Haskell, provides a framework for
using the dataflow algorithm. \Hoopl enables the user to implement
their own analyses for their own programming language. A thorough
description of the library's implementation can be found in the
authors' paper \citep{Ramsey2010}; here, we discuss the abstractions
they provide and how to use them.

\intent{Overview of the implementation provided by \hoopl.} \Hoopl's
implementation follows a variation of the dataflow algorithm described
by Lerner, Grove and Chambers \citeyearpar{Lerner2002}. In brief,
Lerner and colleagues' dataflow algorithm interleaves analysis and
transformation. While this technique does not provide any better
quality solutions than Kildall's original formulation
\citep{Kildall1973}, it arguably simplifies the implementation of individual
analysis. We return to Lerner and colleagues' work in Section~\ref{hoopl_sec9}.

\intent{Broad description of how \hoopl abstracts the dataflow
  algorithm.} \Hoopl implements the generic portions of the dataflow
algorithm: iterative computation, traversing the control-flow graph
(\cfg), and combining facts. The \emph{client program}, a term \hoopl
uses to mean the program using the library for some optimization,
provides data structures and functions specific to that optimization:
the representation of facts, a transfer function, a rewriter, and a
meet operator.

\intent{Introduce example} We will illustrate \hoopl concepts using a
running example motivated by the C-language function defined in
Figure~\ref{hoopl_fig1_a}. A cursory examination of that listing shows
the assignments to !+a+! on Lines~\ref{hoopl_lst1_assign_a} and
\ref{hoopl_lst1_add} do not affect the output (i.e., observable
behavior) of !+example+!. We could eliminate them without changing the
program's meaning; we may even improve its performance. However, we
could not eliminate the assignment to !+c+!  on
Line~\ref{hoopl_lst1_assign_c} because that may change the value
printed on Line~\ref{hoopl_lst1_print}. We call variables that may
affect observable behavior \emph{live}; a \emph{dead} variable is not
live. Figure~\ref{hoopl_fig1_b} shows one way we could optimize this
program by eliminating the ``dead'' statements in
Figure~\ref{hoopl_fig1_a}.

\begin{myfig}[tb]
\begin{tabular}{ccc}
  \begin{minipage}[t]{\widthof{!+\ \ printf("\%d",c);+!}}
  \begin{AVerb}[numbers=left,gobble=4]
    void example() \{
      int a, c;
      c = 4; \label{hoopl_lst1_assign_c}
      a = c + 1;  \label{hoopl_lst1_assign_a}
      printf("\%d",c); \label{hoopl_lst1_print}
      a = c + 2; \label{hoopl_lst1_add}
    \}
  \end{AVerb}
  \end{minipage} & \quad &
  \begin{minipage}[t]{\widthof{!+\ \ printf("\%d",c);+!}}
  \begin{AVerb}[numbers=left,gobble=4]
    void example() \{
      int c;
      c = 4; \label{hoopl_lst2_assign_c}
      printf("\%d",c); \label{hoopl_lst2_print}
    \}
  \end{AVerb}
  \end{minipage} \\

  \scap{hoopl_fig1_a} & & \scap{hoopl_fig1_b}
\end{tabular}
\caption{Part~\subref{hoopl_fig1_a} defines a function using the C
  language. Part~\subref{hoopl_fig1_b} shows the program after
  performing dead-code elimination.}
\label{hoopl_fig1}
\end{myfig}

\emph{Dead-code elimination} refers to the optimization that first
determines ``liveness'' and then removes dead statements (i.e., those
only using dead variables). Our running example will implement a
client program that can apply dead-code elimination to the program in
Figure~\ref{hoopl_fig1_a}, transforming it to resemble
Figure~\ref{hoopl_fig1_b}.

\intent{Provides signposts for chapter.}  This chapter provides enough
background to understand the use of \hoopl in later chapters. It
assumes the reader has a fair knowledge of the Haskell programming
language. We also assume familiarity with language extensions, such as
GADTs \citep{Schrijvers2009}, as implemented by GHC 7.2
\citep{GHC-7.2.1}. This chapter's structure mirrors that covering
dataflow analysis (Chapter~\ref{ref_chapter_background}), presenting
parallel concepts in terms of \hoopl
structures. Section~\ref{hoopl_sec1} gives an overview of the types,
data structures, and functions provided by
\hoopl. Sections~\ref{hoopl_sec_cfg} through \ref{hoopl_sec6} give
detailed information about each item. Throughout, we develop our
client program to implement dead-code elimination. We conclude with a
summary of \hoopl in Section~\ref{hoopl_sec3}. Section~\ref{hoopl_sec7}
shows all the code for our dead-code optimization in one place, as
well as output demonstrating the optimization shown in
Figure~\ref{hoopl_fig1_b}.

\section{\Hoopl's API}
\label{hoopl_sec1}

\intent{Introduce \hoopl-managed structures} In order to implement
dataflow analysis generically, \hoopl defines several core data
structures which client programs must use. These include the
representation of \cfgs, the type of transfer and rewrite functions,
and the representation of the meet operator. \Hoopl controls the \cfg
representation so it can traverse, propagate facts around, and rewrite
the \cfg. \Hoopl specifies the type of the transfer and rewrite function
such that they produce usable information (and rewrites). Finally,
\hoopl specifies the meet operator (but not its implementation) so that
the library can recognize fixed points.

\intent{Introduce client-managed structures} \Hoopl requires that
client programs specify those items related to their specific
optimization: the abstract syntax tree (AST) of the language analyzed,
the representation of facts, and the implementation of the transfer
and rewrite functions. Each node in the \cfg typically contains an
expression or statement from the AST of the language which the client
program analyzes. While \hoopl controls the edges between nodes in the
\cfg, it does not specify the contents of those nodes. Similarly, while
\hoopl determines when the analysis reaches a fixed point, it requires
that the client specify when one set of facts equals another. Finally,
\hoopl applies the transfer and rewrite functions to the \cfg but
requires that the client program implement them for their specific AST
and optimization.

\section{Control-Flow Graphs}
\label{hoopl_sec_cfg}

\intent{Introduce parameterization of blocks by AST and shape. }
\Hoopl defines \cfgs in terms of basic blocks, parameterized by
\emph{content} and \emph{shape}. Content means statements or
expressions from the client's AST. Shape applies to both the entry and
exit point of a block and specifies how control-flow enters and leaves
that block. An ``open'' block allows control-flow to fall-through
implicitly from its predecessor or to fall-through to its
successor. A ``closed'' block requires that control-flow explicitly
transfer to or from the block. Shape constrains the \cfg such that only
blocks with compatible shapes can be connected: successors of a
closed block must be closed; the predecessor of an open block must be
open.

\intent{Introduce meaning and definition of O and C types.}  \Hoopl
provides types named |O| (for open) and |C| (for closed) to describe
the entry and exit shape of a given block. We write |O O|
(``open/open''), |O C| (``open/closed''), etc., where the first type
describes the block's entry shape and the latter its exit shape. An |O
C| block requires a unique predecessor. Control-flow will fall-through
from the predecessor to the |O C| block, but control-flow must
explicitly pass transfer to a successor block on exit. An |O O| block
requires a unique predecessor and a unique successor. The block allows
control-flow to fall-through from its predecessor and similarly allows
control-flow to implicitly pass to its successor. A |C O| block
requires that control-flow pass explicitly from its
predecessors. However, control-flow falls-through from the block to
its successor. A |C C| block must be the target of an explicit
control-flow transfer and must, in turn, explicity pass control-flow
to a successor block. Figure~\ref{hoopl_tbl1} summarizes the four
possible block shapes.

\newbox\graphbox
\setbox\graphbox=\hbox{\begin{tikzpicture}[>=stealth, node distance=.5in, on grid]
      \node[stmt] (pred) at (-1,0) {$e\ O$};
      \node[stmt] (curr) [right=of pred] {$O\ O$};
      \node[stmt] (succ) [right=of curr] {$O\ x$};
      \draw [->] (pred) to (curr);
      \draw [->] (curr) to (succ);
    \end{tikzpicture}}
\begin{myfig}[tb]
  \begin{tabular}{c>{\hfuzz=100pt}m{\wd\graphbox}>{\hfuzz=5pt\emergencystretch=0pt}m{\widthof{Example Statements}}}
    Shape & \hfil Example Graph\hfil & Example Statement \\\midrule
    \begin{minipage}{\widthof{(``open/open'')}}\centering
      |O O|\\
      (``open/open'')
    \end{minipage}
    & \unhbox\graphbox & Assignments. \\
    \begin{minipage}[c]{\widthof{(``open/closed'')}}\centering
      |O C|\\
      (``open/closed'')
    \end{minipage}
    & 
    \begin{tikzpicture}[>=stealth, node distance=.5in, on grid]
      \node[optional] (succ1) at (1, 1) {$C\ x$};
      \node[invis] (succ2) at (1, 0) {$\strut\vdots$};
      \node[optional] (succ3) at (1, -1) {$C\ x$};
      \node[stmt] (curr) [left=of succ2] {$O\ C$};
      \node[stmt] (pred) [left=of curr] {$e\ O$};
      \draw [->] (pred) to (curr);
      \draw [->] (curr) to (succ1);
      \draw [->] (curr) to (succ3);
    \end{tikzpicture} & Conditionals, jumps. \\
    \begin{minipage}{\widthof{(``closed/open'')}}\centering
      |C O|\\
      (``closed/open'')
    \end{minipage}
    &
    \begin{tikzpicture}[>=stealth, on grid, node distance=.5in]
      \node[optional] (pred1) at (-1,1) {$e\ C$};
      \node[invis] (pred2) at (-1,0) {$\strut\vdots$};
      \node[optional] (pred3) at (-1,-1) {$e\ C$};
      \node[stmt] (curr) [right=of pred2] {$C\ O$};
      \node[stmt] (succ) [right=of curr] {$O\ x$};
      \draw [->] (pred1) to (curr);
      \draw [->] (pred3) to (curr);
      \draw [->] (curr) to (succ);
    \end{tikzpicture} & Function entry points, alternatives. \\ %% prevents a badly stretched paragraph 
    \begin{minipage}{\widthof{(``closed/closed'')}}\centering
      |C C|\\
      (``closed/closed'')
    \end{minipage}
    & 
    \begin{tikzpicture}[>=stealth, node distance=.5in, on grid]
      \node[optional] (pred1) at (-1,1) {$e\ C$};
      \node[invis] (pred2) at (-1,0) {$\strut\vdots$};
      \node[optional] (pred3) at (-1,-1) {$e\ C$};
      \node[stmt] (curr) [right=of pred2] {$C\ C$};
      \node[optional] (succ1) [right=1in of pred1] {$C\ x$};
      \node[invis] (succ2) [right=1in of pred2] {$\strut\vdots$};
      \node[optional] (succ3) [right=1in of pred3] {$C\ x$};
      
      \draw [->] (pred1) to (curr);
      \draw [->] (pred3) to (curr);
      \draw [->] (curr) to (succ1);
      \draw [->] (curr) to (succ3);
    \end{tikzpicture} & Function bodies. 
  \end{tabular}
  \caption{This table shows the four possible block shapes. Each row
    gives example statements and a representative \cfg using a block of
    the given shape. Dashed lines indicate optional blocks. Solid
    lines show required blocks. }
  \label{hoopl_tbl1}
\end{myfig}

\intent{Show example with O and C types applied.}
Figure~\ref{hoopl_fig3} gives Haskell declarations that can represent
the AST for !+example+!. We use GHC's GADT syntax
\citep[Section~7.4.7]{GHCManual} to specify the value of the |e| and
|x| (``entry'' and ``exit'') types for each constructor. The entry and
exit types reflect the control-flow of the
represented statement. The |CExpr| and |Var| types do not affect
control flow in our subset, so we do not annotate them like
|CStmt|. \Hoopl defines the |Label| type; we use it to define the
successors and predecessors of closed blocks.

\begin{myfig}
  \begin{minipage}{\hsize}
%let includeAst = True
%include DeadCodeC.lhs
%let includeAst = False
  \end{minipage}
  \caption{Haskell data declarations for representing the AST of !+example+!.}
\label{hoopl_fig3}
\end{myfig}

\intent{Explain each |CStmt| constructor, except |Call|.}  The |Entry|
value represents a function entry point; we give it type |C O| because
control-flow can only explicitly enter a function through a call. The
|Return| constructor creates a value with the type |O C|, meaning
control-flow will not implicitly pass from the statement but rather
explicitly transfers to another block (i.e., the caller of the
function). The |Assign| constructor's type, |CStmt O O|, indicates
that control-flow \emph{can} fall-through, reflecting the behavior of
the assignment statement.

\intent{Excuse why |Call| has a funny type.}  The |Call| statement's
type could be |O C| to reflect that control-flow implicitly enters the
statement from its predecessor and then transfers explicitly to
another block. However, we can think of this as an "external call" to
a block defined outside the program. Then |Call| then acts like an
assignment --- control-flow implicitly passes through the function
call to the next statement. Therefore, we give |Call| the type |O O|.

\begin{myfig}
  \begin{tabular}{cc}
    \input{hoopl_lst3} &  \input{hoopl_lst4} \\\\
    \scap{hoopl_fig2_a} & \scap{hoopl_fig2_b} 
  \end{tabular}
  \caption{Our example function as a control-flow
    graph. Part~\ref{hoopl_fig1_a} uses C syntax for each
    statement. Part~\ref{hoopl_fig1_b} uses the AST given in
    Figure~\ref{hoopl_fig3}.}
  \label{hoopl_fig2}
\end{myfig}

\intent{Make connection between \cfg using program text and \cfg using
  AST.}  Figure~\ref{hoopl_fig2} shows a \cfg for
!+example+!. Part~\subref{hoopl_fig2_a} shows the program with C
syntax. Part~\subref{hoopl_fig2_b} uses the AST just given.  Each
block in Part~\subref{hoopl_fig2_a} corresponds to the adjacent
block in Part~\subref{hoopl_fig2_b}. For example,
Block~\refNode{hoopl_lst3_assignc} (``!+c = 4+!'') corresponds to
Block~\refNode{hoopl_lst4_assignc} (``|Assign "c" (Const 4)|''). Also
notice that the entry and exit points ($E$ and $X$, respectively) in
Part~\subref{hoopl_fig2_a} do not appear explicitly in our program
text, but they must be represented in the \cfg. 

\intent{Show how types constrain control flow.}  Each block in
Figure~\ref{hoopl_fig2_b} shows the type associated with its
value. For example, the type of Block~\refNode{hoopl_lst4_assignc},
|CStmt O O|, shows that control-flow falls-through the
statement. However, the type of \refNode{hoopl_lst4_start}, |CStmt C
O|, shows that control-flow must explicitly transfer to the block (in
this case, through a function call). The type |CStmt O C| on
\refNode{hoopl_lst4_return} shows the opposite --- control-flow does
not implicitly exit the block; instead, control-flow explicitly returns to
the caller of the function. 

\begin{myfig}
\begin{minipage}{\hsize}
> mkFirst   :: n C O -> Graph n C O
> mkMiddle  :: n O O -> Graph n O O
> mkLast    :: n O C -> Graph n O C
> (<*>)     :: Graph n e O -> Graph n O x -> Graph n e x
> (|*><*|)  :: Graph n e C -> Graph n C x -> Graph n e x
\end{minipage}
\caption{Primitives provided by \hoopl for constructing graphs.}
\label{hoopl_fig4}
\end{myfig}

\intent{Introduce \hoopl functions for building graphs.}
Figure~\ref{hoopl_fig4} shows the five primitive functions that \hoopl
provides for client programs to use when constructing \cfgs. The |n| type parameter
represents the AST defined by the client program (|CStmt| in our
example). \Hoopl defines the |Graph| type. 

\intent{Introduce |mkFirst|, |mkMiddle|, and |mkLast|.}
The |mkFirst|, |mkMiddle| and |mkLast| functions turn a single block
into a graph of one block with the same shape. 

\intent{Introduce |(<*>)|.}  The |(<*>)| operator, pronounced
``concat,'' connects an ``open on exit'' (|e O|) graph to one ``open
on entry'' (|O x|). The resulting graph's shape, |e x|, combines the
entry shape of the first argument and the exit shape of the
second. Necessarily, the graph represented by first argument becomes
the predecessor of the graph represented by the second argument. For
example, if |n1| has type |CStmt C O| and |n2| has type |CStmt O O|,
then |n1 <*> n2| would have type |CStmt C O| and |n1| will be the
unique predecessor to |n2| in |n1 <*> n2|.

\begin{myfig}
\begin{minipage}{\hsize}
%let buildFoo = True
%include DeadCodeC.lhs
%let buildFoo = False
\end{minipage}
\caption{A definition that creates a \cfg for !+example+!, using the
  AST from Figure~\ref{hoopl_fig3} and the functions shown in
  Figure~\ref{hoopl_fig4}.}
\label{hoopl_fig5}
\end{myfig}

\intent{Illustrate use of |(<*>)|.}  Returning to our example, we can
construct the \cfg from Figure~\ref{hoopl_fig2_b} using the code in
Figure~\ref{hoopl_fig5}.  The |l| parameter (with type |Label|)
defines the entry point for this block. Each statement in the block is
mapped to a graph by applying |mkFirst|, |mkMiddle| or |mkLast| as
appropriate. We concatenate the graphs using the |(<*>)| operator,
forming one large graph with type |CStmt C C|. This construction
exactly represents the \cfg in Figure~\ref{hoopl_fig2_b}.

\intent{Show how \hoopl manages control-flow between blocks.}  \Hoopl
combines smaller graphs into larger graphs using the |(||*><*||)|
operator (pronounced ``append''). Unlike |(<*>)|, this operator does
not imply any control-flow between its arguments. 

The (<*>) operator defines control-flow within a basic block, and the
|(||*><*||)| operator combines unconnected blocks into a larger
graph. \Hoopl defines the |NonLocal| class to bridge the gap between
these two operators:\footnote{The |(||*><*||)| and |(<*>)| operators
  in Figure~\ref{hoopl_fig4} specify a |NonLocal| constraint on |n|,
  which we hid to simplify the presentation.}

\begin{singlespace}
> class NonLocal n where 
>   entryLabel  :: n C x -> Label 
>   successors  :: n e C -> [Label]
\end{singlespace}

\noindent \Hoopl defines the |Label| type and the client program uses
them for two purposes: uniquely identifying each block in the graph,
and for specifying the explicit successors of each block in the
graph. \Hoopl use |entryLabel| method to find the entry point for a
given block. The |n C x| type of its argument ensures |entryLabel| can
only be applied to ``closed on entry'' nodes; precisely those nodes
that can be the target of an explicit control-flow
transfer. Similarly, \hoopl uses |successors| to determine the explicit
successors of a ``closed on exit'' block.

\intent{Illustrate use of |NonLocal| in our example.}  The client
program must define an instance of |NonLocal| for its AST. \Hoopl will
use that instance to recover the control-flow between basic blocks in
the \cfg. Therefore, as seen in Figure~\ref{hoopl_fig3}, the AST must
store the label of a ``closed on entry'' node and the labels of
successors for a ``closed on exit'' node in the AST itself. 

We define the following instance of |NonLocal| for |CStmt|:

\begin{singlespace}
%let nonLocalInst = True
%include DeadCodeC.lhs
%let nonLocalInst = False
\end{singlespace}

\noindent We only define |entryLabel| for the |Entry| constructor,
because only it is ``closed on entry.''  We only need define one case
for |successors| as |Return| is the only ``closed on exit'' |CStmt|
value. However, we do not specify the destination of a |Return| so
|successors| always returns an empty list.

\section{Facts, Meet Operators and Lattices}
\intent{Reminder about the role that facts and the meet operator
  play.}

The dataflow algorithm, as given for the forwards case in
Figure~\ref{fig_back14} on Page~\pageref{fig_back14}, iteratively
computes output \emph{facts} for each block in the \cfg until reaching
a fixed point. Input facts correspond to the \inBa set for each block;
output facts correspond to the \outBa set for the block.\footnote{In a
  backwards analysis, the correspondence is reversed}. The first
iteration uses some initial value for each \inBa and \outBa set. Each
subsequent iteration uses a \emph{meet operator} to combine \outBa
sets from the predecessors of each block into an \inBa set for that
block. The set of values representing facts and the meet operator
together form a \emph{lattice}.

\intent{Introduce |DataflowLattice| type and show connection to facts
  and the meet operator.}  \Hoopl provides the |DataflowLattice|
type (shown in Figure~\ref{hoopl_fig7}). |DataflowLattice| defines the
following fields: |fact_name|, used for documentation; |fact_bot|,
for specifying initial facts; and |fact_join|, for the implementation
of the analysis' meet operator.

\begin{myfig}
  \begin{minipage}{\hsize}
> data DataflowLattice a = DataflowLattice { 
>   fact_name  :: String,
>   fact_bot   :: a,
>   fact_join  :: Label -> OldFact a -> NewFact a -> (ChangeFlag, a) }
>
> newtype OldFact a  = OldFact a 
> newtype NewFact a  = NewFact a 
>
> data ChangeFlag = NoChange | SomeChange 
  \end{minipage}
  \caption{|DataflowLattice| and associated types defined by \hoopl for
    representing and combining facts.}
  \label{hoopl_fig7}
\end{myfig}

The meet operator, |fact_join|, takes two arguments and returns a pair
consisting of a value and a |ChangeFlag|. The arguments represent
possibly differing output facts; the result represents the meet of
those facts. \Hoopl determines that a fixed point has been reached when
|fact_join| returns |NoChange| for all blocks in the
\cfg.\footnote{\Hoopl uses this strategy for efficiency: if the client
  does not specify when facts change, \hoopl would need to do many
  comparisons on each iteration to determine if a fixed point had been
  reached.} The client program must ensure that the meet defines a
finite-height lattice; otherwise, the analysis may not terminate.

\intent{Introduce meet for liveness} As stated previously, dead-code elimination uses \emph{liveness}
analysis to find dead code. A live variable is one used after
assignment or declaration; otherwise the variable is
dead.\footnote{For simplicity, our AST does not explicitly represent
  declarations. Instead, we only represent assignment.} Liveness
analysis is implemented as a backwards dataflow analysis. In a
backwards analysis, \outBa is the set of input facts to block $B$;
\inBa is the set of output facts. All live variables from $B$'s
successors may be live in $B$; therefore, we implement our meet
operator as \emph{set union}: to compute \outBa for block $B$, we take
the union of all the \inE sets of $B$'s successors.

\intent{Introduce facts used during liveness analysis.} We define the
set \setL{Vars} as the set of all declared variables in the
program. For each block $B$, our analysis computes the set of
variables live at the beginning of each block, \inBa, using the
transfer function (defined in Section~\ref{hoopl_sec5}) and the
block's input set, \outBa. Both \inBa and \outBa are subsets of
\setL{Vars}. We set \inBa and \outBa to the empty set when analysis
begins.

\intent{Show fact and meet operator for example as Haskell code and as
  dataflow equations.} Figure~\ref{hoopl_fig9} shows Haskell code
implementing the definitions of meet operator and facts just
given. The type |Vars| corresponds to \setL{Vars}. The definition of
|meet| corresponds to set union. If |old| does not equal |new| we
return |SomeChange| and the union of the two sets (the
|changeIf| function maps |Bool| values to |ChangeFlag| values). The
|lattice| definition puts all the pieces together into a
|DataflowLattice| value. Notice we set |fact_bot| to |Set.empty|, the
initial value for all \inBa and \outBa sets.

\begin{myfig}\disableoverfull
  \begin{tabular}{c}
    \begin{minipage}{\hsize}\disableoverfull
%let latticeDef = True
%include DeadCodeC.lhs
%let latticeDef = False
    \end{minipage} 
  \end{tabular}
  \caption{Haskell definitions implementing fact and meet
    definitions for our liveness analysis.}
  \label{hoopl_fig9}
\end{myfig}

\section{Direction \& Transfer Functions}
\label{hoopl_sec5}
\intent{Reminder about what transfer functions do \& that they can go
  forwards or backwards.}  The dataflow algorithm specifies two sets
of facts for every block in the \cfg: \inBa and \outBa.  \inBa
represents facts known when control-flow enters the block; \outBa
those facts known when control-flow leaves the block. The
\emph{transfer function} computes output facts for each block in the
\cfg, using the contents of the block and its input facts. A forwards
analysis uses \inBa as the input facts and computes \outBa; A
backwards analysis does the opposite, computing \inBa from \outBa and
the contents of the block.

\intent{Introduce |FwdTransfer| and |BwdTransfer| types; Show how
  |mkFTransfer| and |mkBTransfer| construct transfer functions.}
\Hoopl defines the |FwdTransfer| and |BwdTransfer| types, shown in
Figure~\ref{hoopl_fig10}, to represent forwards and backwards transfer
functions. The |n| parameter represents the block's contents (i.e.,
the AST of the language analyzed). The |f| parameter represents the
facts computed. \Hoopl does not export the constructors for
|FwdTransfer| or |BwdTransfer|; instead, clients use the |mkFTransfer|
and |mkBTransfer| functions, whose signatures are also shown in
Figure~\ref{hoopl_fig10}.

\begin{myfig}
    \begin{minipage}{\hsize}
> newtype FwdTransfer n f 
> newtype BwdTransfer n f

> mkFTransfer :: (forall e x . n e x -> f -> Fact x f) -> FwdTransfer n f
> mkBTransfer :: (forall e x . n e x -> Fact x f -> f) -> BwdTransfer n f      
    \end{minipage}
  \caption{\Hoopl's |FwdTransfer| and |BwdTransfer| types. They can be
    constructed with the functions |mkFTransfer| and |mkBTransfer|.}
  \label{hoopl_fig10}
\end{myfig}

\intent{Explain why |mkFTransfer| and |mkBTransfer| require
  higher-rank types.}  \Hoopl requires that we parameterize our AST
(i.e., the |n| type) using the |O| and |C| types from
Section~\ref{hoopl_sec_cfg}.  A standard Haskell function cannot
pattern match on values with different types (e.g., |Assign| has type
|CStmt O O|, but |Entry| has type |CStmt C O|).  Therefore, to
pattern-match on all constructors, |mkFTransfer| and |mkBTransfer|
require that the transfer function given be defined with a
\emph{higher-rank} type \citep[Section~7.8.5]{GHCManual}. This allows
client programs to write one transfer function that can match on all
constructors in the AST.

\intent{Types families and |Fact C| vs. |Fact O|} Notice that
|mkFTransfer| takes a transfer function that produces a |Fact x f|
value. \Hoopl defines |Fact x f| as an \emph{indexed type family}
\citep[Section~7.2.2]{GHCManual}, where the meaning of |Fact x f|
depends on the type of |x|.  When |x| is |C|, then |Fact x f| is a
synonym for |FactBase f| (another \hoopl type), which is a dictionary
of facts indexed by |Labels|. When |x| is |O|, |Fact x f| is just a
synonym for |f| (i.e., a plain fact). The definition of |Fact x f|
extends the dataflow algorithm slightly by allowing the transfer
function to produce different facts for each successor node. 

In the case of a backwards analysis, |mkBTransfer| specifies that the
transfer function \emph{receive} an argument of type |Fact x f|, and
that it always produce a plain fact. When a node is closed on
exit, the transfer function receives a dictionary of all facts
(indexed by label) from the successors of the node. This definition
also extends the dataflow algorithm slightly because it does not force
the transfer function to take the meet of its input facts.

\intent{Give definition for example's transfer function.}
Figure~\ref{hoopl_fig11} shows the implementation of the transfer
function for our example. The subsidiary definition, |transfer|,
computes facts for each constructor in |CStmt|:

{\everypar={\hangindent=\parindent\hangafter=1}\narrower

\noindent|transfer (Entry _) f|\quad This statement represents the
entry point of the function. No variables are live before the
procedures executes, so |transfer| returns the empty set.

\noindent|transfer (Assign var expr) f|\quad In this case, |f|
represents the set of live variables found so far. We first remove
|var| from |f|, as assignments always eliminate live
variables.\footnote{If this statement represents the declaration of
  |var|, then |var| will not be live again. However, if |var| is used
  again we will add it back to the live set.}  The auxiliary function |uses|
computes the live variables in |expr|; we add those variables to 
our updated |f| and return the result. 

\noindent|transfer (Call _ exprs) f|\quad This case resembles
|Assign|, except that we do not remove any variables from |f|. We add all
variables used in any of the |exprs| given to the live set.

\noindent|transfer Return f|\quad No variables (in our AST) will be
live after the procedure returns. Therefore, nothing is live at this
point, and we return the empty set.\par}

\begin{myfig}
  \begin{minipage}{\hsize}
%let includeLiveness = True
%include DeadCodeC.lhs
%let includeLiveness = False
  \end{minipage}
  \caption{The transfer function implementing liveness analysis.}
  \label{hoopl_fig11}
\end{myfig}

\section{Iteration \& Fixed Points}
\intent{Describe how \hoopl iterates on facts; how \hoopl determines
  when a fixed point has been reached.}  The dataflow algorithm
iterates over a program's \cfg until the facts for each block reach a
fixed point. \Hoopl uses the meet operator (the |fact_join| field of
the |DataflowLattice| type) given by the client to determine when
the analysis should terminate.

\Hoopl associates each block in the \cfg with a |Label|. On each
iteration, at each label, \hoopl computes the meet of facts from the
prior iteration with facts from the current iteration. Recall that
|fact_join| returns a |ChangeFlag|, as well as new facts. Therefore,
if any application of |fact_join| results in |SomeChange|, \hoopl
continues to iterate. Otherwise, the analysis terminates.

\section{Interleaved Analysis \& Rewriting}
\label{hoopl_sec9}
\intent{Introduce rewriting in \hoopl.} Kildall's formulation of the
dataflow algorithm \citep{Kildall1973} does not give a general method
for transforming \cfgs based on the results of the analysis
performed. He assumed that the \cfg would be transformed after each
analysis; he did not address the issue of determining when an analysis
should be performed again (possibly leading to further
rewrites). Kildall also did not address the question of composing
multiple analyses; instead, each analysis is assumed to be applied one
at a time, in no particular order.

Lerner, Grove and Chambers \citeyearpar{Lerner2002} developed a
variation of the dataflow algorithm that addresses both of these
concerns. Kildall's dataflow algorithm computes facts over a static
\cfg; Lerner and colleagues' algorithm recursively transforms the \cfg
\emph{during} analysis. After transforming some or all of the \cfg,
their algorithm recursively computes facts for the new \cfg; the
transformation and analysis of the \cfg continues until reaching a
fixed point.

This algorithm does not produce better results than Kildall's, in the
sense defined by Section~\ref{back_sec_quality} (Page
\pageref{back_sec_quality}). However, as Lerner and colleagues
describe, their algorithm removes the need to manually combine
multiple dataflow analyses' into one ``super-analysis.'' Instead, each
dataflow analysis can be implemented separately; their algorith
composes those separate pieces automatically. \Hoopl implements a
version of the interleaved analysis and rewriting algorithm just
described.

\section{Rewriting with \hoopl}
\intent{Introduce |FwdRewrite| and |BwdRewrite| type.}
Figure~\ref{hoopl_fig15} shows the two types \hoopl provides for
rewriting, |FwdRewrite| and |BwdRewrite|. These types correspond to
the |FwdTransfer| and |BwdTransfer| types; \hoopl requires that a
|FwdTransfer| be paired with a |FwdRewrite|, and a |BwdTransfer| with
a |BwdRewrite|.  Client programs use the |mkFRewrite| and |mkBRewrite|
functions to create |FwdRewrite| and |BwdRewrite| values. For the same
reason as the transfer function, rewrite functions must be defined
with a higher-rank type.

\intent{Explain arguments to rewrite functions.} The argument to
|mkFRewrite| (and |mkBRewrite|) gives the signature for rewrite
functions. A rewrite function receive the node to rewrite as its first
argument. The facts computed for that node are given in the second
argument. Like the backwards transfer function, a backwards rewriter
receives a dictionary of facts, indexed by labels, if the node is
closed on exit; otherwise, the rewriter receives a plain fact. A
forwards rewriter always receives a plain fact.

\intent{Describe result of rewrite function.}  The rewrite function
returns a monadic |Maybe (Graph n e x)| value. The monadic portion
relates to optimization fuel, a concept described in
Section~\ref{hoopl_sec8}. The |Maybe| portion indicates if the
rewriter wants to change the node given in any way. |Nothing| means no
change to the node. A |Just| value causes \hoopl to replace the current
block with a |Graph n e x| value. Returning a |Graph| value allows the
rewriter to replace a single node with many nodes, but the graph
returned must have the same |e x| type (i.e., shape) as the input
node.

Rewriters can delete nodes |O O| nodes by returning |Just
emptyGraph|. The shape type prevents |C O| and |O C| nodes from being
deleted. To see why, consider the shape of each node and its successor
(or predecessor, in the second case). A |C O| node necessarily
precedes an |O x| node. If the |C O| node were deleted, the |O x| node
cannot replace it. A |C O| node can have zero or more predecessors; a
|O x| node can only have one. The predecessors to the |C O| node
cannot become the predecessors to the |O x| node; therefore, deleting
a |C O| node is not possible. A similar argument holds for |O C|
nodes.

\begin{myfig}
  \begin{minipage}{\hsize}
> newtype FwdRewrite m n f 
> newtype BwdRewrite m n f 

> mkFRewrite :: FuelMonad m => 
>   (forall e x . n e x -> f -> m (Maybe (Graph n e x))) 
>   -> FwdRewrite m n f
> mkBRewrite :: FuelMonad m => 
>   (forall e x . n e x -> Fact x f -> m (Maybe (Graph n e x)))
>   -> BwdRewrite m n f
  \end{minipage}
  \caption{The |FwdRewrite| and |BwdRewrite| types provided by \hoopl,
    as well as the functions used to construct them, |mkBRewrite| and
    |mkFRewrite|.}
  \label{hoopl_fig15}
\end{myfig}

\begin{myfig}
  \begin{minipage}{\hsize}
%let includeRewrite = True
%include DeadCodeC.lhs
%let includeRewrite = False    
  \end{minipage}
  \caption{The rewrite function for our dead-code elimination
    optimization. |Assign| statements are deleted when they assign to
    a dead variable. In all other cases the \cfg remains unchanged.}
  \label{hoopl_fig12}
\end{myfig}

\intent{Give definition of example's rewrite function.}
Figure~\ref{hoopl_fig12} shows |eliminate|, the rewrite function for
our example optimization. We define the local function |rewrite| by
cases for each constructor in |CStmt|. All cases except |Assign|
return |Nothing|, leaving the \cfg unchanged. If the test |not (var
`member` live)| in the |Assign| case succeeds, |rewrite| removes the
assignment by returning |Just emptyGraph|. Otherwise, the assignment
remains.

\subsection{Optimization Fuel}
\label{hoopl_sec8}
\intent{Describe optimization fuel and purpose of |FuelMonad|
  constraint.}  \Hoopl implements ``optimization fuel,'' originally
described by Whalley \citeyearpar{Whalley1994}, as an aid in debugging
optimizations. Each rewrite costs one ``unit'' of fuel. If fuel runs
out, \hoopl stops iterating. This allows the programmer to debug faulty
optimizations by decreasing the fuel supply in a classic
divide-and-conquer approach. The |FuelMonad| constraint ensures \hoopl
can manage fuel during rewriting. Normally, the client program does
not worry about fuel.

\section{Executing an Optimization}
\label{hoopl_sec6}
\intent{Introduce |BwdPass|/|FwdPass| and
  |analyzeAndRewriteBwd|/|analyzeAndRewriteFwd|.}
Figure~\ref{hoopl_fig14} shows \hoopl's |BwdPass| and |FwdPass|
types. The figure also shows the signatures for |analyzeAndRewriteBwd|
and |analyzeAndRewriteFwd|, \hoopl functions that the client program
uses to apply a given analysis and transformation. As the names
suggest, one pair applies to backwards dataflow-analyses and the other
to forwards analyses. We will only discuss the backwards case here.

\begin{myfig}[hbpt]\disableoverfull
  \begin{minipage}{\hsize}\disableoverfull
> data FwdPass m n f = FwdPass	{
>     fp_lattice :: DataflowLattice f
>   , fp_transfer :: FwdTransfer n f
>   , fp_rewrite :: FwdRewrite m n }

> data BwdPass m n f = BwdPass {
>     bp_lattice :: DataflowLattice f
>   , bp_transfer :: BwdTransfer n f
>   , bp_rewrite :: BwdRewrite m n f }

> analyzeAndRewriteFwd :: (CheckpointMonad m, NonLocal n, LabelsPtr entries) => 
>   FwdPass m n f 
>   -> MaybeC e entries 
>   -> Graph n e x 
>   -> Fact e f 
>   -> m (Graph n e x, FactBase f, MaybeO x f)

> analyzeAndRewriteBwd :: (CheckpointMonad m, NonLocal n, LabelsPtr entries) => 
>   BwdPass m n f 
>   -> MaybeC e entries 
>   -> Graph n e x 
>   -> Fact x f 
>   -> m (Graph n e x, FactBase f, MaybeO e f)
  \end{minipage}
  \caption{\Hoopl's types and functions used to execute backwards and
    forwards analysis and transformation. |BwdPass| and |FwdPass|
    package the client program's definition of lattice, transfer
    function, and rewrite function. Except for direction,
    |analyzeAndRewriteFwd| and |analyzeAndRewriteBwd| behave
    similarly; they execute the optimization defined by the client
    program.}
  \label{hoopl_fig14}
\end{myfig}

\intent{Describe pieces of |BwdPass| and |analyzeAndRewriteBwd|.}
The |BwdPass| type packages a lattice definition, transfer function, and
rewrite function into one structure. The |analyzeAndRewriteBwd|
function takes a number of interesting arguments and must be run
inside a \hoopl-specified monad. We address those arguments in turn.

\itempar{(|CheckpointMonad m|, |NonLocal n|, |LabelsPtr entries|)} These constraints reflect
several \hoopl requirements:
\begin{itemize}
\item |CheckpointMonad| -- This class provides methods that allow
  \hoopl to rollback monadic changes to the \cfg, providing support for
  \hoopl's implementation of Lerner and colleague's technique.
\item |NonLocal| -- This class allows \hoopl to traverse the \cfg.
\item |LabelsPtr| -- This class gives \hoopl the means to find external entry
  points to the \cfg.
\end{itemize}

\itempar{|BwdPass m n f|} This argument packages the client's
definitions of the lattice, transfer function, and rewrite function
for this particular analysis.

\itempar{|MaybeC e entries|} This gives all the entry points to the
program, which may not always be all the |Labels| in the \cfg ---
just those where control-flow can start. 

\itempar{|Graph n e x|} This argument holds the \cfg to be
optimized. In practice, |e x| is always |C C|. 

\itempar{|Fact x f|} This argument gives the initial input facts for
all nodes in the graph.

\intent{Describe how |deadCode| uses |runInfinite|,
  |runSimpleUniqueMonad|} Figure~\ref{hoopl_fig13} shows |deadCode|,
which puts all the pieces of our example optimization together and
applies them to a given program. The type, |Graph CStmt C C -> Graph
CStmt C C|, shows that |deadCode| modifies a \cfg composed of |CStmt|
values. 

\intent{Describe how arguments to |analyzeAndRewriteBwd| are
  constructed.}  The |opt| definition implements our analysis and
transformation. Our analysis must run in a monadic context that is an
instance of |CheckpointMonad| and
|UniqueMonad| (a class that controls the creation of new
  |Label| values --- allowing rewriters to create new |C x|
  nodes). The |CheckingFuelMonad| and |SimpleUniqueMonad| types in the
signature of |opt| are the \hoopl-provided implementations of
|CheckpointMonad| and |UniqueMonad|. 

The first argument to |analyzedAndRewriteBwd|, |pass|, packages up the
lattice definition, transfer function, and rewrite function previously
discussed. The second argument, |(JustC entryPoints)|, gives all entry
points for the program. The third argument is the the program we are
optimizing. Finally, the inputs facts (an empty set) are given in the
fourth argument.

|analyzeAndRewriteBwd| returns a transformed program, the final facts
computed, and any facts that should propagate ``out'' of the \cfg. We capture
the transformed program in |program'| and return it. 

In |deadCode|, we use |(runWithFuel infiniteFuel)| and
|runSimpleUniqueMonad| (all provided by \hoopl) to execute the monadic
program returned by |opt| and ultimately, we return the transformed
program.

\begin{myfig}\disableoverfull
  \begin{minipage}{\hsize}\disableoverfull
%let includeDeadCode = True
%include DeadCodeC.lhs
%let includeDeadCode = False
  \end{minipage}
  \caption{|deadCode| applies the optimization developed so far to a particular
    program.}
  \label{hoopl_fig13}
\end{myfig}

\section{Summary}
\label{hoopl_sec3}
\intent{Summarize \hoopl's features.} This chapter gave an introduction
to the essential features of the \hoopl library. \Hoopl implements the
generic portions of the dataflow algorithm; in particular, it
determines when facts reach a fixed point. \Hoopl's implementation of
the dataflow algorithm interleaves analysis and rewriting, a technique
originally described by Lerner and colleagues
\citep{Lerner2002}. \Hoopl requires that the client program define the
facts to analyze, a transfer function, a rewriting function, and a
meet operator (which, in turn, defines a lattice for the facts given).

\standaloneBib 
%% Some interaction with standalone makes the thesis break unless we
%% end with \noindent. The error is:
%%
%%   "You can't use `\\unskip' in vertical mode.\\sa@atenddocument
%%   ->\\unskip".
%%
\noindent\end{document}


% LocalWords:  Hoopl dataflow Haskell Hoopl's Kildall's CFG rewriter hoopl API
% LocalWords:  liveness CFGs AST parameterization parameterized stmt pred curr
% LocalWords:  succ invis GHC's GADT CExpr CStmt lst assignc Const mkFirst Bool
% LocalWords:  mkMiddle mkLast GraphRep concat NonLocal entryLabel OldFact expr
% LocalWords:  DataflowLattice NewFact ChangeFlag newtype NoChange SomeChange
% LocalWords:  changeIf FwdTransfer BwdTransfer mkFTransfer mkBTransfer forall
% LocalWords:  parameterize GHCManual FactBase exprs Kildall FwdRewrite monadic
% LocalWords:  mkFRewrite mkBRewrite Rewriters emptyGraph FuelMonad Whalley fp
% LocalWords:  BwdPass FwdPass analyzeAndRewriteBwd analyzeAndRewriteFwd bp
% LocalWords:  CheckpointMonad LabelsPtr MaybeC MaybeO monad deadCode JustC
% LocalWords:  runInfinite runSimpleUniqueMonad UniqueMonad CheckingFuelMonad
% LocalWords:  SimpleUniqueMonad analyzedAndRewriteBwd entryPoints runWithFuel
% LocalWords:  infiniteFuel printf
