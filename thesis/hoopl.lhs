\documentclass[12pt]{report}
%include polycode.fmt
%include lineno.fmt
\input{preamble}
\numbersoff
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
\label{hoopl_sec_cfg}

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

We only define |entryLabel| for the |Entry| constructor, because only
it is ``open on entry'' (i.e., due to its type |C O|).  We do not
define any cases for |successors| even though |Return| is ``closed on
exit'' (i.e., due to its type |O C|), because our AST does not
represent the destination of a return (implicit or explicit). If our
AST supported branching (such as \texttt{if} statements), then
|successors| would be more interesting.

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

Recall that dataflow analysis computes \emph{facts} on each edge for
each block $B$ in the CFG. We call the set of facts computed on the
inbound edges of a block $B$ \inBa and the set facts on outbound edges
\outBa. A \emph{meet operator} combines facts when multiple edges
enter or leave the block (depending on the direction of the
analysis). The analysis will always terminate if the meet operator
defines a finite-height lattice. A \emph{forwards} dataflow-analysis
computes the set \outBa, for a block $B$ in the CFG, using \inBa and
the transfer function; \inBa then equals the meet of all \outBa from
predecessor blocks. A backwards analysis does the same, except in
reverse.

\intent{Introduce |DataflowLattice| type and show connection to facts and 
the meet operator.}

Hoopl provides the type |DataflowLattice| (shown with several
associated definitions in Figure~\ref{hoopl_fig7}) so clients can
define the facts and meet operator for their specific analysis. The
field |fact_name| exists only for documentation. Hoopl uses the value
in the |fact_bot| field to create initial facts for each block in
the CFG when analysis starts. The |fact_join| field will hold the
client's implementation of their meet operator.

The meet operator, |fact_join|, takes two arguments and returns a pair
consisting of a value and a |ChangeFlag|. The arguments, of type
|OldFact| and |NewFact|, represent two, possibly different, sets of
facts for the same block. \margin{The facts may differ for two
  reasons: |OldFact| and |NewFact| could be from different iterations
  of the analysis, or they could be from multiple predecessors or
  successors\footnote{Facts come from multiple predecessors when doing
    forwards analysis, multiple successors when going backwards.} of
  the current block.}{Is |fact_join| used to combine facts from nodes,
  or does th transfer function implicitly do that with |FactBase|?}
The client determines if the facts differ and returns |SomeChange|,
plus the new facts, if so. Otherwise, the client returns |NoChange|,
indicating the the |OldFact| and |NewFact| values are equal. Hoopl
choose this implementation for efficiency: the client can determine if
facts change during each join, rather than the library comparing all
facts on every iteration.

\begin{myfig}
  \begin{minipage}{\hsize}
> data DataflowLattice a = DataflowLattice { fact_name :: String,
>   fact_bot :: a,
>   fact_join :: Label -> OldFact a -> NewFact a 
>                -> (ChangeFlag, a) }
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

\intent{Remind reader how liveness is computed for dead-code
  elimination} As stated in Section~\ref{hoopl_sec4}, dead-code
elimination uses \emph{liveness} analysis to find dead code. A
variable is live if it is used after declaration; otherwise, it is
dead.

\intent{Introduce fact definition for liveness.} 

We define the set \setL{Live} as the set of all declared variables
in the program. Recall that dataflow analysis computes two sets for
each block in the CFG, named \inBa and \outBa. For liveness analysis,
\inBa and \outBa are subsets of \setL{Live}. 

\intent{Introduce meet for liveness}

Our transfer function, given in Section~\ref{hoopl_sec5}, will show
that we traverse the CFG backward. To compute the \outBa set for block
$B$, we take the union of all the \inE sets of $B$'s successors. That
is, the meet operator for liveness is set union.

\intent{Illustrate liveness using a better example than our sample
  program.}  

Consider Figure~\ref{hoopl_fig8}, which shows a fragment of C code and
its associated CFG. In Block~\refNode{hoopl_lst6_assignx2} only !+x+!
is live due to ``!+x = 0+!.'' Therefore, $\inB{hoopl_lst6_assignx2} =
\{\facts{x}\} \subset \setL{Live}$.  However, in
Block~\refNode{hoopl_lst6_assignx1} both !+x+! and !+y+!  are live due
to ``!+x = 1 + y+!'' (and thus, $\inB{hoopl_lst6_assignx1} =
\{\facts{x,y}\} \subset \setL{Live}$). Because both
Block~\refNode{hoopl_lst6_assignx1} and
Block~\refNode{hoopl_lst6_assignx2} are successors to
Block~\refNode{hoopl_lst6_test}, \outB{hoopl_lst6_test} must be the
union of \inB{hoopl_lst6_assignx2} and \inB{hoopl_lst6_assignx1}; that
is, we compute that $\outB{hoopl_lst6_test} = \{\facts{x,y}\} \subset
\setL{Live}$.

\begin{myfig}
  \begin{tabular}{cc}
    \input{hoopl_lst5} & \input{hoopl_lst6} \\
    \scap{hoopl_fig8_a} & \scap{hoopl_fig8_b}
  \end{tabular}
  \caption{A fragment of C code and its associated CFG.}
  \label{hoopl_fig8}
\end{myfig}

\intent{Show fact and meet operator for example as Haskell code and as
  dataflow equations.}  

Figure~\ref{hoopl_fig9} shows definitions for our liveness facts and
meet operator. Part~\subref{hoopl_fig9_a} shows dataflow equations
(using the notation of Chapter~\ref{ref_chapter_background}) and
Part~\subref{hoopl_fig9_b} shows Haskell
code. Equation~\ref{hoopl_eqn_facts} in Part~\subref{hoopl_fig9_a}
defines \setL{Live} as the set of variables in the CFG; in
Part~\subref{hoopl_fig9_b}, we define an analogous synonym, |Live|, as
a |Set Var| (using Haskell's standard  |Set|
type). Equation~\ref{hoopl_eqn_meet} defines our meet operator as set
union. The |meet| function implements the operator. |meet| takes two sets
, |(OldFact old)| and |(NewFact new)|. If |old| does not equal |new| we
return |SomeChange| and the union of the two sets. Hoopl provides the
|changeIf| function that maps |Bools| to |ChangeFlag|
values.\footnote{If the sets are equal, the second value of the pair
  will be ignored and lazy evaluation saves us from computing a union
  we never use.}


\begin{myfig}
  \begin{tabular}{cc}
    \begin{minipage}{3in}
      \input{hoopl_fact_def}
    \end{minipage} & \begin{minipage}{3.5in}
%let latticeDef = True
%include DeadCodeC.lhs
%let latticeDef = False
    \end{minipage} \\
    \scap{hoopl_fig9_a} & \scap{hoopl_fig9_b}
  \end{tabular}
  \caption{Fact and meet definitions for liveness
    analysis. Part~\subref{hoopl_fig9_a} shows dataflow equations;
    Part~\subref{hoopl_fig9_b} shows Haskell code.}
  \label{hoopl_fig9}
\end{myfig}

The |lattice| function in Part~\subref{hoopl_fig9_b} creates a
|DataflowLattice| value for our analysis. Its type, |Live|, reflects
the facts computed. The bottom element for the lattice is also
|Set.empty|, an empty set, meaning we have no knowledge about liveness
when analysis begins.

%% \intent{Aside: |WithTop|/|WithBottom| types.}
%% \lipsum

\intent{Conclude \& Summarize}
\lipsum

\section{Direction \& Transfer Functions}
\label{hoopl_sec5}
\intent{Reminder about what transfer functions do \& that they can go forwards or
backwards.}

The \emph{transfer function}, as defined by dataflow analysis,
computes either \inBa or \outB for a some block $B$ in the CFG. A
\emph{forwards} analysis calculates \outBa, based on the contents of
$B$ and \inBa. A \emph{backwards} analysis does the reverse: computing
\inBa from the block's contents and its \outBa.

\intent{Introduce |FwdTransfer| and |BwdTransfer| types; Show how
  |mkFTransfer| and |mkBTransfer| construct transfer functions.} 

Hoopl defines the |FwdTransfer| and |BwdTransfer| types, shown in
Figure~\ref{hoopl_fig10}, to represent forwards and backwards transfer
functions. The |n| parameter represents the blocks contents (i.e., the
AST of the language analyzed). The |f| parameter represents the facts
computed. Hoopl does not export the constructors for |FwdTransfer| or
|BwdTransfer|; instead, clients use the |mkFTransfer| and
|mkBTransfer| functions, whose signatures are also shown in
Figure~\ref{hoopl_fig10}. 

\begin{myfig}
    \begin{minipage}{\hsize}
> newtype FwdTransfer n f 
> newtype BwdTransfer n f

> mkFTransfer :: (forall e x . n e x -> f -> Fact x f) -> FwdTransfer n f
> mkBTransfer :: (forall e x . n e x -> Fact x f -> f) -> BwdTransfer n f      
    \end{minipage}
  \caption{Hoopl's |FwdTransfer| and |BwdTransfer| types. They can be
    constructed with the functions |mkFTransfer| and |mkBTransfer|.}
  \label{hoopl_fig10}
\end{myfig}

The signatures for |mkFTransfer| and |mkBTransfer| use
\emph{existential} types. Hoopl requires that we parameterize our AST
(i.e., the |n| type) using the |O| and |C| types from
Section~\ref{hoopl_sec_cfg}.  A standard Haskell function cannot
pattern match on values with different types (e.g., |Assign| has type
|CStmt O O|, but |Entry| has type |CStmt C O|).  Therefore, to
pattern-match on all constructors, the transfer function must be
defined with an \emph{existential} type. The notation |(forall e x. n
e x -> {-"\dots"-})| indicates that the |e| and |x| types will not be
visible outside the function definition. This allows us to write one
transfer function that can match on all constructors in the
AST.\footnote{Hoopl also exports |mkFTransfer3| and |mkBTransfer3|
  which take separate arguments for each |C O|, |O O| and |O C| type,
  in case the node type is not known and an existential transfer
  function cannot be defined.}

\intent{Types families and |Fact C| vs. |Fact O|} 

The |mkFTransfer| and |mkBTransfer| functions look almost identical
but for their |Fact x f| argument. |Fact x f| defines a type family
(another GHC extension) such that the \emph{actual} type of |Fact x f|
depends on the type of |x|. When |x| is |C|, then |Fact x f| is a
|FactBase f| type. A |FactBase| maps |Labels| to |f| values. When |x|
is |O|, |Fact x f| is only |f|.

Recall that a |C| type on exit means the block may branch to one of
many successors. In a forwards analysis, the transfer function
distributes facts to all successors. \margin{In a backwards analysis,
  the transfer function gathers facts from all successors.}{Doesn't
  this imply a meet operation?}

A forwards transfer function produces a |Fact| type. The
parameterization of |FactBase| by |C| allows the transfer function to
distribute facts to any (or all) of the block's successors, as
required by the particular analysis. That is, it produces a map of
|Labels| to |Facts|. A backwards transfer function receives a |Fact|
argument. If the block has type |n e C|, then the transfer function
receives a map of |Labels| to |Facts| for all its successor blocks. 

\intent{Explain how |Fact e C| does not conflict with the meet operator --- or does it?}
%% The |FactBase| argument given to the backwards transfer function might
%% seem to conflict with the meet operator defined for the analysis. In
%% fact, the |FactBase| is provided for informational purposes only ---
%% the transfer function is free to use it in any way. \margin{Because
%%   Hoopl interleaves rewriting and analysis (as discussed in
%%   Section~\ref{hoopl_sec_iter}), the facts in the |FactBase|
%%   associated with each successor label will evolve. converge until the
%%   analysis reaches a fixed point.}{Better verify this!}

\intent{Give definition for example's transfer function.}

Figure~\ref{hoopl_fig11} shows the transfer function, |liveness|, for
our example. The |vars| function takes an expression and returns the
set of all variables used in the expression. The |transfer| function
computes the facts for each value in |CStmt|, which we now detail:

\begin{myfig}
  \begin{minipage}{\hsize}
    \begin{withHsNum}
%let includeLiveness = True
%include DeadCodeC.lhs
%let includeLiveness = False
    \end{withHsNum}
  \end{minipage}
  \caption{The transfer function for our liveness example.}
  \label{hoopl_fig11}
\end{myfig}

{\narrower

\noindent\hangindent=\parindent\hangafter=1|transfer (Assign var expr) f|\quad In this case, |f| represents the
set of live variables found so far. We first remove |var| from |f|,
since (this) instance of |var| can no longer be live. Any variables in
|expr| are live, so we add them to |f|.\footnote{The order is not
  import for C, but may be for other languages that allow the same
  variable to be declared more than once in the same scope.}

\noindent\hangindent=\parindent\hangafter=1|transfer (Call _ exprs) f|\quad This case resembles |Assign|, except
we do not remove any variables from |f|. We just add all variables found in all
the elements of |exprs|.

\noindent\hangindent=\parindent\hangafter=1|transfer Return f|\quad We do not add any variables here, since our |Return|
does not take an argument. However, |f| will be a |FactBase| value here. We
take the union of all live variables in all successors and return that as our
result. If our AST was more complicated this would have an effect --- as it is,
|f| will always be an empty |FactBase|.

}
\section{Iteration \& Fixed Points}

\intent{Describe how Hoopl iterates on facts; how Hoopl determines when
a fixed point has been reached.}
\lipsum

\section{Rewriting}

\intent{Briefly describe rewriting as transformation.}
\lipsum
\intent{Introduce |FwdRewrite| and |BwdRewrite| types; show
  how to construct them with |mkFRewrite3| and |mkBRewrite3|.}
\lipsum

\intent{Segue to |mkFRewrite|, |mkBRewrite|, existentials and type families.}
\lipsum

\intent{Give definition of examples transfer functino.}
\lipsum

\section{Interleaved Analysis \& Rewriting}

\intent{Discuss how Hoopl manages to interleave both.}
\lipsum

\section{Dead-Code Elimination}

\intent{Apply the optimization developed to the example program with 
lots of illustratin.}
\lipsum

\section{The Rest of Hoopl}

\intent{Items that don't fit in elsewhere: combinators for rewriting,
  the |CheckPoint| monad, optimization fuel, |liftFuel|,
  |runInfinite|, |runChecked|, etc. }
\lipsum

\section{Summary}
\label{hoopl_sec3}
\intent{Discuss experience with Hoopl; summarize features, move on.}
\lipsum

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

