%&preamble
\input{nodocclass}\dodocclass
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\begin{document}
\numbersoff
\input{document.preamble}
\renewcommand{\textfraction}{0.1}
\renewcommand{\topfraction}{0.9}

\chapter{Dataflow Optimization}
\label{ref_chapter_background}

%% A short section giving the history of dataflow optimization techniques
%% and basic concepts.

In 1973, Gary Kildall described a framework for analyzing and
transforming programs, calling it a \emph{global analysis algorithm}
\citep{Kildall1973}. His algorithm represents programs as
\emph{directed graphs}, where each node corresponds to a statement or
expression in the program. The edges between nodes represent possible
runtime execution paths. An \emph{optimizing function} is applied to
each node in the graph, transforming an \emph{input pool} of facts
into an \emph{output pool}. When cycles occur in the graph, output
pools can change input pools, causing the algorithm to apply the
optimizing function again. His algorithm terminates when all output
pools stop changing; the facts gathered can then be used to transform
the program.

Though Kildall named his algorithm ``global,'' he also applied it to
smaller pieces of programs such as subroutines or function
definitions. He showed that some analysis' required reversing the
input and output pools; in other words, running the algorithm
backwards.

This chapter describes Kildall's algorithm, now known as \emph{the
  dataflow algorithm} or the technique of \emph{dataflow analysis}. In
Section~\ref{sec_back1} we define \emph{control-flow graphs} (\cfgs),
which the directed graphs representing the program are now called.
Section~\ref{sec_back3} introduces ``basic blocks,'' not something
originally defined by Kildall but now a fundamental way of
representing nodes in \cfgs. We show the modern representation
of the dataflow algorithm in Section~\ref{back_sec_df}, introducing
terms and definitions that have been defined since Kildall's original
work. In Section~\ref{back_subsec_eq} we show the general form of
\emph{dataflow equations} that can be used to describe any dataflow
analysis; we will use these equations later in the thesis to describe
our own analysis'. Section~\ref{back_sec_quality} discusses the
trustworthiness of the dataflow algorithm --- that is, it shows how we
can know a particular analysis has given the best possible
solution. Transforming programs based on a dataflow analysis is
discussed in Section~\ref{back_sec_apply}, and we conclude in
Section~\ref{sec_back9}.

\section{Control-Flow Graphs}
\label{sec_back1}

%% Begin by placing the specific concept in the overall context of
%% dataflow. Give a small example highlighting the concept. Point
%% out fine points or subtleties that occur when generalizing the concept. End
%% by summarizing how the concept fits into dataflow (in a bit larger
%% sense than the first summary).

Figure~\ref{fig_back1} shows a simple C program and its
\emph{control-flow graph} (\cfg). Each \emph{node} in
Part~\subref{fig_back1_b} represents a statement or expression in the
original program. For example, \refNode{lst_back2_assigna} and
\refNode{lst_back2_assignb} represent the assignment statements on
line \ref{lst_back1_assign}. Notice that the declaration of !+c+! does
not appear in a corresponding node; because the declaration does not
cause a runtime effect, we do not represent it in the graph.  Nodes
\entryN and \exitN designate where program execution \emph{enters} and
\emph{leaves} the graph. If the graph represented the entire program,
we would say execution \emph{begins} at \entryN and \emph{terminates}
at \exitN. However, the \cfg may be embedded in a larger program, for
which reason we say \emph{enters} and \emph{leaves}.

\begin{myfig}[th]
\begin{tabular}{cc}
  \begin{minipage}[b]{\hsize/2-0.5in}
    \input{lst_back1} 
  \end{minipage} & \input{lst_back2} \\
\scap{fig_back1_a} & \scap{fig_back1_b} 
\end{tabular}
\caption{\subref{fig_back1_a} A C-language program fragment. \subref{fig_back1_b} The
  \emph{control-flow graph} (\cfg) for the program.}
\label{fig_back1}
\end{myfig}

Directed edges show the order in which nodes execute. The edges
leaving \refNode{lst_back2_test} (representing the test
``!+if(a > b)+!'' on line \ref{lst_back1_test}) show that
execution can branch to either \refNode{lst_back2_true} (when
$a > b$) or \refNode{lst_back2_false} (when
$a \leq b$). A node followed by multiple successors
(i.e., where multiple edges leave the node) represents a \emph{branch}
or \emph{conditional} statement. Any one of the successor nodes may
execute following the conditional statement.

In this particular example, it is obvious that
\refNode{lst_back2_false} will always execute after
\refNode{lst_back2_test}, because the test will always fail. However,
control-flow graphs show \emph{possible} execution paths. They do not
take into account the actual runtime values in a given graph. While in
this case it is easy to determine how the program will behave, in
general we cannot predict behavior without running the program. 

The dataflow algorithm approximates a program's runtime state by
analyzing the control flow of the program. Control-flow graphs show
the order in which expressions and statements in a program are
evaluated. It is the job of our \emph{dataflow analysis} to determine
how to make the program more efficient.

\section{Basic Blocks}
\label{sec_back3}

%% %% Begin by placing the specific concept in the overall context of
%% %% dataflow. Give a small example highlighting the concept. Point
%% %% out fine points or subtleties that occur when generalizing the concept. End
%% %% by summarizing how the concept fits into dataflow (in a bit larger
%% %% sense than the first summary).

%% Basic blocks
Consider the C-language fragment and control-flow graphs (\cfg) in
Figure~\ref{fig_back4}.  Part~\subref{fig_back4_b} shows the \cfg for
Part~\subref{fig_back4_a}: a long, straight sequence of nodes, one
after another. Part~\subref{fig_back4_c} represents the assignment statements on
lines~\ref{lst_back3_start} -- \ref{lst_back3_end} as a \emph{basic
  block}: a sequence of statements with one entry, one exit, and no
branches in-between. Execution cannot start in the ``middle'' of the
block, nor can it branch anywhere but at the end of the block. In fact,
Part~\ref{fig_back4_b} also shows four basic blocks --- they just happen
to consist of one statement each.

\begin{myfig}
\begin{tabular}{m{1.5in}m{1.5in}m{1.5in}}
  \begin{center}
    \input{lst_back3}
  \end{center} & %%
  \begin{center}
    \input{lst_back4}
  \end{center}
  & %%
  \begin{center}
    \input{lst_back5}
  \end{center} \\
  \vtop{\centering\scap{fig_back4_a}} & \vtop{\centering\scap{fig_back4_b}} & \vtop{\centering\scap{fig_back4_c}} \\
\end{tabular}
\caption{\subref{fig_back4_a}: A C-language fragment to illustrate
  \emph{basic blocks}.  \subref{fig_back4_b}: The \cfg for
  \subref{fig_back4_a} without basic blocks. \subref{fig_back4_c}: The
  \cfg for \subref{fig_back4_c} using basic blocks.}
\label{fig_back4}
\end{myfig}

The representation given in Part~\subref{fig_back4_c} has a number of
advantages. It tends to reduce both the number of nodes and the number
of edges in the graph. The dataflow algorithm maintains two sets of
\emph{facts} for every node --- reducing the number of nodes obviously
reduces the number of facts stored. The algorithm also iteratively
propagates facts along edges --- so reducing the number of edges
reduces the amount of work we need to do. When rewriting, blocks allow
us to move larger amounts of the program at once. It also can be shown
(see \cite{Aho2006}) that we do not lose any information by collapsing
statements into blocks. For efficiency and brevity, we will work with
basic blocks rather than statements from here forward.

\section{The Dataflow Algorithm}
\label{back_sec_df}

Kildall's dataflow algorithm provides a general-purpose mechanism for
analyzing control-flow graphs of programs. The algorithm itself does
not mandate a specific analysis. Rather, it is parameterized by the
choice of \emph{facts}, \emph{meet operator}, \emph{transfer
  function}, and \emph{direction}. The facts and meet operator form a
lattice. Together, they approximate some property of the program that
we wish to analyze. The transfer function transforms facts to mimic
the flow of information in the control-flow graph. The direction is
dictated by the type of analysis --- each particular analysis runs
\emph{forwards} or \emph{backwards}.

%% Constant-propagation
Consider Figure~\ref{fig_back7}, Part~\subref{fig_back7_initial}, which
shows a C function containing a loop that multiplies the argument by 10
some number of times. Line~\ref{fig_back7_m} declares !+m+! and assigns
it the value 10. The function uses !+m+! in the loop body on
Line~\ref{fig_back7_loop} to multiply the value passed in
repeatedly. 

\begin{myfig}[tbh]\disableoverfull
  \begin{tabular}{cc}
    \input{lst_back11} & \input{lst_back12} \\
    \scap{fig_back7_initial} & \scap{fig_back7_opt} 
  \end{tabular}
  \caption{A C program which multiplies its argument, !+val+!, by
    10 !+cnt+! times. Part~\subref{fig_back7_initial} shows the
    original program. In Part~\subref{fig_back7_opt}, we have used
    \emph{constant propagation} to replace the use of !+m+! in
    the loop body with 10.}
  \label{fig_back7}
\end{myfig}

This function is just used for illustration --- we do not expect anyone
would actually write code this way (after all, !+mult10+! is just
!+10 * val * cnt+!). In any case, the program in
Figure~\ref{fig_back7_initial} can be transformed by replacing the
variable !+m+! with 10 in the loop body. This may allow the compiler to
generate code that directly multiplies !+val+! times 10 and saves using
a register to hold the value of !+m+!. We can use a dataflow analysis
known as \emph{constant propagation} to justify this
transformation. The constant propagation analysis recognizes when a
variable's value does not change in some context and then replaces
references to the variable with the constant
value. Figure~\ref{fig_back7}, Part~\subref{fig_back7_opt} shows the
optimized program, replacing !+m+! with 10 on
Line~\ref{fig_back7_opt_loop}.

\subsection{Facts and Lattices} 
\label{back_subsec_facts}

Constant propagation determines if each variable's value changes
during execution. The analysis \emph{approximates} the actual values
of the variables, as we cannot in general determine their exact
value. We will place the value of each variable into one of three
categories at each point in the control-flow graph: \emph{unknown}, a
\emph{known integer constant}, or
\emph{indeterminate}. \emph{Unknown}, represented by $\bot$
(``bottom''), is the initial value for all variables in our
analysis. A \emph{known integer constant}, $C \in \ZZ$, means our
analysis identified that the variable was assigned a specific value
that does not change. \emph{Indeterminate}, indicated by $\top$
(``top''), means our analysis could not identify a constant value
for the variable. Together, $\{\bot, \top\} \cup \ZZ$ forms a set
which we will denote as \setLC.

\begin{myfig}
  \input{lst_back17}
  \caption{Our program, annotated with facts partway through the
    analysis. Notice that \outB{lst_back17_assign} and
    \outB{lst_back17_incr} give differing values to $i$. We use a \emph{meet
      operator} when combining these two values while calculating
    \inB{lst_back17_test}.}
  \label{fig_back11}
\end{myfig}

Figure~\ref{fig_back11} shows the control-flow graph of our program,
annotated with \emph{facts} about the variable $i$ before and
after nodes \refNode{lst_back17_assign}, \refNode{lst_back17_test}
and \refNode{lst_back17_incr}. This analysis defines facts as pairs,
$(a,x)$, where $a$ is the name of a variable and $x \in \setLC$. The
\inE sets represent the value of the variables \emph{before} the
statement in the node executes; the \out sets give the value of the
variables afterwards. Together these sets represent our knowledge
about each variable's value at each point in the program.

Constant propagation is a \emph{forwards} analysis, meaning the values
for each \inE set are calculated based on the \out values of its
predecessors. Figure~\ref{fig_back11} shows the facts computed partway
through this analysis, concentrating on the nodes that reference $i$:
\refNode{lst_back17_assign}, \refNode{lst_back17_test} and
\refNode{lst_back17_incr}. \refNode{lst_back17_test} has two
predecessors: \refNode{lst_back17_assign} and
\refNode{lst_back17_incr}. Their \out sets,
\outB{lst_back17_assign} and \outB{lst_back17_incr}, give differing
values to $i$: $0$ and $\top$. To combine these values when computing
\inB{lst_back17_test}, we use a \emph{meet operator}.

The \emph{meet operator}, \lub, defines how we will combine values in
\setLC. Figure~\ref{tbl_back4} gives the definition of \lub. For any
value of $x \in \setLC$, $\bot \lub x$ results in $x$. Conversely, $x
\lub \top$ results in $\top$. Two differing constants, $C_1$ and
$C_2$, result in $\top$, while equal constants give the same constant. 

\begin{myfig}
  \begin{math}
    \begin{array}{cccc}
      v_1 & v_2 & v_1 \lub v_2 \\
      \cmidrule(r){1-1}\cmidrule(r){2-2}\cmidrule(r){3-3}
      \bot & x & x \\
      x & \top & \top & \\ 
      C_1 & C_2 & \top & \text{($C_1 \neq C_2$)} \\
      C_1 & C_2 & C_1 & \text{($C_1 = C_2$)}
    \end{array}
  \end{math}
  \caption{Definition of the \emph{meet operator}, \lub, for the
    lattice used in our constant propagation analysis. $v_1$ and $v_2$
    are values in \setLC. The table shows how lub combines any two
    values.}
  \label{tbl_back4}
\end{myfig}

Our definition of \lub allows us to distinguish variables for which we
have no information from those with non-constant values. This matches
the definition of the C language, where a variable that is not
initialized has an undefined value. This allows us to legally
transform some programs by assuming the undefined variable has the
best possible value. For example, Figure~\ref{fig_back15} shows a
block with two predecessors. \OutB{fig_back15_b1} has the fact
\factC{x}{1}, while \outB{fig_back15_b2} says \factC{x}{\bot}. Our
definition of \lub intuitively says that, when we do not know anything
about a variable, we can use the information we already have
instead. \OutB{fig_back15_b2} adds no information about $x$; we can
assume it is $1$, the best possible value. Our definition of \lub
follows that intuition and tells us that \inB{fig_back15_b3} should be
\factC{x}{1 \lub \bot}, or \factC{x}{1}.

\begin{myfig}
  \input{lst_back19}
  \caption{A control-flow graph illustrating the behavior of \lub with
    $\bot$ (i.e., undefined) values.}
  \label{fig_back15}
\end{myfig}

We would not make this assumption if we wished to warn the programmer
that a potentially uninitialized variable could be used. In that case,
we would define \lub such that $x \lub \bot$ was $\bot$. Then, when
the fact \factC{x}{\bot} appeared, we could warn that a variable might
be used before being initialized. Similarly, if our language defined
an initial value for all variables, our assumption would have no
effect. We could use the same definition, but no variable would have
the value $\bot$ --- each would have a known initial value. 

We have defined \lub on elements in \setLC, but our facts are pairs
$(a,x)$ where $a$ is a variable and $x$ a value in \setLC; \inE and
\out are sets of facts.  Therefore, we define the $\wedge$ (``wedge'')
operator to apply \lub to sets of facts ($F_1$ and $F_2$ below):

\begin{singlespace}\correctspaceskip
  \begin{align*}\allowdisplaybreaks[0]
    F_1 \wedge F_2 &= \setdef{(a, x_1 \lub x_2)}{(a,x_1) \in F_1, (a,x_2) \in F_2} \\
    &\; \cup \setdef{(a,x_1)}{(a,x_1) \in F_1, a \not\in \dom(F_2)} \\
    &\; \cup \setdef{(a,x_2)}{(a,x_2) \in F_2, a \not\in \dom(F_1)} \label{eqn_back18}\addtag\\
    \dom(F) &= \setdef{a}{(a,x) \in F} \label{eqn_back_dom}\addtag
  \end{align*}
\end{singlespace}

Our $\wedge$ operator acts like union when a variable in $F_1$ does
not appear in the domain of $F_2$; likewise for a variable only in
$F_2$. When a variable appears in both $F_1$ and $F_2$, the values for
the variable are combined using \lub.

To compute \inBa, we apply $\wedge$ to each \out set of $B$'s
predecessors. We use a subscripted $\bigwedge$ to indicate we combine
all of the \out sets into one using $\wedge$:

\begin{singlespace}\correctspaceskip
\begin{equation}
  \inBa = \bigwedge\limits_{\mathclap{P \in \mathit{pred}(B)}} \outXa{P} \label{eqn_back8}.
\end{equation}
\end{singlespace}

\noindent With these definitions, we can now show how the \inB{lst_back17_test}
set in Figure~\ref{fig_back11} is derived:

\begin{singlespace}\correctspaceskip
\begin{align*}\allowdisplaybreaks[0]
  \inB{lst_back17_test} &= \bigwedge\limits_{\mathclap{P \in \mathit{pred}(\refNode{lst_back17_test})}} \outXa{P} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Predecessors of \refNode{lst_back17_test}; Equation~\eqref{eqn_back8}.}}}
  &= \outB{lst_back17_assign} \wedge \outB{lst_back17_incr} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Definition of \outB{lst_back17_assign} and \outB{lst_back17_incr}.}}}
  &= \{\factC{i}{0}\} \wedge \{\factC{i}{\top}\} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Equation~\eqref{eqn_back18}.}}}
  &= \{\factC{i}{0 \lub \top}\} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Definition of \lub from Figure~\ref{tbl_back4}.}}}
  &= \{\factC{i}{\top}\} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Definition of \inB{lst_back17_test}.}}}
  &= \{\factC{i}{\top}\}.
\end{align*}
\end{singlespace}

Together, \setLC and \lub form a \emph{lattice}.\footnote{The lattice
  can also have a \emph{join} operator, but for our purposes we solely
  use the meet.}  The lattice precisely defines the facts computed in
our analysis. In this case, the lattice represents
knowledge about a variable's value. Each specific dataflow analysis
computes different facts, but those facts are always represented by a
lattice.

We have established that our analysis computes \emph{facts} at each
node in our programs control-flow graph. The facts assign a value from
the set $\{\bot, \top\} \cup \ZZ$ to each variable in the program,
at each node in the graph. We defined a \emph{meet operator}, \lub,
which is used to combing conflicting values when computing \inBa.  The
facts and meet operator together define a \emph{lattice}. We next
explore how \out facts are computed for each node.

\subsection{Transfer Functions}
\label{back_subsec_transfer}

The dataflow algorithm calculates new facts using a \emph{transfer
  function}. The transfer function is specific to both the analysis
performed and the semantics of the programming language used to write
the program analyzed. Theoretically, each node in the graph can
have its own transfer function, but in practice the function is 
defined by cases for each statement or expression in the language. 

In a \emph{forwards} analysis, the transfer function computes the \out
set for a given node. In a backwards analysis, the transfer function
computes the \inE set. That is, a forwards analysis computes facts
that hold \emph{after} a node executes. A backwards analysis computes
facts that were true \emph{before} a node executed.  In both cases,
the transfer function also considers known facts (i.e., \inE facts for
forwards, \out for backwards) as well as the statements in the node.

For our example analysis, we only consider two kinds of statements:
constant and non-constant updates. A constant update is one of the
form $a !+=+! C$, where $C$ is a known integer value. A non-constant
update is any other type of assignment; in our example, something like
$i!++++!$.

We define a transfer function, $t$, for our analysis in terms over
these two types of statements. Our function takes a set of input facts
($F$), and a statement; it produces a set of output facts:

\begin{singlespace}\correctspaceskip
  \begin{equation}\allowdisplaybreaks[0]
    \begin{array}{rl}
      t (F, a\ \text{\tt =}\ C) &= \{(a, x \lub C), \text{when\ } (a, x) \in F\ \text{or} \\
      & \phantom{= \{}(a, C), \text{when\ } a \not\in \dom(F)\}\ \cup \\
      & \phantom{=} F\ \backslash\ \mfun{uses}(F, a).\\
      t (F, a\text{\tt ++}) &= \{(a, \top)\} \cup (F\ \backslash\ \mfun{uses}(F, a)). \\
      t (F, a\ \text{\tt +=\ } b) &= \{(a, \top)\} \cup (F\ \backslash\ \mfun{uses}(F, a)). \\\\
      \mfun{uses}(F, a) &= \{(a, x)\ ||\ a \in \dom(F)\}. 
    \end{array}\label{eqn_back4}
  \end{equation}
\end{singlespace}

When a node contains a constant update ($a !+=+! C$) and the input
facts do not contain a fact for $a$, then
Equation~\eqref{eqn_back4} combines the fact \factC{a}{C} with the
input set. Otherwise, the \lub operator is used to combine the
existing fact \factC{a}{x} with the new fact. For a non--constant
update, a new fact \factC{a}{\top} is always added to the output
set. In both cases, all mentions of $a$ in the input set are removed
before being combined with the new fact --- this ensures that no more
than one fact per variable exists in our fact set.

The definition in Equation~\eqref{eqn_back4} matches our intuition for
constant propagation. When we know a variable is assigned a constant,
we add that fact to our knowledge. When we know it is changed in a
non-constant way, we update our knowledge to show we no longer know
the value of the variable.

Figure~\ref{fig_back9}, Part~\subref{fig_back9_initial}, shows our
program, annotated with initial \inE and \out
facts. Figure~\ref{fig_back9}, Part~\subref{fig_back9_transfer}, shows
the same graph with annotations updated using
Equation~\eqref{eqn_back4}. The assignments in
\refNode{lst_back18_assign} create the facts \factC{m}{10},
\factC{n}{0}, and \factC{i}{0} in \outB{lst_back18_assign}. The
assignment to $n$ in \refNode{lst_back18_mult} is a non-constant
update so \outB{lst_back18_mult} contains \factC{n}{\top}. Similarly,
the increment to $i$ in \refNode{lst_back18_incr} creates the fact
\factC{i}{\top} in \outB{lst_back17_incr}.  

Notice that the updated \out sets do not affect subsequent \inE sets.
\InB{lst_back18_mult} does not contain the fact \factC{m}{10} from
\outB{lst_back18_assign}. \InB{lst_back18_test} also does not show the
facts \factC{i}{\top} or \factC{i}{0} from either
\outB{lst_back18_incr} or \outB{lst_back18_test}. The next section on
iteration will discuss how we update \inE sets as \out sets change.

\input{fig_back9}

Every dataflow analysis defines a \emph{transfer function} for
creating (or updating) facts. The function is specific to both the
analysis performed and the semantics of the underlying
program. Equation~\eqref{eqn_back4}, the transfer function for our
constant propagation example, defines how we derive information about
a variable's value after the statements in the given node execute.  In
the next section, we iteratively apply our transfer function and
lattice to the control-flow graph.

\subsection{Iteration \& Fixed Points}
\label{back_subsec_iter}

Figure~\ref{fig_back9} hints that facts
develop over time during analysis. In fact, the transfer function is
applied to each node in turn, creating new facts from old, until the
facts stop changing. In other words, the control-flow graph is
analyzed \emph{iteratively} until all \out (in the case of a forwards
analysis) or \inE (in the case of a backwards analysis) sets reach a
\emph{fixed point}.

Figure~\ref{fig_back13}, Part~\subref{fig_back13_tbl} shows how the
\inE and \out sets for each node change during our
analysis. The ``zeroth'' iteration corresponds to the initial value
for all facts: everything is $\bot$, i.e., unknown. Reading from
left-to-right gives the \inE and \out facts for a given node at each
iteration of the analysis. The control-flow graph is reproduced in
Part~\subref{fig_back13_cfg}. Following the control-flow between nodes
shows which \out sets are used to calculate \inE sets.

\begin{myfig}[tb]
  \setlength{\tabcolsep}{2pt}
  \hbox to \textwidth{\hss
  \begin{tabular}{cc}
    \input{fig_back13_tbl} & \def\prefix{fig_back13}\input{df_eg_cfg} \\
    \scap{fig_back13_tbl} & \scap{fig_back13_cfg}
  \end{tabular}\hss}
  \caption{This figure shows the values for $i$ calculated by all nodes in our
    example program. Part~\subref{fig_back13_tbl} shows the \inE and
    \out facts associated with each node, for variable $i$. Part~\subref{fig_back13_cfg}
    reproduces the control-flow graph for our program. After 4
    iterations the facts reach a fixed point (i.e., they stop
    changing).}
  \label{fig_back13}
\end{myfig}

Consider the value for $i$ in \inB{lst_back15_test}, the node that
tests the condition !+i < cnt+!. In the first iteration,
\inB{lst_back15_test} still assigns $\bot$ to
$i$. Equation~\eqref{eqn_back8} states that \inB{lst_back15_test} is
derived from the \out sets of \refNode{lst_back15_test}'s
predecessors: \refNode{lst_back15_assign} and
\refNode{lst_back15_incr}. By Equation~\eqref{eqn_back8} we can
calculate the value of $i$ in \inB{lst_back15_test}. Crucially, the
\out set used comes from the \emph{previous} iteration of the
analysis, which we emphasize by attaching the iteration number to each
set:

\begin{singlespace}\correctspaceskip
  \begin{align*}
    \inB{lst_back15_test}^1 &= \bigwedge\limits_{\mathclap{P \in \mathit{pred}(B)}} \outXa{P} .\\
    &= \outB{lst_back15_assign}^0 \bigwedge \outB{lst_back15_incr}^0 \\
    &= \left\{\dots, \factC{i}{\bot}, \dots\right\} \wedge \left\{\dots, \factC{i}{\bot}, \dots\right\} \\
    &= \left\{\dots, \factC{i}{\bot \lub \bot}, \dots\right\} \\
    &= \left\{\dots, \factC{i}{\bot}, \dots\right\}.
  \end{align*}
\end{singlespace}

Now consider the second iteration, where \inB{lst_back15_test} assigns
$\top$ to $i$. \outB{lst_back15_assign} gives $i$ the value $0$ (by !+i
= 0+!). However, \outB{lst_back15_incr} assigns $i$ the value $\top$,
because !+i+++! is a non-constant update. We can see why
$\factC{i}{\top} \in \inB{lst_back15_test}$ by
Equation~\eqref{eqn_back8}. Again we attach the iteration number to
each set, emphasizing its origin:

\begin{singlespace}\correctspaceskip
  \begin{align*}
    \inB{lst_back15_test}^2 &= \outB{lst_back15_assign}^1 \bigwedge \outB{lst_back15_incr}^1 \\
    &= \left\{\dots, \factC{i}{0}, \dots\right\} \wedge \left\{\dots, \factC{i}{\top}, \dots\right\} \\
    &= \left\{\dots, \factC{i}{0 \lub \top}, \dots\right\} \\
    &= \left\{\dots, \factC{i}{\top}, \dots\right\}.
  \end{align*}
\end{singlespace}

Notice how the conflicting values for $i$ are resolved with the \lub
operator. The value of $i$ in \outB{lst_back15_test} has reached a fixed point
with this iteration; it will no longer change.

The above example raises an important question: how do we know we have
reached a fixed point? How do we know we have gotten the best possible
answer?  Both of these questions can be answered if our lattice has
\emph{finite height} and the transfer function is \emph{monotone}.

Let us begin with the lattice. Consider again the meet operator, \lub,
defined in Figure~\ref{tbl_back4} and our set of values, \setLC:
\begin{singlespace}\correctspaceskip
  \begin{align*}
    \setLC &= \left\{ \bot, \top \right\} \cup \ZZ. \\\\
    \bot \lub x &= x. \\
    x \lub \top &= \top.\\
    C_1 \lub C_2 &= \top, \text{where}\ C_1 \neq C_2.\\
    C_1 \lub C_1 &= C_1.
  \end{align*}
\end{singlespace}
The definition of \lub imposes a \emph{partial order} on the values
in \setLC. That is, we can define an operator, \sqlte, such that
for all $x$ and $y$ in \setLC:
\begin{equation}
  x \sqlte y\ \text{if and only if}\ x \lub y = y.
  \label{eqn_back9}
\end{equation}
That is, $x$ is ``less than or equal to'' $y$ only when $x \lub y$ equals
$y$.

We now define the \emph{height} of our lattice as the
longest possible ordering of values in \setLC such that:
\begin{equation}
  x_1 \sqlte x_2 \dots \sqlte x_n, \text{where}\ x_1 \neq x_2 \neq \dots \neq x_n.
  \label{eqn_back10}
\end{equation}
That is, the height is the longest possible path from the ``lowest''
to ``highest'' element of the lattice where we do not repeat any
values and where the \sqlte relation holds among all values.

We can more succinctly define the height using a strict ``less than''
ordering. First, the \sqlt relation:
\begin{equation}
  x \sqlt y\ \text{if and only if}\ x \lub y = y\ \text{and}\ x \neq y.
\end{equation}
And now we can redefine height as the largest $n$ such that:
\begin{equation}
  x_1 \sqlt x_2 \dots \sqlt x_n.
  \label{eqn_back17}
\end{equation}

We can show by contradiction that the height of our lattice is
$3$. Suppose there exists $x_1 \sqlt x_2 \sqlt \dots \sqlt x_n$, such that $n = 4$. If
$x_4$ is $\top$, then $x_3$ must be an integer or $\bot$. If $x_3$ is
$\bot$, by Equation~\eqref{eqn_back17}, there is no such $x_2$ such
that $x_2 \sqlt \bot$. Therefore, $x_3$ cannot be $\bot$. If $x_3$ is
an integer, again by Equation~\eqref{eqn_back17}, $x_2$ must be
$\bot$. In turn, there is no such $x_1$ such that $x_1 \sqlt
\bot$. Therefore, $x_4$ cannot be $\top$ and in fact, by similar
arguments, it cannot exist. Using similar logic, we can show by cases
that $n$ (and the height of our lattice) must be $3$.

Now let us address the transfer function. A \emph{monotone} function 
has the following property:
\begin{equation}
  f(x) \sqlte f(y)\ \text{whenever}\ x \sqlte y.
  \label{eqn_back11}
\end{equation}
That is, a monotone function does not change the ordering between its
inputs. If $x$ is ``less than or equal to'' $y$, $f(x)$ will also be
``less than or equal to'' $f(y)$. 

The transfer function moves our facts along the lattice. A monotone
transfer function will never ``decrease'' its argument --- $f$ will
always produce a value that is at the same ``height'' or ``higher'' in
the lattice. The lattice represents the information we have gathered
during our analysis. In turn, the ordering of values represents ``how
much'' we know. That is, when a variable is assigned $\bot$, we do not
know anything about it. If it is assigned $\top$, we have seen ``too
many'' assignments (or some other update).  This means our transfer
function always increases (or does not change) the information we
have. 

To show that our transfer function (Equation~\eqref{eqn_back4}) is
monotone, consider some fact $(v,x)$ and some block $B$. $v$ is a
variable in the program; $x$ is a value in \setLC; and $B$ contains
some number of statements.  We analyze the fact, $(v,x')$ produced
applying our transfer function $f$ to $B$. If $B$ does not contain an
assignment affecting $v$, then $x = x'$, and we already know that $x \sqlte
x'$. If $B$ makes a non-constant update to $v$, then $x' = \top$ and we
know $x \sqlte \top$ for all $x$ by the definition of \lub. Finally,
if $B$ assigns some constant $C$ to $x$, then $x' = x \lub C$, which
again satisfies our relation. Therefore our transfer function is
monotone.

\section{Dataflow Equations}
\label{back_subsec_eq}

As stated at the beginning of this chapter, the dataflow algorithm
specifies four parameters: facts, meet operator, transfer function,
and direction. The prior section presented each parameter for the
constant propagation analysis separately. Figure~\ref{fig_back10}
presents all of them together, as a set of \emph{dataflow
  equations}. Pairs of elements from \setLC and \setL{Var} define
\setL{Fact}, our set of facts. Equation~\eqref{eqn_back12} defines our
meet operator, $\wedge$, on \setL{Fact} values. Our transfer function $t$,
defined by Equation~\eqref{eqn_back14}, shows how we create new facts based on
the statements in each node and our existing
facts. Equation~\eqref{eqn_back3} shows that we compute \outBa using
the transfer function $t$ and the \inBa facts for the
block. Equation~\eqref{eqn_back16} states that we apply $\wedge$ to
all of the \out sets for the predecessors of a block $B$ in order to
calculate \inBa. Together, Equations~\eqref{eqn_back3} and
\eqref{eqn_back16} specify a forwards dataflow analysis.

\begin{myfig}[p]
  \input{fig_back10}
  \caption{The transfer function and associated definitions for the
    constant propagation analysis. Equation~\eqref{eqn_back3} shows
    how \out facts are created from \inE facts. \InBa facts, for some
    block $B$, are created from the \outBa facts of its
    predecessors. Facts are combined using the set-wise $\bigwedge$
    operator.}
\label{fig_back10}
\end{myfig}

We can define an iterative dataflow algorithm in terms of these
parameters. Figure~\ref{fig_back14} gives the algorithm for a forwards
analysis.\footnote{The backwards case is almost identical.} On
Line~$\ref{fig_back14_init}$, we initialize all \out and \inE sets to
some suitable initial value from \setL{Fact}. The superscript on \inE
and \out sets refer to sets from the $i^{th}$ iteration;
initialization constitutes the ``zeroth'' iteration. Sometimes the
entry node's \out set gets special treatment, in which case we could
add the line:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    Out(\emph{Entry})$^0$ = $v$, $v \in \setL{Fact}$.
  \end{AVerb}
\end{singlespace}

\noindent However, \outXa{Entry} normally gets the same value as
other \out sets.

\begin{myfig}
  \begin{minipage}{\hsize}
    \begin{AVerb}[numbers=left,gobble=6]
      in($B$)$^0$ = $u$, out($B$)$^0$ = $f$, $\forall$\ nodes $B$; $f, u \in$\ \setL{Fact} \label{fig_back14_init}
      \textbf{do} \{
        in($B$)$^{i+1}$ = $\bigwedge\limits_{\mathclap{P \in pred(B)}} \text{out}^{i}$($P$) \label{fig_back14_in}
        out($B$)$^{i+1}$ = $t$(in($B$)$^i$, $B$)  \label{fig_back14_out}
      \} \textbf{until} out($B$)$^{i+1}$ = out($B$)$^{i}$, $\forall B$ \label{fig_back14_loop}
    \end{AVerb}
  \end{minipage}
  \caption{The dataflow algorithm, using parameters for facts, the meet operator,
    direction, and the transfer function.}
  \label{fig_back14}
\end{myfig}

The main loop of the algorithm always executes at least once. On
Line~$\ref{fig_back14_in}$, we calculate \inE facts for each node $B$ in
the next iteration, $\inBa^{i+1}$, by applying $\wedge$ to the
$\out^i$ sets of $B$'s predecessors from the current
iteration. Line~$\ref{fig_back14_out}$ calculates $\outBa^{i+1}$ for
each node by applying the transfer function, $t$, to that node, along
with $\inBa^{i}$, the \inE facts for the current iteration.

Line~$\ref{fig_back14_loop}$ checks if all \out$^{i+1}$ sets are equal
to their previous value, \out$\mathllap{^i}$. If not, the loop
repeats. Otherwise the algorithm terminates. The final values for each
\outBa set then hold the facts representing the result of our
analysis.

We have presented the iterative, forwards dataflow algorithm and shown
how the algorithm can be parameterized for a particular analysis. We
gave the parameterization for our constant propagation analysis in
Figure~\ref{fig_back10}. We know the algorithm will terminate if our
transfer function is \emph{monotone} and our lattice has 
\emph{finite} height. However, we have not discussed how to measure
the results our analysis gives us --- how do we know that they are the
best possible? We will address that question in the next section.

\section{Quality of Solutions to the Dataflow Equations}
\label{back_sec_quality}

Aho \citep{Aho2006} shows that for a dataflow analysis defined with a
finite lattice and monotone transfer function, Figure~\ref{fig_back14}
will compute a \emph{maximum fixed point}. A maximum fixed point means
that for any $F = \outBa$ computed by the algorithm, no other $F'$ can
be computed such that $F \sqlt F'$. In other words,
Figure~\ref{fig_back14} will compute \out facts with the best
possible information that our algorithm is capable of.

The maximum fixed point solution differs from the \emph{ideal}
solution in that the maximum fixed point solution may make more
conservative estimates than necessary. In particular,
the algorithm does not consider branches that will never be taken. For
example, the C program from Figure~\ref{fig_back1_a} will never
execute Line~$\ref{lst_back19_test_true}$, because the test !+if(a > b)+!
is always false:

\begin{singlespace}\correctspaceskip
\begin{AVerb}[numbers=left]
int a = 1, b = 2, c; \label{lst_back19_assign}
if(a > b) \label{lst_back19_test}
  c = 4; \label{lst_back19_test_true}
else     
  c = 3; \label{lst_back19_test_false}
\dots
\end{AVerb}
\end{singlespace}

Our algorithm, however, does not take such conditions into
account. The ideal solution is called the \emph{meet over paths}
solution because it takes into account only the paths that will taken
by the program. Determining the actual paths taken is an undecidable
problem --- thus we settle for the maximum fixed point. Fortunately,
the algorithm is conservative --- it never ignores (or adds) paths ---
so we can be sure that its analysis will never be wrong, just that it
probably will not be as good as the ideal.

\section{Applying Results}
\label{back_sec_apply}

Figure~\ref{fig_back7}, Part~\subref{fig_back7_initial} gave a sample
program which we wished to optimize using a \emph{constant propagation}
dataflow analysis. Figure~\ref{fig_back7}, Part~\subref{fig_back7_opt} gave
the result, replacing all occurrences of $m$ with $10$. Now knowing
the dataflow algorithm and the equations for constant propagation, we
can derive how that transformation is made.

Figure~\ref{fig_back12} gives the facts calculated for all nodes in our
program, during each iteration of the analysis. The first iteration
calculates that \outB{lst_back15_assign} assigns $m$ the value $10$, due
to the assignment !+m = 10+! on Line~\ref{fig_back7_m}. The second
iteration propagates this value to \inB{lst_back15_test} and in turn
to \outB{lst_back15_test}, because the test on
Line~$\ref{fig_back7_test}$ does not affect $m$. In the third iteration,
we see the same with \inB{lst_back15_mult} and \outB{lst_back15_mult}
on Line~$\ref{fig_back7_loop}$. The analysis continues for two more
iterations as other values propagate, but at this point we have all
the information we need to optimize the program. Once the analysis
reaches a fixed point, we can safely replace all occurrences of $m$
with $10$, resulting in the optimized program given in
Figure~\ref{fig_back7}, Part~\subref{fig_back7_opt}.

\begin{myfig}
  \setlength{\tabcolsep}{2pt}
  \hbox to \textwidth{\hss
  \begin{tabular}{cc}
    \input{fig_back12_tbl} & \def\prefix{fig_back12}\input{df_eg_cfg} \\
    \scap{fig_back12_tbl} & \scap{df_eg_cfg}
  \end{tabular}\hss}
  \caption{This figure shows the facts calculated for all nodes in our
    example program. Part~\subref{fig_back12_tbl} shows the \inE and
    \out facts associated with each node. Part~\subref{df_eg_cfg}
    reproduces the control-flow graph for our program. After 5
    iterations the facts reach a fixed point (i.e., they stop
    changing) and we can see that \inB{lst_back15_mult} shows that $m$
    is always $10$, proving we can rewrite the multiplication safely. }
  \label{fig_back12}
\end{myfig}

We have now seen how we can use constant propagation to optimize a
simple program. Typically many more optimizations will be run over the
same code, each (hopefully) improving it a little more. For example,
we could use an optimization called \emph{dead-code elimination} to
remove the declaration of $m$ altogether from our optimized program,
as it is no longer used. 

\section{Summary}
\label{sec_back9}

This chapter gave an overview of \emph{dataflow optimization}. The
dataflow \emph{algorithm} gives a general technique for applying an
\emph{optimizing function} to the \emph{control flow graph} (\cfg)
representing a given program. The optimizing function computes
\emph{facts} about each node in the graph, using a \emph{transfer}
function. A given analysis can proceed \emph{forwards} (where \inBa
facts produce \outBa facts) or \emph{backwards} (where \outBa facts
produce \inBa facts). Each optimization defines a specific \emph{meet
  operator} that combines facts for nodes with multiple predecessors
(for forwards analysis) or successors (for backwards). We compute
facts \emph{iteratively}, stopping when they reach a \emph{fixed
  point}. Finally, we \emph{rewrite} the \cfg using the facts computed. The 
meaning of our program does not change, but its behavior will be ``better,'' 
whatever that means for the particular optimization applied.

\standaloneBib
\end{document}

% LocalWords:  Dataflow dataflow CFG printf variable's CFGs ccc Uncurrying lst
% LocalWords:  liveness Kildall AhoXX assigna assignb runtime valueOf ccccc lub
% LocalWords:  incr lcccc
