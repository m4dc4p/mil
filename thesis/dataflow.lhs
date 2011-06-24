\documentclass[12pt]{report}
%include polycode.fmt
\input{preamble}
\begin{document}


\input{document.preamble}
\renewcommand{\textfraction}{0.1}
\renewcommand{\topfraction}{0.9}

\chapter{Dataflow Optimization}
\label{ref_chapter_background}

%% A short section giving the history of dataflow optimization techniques
%% and basic concepts.

The \emph{dataflow algorithm}, as described by Gary Kildall
\citep{Kildall1973}, provides a framework analyzing and optimizing
programs.  The algorithm \emph{iteratively} traverses the
\emph{control-flow graph} for a program either \emph{forwards} or
\emph{backwards}, computing \emph{facts} at each node using a
\emph{transfer function}, until the facts reach a \emph{fixed
  point}. The choice of facts, transfer function, and direction depend
on the particular analysis performed. In essence, the dataflow
\emph{algorithm} is parameterized by these choices; a dataflow
\emph{analysis} is a specific instance of the algorithm.

%% This chapter describes the concepts necessary to understand the
%% dataflow algorithm and gives an extended example demonstrating the use
%% of \emph{liveness analysis} to eliminate
%% \emph{dead-code}. Section~\ref{sec_back1} describes control-flow
%% graphs. We discuss facts, direction, the transfer function and the
%% meet operator in Section \ref{sec_back4}. We illustrate why dataflow
%% must be an iterative algorithm (and define what a fixed point means in
%% this context) in Section~\ref{sec_back6}. We treat rewriting in
%% Section~\ref{sec_back7}. To demonstrate these concepts together, we
%% give an extended example of \emph{dead-code elimination} in
%% Section~\ref{sec_back2}.

\section{Control-Flow Graphs}
\label{sec_back1}

%% Begin by placing the specific concept in the overall context of
%% dataflow. Give a small example highlighting the concept. Point
%% out fine points or subtleties that occur when generalizing the concept. End
%% by summarizing how the concept fits into dataflow (in a bit larger
%% sense than the first summary).

Figure~\ref{fig_back1} shows a simple C program and its
\emph{control-flow graph} (CFG). Each \emph{node} in
\subref{fig_back1_b} represents a statement or expression in the
original program. For example, \refNode{lst_back2_assigna} and
\refNode{lst_back2_assignb} represent the assignment statements on
line \ref{lst_back1_assign}. Notice that the declaration of #c# does
not appear in a corresponding node; because the declaration does not
cause a runtime effect, we do not represent it in the graph.  Nodes
\entryN and \exitN designate where program execution \emph{enters} and
\emph{leaves} the graph. If the graph represented the entire program,
we would say execution \emph{begins} at \entryN and \emph{terminates}
at \exitN. However, the CFG may be embedded in a larger program, for
which reason we say \emph{enters} and \emph{leaves}.

\begin{myfig}[th]
\begin{tabular}{cc}
\subfloat{\input{lst_back1}%%
  \label{fig_back1_a}} \vline & 
\subfloat{\input{lst_back2}%%
  \label{fig_back1_b}} \\
\subref{fig_back1_a} & \subref{fig_back1_b} 
\end{tabular}
\caption{\subref{fig_back1_a} A C-language program fragment. \subref{fig_back1_b} The
  \emph{control-flow graph} (CFG) for the program.}
\label{fig_back1}
\end{myfig}

Directed edges show the order in which nodes execute. The edges
leaving \refNode{lst_back2_test} (representing the test
``\verb=if(a > b)='' on line \ref{lst_back1_test}) show that
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
Consider the C-language fragment and control-flow graphs (CFG) in
Figure~\ref{fig_back4}.  Part~\subref{fig_back4_b} shows the CFG for
Part~\subref{fig_back4_a}: a long, straight sequence of nodes, one
after another. Part~\subref{fig_back4_c} represents the assignment statements on
lines~\ref{lst_back3_start} -- \ref{lst_back3_end} as a \emph{basic
  block}: a sequence of statements with one entry, one exit, and no
branches in-between. Execution cannot start in the ``middle'' of the
block, nor can it branch anywhere but at the end of the block. In fact,
Part~\ref{fig_back4_b} also shows four basic blocks -- they just happen
to consist of one statement each.

\begin{myfig}
\begin{tabular}{m{1.5in}m{1.5in}m{1.5in}}
  \begin{center}
    \subfloat{\input{lst_back3}\label{fig_back4_a}}
  \end{center} & %%
  \begin{center}
    \subfloat{\input{lst_back4}\label{fig_back4_b}}
  \end{center}
  & %%
  \begin{center}
    \subfloat{\input{lst_back5}\label{fig_back4_c}}
  \end{center} \\
  \vtop{\centering\subref{fig_back4_a}} & \vtop{\centering\subref{fig_back4_b}} & \vtop{\centering\subref{fig_back4_c}} \\
\end{tabular}
\caption{\subref{fig_back4_a}: A C-language fragment to illustrate
  \emph{basic blocks}.  \subref{fig_back4_b}: The CFG for
  \subref{fig_back4_a} without basic blocks. \subref{fig_back4_c}: The
  CFG for \subref{fig_back4_c} using basic blocks.}
\label{fig_back4}
\end{myfig}

The representation given in Part~\subref{fig_back4_c} has a number of
advantages. It tends to reduce both the number of nodes and the number
of edges in the graph. The dataflow algorithm maintains two sets of
\emph{facts} for every node -- reducing the number of nodes obviously
reduces the number of facts stored. The algorithm also iteratively
propagates facts along edges -- so reducing the number of edges
reduces the amount of work we need to do. When rewriting, blocks allow
us to move larger amounts of the program at once. It also can be shown
(see \citep{Aho2006}) that we do not lose any information by collapsing
statements into blocks. For efficiency and brevity, we will work with
basic blocks rather than statements from here forward.

\section{The Dataflow Algorithm}

Kildall's dataflow algorithm provides a general-purpose mechanism for
analyzing control-flow graphs of programs. The algorithm itself does
not mandate a specific analysis. Rather, it is parameterized by the
choice of \emph{facts}, \emph{meet operator}, \emph{transfer
  function}, and \emph{direction}. The facts and meet operator form a
lattice. Together, they approximate some property of the program that
we wish to analyze. The transfer function transforms facts to mimic
the flow of information in the control-flow graph. The direction is
dictated by the type of analysis -- each particular analysis runs
\emph{forwards} or \emph{backwards}.

%% Constant-propagation
Consider Figure~\ref{fig_back7}, Part~\subref{fig_back7_initial}, which
shows a C function containing a loop that multiplies the argument by 10
some number of times. Line~\ref{fig_back7_m} declares #m# and assigns
it the value 10. The function uses #m# in the loop body on
Line~\ref{fig_back7_loop} to multiply the value passed in
repeatedly. 

\begin{myfig}[tbh]
  \begin{tabular}{cc}
    \subfloat{\input{lst_back11}\label{fig_back7_initial}} & %%
    \subfloat{\input{lst_back12}\label{fig_back7_opt}} \\

    \subref{fig_back7_initial} & \subref{fig_back7_opt} 
  \end{tabular}
  \caption{A C program which multiplies its argument, \texttt{val}, by
    10 \texttt{cnt} times. Part~\subref{fig_back7_initial} shows the
    original program. In Part~\subref{fig_back7_opt}, we have used
    \emph{constant propagation} to replace the use of \texttt{m} in
    the loop body with 10.}
  \label{fig_back7}
\end{myfig}

This function is just used for illustration -- we do not expect anyone
would actually write code this way (after all, #mult10# is just
\texttt{10 * val * cnt}). In any case, the program in
Figure~\ref{fig_back7_initial} can be transformed by replacing the
variable #m# with 10 in the loop body. This may allow the compiler to
generate code that directly multiplies #val# times 10 and saves using
a register to hold the value of #m#. We can use a dataflow analysis
known as \emph{constant propagation} to justify this
transformation. The constant propagation analysis recognizes when a
variable's value does not change in some context and then replaces
references to the variable with the constant
value. Figure~\ref{fig_back7}, Part~\subref{fig_back7_opt} shows the
optimized program, replacing #m# with 10 on
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
analysis. A \emph{known integer constant}, $C \in \mathbb{Z}$, means our analysis identified
that the variable was assigned a specific value that does not
change. \emph{Indeterminate}, indicated by $\top$ (``top''), means our
analysis found that the variable might have more than one value at a
given point. Together, $\{\bot, \top\} \cup C$ forms a set which we
will denote as \setLC.

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
partly annotated with sets of \emph{facts} before (\inE) and after
(\out) the nodes that reference the variable $i$. This analysis
defines facts as pairs, $(a,x)$, where $a$ is the name of a variable
and $x \in \setLC$. The \inE and \out annotations are sets of
facts, representing our knowledge of each variable's value at that
point in the program.

Constant propagation is a \emph{forwards} analysis, meaning the values
for each \inE set are calculated based on the \out values of its
predecessors. Figure~\ref{fig_back11} shows the facts computed partway
through this analysis, concentrating on the nodes that reference $i$:
\refNode{lst_back17_assign}, \refNode{lst_back17_test} and
\refNode{lst_back17_incr}. \refNode{lst_back17_test} has two
predecessors: \refNode{lst_back17_assign} and
\refNode{lst_back17_incr}. Their \out sets,
\outB{lst_back17_assign} and \outB{lst_back17_incr}, give differing
values to $i$: 0 and $\top$. To combine these values when computing
\inB{lst_back17_test}, we use a \emph{meet operator}.

The \emph{meet operator}, \lub (also pronounced ``least upper bound'' or
``lub''), defines how we will combine values in
\setLC. Table~\ref{tbl_back4} gives the definition of \lub. For any
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
  \caption{Definition of the \emph{meet operator}, lub, for the
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
assume it is 1, the best possible value. Our definition of \lub
follows that intuition and tells us that \inB{fig_back15_b3} should be
\factC{x}{1 \lub \bot}, or \factC{x}{1}.

\begin{myfig}
  \input{lst_back19}
  \caption{A control-flow graph illustrating the behavior of \protect\lub with
    $\bot$ (i.e., undefined) values.}
  \label{fig_back15}
\end{myfig}

We would not make this assumption if we wished to warn the programmer
that a potentially unitialized variable could be used. In that case,
we would define \lub such that $x \lub \bot$ was $\bot$. Then, when
the fact \factC{x}{\bot} appeared, we could warn that a variable might
be used before being initialized. Similarly, if our language defined
an initial value for all variables, our assumption would have no
effect. We could use the same definition, but no variable would have
the value $\bot$ -- each would have a known initial value. 

We have defined \lub on elements in \setLC, but our facts are pairs
$(a,x)$ where $a$ is a variable and $x$ a value in \setLC; \inE and
\out are sets of facts.  Therefore, we define the $\wedge$ (``wedge'')
operator to apply \lub to sets of facts ($F_1$ and $F_2$ below):
\begin{align*}\allowdisplaybreaks[0]
  F_1 \wedge F_2 &= \setdef{(a, x_1 \lub x_2)}{(a,x_1) \in F_1, (a,x_2) \in F_2} \\
  &\; \cup \setdef{(a,x_1)}{(a,x_1) \in F_1, a \not\in \mfun{dom}(F_2)} \\
  &\; \cup \setdef{(a,x_2)}{(a,x_2) \in F_2, a \not\in \mfun{dom}(F_1)} \label{eqn_back18}\addtag\\
  \mfun{dom}(F) &= \setdef{a}{(a,x) \in F} \addtag
\end{align*}
Our $\wedge$ operator acts like union when a variable in $F_1$ does
not appear in the domain of $F_2$; likewise for a variable only in
$F_2$. When a variable appears in both $F_1$ and $F_2$, the values for
the variable are combined using \lub.

To compute \inBa, we apply $\wedge$ to each \out set of $B$'s
predecessors. We use a subscripted $\bigwedge$ to indicate we combine
all of the \out sets into one using $\wedge$:
\begin{equation}
  \inBa = \bigwedge\limits_{\mathclap{P \in \mathit{pred}(B)}} \outXa{P} \label{eqn_back8}.
\end{equation}

Using these equations, we can show how the \inB{lst_back17_test}
set in Figure~\ref{fig_back11} is derived:
\begin{align*}\allowdisplaybreaks[0]
  \inB{lst_back17_test} &= \bigwedge\limits_{\mathclap{P \in \mathit{pred}(\refNode{lst_back17_test})}} \outXa{P} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Predecessors of \refNode{lst_back17_test}; Equation~\eqref{eqn_back8}.}}}
  &= \outB{lst_back17_assign} \wedge \outB{lst_back17_incr} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Definition of \outB{lst_back17_assign} and \outB{lst_back17_incr}.}}}
  &= \{\factC{i}{0}\} \wedge \{\factC{i}{\top}\} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Equation~\eqref{eqn_back18}.}}}
  &= \{\factC{i}{0 \lub \top}\} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Definition of \lub from Table~\ref{tbl_back4}.}}}
  &= \{\factC{i}{\top}\} \\
  \shortintertext{\hbox to 1\textwidth{\hfil\textit{Definition of \inB{lst_back17_test}.}}}
  \{\factC{i}{\top}\} &= \{\factC{i}{\top}\}.
\end{align*}

Together, \setLC and \lub form a \emph{lattice}.\footnote{The lattice
  can also have a \emph{join} operator, but for our purposes we solely
  use the meet.}  The lattice precisely defines the facts computed in
our analysis. In this case, the lattice represents
knowledge about a variable's value. Each specific dataflow analysis
computes different facts, but those facts are always represented by a
lattice.

We have established that our analysis computes \emph{facts} at each
node in our programs control-flow graph. The facts assign the value
$\bot$, $C \in \mathbb{Z}$, or $\top$ to each variable in the program,
at each node in the graph. We defined a \emph{meet operator}, \lub,
which is used to combing conflicting values when computing \inBa.  The
facts and meet operator together define a \emph{lattice}. We next
explore how \out facts are computed for each node.

%% Figure~\ref{fig_back11} demonstrates how the lattice computes facts
%% for constant propagation. The set \out{lst_back17_assign} indicates,
%% among other things, that $i$ is assigned 0: \factC{i}{0}. However,
%% \out{lst_back17_incr} indicates that the value of $i$ is indeterminate: 
%% \factC{i}{\top}. 

%% First, the values
%% computed for variables at each program point are in \setLC. Second,
%% the meet operator, \lub, is used to combine facts  The
%% lattice defines our facts. That is, the values in \setLC The lattice
%% defines how our facts will indicate if a variable has a constant
%% value.

%% Figure~\ref{fig_back10} shows our program with the final facts
%% computed. The sets \inB{lst_back13_mult} and \outB{lst_back13_mult}
%% show that #m# has the value 10 when block \refNode{lst_back13_mult}
%% executes. The variables #n# and #i# have the value $\top$, indicating
%% they could one of many different values. However, #cnt# and #val#
%% still have $\bot$, because their values are not modified anywhere in
%% the control-flow graph.

%% \begin{myfig}
%%   \input{lst_back14}
%%   \label{fig_back10}
%%   \caption{Our program, annotated with the final facts computed by the
%%     constant propagation analysis. Notice the \inB{lst_back14_mult}
%%     and \outB{lst_back14_mult} indicate that \texttt{m} has the value 10
%%     while \refNode{lst_back14_mult} executes.}
%% \end{myfig}

%% values. 
%% values $\bot$, an integer value, and $\top$ can be ordered such
%% that $\bot \le x \le \top$, for all integers $x$. The \emph{meet
%% operator} defines this ordering

%% Before
%% and after each block we will determine 

%% To track
%% the value of each variable, we use a \emph{lattice}. This particular
%% lattice encodes three types of values: 
%% Even so,
%% for this analysis all we care to know is if the value remains
%% the same or changes. 

%% approximate by determining, at each point in the control-flow graph,
%% whether a variable has one of three values: an \emph{unknown}, a
%% \emph{constant}, or

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

We choose to use pairs $(a,x)$, where $a$ is variable in the program
and $x$ a value in \setLC, as the facts for our analysis. We define
our transfer function in terms of a single fact:
\begin{equation}
  f (a,x) = 
  \begin{cases}
    (a,x \lub C) & \text{when \texttt{a = \emph{C}}, with \texttt{C} $\in \mathbb{Z}$.} \\
    (a,\top) & \text{when \texttt{a} updated}. \\
    (a,x) & \text{otherwise}. \\
  \end{cases}
  \label{eqn_back4}
\end{equation}

Equation~\eqref{eqn_back4} considers two kinds of statements: constant
and non-constant updates. If the statement #a = C# appears in the
node, our new fact is $(a,x \lub C)$, indicating we combine our
previous knowledge about $x$ with the new constant assigned. We create
the fact $(a,\top)$ for any other update.\footnote{In practice this
  analysis is much more sophisticated, capable of analyzing
  complicated arithmetic expressions. Algebraic properties such as
  associativity and distributivity are also usually considered.}
Finally, if neither type of statement appears in the node, we just
pass $x$ through unchanged.

Though we have defined Equation~\eqref{eqn_back4} in terms of a single
fact, we can easily extend it to sets of facts. To create \outBa for
some node $B$, we apply Equation~\eqref{eqn_back4} element-wise to
each fact in \inBa and combine the results into a set:
\begin{equation}
  \outBa = \bigcup\limits_{\mathclap{(a,x) \in \inBa}} f(a,x).
  \label{eqn_back5}
\end{equation}

Figure~\ref{fig_back9}, Part \subref{fig_back9_initial}, shows our
program, annotated with initial \inE and \out
facts. Figure~\ref{fig_back9}, Part \subref{fig_back9_transfer}, shows
the same graph with annotations updated using
Equation~\eqref{eqn_back4}. The assignments in
\refNode{lst_back18_assign} create the facts \factC{m}{10},
\factC{n}{1}, and \factC{i}{0} in \outB{lst_back18_assign}. The
multiplication in \refNode{lst_back18_mult} is a non-constant update,
so \outB{lst_back18_mult} contains \factC{n}{\top}. However,
\outB{lst_back18_mult} also shows that #m# is not modified in
\refNode{lst_back18_mult}; the value from \inB{lst_back18_mult} is
just copied to \outB{lst_back18_mult}.

\input{fig_back9}

Every dataflow analysis defines a \emph{transfer function} for
creating (or updating) facts. The function is specific to both the
analysis performed and the semantics of the underlying
program. Equation~\eqref{eqn_back4}, the transfer function for our
constant propagation example, defines how we derive information about
a variable's value after the statements in the given node execute.
Equation~\eqref{eqn_back5} extended Equation~\eqref{eqn_back4} to sets,
showing how we can create \outBa from \inBa. In the next section, we
iteratively apply our transfer function and lattice to the
control-flow graph. 

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
shows which \out sets are used to calcuate \inE sets.

\begin{myfig}[tb]
  \setlength{\tabcolsep}{2pt}
  \hbox to \textwidth{\hss
  \begin{tabular}{cc}
    \subfloat{\input{fig_back13_tbl}\label{fig_back13_tbl}} & 
    \subfloat{\input{fig_back12_cfg}\label{fig_back13_cfg}} \\
    \subref{fig_back13_tbl} & \subref{fig_back13_cfg}
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
tests the condition #i < cnt#. In the first iteration,
\inB{lst_back15_test} still assigns $\bot$ to
$i$. Equation~\eqref{eqn_back8} states that \inB{lst_back15_test} is
derived from the \out sets of \refNode{lst_back15_test}'s
predecessors: \refNode{lst_back15_assign} and
\refNode{lst_back15_incr}. By Equations~\eqref{eqn_back8},
\eqref{eqn_back6}, and \eqref{eqn_back7} we can calculate the value of
$i$ in \inB{lst_back15_test}. Crucially, the \out set used comes from
the \emph{previous} iteration of the analysis, which we emphasize by
attaching the iteration number to each set:
\begin{align*}
  \inB{lst_back15_test}^1 &= \outB{lst_back15_assign}^0 \bigwedge \outB{lst_back15_incr}^0 \\
  &= {\factC{i}{\bot}} \wedge {\factC{i}{\bot}} \\
  &= {\factC{i}{\bot \lub \bot}} \\
  {\factC{i}{\bot}} &= {\factC{i}{\bot}}.
\end{align*}
Now consider the second iteration, where \inB{lst_back15_test} assigns
$\top$ to $i$. \outB{lst_back15_assign} gives $i$ the value
0 (by #i = 0#). However, \outB{lst_back15_incr} assigns $i$ the value $\top$,
because #i++# is a non-constant update. We can see why by
Equations~\eqref{eqn_back8}, \eqref{eqn_back6}, and
\eqref{eqn_back7}. Again we attach the iteration number to each set,
emphasizing its origin:
\begin{align*}
  \inB{lst_back15_test}^2 &= \outB{lst_back15_assign}^1 \bigwedge \outB{lst_back15_incr}^1 \\
  &= {\factC{i}{0}} \wedge {\factC{i}{\top}} \\
  &= {\factC{i}{0 \lub \top}} \\
  {\factC{i}{\top}} &= {\factC{i}{\top}}.
\end{align*}
Notice how the conflicting values for $i$ are resolved with the \lub
operator. The value of $i$ in \outB{lst_back15_test} has reached a fixed point
with this iteration; it will no longer change.

The above example raises an important question: how do we know we have
reached a fixed point? How do we know we have gotten the best possible
answer?  Both of these questsion can be answered if our lattice has
\emph{finite height} and the transfer function is \emph{monotone}.

Let us begin with the lattice. Consider again the meet operator, \lub,
defined in Table~\ref{tbl_back4} and our set of values, \setLC:
\begin{align*}
  \setLC &= \bot, \dots \mathit{all\ integers} \dots, \top. \\\\
  \bot \lub x &= x. \\
  x \lub \top &= \top.\\
  C_1 \lub C_2 &= \top, \text{where}\ C_1 \neq C_2.\\
  C_1 \lub C_1 &= C_1.
\end{align*}
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
3. Given $x_1 \sqlt x_2 \sqlt \dots \sqlt x_n$, such that n = 4. If
$x_4$ is $\top$, then $x_3$ must be an integer or $\bot$. If $x_3$ is
$\bot$, by Equation~\eqref{eqn_back17}, there is no such $x_2$ such
that $x_2 \sqlt \bot$. Therefore, $x_3$ cannot be $\bot$. If $x_3$ is
an integer, again by Equation~\eqref{eqn_back17}, $x_2$ must be
$\bot$. In turn, there is no such $x_1$ such that $x_1 \sqlt
\bot$. Therefore, $x_4$ cannot be $\top$ and in fact, by similar
arguments, it cannot exist. Using similar logic, we can show by cases
that $n$ (and the height of our lattice) must be 3.

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
transfer function will never ``decrease'' its argument -- $f$ will
always produce a value that is at the same ``height'' or ``higher'' in
the lattice. The lattice represents the information we have gathered
during our analysis. In turn, the ordering of values represents ``how
much'' we know. That is, when a variable is assigned $\bot$, we do not
know anything about it. If it is assigned $\top$, we have seen ``too
many'' assignments (or some other update).  This means our transfer
function always increases (or does not change) the information we
have. 

To show that our transfer function (from Equation~\eqref{eqn_back4}) is
monotone, consider some fact $(v,x)$ and some block $B$. $v$ is a
variable in the program; $x$ is a value in \setLC; and $B$ contains
some number of statements.  We analyze the fact, $(v,x')$ produced
applying our transfer function $f$ to $B$. If $B$ does not contain an
assignment affecting $v$, then $x = x'$, and we already know that $x \sqlte
x'$. If $B$ makes a non-constant update to $v$, then $x' = \top$ and we
know $x \sqlte \top$ for all $x$ by the definition of \lub. Finally,
if $B$ assigns some constant $C$ to $x$, then $x' = x \lub C$, which
again satisfies our relation. Therefore, Equation~\eqref{eqn_back4} is
monotone and, by a simple extension to sets, so is is
Equation~\eqref{eqn_back5}.

%% If our lattice has finite height, we can be sure that our
%% algorithm will terminate -- our transfer function will not oscillate
%% up and down the lattice!
%% By requiring the our analysis uses a \emph{lattice} with \emph{finite
%%   height} and a \emph{monotone} transfer function, we know our
%% analysis will eventually reach a fixed point and terminate. We will
%% now discuss how these same properties guarantee we have reached the
%% \emph{maximum fixpoint} and thus have the best possible answer.



%% Our goal is to find the ``largest amount'' of ``smallest'' information
%% about each variable. That is, if we assigned $\top$ to all variables,
%% we have the ``largest'' amount of information, but we do not know
%% anything useful. Assigning $\bot$ puts is in the opposite situation,
%% where we know the ``least.'' We want something in the middle, where we
%% have gathered the greatest amount of useful information. 



%% have this
%% property. 
%% In terms of \setLC and
%% Equation~\eqref{eqn_back4} (our transfer function), that means the
%% value for a variable will either stay the same or get ``bigger,'' as
%% defined by the lattice. For example, if \inBa (for some $B$) says $i$ is 10,
%% then $i$ in \outBa will be either 10 or $\top$. If $i$ could become $\bot$ (or
%% some other constant), Equation~\eqref{eqn_back4} would not be monotone. 


%% Trivially holds for our transfer function because it is defined in terms of \lub.

%% Together, guarantees we terminate. How do we get the ``best'' answer?


%% Monotonic
%% Finite height lattice
%% Partial orders
%% Maximum fixed point

%% \begin{myfig}
%%   \begin{tabular}[c]
%%     \subfloat{\input{lst_back15}\label{fig_back8_initial}} \\
%%     \subref{fig_back8_initial} \\
%%     \subfloat{\input{lst_back13}\label{fig_back8_final}} \\
%%     \subref{fig_back8_final} 
%%   \end{tabular}
%%   \caption{The control flow graph for our program. Part~\subref{fig_back8_initial}
%%     shows the initial facts associated with each node. Part~\subref{fig_back8_final}
%%     shows the final facts computed by our constant propagation analysis.}
%%   \label{fig_back8}
%% \end{myfig}


\section{Dataflow Equations}
\label{back_subsec_eq}

As we stated in the beginning of this chapter, the dataflow algorithm
is \emph{parameterized} by four items: facts, meet operator,
direction, and transfer function. The prior section presented each
parameter for the constant propagation analysis
separately. Figure~\ref{fig_back10} presents all of them together, as
a set of \emph{dataflow equations}. Pairs of elements from the sets
\setLC and \setL{Var} define our facts. Equations~\eqref{eqn_back12}
and \eqref{eqn_back13} define our meet operator; together with the set
\setLC, they define our lattice. Equations~\eqref{eqn_back3} and
\eqref{eqn_back16} together defieshow we are defining a \emph{forwards}
  analysis. Equations~\eqref{eqn_back15} and \eqref{eqn_back16} define
our transfer function.

\input{fig_back10}

We can now define any dataflow analysis in terms of these four
parameters:
\begin{align*}
  \setL{Facts} & \qquad & \text{\it Our set of facts}. \\
  \wedge & \qquad & \text{\it Our \emph{meet} operator.} \\
  D & \qquad & \text{\it Direction, \emph{forwards} or \emph{backwards}}. \\
  \mathit{transfer}(v) & \qquad & \text{\it Our transfer function, with $v \in \setL{Facts}$.}
\end{align*}

In turn, we can define the iterative dataflow algorithm for the
\emph{forwards} direction. Figure~\ref{fig_back14} gives the
algorithm.\footnote{The \emph{backwards} algorithm is almost
  identical.} The algorithm initializes all \out sets to $\bot$, or
some suitable initial value from \setL{Facts}. The entry node gets
special treatment in some cases, so we set \outXa{Entry} to its own
initial value (though in many cases \outXa{Entry} is set to the same
value as other \out sets). We now enter the main loop of the
algorithm. The body of the loop always executes at least once. We
first calculate all \inE sets from their predecessors' \out sets on
Line~\ref{fig_back14_in}. On the next line, the new \inE sets are used
to calculate \out sets for each node.  Line~\ref{fig_back14_loop}
gives our termination condition: when \out sets stop changing, we are
done. The superscript on each \out set represents the
iteration. $\outBa^{i}$ means the $i$-th iteration, and $\outBa^{i-1}$
the previous ($i - 1$) iteration. The loop repeats if any \out set has
changed since the last iteration. Otherwise, the algorithm terminates.

\begin{myfig}
  \begin{minipage}{3in}
    \begin{AVerb}[numbers=left,gobble=6]
      Out(\emph{Entry}) = \emph{initial}, \emph{initial} $\in \setL{Facts}$.
      $\text{In(B)}^0$ = $\bot$, for all blocks $B$.
      \textbf{do} \{
        In(B) = $\bigwedge_{P \in pred(B)} \text{Out}(P)$. \label{fig_back14_in}
        Out(B) = \emph{transfer}(In(B)).  \label{fig_back14_out}
      \} \textbf{until}($\text{Out(B)}^{i} == \text{Out(B)}^{i - 1}$, for all $B$)\label{fig_back14_loop}
    \end{AVerb}
  \end{minipage}
  \caption{The dataflow algorithm, using parameters for facts, the meet operator,
    direction, and the transfer function.}
  \label{fig_back14}
\end{myfig}

We have presented the iterative, forwards dataflow algorithm and shown
how the algorithm can be parameterized for a particular analysis. We
gave the parameterization for our constant propagation analysis in
Figure~\ref{fig_back10}. We know the algorithm will terminate if
our transfer function is \emph{monotone} and we have defined lattice
with \emph{finite} height. However, we have not discussed how to measure
the results our analysis gives us -- how do we know that they are the 
best possible? We will address that question in the next section.

\section{Quality of Solutions to the Dataflow Equations}

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
execute Line~\ref{lst_back19_test_true}, because the test #if(a > b)#
is always false:
\begin{center}
\begin{minipage}{2in}\singlespacing\vskip-\baselineskip
\begin{AVerb}[numbers=left]
int a = 1, b = 2, c; \label{lst_back19_assign}
if(a > b) \label{lst_back19_test}
  c = 4; \label{lst_back19_test_true}
else     
  c = 3; \label{lst_back19_test_false}
\dots
\end{AVerb}
\end{minipage}
\end{center}

Our algorithm, however, does not take such conditions into
account. The ideal solution is called the \emph{meet over paths}
solution because it takes into account only the paths that will taken
by the program. Determining the actual paths taken is an undecidable
problem -- thus we settle for the maximum fixed point. Fortunately,
the algorithm is conservative --- it never ignores (or adds) paths ---
so we can be sure that its analysis will never be wrong, just that it
probably will not be as good as the ideal.

\section{Applying Results}

Figure~\ref{fig_back7}, Part~\subref{fig_back7_initial} gave a sample
program which we wished to optimize using a \emph{constant propagation}
dataflow analysis. Figure~\ref{fig_back7}, Part~\subref{fig_back7_opt} gave
the result, replacing all occurrences of #m# with 10. Now knowing
the dataflow algorithm and the equations for constant propagation, we
can derive how that transformation is made.

Table~\ref{fig_back12} gives the facts calculated for all nodes in our
program, during each iteration of the analysis. The first iteration
calculates that \outB{lst_back15_assign} assigns #m# the value 10, due
to the assignment #m = 10# on Line~\ref{fig_back7_m}. The second
iteration propagates this value to \inB{lst_back15_test} and in turn
to \outB{lst_back15_test}, because the test on
Line~\ref{fig_back7_test} does not affect #m#. In the third iteration,
we see the same with \inB{lst_back15_mult} and \outB{lst_back15_mult}
on Line~\ref{fig_back7_loop}. The analysis continues for two more
iterations as other values propagate, but at this point we have all
the information we need to optimize the program. Once the analysis
reaches a fixed point, we can safely replace all occurrences of #m#
with #10#, resulting in the optimized program given in
Figure~\ref{fig_back7}, Part~\subref{fig_back7_opt}.

\begin{myfig}
  \setlength{\tabcolsep}{2pt}
  \hbox to \textwidth{\hss
  \begin{tabular}{cc}
    \subfloat{\input{fig_back12_tbl}\label{fig_back12_tbl}} & 
    \subfloat{\input{fig_back12_cfg}\label{fig_back12_cfg}} \\
    \subref{fig_back12_tbl} & \subref{fig_back12_cfg}
  \end{tabular}\hss}
  \caption{This figure shows the facts calculated for all nodes in our
    example program. Part~\subref{fig_back12_tbl} shows the \inE and
    \out facts associated with each node. Part~\subref{fig_back12_cfg}
    reproduces the control-flow graph for our program. After 5
    iterations the facts reach a fixed point (i.e., they stop
    changing) and we can see that \inB{lst_back15_mult} shows that $m$
    is always 10, proving we can rewrite the multiplication safely. }
  \label{fig_back12}
\end{myfig}

We have now seen how we can use constant propagation to optimize a
simple program. Typically many more optimizations will be run over the
same code, each (hopefully) improving it a little more. For example,
we could use an optimziation called \emph{dead-code elimination} to
remove the declaration of #m# altogether from our optimized program,
as it is no longer used. 

\section{Summary}
\label{sec_back9}

This chapter gave an overview of \emph{dataflow optimization}. The
dataflow \emph{algorithm} gives a general technique for applying an
\emph{optimizing function} to the \emph{control flow graph} (CFG)
representing a given program. The optimizing function computes
\emph{facts} about each node in the graph, using a \emph{transfer}
function. A given analysis can proceed \emph{forwards} (where \inBa
facts produce \outBa facts) or \emph{backwards} (where \outBa facts
produce \inBa facts). Each optimization defines a specific \emph{meet
  operator} that combines facts for nodes with multiple predecessors
(for forwards analysis) or successors (for backwards). We compute
facts\emph{iteratively}, stopping when they reach a \emph{fixed
  point}. Finally, we \emph{rewrite} the CFG using the facts computed. The 
meaning of our program does not change, but its behavior will be ``better,'' 
whatever that means for the particular optimization applied.



%% \runin{Transfer Function} Our transfer function creates 

%% \section{Facts, Transfer Functions, Direction \& The Meet Operator}
%% \label{sec_back4}

%% Begin by placing the specific concept in the overall context of
%% dataflow. Give a small example highlighting the concept. Point
%% out fine points or subtleties that occur when generalizing the concept. End
%% by summarizing how the concept fits into dataflow (in a bit larger
%% sense than the first summary).
%% \begin{myfig}[th]
%% \centering
%% \input{lst_back7}
%% \caption{The CFG for the C-language fragment from
%%   Figure~\ref{fig_back1_a}, annotated with \emph{facts} about the
%%   value of \texttt{a}, \texttt{b}, and \texttt{c} before (``\inBa'') and
%%   after (``\outBa'') each node.}
%% \label{fig_back5}
%% \end{myfig}

%% The dataflow algorithm computes two sets of \emph{facts} for every
%% node in the CFG. Facts are a data structure that describe the state of
%% the program before and after execution of the block represented by the
%% node. Figure~\ref{fig_back5} annotates the program fragment in
%% Figure~\ref{fig_back1} with facts about #a#, #b#, and #c# (the only
%% state we care about in this program). Each \inBa gives the variables'
%% values just prior to executing block $B$, while each \outBa gives
%% their values just after $B$ has executed.  

%% Figure~\ref{fig_back5} shows a \emph{forwards} analysis, where \outBa
%% is computed from \inBa, for each block. Facts are created by a
%% \emph{transfer function} that inspects the statements in each node and
%% updates values assigned to variables, if any. Sometimes a dataflow
%% analysis will run \emph{backwards}, computing \inBa from
%% \outBa. Section \ref{sec_back2} gives a detailed example illustrating
%% a \emph{backwards} analysis. In general, the transfer function and
%% direction vary depending on the particular analysis performed.

%% To help define our transfer function, we define |valueOf|,
%% which either returns the value assigned to a variable, or its value
%% from \inBa:
%% \begin{equation} |valueOf|(v) = 
%%   \begin{cases}
%%     |assign|(v) & \text{when $v$ is assigned a value in the node,} \\
%%     \text{\inBa}(v) & \text{when $v$ is not assigned.} 
%%   \end{cases}
%% \label{eqn_back2}
%% \end{equation}
%% In the above, $v$ represents a variable; |assign| retrieves the value
%% assigned to that variable, if any.  Our transfer function just needs
%% to apply |valueOf| to all variables in \inBa, as well as all
%% variable assignments in the node itself. If |assigned| is the set of
%% all assigned variables in the node, we can define how our transfer
%% function relates \inBa and \outBa using set notation:
%% \begin{equation}
%%   \text{\outBa} = [|valueOf|(v) || v \in (\text{\inBa} \cup |assigned|)].
%% \end{equation}

%% Our initial fact, \inB{lst_back7_assign}:~\facts{a/\top, b/\top,
%%   c/\top}, assigns the value ``$\top$'' (``top'') to all variables,
%% indicating that we do not know the value for the given variable. Our
%% transfer function determines that \outB{lst_back7_assign} should be
%% \facts{a/1, b/2, c/\top}, showing that we know #a# is 1, #b# is 2, and
%% that we still do not know the value of #c#. At each block we perform a
%% similar analysis, except \refNode{lst_back7_print}, where we need to
%%   take special action.

%% When a node has multiple predecessors, like \refNode{lst_back7_print},
%% we must combine multiple \outBa values into a single \inBa. The value
%% for #c# in \outB{lst_back7_true} is 4, while in \outB{lst_back7_false}
%% #c# is 3. We have two distinct values for #c# and no way to determine
%% which will be the case when \refNode{lst_back7_print} executes. We
%% must be conservative, so we assign the value $\top$ to #c# in
%% \inB{lst_back7_print}.

%% \begin{table}[tbh]
%%   \centering
%%   \figbegin
%%   \begin{math}
%%     \begin{array}{ccccc}
%%       & v_1 & v_2 & v_1 \lub v_2 \\
%%       \cmidrule(r){2-2}\cmidrule(r){3-3}\cmidrule(r){4-4}
%%       1. & \top & v_2 & \top & \\ 
%%       2. & v_1 & \top & \top & \\
%%       3. & v_1 & v_2 & \top & \text{($v_1 \neq v_2$)}\\
%%       4. & v_1 & v_1 & v_1 
%%     \end{array}
%%   \end{math}
%%   \caption{How the meet operator used in Figure \ref{fig_back5}
%%     combines facts. $v_1$ and $v_2$ are values given by separate
%%     \outBa facts to the same variable. The table shows how they are
%%     combined.}
%%   \label{tbl_back2}
%%   \figend
%% \end{table}

%% A \emph{meet operator} defines how we combine facts when values
%% conflict. Table~\ref{tbl_back2} defines ``\lub'' (``least upper
%% bound'' or ``lub''), which combines values as we did for
%% \outB{lst_back7_true} and \outB{lst_back7_false}. $v_1$~and $v_2$
%% represent values given to the same variable by different
%% facts. Lines~1 and 2 show that when either value is $\top$, the result
%% is $\top$. When values differ, as in Line~3, again the result is
%% $\top$. Only when values are equal, as shown in the last line, do we
%% preserve the value.

%% Facts define the state of the program that we are analyzing. The
%% transfer function transforms input facts into output facts. In a
%% forwards analysis, input facts come from predecessor nodes and output
%% facts flow to successors. For a backwards analysis, the opposite
%% occurs. When multiple facts need to be combined, we use a meet
%% operator. Each of these elements will vary depending on the specific
%% analysis performed.

%% \section{Iterative Analysis}
%% \label{sec_back6}
%% Begin by placing the specific concept in the overall context of
%% dataflow. Give a small example highlighting the concept. Point
%% out fine points or subtleties that occur when generalizing the concept. End
%% by summarizing how the concept fits into dataflow (in a bit larger
%% sense than the first summary).

%% \begin{equation}
%%   \begin{split}
%%     B \bigwedge\ \emptyset\ &= B \\
%%     B \bigwedge\ C &= [\{a=v_b\} \wedge\ \{a=v_c\} || \{a=v_b\}\ \in\ B, \{a=v_c\}\ \in\ C] \\%%
%%                    &\; \cup\ [\{b=v_b\} || \{b=v_b\}\ \in\ B, \{b=v_c\}\ \not\in\ C] \\%%
%%                    &\; \cup\ [\{c=v_c\} || \{c=v_b\}\ \not\in\ B, \{c=v_c\}\ \in\ C] \\
%%     \{a=\bot\} \wedge\ \{a=v\} &= \{a=v\} \\
%%     \{a=\top\} \wedge\ \{a=v\} &= \{a=\top\} \\
%%     \{a=v\} \wedge\ \{a=u\} &= \{a=\top\} (u \neq v) \\
%%     \{a=v\} \wedge\ \{a=v\} &= \{a=v\} \\
%%   \end{split}
%% \end{equation}

%% \begin{equation}
%%   \begin{split}
%%     f_B(In) &= [\mathit{assign}(v) || v \in\ In], \text{where $B$ is a block in the CFG} \\
%%     assign(v) &= %%
%%     \begin{cases}
%%       c & \text{when $v$ assigned $c$ in B.} \\
%%       In(v) & \text{when v not assigned in B.}
%%     \end{split}
%%   \end{align}
%% \end{equation}

%% \begin{tabular}{ll}
%%   \textbf{Lattice} & $\bot$, 0, 1, \ldots, and $\top$. \\
%%   \textbf{Meet} &  As above. \\
%%   \textbf{Transfer} & As above. \\
%%   \textbf{Direction} & Forward.
%% \end{tabular}


%% As we saw in Figure \ref{fig_back5}, facts can conflict when nodes
%% have multiple predecessors. Even more complicated situations arise
%% when a program contains loops. Consider the fragment in
%% \ref{fig_back6}. To compute \inB{lst_back9_test}, we need
%% \outB{lst_back9_assign} and and \outB{lst_back9_incr}. To compute
%% \inB{lst_back9_incr} (in order to find \outB{lst_back9_incr}, we need
%% \outB{lst_back9_test}. But to compute \outB{lst_back9_test} we need
%% \inB{lst_back9_test}.  How do we apply our |valueOf| function
%% (Equation \ref{eqn_back2}) to a \refNode{lst_back9_test} when
%% \inB{lst_back9_test} depends on \outB{lst_back9_test}?

%% \begin{myfig}
%% \begin{tabular}{cc}
%%   \subfloat{\input{lst_back8}%%
%%     \label{fig_back6_a}} \vline &%%
%%   \subfloat{\input{lst_back9}%%
%%     \label{fig_back6_b}} \\ 
%%   \subref{fig_back1_a} & \subref{fig_back1_b}
%% \end{tabular}
%% \caption{\subref{fig_back6_a}: A simple C-language program with a loop. \subref{fig_back6_b}: The CFG 
%% for the fragment.}
%% \label{fig_back6}
%% \end{myfig}

%% We solve this problem by applying our transfer function
%% \emph{iteratively}. In the case of Figure \ref{fig_back6}, we first
%% initialize each all \inBa and \outBa facts to some default. We then use
%% |valueOf| to compute each \outBa. Of course, facts will change over
%% the course of iteration -- especially in the case of node
%% \ref{lst_back9_test}. We keep iterating until we reach a \emph{fixed
%%   point}, meaning the facts stop changing.

%% \begin{table}
%%   \centering
%%   \begin{math}
%%     \begin{array}{lcccc}
%%       \mathit{Iteration} & \outB{lst_back9_assign} & \outB{lst_back9_incr} & \inB{lst_back9_test} & \outB{lst_back9_test} \\
%%       \cmidrule(r){1-1}\cmidrule(r){2-5} 
%%       0 & \bot & \bot & \bot & \bot  \\
%%       1 & 0 & 10 & \bot & \bot \\
%%       2 & 0 & 10 & \bot & \bot \\
%%       \multicolumn{5}{c}{\dots} \\
%%       \multicolumn{5}{l}{\inB{lst_back9_test} = \outB{lst_back9_assign} \lub \outB{lst_back9_incr}} \\
%%     \end{array}
%%   \end{math}
%%   \caption{Iterative analysis of the CFG from Figure
%%     \ref{fig_back6}. We how the inputs used to calculate
%%     \outB{lst_back9_test} change in one iteration. The zeroth
%%     iteration represents the initial values given to \inBa and \outBa
%%     for all nodes.}  
%%   \figend
%%   \label{tbl_back3}
%% \end{table}

%% Table \ref{tbl_back3} shows \inE and \out for
%% \refNode{lst_back9_test}. To compute \inB{lst_back9_test}, we combine
%% \outB{lst_back9_assign} and \outB{list_back9_incr} using the meet
%% operator from Section~\ref{sec_back4}:
%% \begin{equation}
%%   \inB{lst_back9_test} = \outB{lst_back9_assign} \lub \outB{lst_back9_incr}.
%% \end{equation}
%% The zeroth iteration shows the initial
%% value for all sets. On the first iteration, we can see \inB{lst_back9_test} is $\bot$:
%% \begin{equation}
%%   \begin{split}
%%     \inB{lst_back9_test} &= \outB{lst_back9_assign} \lub \outB{lst_back9_incr} \\
%%     &= \bot \lub \bot \\
%%     &= \bot.
%%   \end{split}
%% \end{equation}
%% When computing \inBa, we always use \outBa from the
%% \emph{previous} iteration. In the above we use $\bot$ for \outB{lst_back9_incr} and
%% \outB{lst_back9_assign}. 

%% When computing \inB{lst_back9_test} in the second iteration,
%% \outB{lst_back9_incr} is 10 and \outB{lst_back9_assign} is
%% 0. According to our meet operator, \inB{lst_back9_test} still equals
%% $\bot$:
%% \begin{equation}
%%   \begin{split}
%%     \inB{lst_back9_test} &= \outB{lst_back9_assign} \lub \outB{lst_back9_incr} \\
%%     &= 0 \lub 10 \\
%%     &= \bot.
%%   \end{split}
%% \end{equation}
%% At this point, our facts have stopped changing so we stop
%% iterating. Our final result $\bot$ for #c# in \outB{lst_back9_test}.

%% \section{Rewriting}
%% \label{sec_back7}

%% Begin by placing the specific concept in the overall context of
%% dataflow. Give a small example highlighting the concept. Point
%% out fine points or subtleties that occur when generalizing the concept. End
%% by summarizing how the concept fits into dataflow (in a bit larger
%% sense than the first summary).

%% Direction, the meet operator, facts, and the transfer function
%% together define a particular dataflow analysis. We can use the result
%% of the analysis to alter, or ``rewrite,'' the CFG of the program. The
%% meaning of the program should not change, but it should behave
%% differently: execute faster, use less memory, or whatever
%% characteristic the optimization should improve.  We do not have to
%% rewrite, of course. In some cases, we use the analysis to drive later
%% optimizations, or to report errors to the programmer. For example, a
%% \emph{reaching definitions} \citep{AhoXX} analysis can warn if
%% variables are used without being initialized. However, in most cases
%% we do want to rewrite the CFG.

%% \section{Example: Dead-Code Elimination}
%% \label{sec_back2}

%% Begin by placing the specific concept in the overall context of
%% dataflow. Give a small example highlighting the concept. Point
%% out fine points or subtleties that occur when generalizing the concept. End
%% by summarizing how the concept fits into dataflow (in a bit larger
%% sense than the first summary).

%% Consider Figure \ref{fig_back2}, again showing a C-language fragment.
%% The assignment to #b# on line~\ref{fig_back2_dead_line} has no visible
%% effect and can be removed without affecting the meaning of the
%% program. We call this optimization \emph{dead-code elimination}.

%% \begin{myfig}[ht]
%% \begin{minipage}{1in}
%%   \begin{AVerb}[numbers=left]
%%     a = 1;
%%     b = a + 1;\label{fig_back2_dead_line}
%%     return a + 1;
%%   \end{AVerb}
%% \end{minipage}
%% \caption{A C-language fragment illustrating \emph{dead code}. After
%% assignment on line \ref{fig_back2_dead_line}, \verb=b= is not used
%% and can be considered ``dead.''}
%% \label{fig_back2}
%% \end{myfig}

%% Of course, programmers do not normally write programs with such
%% obviously useless statements, but other compiler optimizations can
%% leave behind many such statements. \emph{Uncurrying}, described in
%% Chapter~\ref{ref_chapter_uncurrying}, in fact depends on dead-code
%% elimination.

%% The assignment on line~\ref{fig_back2_dead_line} can be eliminated
%% because #b# does not get referenced again. If a variable is referenced
%% after assignment, we say it is ``live.'' We call the dataflow
%% analysis that finds all live variables a ``liveness'' analysis. 

%% \begin{myfig}[th]
%% \begin{minipage}{2in}
%% \input{lst_back10}
%% \end{minipage}
%% \caption{The CFG for our example program, annotated with the live
%% set for each node.}
%% \label{fig_back3}
%% \end{myfig}

%% Figure \ref{fig_back3} shows the CFG for this example. The annotations
%% on edges show the facts computed for this analysis: the set of live
%% variables. Recall from Section~\ref{sec_back4} that we can choose to
%% traverse the CFG forwards or backwards. Going forwards would require
%% us to track each assignment and then, after traversing the CFG,
%% determine if the variable was referenced again. The backwards case
%% requires that we add each variable reference to the live set. When an
%% assignment occurs, we can check if the variable appears in the live
%% set. If not, we know the variable was never referenced and is not
%% live. For simplicity and efficiency, we choose to go backwards rather
%% than forwards.

%% We define our transfer function such that, for some statement $B$,
%% \inBa represents the variables that are live in the statement. A live
%% variable is referenced (i.e., \emph{used}) in $B$ or one
%% of its successors. A variable that appears in \outBa but not \inBa must
%% not be live. The only way to remove a variable from \outBa is if it is 
%% assigned (i.e. or \emph{defined}) in $B$. We can then define our transfer
%% function from \outBa to \inBa in terms of the \emph{use} and \emph{def} sets:
%% \begin{align}
%%   & \inBa = (\outBa \cup |use|(B)) - |def|(B), \label{eqn_back1} \\
%% \text{where} \notag\\
%%   & B     & \text{Statement considered.} \notag\\
%%   & |use|(B) & \text{Variables referenced in $B$}. \notag\\
%%   & |def|(B) & \text{Variables assigned $B$}. \notag\\
%% \end{align}

%% Table \ref{tbl_back1} shows the |use|, |def|, \inBa and \outBa sets for
%% each statement. We include the exit node (``\exitN'') in the table to
%% show the initial value of \outBa for the last statement -- $\emptyset$,
%% the empty set. Our analysis then works backwards through the
%% program. Each \inBa becomes the input, \outBa, for the statement's
%% predecessor. If our program (and its CFG) contained any loops, we
%% would need to run this algorithm multiple times, until the live set
%% for each statement reached a fixed point.

%% \begin{table}
%%   \centering
%%   \begin{math}
%%     \begin{array}{lcccc}
%%       & |use|(B) & |def|(B) & \outBa & \inBa \\
%%       \cmidrule(r){2-5} %%\cmidrule(r){1-1}\cmidrule(r){2-2}\cmidrule(r){3-3}\cmidrule(r){4-4}\cmidrule(r){5-5}
%%       \exitN & \emptyset & \emptyset & \emptyset & \emptyset \\
%%       #return a + 1# & \{a\} & \emptyset & \emptyset & \{a\} \\
%%       #b = a + 1# & \{a\} & \{b\} & \{a\} & \{a\} \\
%%       #a = 1# & \emptyset & \{a\} & \{a\} & \emptyset \\
%%     \end{array}
%%   \end{math}
%%   \caption{The $|use|$, $|def|$, \inBa and \outBa sets computed using
%%     equation \ref{eqn_back1} for our example program.}
%%   \label{tbl_back1}
%%   \figend
%% \end{table}

%% With the live set computed for each statement, our analysis can now
%% determine which statements to eliminate. Only
%% \refNode{lst_back10_assigna} and \refNode{lst_back10_assignb} in
%% Figure~\ref{fig_back3} perform an assignment. The live set for
%% \refNode{lst_back10_assigna} (``#a = 1#'') contains #a#, so we do not
%% eliminate it. For \refNode{lst_back10_assignb} (``#b = a + 1#''), the
%% live set does \emph{not} contain #b#. Therefore, we can eliminate
%% \refNode{lst_back10_assignb}, giving us the new program in
%% Figure~\ref{fig_back6}.

%% \begin{myfig}[th]
%%   \centering
%%   \begin{minipage}{1in}
%%   \begin{AVerb}[numbers=left]
%% a = 1;
%% return a + 1;
%%   \end{AVerb}
%%   \end{minipage}
%%   \caption{The program from Figure~\ref{fig_back3} with the useless assignment to
%%     \verb=b= eliminated.}
%% \end{myfig}

%% In the
%% forwards case, we must track each assignment and determine, when we
%% exit the CFG, if the variable was ever used. We would need to track
%% every assignment until our traversal finished. However, if we traverse
%% backwards, we only need to add each reference to our live set. When we
%% see an assignment to a variable \emph{not} in our live set, we know it
%% has never been referenced.

%% \emph{live set} The \inE and \out sets show the facts computed for this
%% analysis. The computed show the live variables for that program point
%% \emph{live set}, annotates edges between each statement. The live set
%% is the \emph{fact} we compute for this analysis.

%% Annotations
%% show the facts we will compute
%% Recall from Section~\ref{sec_back4} that a dataflow analysis can
%% go \emph{forwards} or \emph{backwards}. 

%% To eliminate the assignment like that on
%% line~\ref{fig_back2_dead_line}, we need to determine which variables
%% are ``live'' -- that is, variables referenced after assignment. Such variables are ``live''; if a
%% variable is \emph{not} live, then it is dead. We use this ``liveness''
%% analysis to determine if a particular assignment is dead.

%% To determine if a variable is live, we need to know if it is
%% referenced after assignment. Such variables make up a \emph{live set}
%% that we can compute between each statement. To compute the live set,
%% we can choose to traverse the CFG for the program forwards or
%% backwards.  In the forwards case, we must track each assignment and
%% determine, when we exit the CFG, if the variable was ever used. We
%% would need to track every assignment until our traversal
%% finished. However, if we traverse backwards, we only need to add each
%% reference to our live set. When we see an assignment to a variable
%% \emph{not} in our live set, we know it has never been
%% referenced. Therefore we compute ``liveness'' using a backwards
%% traversal over the CFG.

%% \begin{myfig}[th]
%% \begin{minipage}{2in}
%% \input{lst_back10}
%% \end{minipage}
%% \caption{The CFG for our example program, annotated with the live
%% set for each node.}
%% \label{fig_back3}
%% \end{myfig}

%% Figure \ref{fig_back3} shows the CFG for this example. Annotations
%% show the facts we will compute: the live set before and after. Though
%% execution follows the arrows in the CFG, our analysis proceeds
%% backwards. For example, the input to node 2 is the live set computed
%% for node 3 (``$\{a\}$'' in this case).

%% Our transfer function computes the live set based on \emph{uses} and
%% \emph{definitions} in a statement. Any reference (or use) of a
%% variable goes into the live set. Any assignment (or definition) of a
%% variable removes it from the live set. We can then define our transfer
%% function, |live|, for a statement as:

%% \begin{align}
%%   & |live|(s) = (\Varid{in}(s) \cup |use|(s)) - |def|(s), \label{eqn_back1} \\
%% \intertext{where}
%%   & s     & \text{Statement considered.} \notag\\
%%   & |use|(s) &  \text{Set of variables used in $s$}. \notag\\
%%   & |def|(s) & \text{Variable assigned to in $s$ (a singleton set)}. \notag\\
%%   & \Varid{in}(s) & \text{Live variables computed for $s$' successor}. \notag
%% \end{align}

%% Table \ref{tbl_back1} shows the |use| and |def| sets for each
%% statement. The live set computed, |live|, becomes the input, $\Varid{in}$, for
%% the statement's predecessor. We include the exit node (``#X#'') in the
%% table to show the initial value of $\Varid{in}$ for the last statement --
%% $\emptyset$, the empty set. Our analysis then works backwards through the
%% program. If our program (and its CFG) contained any loops, we would
%% need to run this algorithm multiple times, until the live set for each
%% statement reached a fixed point.

%% \begin{table}
%%   \centering
%%   \begin{tabular}{lcccc}
%%     $s$ & $|use|(s)$ & $|def|(s)$ & $\Varid{in}(s)$ &  $|live|(s)$ \\
%%     \cmidrule(r){1-1}\cmidrule(r){2-2}\cmidrule(r){3-3}\cmidrule(r){4-4}\cmidrule(r){5-5}
%%     #X# & & & & $\emptyset$ \\
%%     #return a + 1# & $\{a\}$ & $\emptyset$ & $\emptyset$ & $\{a\}$ \\
%%     #b = a + 1# & $\{a\}$ & $\{b\}$ & $\{a\}$ & $\{a\}$ \\
%%     #a = 1# & $\emptyset$ & $\{a\}$ & $\{a\}$ & $\emptyset$ \\
%%     \bottomrule
%%   \end{tabular}
%%   \caption{The $|use|$, $|def|$ and $|live|$ sets computed using equation \ref{eqn_back1} for our example program.}
%%   \label{tbl_back1}
%% \end{table}

%% With the live set computed for each statement, our analysis can now
%% determine which statements to eliminate. Only nodes 1 and 2 in Figure
%% \ref{fig_back3} perform an assignment. The live set for node 1 (``#a = 1#'')
%% contains #a#, so we do not eliminate it. In node 2 (``#b = a + 1#''),
%% the live set does \emph{not} contain #b#. Therefore, we can eliminate
%% node 2, giving us a new program without any dead code:

%% \begin{Verbatim}
%% a = 1;
%% return a + 1;
%% \end{Verbatim}

%% \subsection{Basic Blocks and Control-Flow Graphs}

%% A dataflow optimization operates over a ``control-flow graph'' (CFG)
%% of the program -- a directed graph where edges encode branches or
%% jumps and nodes represent statements. Programs run by entering a node
%% from a predecessor, executing the statements in turn, and exiting the
%% node to a successor. Multiple successors imply a conditional branch,
%% though the program can only choose one. A special ``entry'' node, with
%% no predecssors, exists to give the program a starting point.

%% The statements in each node must define a ``basic block,'' which means
%% there can only be one entry and one exit to the node. Each
%% predeccessor starts at the same statement; execution cannot start in
%% the ``middle'' of the statements in the node. Each successor also
%% leaves from the same instruction, so only one ``branch'' can exist in
%% each node.

%% For example, consider the ``fall-through'' implied by the use of #case#
%% statements in this C-language program fragment:

%% \begin{verbatim}
%%   switch(i) {
%%   case 1:
%%     printf("1");
%%     break;
%%   case 2:
%%     printf("2");
%%   case 3:
%%     printf("3");
%%   }
%% \end{verbatim}

%% \begin{figure}[h]
%% \begin{verbatim}
%%    A
%%   switch   ----<-
%%   | |  |  |      |
%%   | |  |  v C    ^
%%   | |   ->case 3 |
%%   | |     |      |
%%   | |      ->----_--
%%   | | B          |  |
%%   |  ->case 2 ->-   v
%%   |                 |
%%   |   D       ----<-
%%    ->case 1  |
%%      |       v
%%      v       |
%%    --+-----<-
%%   |
%%    -> ...
%% \end{verbatim}
%% \caption{CFG illustrating \emph{fall-through} allowed by the
%%   C-language \texttt{switch} statement.}
%% \label{switchCfgEg}
%% \end{figure}

%% Figure \ref{switchCfgEg} shows a CFG for this fragment. Execution
%% begins at node A. Node C has two predeccessors: A and B. The edge
%% between Node B and C represents fall-through from the second to third
%% case. They cannot be combined because the node would need two distinct
%% entry points. Encoding a program into basic blocks usually involves
%% inserting similar branches. The CFG makes explicit control--flow that
%% exists by implication in the source program.

%% \subsection{Direction, Facts and Rewrites}

%% \subsection{Example: Bind/Return Collapse}

%% Dataflow optimizations transform the CFG representation of a program,
%% with the goal of making a faster (or smaller, or more efficient, etc.)
%% program. Dataflow computes a set of ``entry'' assumptions and ``exit''
%% facts for each node in the graph. Facts for one node become
%% assumptions for the nodes' successors (thus the term
%% ``dataflow''). The algorithm iteratves over the entire graph until a
%% fixed point is reached -- that is, facts and assumptions no longer
%% change. The computed facts can then be used to transform the graph.

%% \emph{Constant propagation example -- or something more functional?}

%% \emph{Introduce forward and backwards dataflow.}

% What does dataflow mean?

% How do you use it?

% Example

\standaloneBib
\end{document}

% LocalWords:  Dataflow dataflow CFG printf variable's CFGs ccc Uncurrying lst
% LocalWords:  liveness Kildall AhoXX assigna assignb runtime valueOf ccccc lub
% LocalWords:  incr lcccc