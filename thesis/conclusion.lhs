%&preamble
\input{nodocclass}\dodocclass
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\begin{document}
\numbersoff
\input{document.preamble}
\chapter{Conclusion \& Future Work}
\label{ref_chapter_conclusion}

\section{Hoopl Refinements}

\section{Future Work}

\subsection{Inlining Monadic Code}

Wadler gave the so-called \emph{monad laws} \citeyearpar{Wadler1995},
which state properties that all well-defined monads will obey. Figure
~\ref{conc_fig_monad_laws} gives the three laws: left-unit,
right-unit, and associativity.\footnote{Left-unit and right-unit can
  also be called left-identity and right-identity.} While these laws
can be interpreted as specifications of behavior, they can also be
interpreted as \emph{transformations}.

\begin{myfig}
  \begin{math}
    \begin{aligned}
      |do { x <- return y; m }| & \equiv\
      \begin{cases}
        |do { m }| & \text{when |x| is |y|.} \\
        |do { {-"\lamSubst{y}{x}\ "-} m}| & \text{otherwise.}
      \end{cases} & \text{\it Left-Unit} & \quad\labeledeq{eq_left_unit} \\
      |do { x <- m; return x }| & \equiv\ |do { m }| & \text{\it Right-Unit} & \quad\labeledeq{eq_right_unit} \\
      \llap{|do { x <- do {y <- m; n}; o }|} & \equiv\ |do { y <- m; x <- n; o} |& \text{\it Associativity} & \quad\labeledeq{eq_assoc}
    \end{aligned}
  \end{math}
  \caption{The monad laws, as stated by Wadler
    \citeyearpar{Wadler1995}. The notation ``$\lamSubst{y}{x}\ m$''
    means that $y$ should be substituted for $x$ everywhere in $m$.  }
  \label{conc_fig_monad_laws}
\end{myfig}

In fact, transformations of MIL programs using the monad laws can be
interpreted as optimizations. For example, the following block binds
\var x/ to the value of \var y/, keeping both variables live between
the ``\binds x\ <-\ \return y/;'' and \goto l(x,y) statements::

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b():
      \vbinds x <- \return y/;
      \dots
      \goto l(x, y)
  \end{AVerb}
\end{singlespace}

\noindent If no interverning statement binds \var x/ again, we can use
the Left-Unit law to replace all occurrences of \var x/ with \var y/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b():
      $\dots$
      \goto l(y, y)
  \end{AVerb}
\end{singlespace}

\noindent If variables represent registers, then this can reduce the number of registers used
in a given block of MIL code.

The Right-Unit law shortens the ``tail'' of MIL blocks that end with a
\return/ statement. For example, Right-Unit can be used to transform the
following MIL block:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b(\dots):
      \dots
      \vbinds x <- \app f*y/;
      \return x/
  \end{AVerb}
\end{singlespace}

\noindent into the shorter block:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b(\dots):
      \dots
      \app f*y/
  \end{AVerb}
\end{singlespace}

The Associativity law provides an inlining mechanism for MIL
programs. The inner monadic computation mentioned on the left-hand
side of the law, |do { y <- m }|, can be an arbitrarily long monadic
program. All MIL blocks are monadic programs --- therefore, we can use
this law to inline any block. For example, consider these two blocks:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block compose(f, g, x): 
      \vbinds t1 <- \app g*x/;
      \vbinds t2 <- \app f*t1/;
      \return t2/ 

    \block main(a,b,c): 
      x <- compose(a,b,c)
      \goto b(x)
  \end{AVerb}
\end{singlespace}

Equation~\eqref{eq_assoc} lets us inline \lab compose/ into \lab main/, as
long as we appropriately rename variables:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main(a,b,c): 
      \vbinds t1 <- \app b*c/;
      \vbinds t2 <- \app a*t1/;
      x <- \return t2/ 
      \goto b(x)
  \end{AVerb}
\end{singlespace}

\noindent Notice we can now also apply Equation~\eqref{eq_left_unit}, eliminating
the use of \var x/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main(a,b,c): 
      \vbinds t1 <- \app b*c/;
      \vbinds t2 <- \app a*t1/;
      \goto b(t2)
  \end{AVerb}
\end{singlespace}

\subsection{Uncurrying Across Blocks}

\subsection{Eliminating Thunks}

\subsection{Dead-Code Eliminiation}

\subsection{Push Through Cases}

\subsection{Lazy Code Motion}

\section{Future Work: Compiling MIL}

\subsection{Register Allocation through Renaming}

\section{Related Work}

\section{Summary}

\standaloneBib 

%% Some interaction with standalone makes the thesis break unless we
%% end with \noindent. The error is:
%%
%%   "You can't use `\\unskip' in vertical mode.\\sa@atenddocument
%%   ->\\unskip".
%%
\noindent\end{document}
