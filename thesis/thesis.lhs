\documentclass[12pt]{report}
\usepackage{standalone}
%include polycode.fmt
%include lineno.fmt
\input{tikz.preamble}
\input{preamble}
% Used by included files to know they
% are NOT standalone
\setboolean{standaloneFlag}{false}

\begin{document}
\VerbatimFootnotes
\DefineShortVerb{\#}
             
\input{front}

\pagenumbering{arabic}
\input{intro}

\input{dataflow}

\input{hoopl}

\input{mil}

\input{uncurrying}

%% \input{deadcode}

%% \chapter{Monadic Optimizations}
%% \label{ref_chapter_monadic}

%% \emph{Describes optimizations based on the monad laws: bind/return collapse and
%%   monadic fuzzbang (inlining)}

%% \section{Copy-propagation}
%% \emph{Collapsing ``|x <- return y; p|'' to ``|[y/x] p|''.}
%% \subsection{Example of Desired Optimization}
%% \subsection{Implementation}
%% \subsection{Reflection}

%% \section{Inlining}
%% \emph{Monadic inlining using the associativity law. That is:}

%% > y <- (z <- x; p1)
%% > p2

%% \noindent
%% \emph{becomes:}

%% > z <- x
%% > y <- p1
%% > p2

%% \subsection{Example of Desired Optimization}
%% \subsection{Implementation}
%% \subsection{Reflection}

\chapter{Conclusion \& Future Work}

\emph{Where we started and where we ended.}

\begin{singlespace}
  \printbibliography
\end{singlespace}

\end{document}
