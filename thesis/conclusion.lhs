%&preamble
\makeatletter\@@ifundefined{preambledocclass}{%%
  \documentclass[class=report]{standalone}
  \usepackage{standalone}
  \input{tikz.preamble}
  \input{preamble}}{\documentclass[class=report]{standalone}}\makeatother
\begin{document}
\numbersoff
\input{document.preamble}
\chapter{Conclusion \& Future Work}
\label{ref_chapter_conclusion}

\section{Future Work: Optimizations}

\subsection{Inlining Monadic Code}

\subsection{Uncurrying Across Blocks}

\subsection{Eliminating Thunks}

\subsection{Dead-Code Eliminiation}

\subsection{Push Through Cases}

\subsection{Lazy Code Motion}

\section{Future Work: Compiling MIL}

\subsection{Register Allocation through Renaming}

\section{Thoughts on Hoopl}

\section{Related Work}

\subsection{Uncurrying}

\intent{Describe the work of Danvy, Apel, and Tarditi; contrast to MIL uncurrying.}

\subsection{Compiling with Continuations}

\intent{Describe criticisms by Kennedy against his MIL; compare to our MIL.}

\section{Summary}

\standaloneBib 

%% Some interaction with standalone makes the thesis break unless we
%% end with \noindent. The error is:
%%
%%   "You can't use `\\unskip' in vertical mode.\\sa@atenddocument
%%   ->\\unskip".
%%
\noindent\end{document}
