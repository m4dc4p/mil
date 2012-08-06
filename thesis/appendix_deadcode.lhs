%&preamble
\input{nodocclass}\dodocclass
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\begin{document}
\numbersoff
\input{document.preamble}
\addcontentsline{toc}{chapter}{\textbf{Appendix}}
\chaptermark{Appendix}
\thispagestyle{plain}
\makeatletter\@@makechapterhead{Source Code}\makeatother
\label{ref_appendix_deadcode}

\noindent The source code for the \lamC to \mil compiler, our uncurrying 
optimization, the dead-code elimination example from Chapter~\ref{ref_chapter_hoopl},
the ``monadic'' optimizations mentioned in Section~\ref{conc_other}, and a number
of other artifacts of this work (including the entire \TeX\ source of this document)
can be downloaded from \texttt{http://mil.codeslower.com}. The author can also
be contacted via e-mail at \texttt{jgbailey@@codeslower.com}.

\section*{Colophon}

We typeset all elements of this document using \TeX\ and \LaTeX. We
created our graphical figures with the Ti\emph{k}Z library. We
converted our literate Haskell sources to \TeX\ code with Hinze and
L\"oh's lhs$2$\TeX\ pre-processor. We used Chris Monson's
\LaTeX\ \texttt{Makefile}\footnote{Available from
  \texttt{http://code.google.com/p/latex-makefile/}.} to orchestrate
the compilation process that produced this \textsc{pdf}.

This document uses 12-pt Palatino for body text and 12-pt Helvetica
for headings and titles. Margins, line-spacing and font size conform
to guidelines given by Portland State University's Office of Graduate
Studies.

We created this version of the thesis on \today.
\end{document}
