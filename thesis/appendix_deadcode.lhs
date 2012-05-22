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
be contacted via e-mail at \texttt{jgbailey@@gmail.com}.

\noindent\end{document}
