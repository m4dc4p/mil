%&preamble
\input{nodocclass}\dodocclass
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\begin{document}
\numbersoff
\input{document.preamble}
%% \chapter{Dead-Code Elimination Example}
\addcontentsline{toc}{chapter}{\textbf{Appendix}}
\chaptermark{Dead-Code Elimination Example}
\thispagestyle{plain}
\makeatletter\@@makechapterhead{Dead-Code Elimination Example}\makeatother
\label{ref_appendix_deadcode}

\intent{Give complete text of our example.}  This section gives our
entire example program from Chapter~\ref{ref_chapter_hoopl}. All the
code shown appears, as well as code for printing before and
after results and |main|, which runs the optimization over our sample
program.

\begin{singlespace}\disableoverfull
%let includeAll = True
%include DeadCodeC.lhs
%let includeAll = False
\end{singlespace}

\noindent Executing ``main'' produces output showing our optimized function:
\begin{singlespace}\correctspaceskip
\begin{AVerb}
Original Program
----------------
void example() \{
  c = 4;
  a = c + 1;
  printf("%d",c);
  a = c + 2;
\}

Optimized Program
-----------------
void example() \{
  c = 4;
  printf("%d",c);
\}  
\end{AVerb}
\end{singlespace}

%% Some interaction with standalone makes the thesis break unless we
%% end with \noindent. The error is:
%%
%%   "You can't use `\\unskip' in vertical mode.\\sa@atenddocument
%%   ->\\unskip".
%%
\noindent\end{document}
