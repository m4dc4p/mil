%&preamble
\input{nodocclass}\dodocclass
\usepackage{beamer}
\usetheme{Warsaw}
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\renewcommand\intent[1]{{\begin{singlespace}\noindent\leftskip=-1in\emph{\footnotesize Intent: #1}\end{singlespace}}\nopagebreak[1]}
\begin{document}
\numbersoff
\input{document.preamble}
\begin{itemize}
\item Introduction
\item Dataflow Analysis
  \begin{itemize}
  \item Control-Flow Graphs
  \item Basic Blocks
  \item Example Program \& Constant Propagation
  \item Facts and the Transfer Function
  \end{itemize}
\item \mil
  \begin{itemize}
  \item Three-Address Code
  \item Closures
    \begin{itemize}
    \item Environments --- Example of a function that captures a
      variable.
    \end{itemize}
  \item Monads
  \item Allocation in \mil; partial application
  \end{itemize}
\item Hoopl
  \begin{itemize}
  \item Used in GHC
  \item Interleaved Analysis \& Rewriting
  \end{itemize}
\item Uncurrying
  \begin{itemize}
  \item Partial Application
  \item Uncurrying within a block (\lab toInt/ example)
    \begin{itemize}
    \item Facts
    \item Step-by-step Transformation of \lab main/ 
    \end{itemize}
  \item Aside: use of multiple optimizations (dead code, inlining)
  \item Uncurrying |map|
    \begin{itemize}
    \item Original \cfg
    \item Development of facts \& the \cfg
    \end{itemize}
  \end{itemize}
\end{itemize}
\end{document}
