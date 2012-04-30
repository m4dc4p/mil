%&preamble
\input{nodocclass}\dodocclassx beamer/
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
\begin{frame}{Uncurrying |map|}
  \begin{tikzpicture}
    \node[stmt] (main) {\block main(ns):};
    
    \node[stmt,below=.3in of main] (caseEval216) {\block caseEval216(xs, f):};
    
    \node[stmt,below left=.3in and -0.5in of caseEval216] (altNil206) {\block altNil206():};
    
    \node[stmt,below right=.3in and -0.7in of caseEval216] (altCons208) {\block altCons208(f, x, xs):};

    \node[overlay,invis,below left=.05in and -.2in of caseEval216] () {$\emptyset$};

    \node[overlay,invis,below right=.05in and -.2in of caseEval216] () {$\{\var f/\,:\,\top\}, \{\var x/\,:\,\top\}, \{\var xs/\,:\,\top\}$};

    \draw [->] (caseEval216) to (altNil206);
    \draw [->] (caseEval216) to (altCons208);
  \end{tikzpicture} \\\\
  \scap{uncurry_global_blocks_a}\\
  \begin{tikzpicture}
    \node[stmt] (main) {\block main(ns):};
    \node[stmt,below=.3in of main] (caseEval216) {\block caseEval216(xs, f):};

    \node[stmt,below left=.3in and -0.5in of caseEval216] (altNil206) {\block altNil206():};

    \node[stmt,below right=.3in and -0.7in of caseEval216] (altCons208) {\block altCons208(f, x, xs):};

    \node[overlay,invis,below right=.07in and -.2in of main] () { $\{\var xs/\,:\,\top\}, \{\var f/\,:\,\mkclo[k219:]\unskip\}$};
    \node[overlay,invis,below left=.05in and -.2in of caseEval216] () {$\emptyset$};
    \node[overlay,invis,below right=.05in and -.2in of caseEval216] () {$\{\var f/\,:\,\mkclo[k219:]\unskip\}, \{\var x/\,:\,\top\}, \{\var xs/\,:\,\top\}$};

    \draw [->] (main) to (caseEval216);
    \draw [->] (caseEval216) to (altNil206);
    \draw [->] (caseEval216) to (altCons208);
  \end{tikzpicture}
\end{frame}
\end{document}
