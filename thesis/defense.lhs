\documentclass[t]{beamer}
\usepackage[T1]{fontenc}
\usetheme{Warsaw}
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
%% Footnotes with old style caps hard to read - this helps.
\usepackage{etoolbox}
\usepackage{calc}
\usepackage[osf,sc]{mathpazo}
\renewcommand\ttdefault{lmtt}
\usepackage{helvet}
\usepackage{xspace}
\usepackage{url}
\usepackage{fancyvrb}
%% Make sure line numbers are printed with math numerals,
%% not old-style numbers
\usepackage{amsmath}
\usepackage{booktabs}
\usepackage{ifthen}
\usepackage{stmaryrd}
\usepackage{longtable}
\usepackage{afterpage}
\usepackage{xifthen}
\usepackage{mathtools}
\usepackage[natbib=true,style=authoryear,backend=bibtex8]{biblatex}
\setlength{\bibitemsep}{\bigskipamount}
\addbibresource{thesis.bib}
\usepackage{microtype}
\usepackage[normalem]{ulem}
\usepackage{array}
\input{tikz.preamble}
\makeatletter\input{common}\makeatother
\begin{document}\nomd
\numbersoff
%%\begin{itemize}
%%\item Introduction
%% \item Dataflow Analysis
%%   \begin{itemize}
%%   \item Control-Flow Graphs
%%   \item Basic Blocks
%%   \item Example Program \& Constant Propagation
%%   \item Facts and the Transfer Function
%%   \end{itemize}
%% \item \mil
%%   \begin{itemize}
%%   \item Three-Address Code
%%   \item Closures
%%     \begin{itemize}
%%     \item Environments --- Example of a function that captures a
%%       variable.
%%     \end{itemize}
%%   \item Monads
%%   \item Allocation in \mil; partial application
%%   \end{itemize}
%% \item Hoopl
%%   \begin{itemize}
%%   \item Used in GHC
%%   \item Interleaved Analysis \& Rewriting
%%   \end{itemize}
%% \item Uncurrying
%%   \begin{itemize}
%%   \item Partial Application
%%   \item Uncurrying within a block (\lab toInt/ example)
%%     \begin{itemize}
%%     \item Facts
%%     \item Step-by-step Transformation of \lab main/ 
%%     \end{itemize}
%%   \item Aside: use of multiple optimizations (dead code, inlining)
%%   \item Uncurrying |map|
%%     \begin{itemize}
%%     \item Original \cfg
%%     \item Development of facts \& the \cfg
%%     \end{itemize}
%%   \end{itemize}
%%\end{itemize}
\begin{frame}{Uncurrying |map|}
  \begin{tikzpicture}
    \node[stmt] (main) {\block main(ns):};
    \node[stmt,below=.3in of main] (caseEval216) {\block caseEval216(xs, f):};
    \node[stmt,below left=.3in and -0.5in of caseEval216] (altNil206) {\block altNil206():};
    \node[stmt,below right=.3in and -0.7in of caseEval216] (altCons208) {\block altCons208(f, x, xs):};
    \draw [->] (caseEval216) to (altNil206);
    \draw [->] (caseEval216) to (altCons208);
  \end{tikzpicture}
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{AVerb}[gobble=4,numbers=left]
    \block main(ns):  \anchorF(nsa)
      \vbinds v227<-\mkclo[k203:];\anchorF(v227a) \label{main_v227a}
      \vbinds v228<-\mkclo[k219:];\anchorF(v228a)
      \vbinds v229<-\app v227*v228/;\anchorF(v229a) \label{main_v229a}
      \app v229 * ns/ 
  \end{AVerb}
  \begin{onlyenv}<2->\begin{tikzpicture}[overlay,remember picture]
    \node[fact, anchor=west, right=1in of nsa] (fvnsa) {$\{\var ns/\,:\,\top\}$};
    \draw [->] (fvnsa) to (nsa);
  \end{tikzpicture}\end{onlyenv}%%
  \begin{onlyenv}<3->\begin{tikzpicture}[overlay,remember picture]
    \node[fact] (fv227a3) at ($(fvnsa) + (1in, 0in)$) {$\{\var v227/\,:\,\mkclo[k203:]\unskip\}$};
    \draw [->] (fv227a3) to (v227a);
  \end{tikzpicture}\end{onlyenv}%%
  \begin{onlyenv}<4->\begin{tikzpicture}[overlay,remember picture]
    \node[fact, right=0.25in of v228a, anchor=west] (fv228a4) {$\{\var v228/\,:\,\mkclo[k219:]\unskip\}$};
    \draw [->] (fv228a4) to (v228a);
  \end{tikzpicture}\end{onlyenv}%%
  \begin{onlyenv}<5->\begin{tikzpicture}[overlay,remember picture]
    \node[fact, right=0.25in of v229a, anchor=west] (fv229a5) {$\{\var v229/\,:\,\top\}$};
    \draw [->] (fv229a5) to (v229a);
  \end{tikzpicture}\end{onlyenv}%%
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{onlyenv}<1>
    \begin{AVerb}[gobble=6,numbers=left]
      \block main(ns): 
        \vbinds v227<-\mkclo[k203:];
        \vbinds v228<-\mkclo[k219:];
        \llap{\ensuremath{\rightarrow} }\vbinds v229<-\mkclo[k204:v228];\anchorF(v229b) \label{main_v229b}
        \app v229 * ns/\label{main_app_b}
    \end{AVerb}
  \begin{tikzpicture}[overlay,remember picture]
    \node[fact, right=0.25in of v229b, anchor=west] (fv229b) {$\{\var v229/\,:\,\{\mkclo[k204:v228]\unskip\}$};
    \draw [->] (fv229b) to (v229b);
  \end{tikzpicture}%%
  \end{onlyenv}

  \begin{onlyenv}<2>
    \begin{AVerb}[gobble=6,numbers=left]
      \block main(ns): 
        \xout{\vbinds v227<-\mkclo[k203:];}
        \vbinds v228<-\mkclo[k219:];
        \xout{\vbinds v229<-\mkclo[k204:v228];}
        \llap{\ensuremath{\rightarrow} }\goto caseEval216(ns, v228) \anchorF(gotoCaseEval216a)
    \end{AVerb}
  \begin{tikzpicture}[overlay,remember picture]
    \node[fact, right=0.25in of gotoCaseEval216a, anchor=west] (fvGotoCaseEval216a) {$\{\var ns/\,:\,\top\}, \{\var v228/\,:\,\mkclo[k219:]\unskip\}$};
    \draw [->] (fvGotoCaseEval216a) to (gotoCaseEval216a);
  \end{tikzpicture}%%
  \end{onlyenv}
\end{frame}

\begin{frame}{Uncurrying |map|}
  \begin{onlyenv}<1>\begin{tikzpicture}
    \node[stmt] (main) {\block main(ns):};
    
    \node[stmt,below=.3in of main] (caseEval216) {\block caseEval216(xs, f):};
    
    \node[stmt,below left=.3in and -0.5in of caseEval216] (altNil206) {\block altNil206():};
    
    \node[stmt,below right=.3in and -0.7in of caseEval216] (altCons208) {\block altCons208(f, x, xs):};

    \node[overlay,invis,below left=.05in and -.2in of caseEval216] () {$\emptyset$};

    \node[overlay,invis,below right=.05in and -.2in of caseEval216] () {$\{\var f/\,:\,\top\}, \{\var x/\,:\,\top\}, \{\var xs/\,:\,\top\}$};

    \draw [->] (caseEval216) to (altNil206);
    \draw [->] (caseEval216) to (altCons208);
  \end{tikzpicture}
  \end{onlyenv}

  \begin{onlyenv}<2>\begin{tikzpicture}
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
  \end{onlyenv}
\end{frame}
\end{document}
