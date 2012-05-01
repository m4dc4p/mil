%&pre_defense
\makeatletter%
\@@ifundefined{preambleloaded}
             {\input{pre_defense}}
             {}\makeatother%%
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\def\balt#1#2#3{\alt<#1>{#2}{#3}}
\author{Justin Bailey (\texttt{jgbailey@@gmail.com})}
\institute{Portland State University}
\date{\today}
\begin{document}\nomd\numbersoff

\section{Introduction}
\begin{frame}
\end{frame}

\section{MIL}
\subsection{Compilation}
\begin{frame}{Compiling |map|}
  \begin{itemize}
  \item Definition of |map|
  \item Evaluating |map| using call-by-value: |map toList [1,2,3]|
  \item Closures
  \end{itemize}
\end{frame}
\subsection{Translating |map| to MIL}

\begin{frame}
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
\end{frame}

\section{Dataflow Analysis}
\begin{frame}{Dataflow Analysis}
  \begin{itemize}
  \item Control-Flow Graphs
  \item Basic Blocks
  \item Example Program \& Constant Propagation
  \item Facts and the Transfer Function
  \end{itemize}
  
  \begin{itemize}
  \item Hoopl
  \item Used in GHC
  \item Interleaved Analysis \& Rewriting
  \end{itemize}

\end{frame}

\section{Uncurrying}
\begin{frame}{Uncurrying}
  \begin{itemize}
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
\end{frame}

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
      \vbinds v227<-\mkclo[k203:];\anchorF(v227a) 
      \vbinds v228<-\mkclo[k219:];\anchorF(v228a)
      v229 <- \balt{3-}{{\color{red}v227} @@ {\color{red}v228}}{v227 @@ v228}\anchorF(v229a) 
      \app v229 * ns/ 
  \end{AVerb}
  \begin{onlyenv}<2>\begin{tikzpicture}[overlay,remember picture]
    \node[fact, right=0.25in of v227a, anchor=west] (fv227a3) {$\{\var v227/\,:\,\mkclo[k203:]\unskip\}$};
    \node[fact, right=0.25in of v228a, anchor=west] (fv228a3) {$\{\var v228/\,:\,\mkclo[k219:]\unskip\}$};
    \draw [->] (fv227a3) to (v227a);
    \draw [->] (fv228a3) to (v228a);
  \end{tikzpicture}\end{onlyenv}%%
  \begin{onlyenv}<3->\begin{tikzpicture}[overlay,remember picture]
    \node[fact, right=0.25in of v227a, anchor=west] (fv227a4) {$\{{\color{red}\var v227/}\,:\,\mkclo[k203:]\unskip\}$};
    \node[fact, right=0.25in of v228a, anchor=west] (fv228a4) {$\{{\color{red}\var v228/}\,:\,\mkclo[k219:]\unskip\}$};
    \draw [->] (fv228a4) to (v228a);
    \draw [->] (fv227a4) to (v227a);
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
