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
\newbox\consbox
\setbeameroption{show notes}
\begin{document}\nomd\numbersoff

\section{Introduction}
\begin{frame}
  \begin{itemize}
  \item Our Monadic Intermediate Language
    \begin{itemize}
    \item Compiling Functional Languages
    \end{itemize}
  \item Dataflow Analysis
  \item Uncurrying
  \end{itemize}
\end{frame}

\section{MIL}
\subsection{Blocks}
\begin{frame}[fragile]
\note[item]<1>{This sequence will connect a simple definition with a block of
\mil code. I will illustrate closure-capturing and ordinary blocks.}
\begin{onlyenv}<1>
Haskell-like definition.

> toList :: a -> [a]
> toList x = [x] {-"\phantom{\fbox{\ensuremath{"-}Cons x Nil{-"}}}"-}
\end{onlyenv}

\note[item]<1>{I start by removing the syntactic sugar to
show the real constructors.}

\begin{onlyenv}<2,3>
Haskell-like definition.

> toList :: a -> [a]
> toList x = {-"\mathrlap{"-}Cons x Nil{-"}"-}{-"\phantom{\fbox{\ensuremath{"-}Cons x Nil{-"}}}"-}
\end{onlyenv}

\note[item]<2>{Now I transform |toList| into a \mil block. I leave
both bits of code on the slide, so I can talk about the correspondances.

On the succeeding slides I connect each expression (Nil and Cons x Nil) to
the corresponding statement in the block.
}
\begin{onlyenv}<4>
Haskell-like definition.

> toList :: a -> [a]
> toList x = Cons x {-"\fbox{\ensuremath{"-}Nil{-"}}"-}{-"\anchorF(toListNil)"-}
\end{onlyenv}

\begin{onlyenv}<5>
Haskell-like definition.

> toList :: a -> [a]
> toList x = {-"\fbox{\ensuremath{"-}Cons x Nil{-"}}"-}{-"\anchorF(toListCons)"-}
\end{onlyenv}

\begin{onlyenv}<3->
\Mil definition.

  \begin{AVerb}[gobble=4,numbers=left]
    \block toList(x):  
      \vbinds nil<- \prim Nil();\anchorF(milNil)
      \vbinds cons<- \prim Cons(x,nil);\anchorF(milCons)
      \return cons/
  \end{AVerb}
\end{onlyenv}

\begin{onlyenv}<4>
  \begin{tikzpicture}[overlay,remember picture]
    \draw [->] (milNil) -|| (toListNil);
  \end{tikzpicture}
\end{onlyenv}

\begin{onlyenv}<5>
  \begin{tikzpicture}[overlay,remember picture]
    \draw [->] (milCons) ||- (toListCons);
  \end{tikzpicture}
\end{onlyenv}
\end{frame}
\end{document}

\subsection{Monadic Effects}

\subsection{Tails}

\subsection{Compilation}
%   \item Definition of |map|
\begin{frame}
> map :: (a -> b) -> [a] -> [b]
> map f xs = case xs of
>   (x:xs') -> map (f x) xs'
>   [] -> []
>
> toList :: a -> [a]
> toList x = [x]
\end{frame}

\begin{frame}{Evaluating |map| (call-by-value)}
  %  \item Evaluating |map| using call-by-value: |map toList [1,2,3]|
  \begin{onlyenv}<1>
> map toList [1,2] = case [1,2] of {-"\hfill\text{\it Definition of \mfun{map}.}"-}
>   (x:xs') -> toList x : map f xs'
>   [] -> []
  \end{onlyenv}

  \begin{onlyenv}<2>
> {-"\dots"-} = toList 1 : map f [2] {-"\hfill\text{\it ``Cons'' arm of \mfun{map}.}"-}
  \end{onlyenv}

  \begin{onlyenv}<3>
> {-"\dots"-} = [1] : map f [2] {-"\hfill\text{\it Definition of \mfun{toList}.}"-}
  \end{onlyenv}

  \begin{onlyenv}<4>
> {-"\dots"-} = [1] : case [2] of {-"\hfill\text{\it Definition of \mfun{map}.}"-}
>   (x:xs') -> toList x : map f xs'
>   [] -> []
  \end{onlyenv}

  \begin{onlyenv}<5>
> {-"\dots"-} = [1] : toList 2 : map f [] {-"\hfill\text{\it ``Cons'' arm of \mfun{map}.}"-}
  \end{onlyenv}

  \begin{onlyenv}<6>
> {-"\dots"-} = [1] : [2] : map f [] {-"\hfill\text{\it Definition of \mfun{toList}.}"-}
  \end{onlyenv}


  \begin{onlyenv}<7>
> {-"\dots"-} = [1] : [2] : case [] of {-"\hfill\text{\it Definition of \mfun{map}.}"-}
>   (x:xs') -> toList x : map f xs'
>   [] -> []
  \end{onlyenv}

  \begin{onlyenv}<8>
> {-"\dots"-} = [1] : [2] : [] {-"\hfill\text{\it ``Nil'' arm of \mfun{map}.}"-}
  \end{onlyenv}


  \begin{onlyenv}<9>
> {-"\dots"-} = [[1],[2]] {-"\hfill\text{\it Syntatic sugar.}"-}
  \end{onlyenv}

  %% \begin{itemize}
  %% \item Closures
  %% \end{itemize}
\end{frame}

\subsection{Hidden Effects in |toList|}
\begin{frame}
  \frametitle<1>{Definition of |toList|}
  \begin{onlyenv}<1>
> toList :: a -> [a]
> toList x = [x] {-"\vphantom{\fbox{\mfun{Cons}}}"-}
  \end{onlyenv}

  \frametitle<2>{Removing Syntatic Sugar \ldots}
  \begin{onlyenv}<2>
> toList :: a -> [a]
> toList x = Cons x Nil {-"\vphantom{\fbox{\mfun{Cons}}}"-}
  \end{onlyenv}

  \frametitle<3>{Allocation!}
  \begin{onlyenv}<3>
> toList :: a -> [a]
> toList x = {-"\fbox{\ensuremath{"-}Cons x Nil{-"}}"-}
  \end{onlyenv}

  \frametitle<4>{Allocation!}
  \begin{onlyenv}<4>
> toList :: a -> [a]{-"\mathllap{\xout{\phantom{"-}[a]{-"}}}"-}
> toList x = {-"\fbox{\ensuremath{"-}Cons x Nil{-"}}"-}
  \end{onlyenv}

  \frametitle<5>{The real type of |toList|.}
  \begin{onlyenv}<5>
> toList :: a -> M [a]
> toList x = {-"\dots\phantom{\fbox{\ensuremath{"-}Cons x Nil{-"}}}"-}
  \end{onlyenv}

  \frametitle<6>{A monadic |toList|}
  \begin{onlyenv}<6>
> toList :: a -> M [a]
> toList x = do {-"\phantom{\fbox{\ensuremath{"-}Cons x Nil{-"}}}"-}
>   nil <- mkData Nil
>   cons <- mkData Cons x nil
>   return cons
  \end{onlyenv}
  
\end{frame}

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
