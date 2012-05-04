%&pre_defense
\makeatletter%
\@@ifundefined{preambleloaded}
             {\input{pre_defense}}
             {}\makeatother%%
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\def\balt#1#2#3{\alt<#1>{#2}{#3}}
\def\bonly#1{\only<#1>}
\def\buncover#1{\uncover<#1>}
\def\labF#1;{\lab #1/}
\author{Justin Bailey}
\institute{Portland State University}
\date{\today}
\setbeameroption{show notes}
\setbeamertemplate{navigation symbols}{}
\setbeamersize{text margin left=1.5em}
\usepackage{verbatim}
\begin{document}\nomd\numbersoff

\section{Introduction}
\begin{frame}{Introduction}\vspace{12pt}
  \begin{itemize}
  \item Overview
    \begin{itemize}
    \item Optimizing Functional Languages
    \item Dataflow Analysis
    \item Monadic Intermediate Language
    \end{itemize}
  \item Monadic Intermediate Language (\mil)
    \begin{itemize}
    \item \Mil: blocks.
    \item \Mil: closures and function application.
    \item \Mil: side-effects.
    \item \Mil syntax
    \end{itemize}
  \item Dataflow Analysis
    \begin{itemize}
    \item Control-Flow Graphs
    \item Basic Blocks
    \item Example Program \& Constant Propagation
    \item Facts and the Transfer Function
    \end{itemize}
  \item Uncurrying
  \end{itemize}
\end{frame}

\begin{comment}
\section{\Mil}
\subsection{Blocks}
\begin{frame}[fragile]{\Mil: Blocks}
\vspace{12pt}
\note[item]<1>{This sequence will connect a simple definition with a block of
\mil code. I will first illustrate ordinary blocks.

I start by removing the syntactic sugar to
show the real constructors.}
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}{.45\hsize}\elimdisplayskip\begin{onlyenv}<1>
> toList :: a -> [a]
> toList x = [x] {-"\strut"-}
\end{onlyenv}\begin{onlyenv}<2,3>
> toList :: a -> [a]
> toList x = Cons x Nil{-"\strut"-}
\end{onlyenv}\begin{onlyenv}<4>
> toList :: a -> [a]{-"\phantom{(}"-}
> toList x = Cons x {-"\uline{"-}Nil{-"}"-}
\end{onlyenv}\begin{onlyenv}<5>
> toList :: a -> [a]{-"\phantom{(}"-}
> toList x = {-"\uline{"-}Cons x Nil{-"}"-}
\end{onlyenv}\end{minipage} & \begin{minipage}{.45\hsize}\begin{uncoverenv}<3->
  \begin{AVerb}[gobble=4,numbers=left]
    \block toList(x):  
      \vbinds nil<- \balt{4}{\uline{\smash{\prim Nil()}}}{\prim Nil()};
      \vbinds cons<- \balt{5}{\uline{\smash{\prim Cons(x,nil)}}}{\prim Cons(x,nil)};
      \return cons/
  \end{AVerb}
\end{uncoverenv}\end{minipage}
\end{tabular*}


\note[item]<2>{Now I transform |toList| into a \mil block. I leave
both bits of code on the slide, so I can talk about the correspondances.

On the succeeding slides I connect each expression (Nil and Cons x Nil) to
the corresponding statement in the block.}
\end{frame}

\subsection{Closures \& Function Application}
\note{I define closures as a data structure with two properties: a
  pointer to some body of code and an environment -- a
  map that associates variables with values.

  To explain closures, I start by explaining free variables
  and environments. The first slide shows an expression with
  a free variable, |name|. I explain that the value of
  name must come from the environment, because it is 
  not given as an argument to any function shown.}

\begin{frame}[fragile]\vspace{12pt}
\begin{tabular*}{\hsize}{@@{}l}
\begin{minipage}{\hsize}\elimdisplayskip\begin{onlyenv}<1>
> putStrLn ("Hello, " ++ {-"\uline{"-}name{-"}"-} ++ "!"{-"\anchorF(nameVar)"-})
\end{onlyenv}\begin{onlyenv}<2>
> main {-"\uline{"-}name{-"}\strut"-} = 
>   putStrLn ("Hello, " ++ {-"\uline{"-}name{-"}"-}++ "!")
\end{onlyenv}\begin{onlyenv}<3-5>
> main {-"\uline{"-}name{-"}\strut"-} = do
>   let msg greeting = greeting ++ ", " ++ {-"\uline{"-}name{-"}"-} ++ "!"
>   {-"\anchorF(hello)"-}putStrLn (msg "Hello")
>   {-"\anchorF(nice)"-}putStrLn (msg "Nice to meet you")
\end{onlyenv}\begin{onlyenv}<6-9>
> main name{-"\strut"-} = do
>   let{-"\anchorF(msgDef)"-} msg greeting = greeting ++ ", " ++ name ++ "!"
>   {-"\anchorF(mapMsg)"-}mapM_ (putStrLn . msg{-"\anchorF(msgClo)"-} ) [{-"\anchorF(msg1)"-}"Hello",{-"\anchorF(msg2)"-}"Nice to meet you"] 
\end{onlyenv}\end{minipage}
\end{tabular*}

\note<1>{I explain that the value of |name| must be declared in some
  outer scope (at least, if we want the program to run). I now show
  |main|, which takes |name| as an argument. In this case, the environment
  contains |name| because it is argument to |main|.}

\note<2>{Now I define a local function, |msg|, explaining that I want
  to print different greetings. |msg| takes one argument, |greeting|, but |name|
  is free in |msg|.}

\note<3>{The next two slides show the environment for each invocation
  of |msg|. We assume |main| is invoked with the argument |"Justin"|, as shown
  on the right.}

\begin{onlyenv}<4>
\begin{tikzpicture}[remember picture,overlay]
  \path let \p1=(hello.west) in node[stmt, anchor=west] (ep1) at ($(\p1) + (0in, -1in)$) {\mfun{name}: |"Justin"|, \mfun{greeting}: |"Hello"|};
  \draw [->] (ep1.west) to ($(ep1.west) + (-.25in,0in)$) ||- (hello.west);
\end{tikzpicture}
\end{onlyenv}

\begin{onlyenv}<5>
\begin{tikzpicture}[remember picture, overlay]
  \path let \p1=(hello.west) in node[stmt, anchor=west] (ep2) at ($(\p1) + (0in, -1in)$) {\mfun{name}: |"Justin"|, \mfun{greeting}: |"Nice to meet you"|};
  \draw [->] (ep2.west) to ($(ep2.west) + (-.25in,0in)$) ||- (nice.west);
\end{tikzpicture}
\end{onlyenv}

\note<5>{Now I explain that I have talked about environments, I move
  to the second half: a pointer to some body of code. I rewrite the
  program to use |mapM_|. I explain that while previously we could
  think of |msg| as executing right away and building a string, we
  really can't anymore. Instead, it represents a delayed or suspended
  value that we need to supply more arguments to to get our string
  out.}

\note<6>{I now show the closure represented by |msg|. The ``hole''
  points to the function defintion; |name| exists in the environment
  (and does not change); |greeting| is shown to indicate that we don't
  have all the arguments yet.}

\begin{onlyenv}<7>
\begin{tikzpicture}[remember picture, overlay,node distance=0in]
  \path let \p1=(mapMsg.west) in node[stmt, anchor=west] (msgHole1) at ($(\p1) + (0in, -1in)$) {\strut\phantom{\textbullet}};
  \node[stmt, right=0in of msgHole1.east, anchor=west] (ep31) {\mfun{name}: |"Justin"|, \mfun{greeting}: ?};
  \draw [->] ($(msgClo.south) + (-.1in,-.1in)$) to (ep31.north);
  \draw [*->] (msgHole1.base) to ($(msgHole1.base) + (-.25in,0in)$) ||- ($(msgDef.base) + (-.25in,0in)$);
\end{tikzpicture}
\end{onlyenv}

\begin{onlyenv}<8>
\begin{tikzpicture}[remember picture, overlay,node distance=0in]
  \path let \p1=(mapMsg.west) in node[stmt, anchor=west] (msgHole2) at ($(\p1) + (0in, -1in)$) {\strut\phantom{\textbullet}};
  \node[stmt, right=0in of msgHole2.east, anchor=west] (ep32) {\mfun{name}: |"Justin"|, \mfun{greeting}: |"Hello"|};
  \draw [->] ($(msg1.south) + (.2in,-.1in)$) to (ep32.north);
  \draw [*->] (msgHole2.base) to ($(msgHole2.base) + (-.25in,0in)$) ||- ($(msgDef.base) + (-.25in,0in)$);
\end{tikzpicture}
\end{onlyenv}

\begin{onlyenv}<9>
\begin{tikzpicture}[remember picture, overlay,node distance=0in]
  \path let \p1=(mapMsg.west) in node[stmt, anchor=west] (msgHole3) at ($(\p1) + (0in, -1in)$) {\strut\phantom{\textbullet}};
  \node[stmt, right=0in of msgHole3.east, anchor=west] (ep33) {\mfun{name}: |"Justin"|, \mfun{greeting}: |"Nice to ..."|};
  \draw [->] ($(msg2.south) + (.5in,-.1in)$) to (ep33.north);
  \draw [*->] (msgHole3.base) to ($(msgHole3.base) + (-.25in,0in)$) ||- ($(msgDef.base) + (-.25in,0in)$);
\end{tikzpicture}
\end{onlyenv}

\end{frame}

\note{Now that I have defined closures, I want to explain
  closure-capturing blocks and the @@ operator in this sequence.

I start by showing a function that applies |map| to arguments, so I
can show how closures are built up and entered.}
\begin{frame}[fragile]
\vspace{12pt}
\begin{onlyenv}<1>
> main xs = map toList xs
\end{onlyenv}

\note<1>{Now I show the \mil code for main, next to the definition of |main|. I
want to illustrate the process of capturing arguments for |map|, while also
showing the syntax for creating closures and defining \cc blocks. I don't give
a lot of detail about the \mil code shown (yet).}

\note<2>{I start by rewriting |main| to show each function
  application. I motivate this rewrite by noting that I want to highlight
  \mil's support for \emph{curried} functions. I give a brief verbal definition of
  curried here and note I'll return to it later.}

\note<3>{Now I show that |main| starts by creating a closure referring to |toList|. This
  closure will be used by |map| to apply |toList| to its arguments. I do not reveal
  the definition of toList's \cc block yet.}

\note<4>{Now I need to do some hand-waving on why we create a closure 
  referring to |map|; I'll just say we create the closure for reasons to be 
  explained later.}

\begin{onlyenv}<2-6>
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}[t]{.45\hsize}
  \begin{AVerb}[gobble=4,numbers=left]
    \block main(xs):
      \vbinds t1<-\balt{4}{\uline{\smash{\mkclo[toListK1:]}}}{\mkclo[toListK1:]};
      \vbinds t2<-\balt{5}{\uline{\smash{\mkclo[mapK1:]}}}{\mkclo[mapK1:]};
      \vbinds t3<-\balt{6}{\uline{\smash{\app t2*t1/}}}{\app t2*t1/};
      \vbinds t4<-\app t3*xs/;
      \return t4/
    \ccblock toListK1()x: \ldots
    \ccblock mapK1()f: \mkclo[mapK2:f]
    \ccblock mapK2(f)xs: \goto map(f, xs)
    \block map(f, xs): \ldots
  \end{AVerb}
\end{minipage} &
\begin{onlyenv}<2>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
> main xs = map toList xs{-"\phantom{(}"-}
\end{minipage}
\end{onlyenv}\begin{onlyenv}<3>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
> main xs = (map toList) xs{-"\phantom{(}"-}
\end{minipage}
\end{onlyenv}\begin{onlyenv}<4>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
> main xs = (map {-"\uline{"-}toList{-"}"-}) xs{-"\phantom{(}"-}
\end{minipage}
\end{onlyenv}\begin{onlyenv}<5>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
> main xs = ({-"\uline{"-}map{-"}"-} toList) xs{-"\phantom{(}"-}
\end{minipage}
\end{onlyenv}\begin{onlyenv}<6>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
> main xs = ({-"\uline{"-}map toList{-"}"-}) xs
\end{minipage}
\end{onlyenv}
\end{tabular*}
\end{onlyenv}

\note<5>{The next slide shows |map| gathering its first argument, the first instance
  of function application so far. I underline the relevant portions in each
definition, but don't show the \cc blocks yet.}

\note<6>{Now I show the two \cc blocks for |map|. I explain how \var t3/ will hold
  \mkclo[mapK2:f] after the statement executes. I also state that the definition
of \lab toListK1/ isn't relevant yet, so I don't show it.}

\note<7>{The next slide will explain
the syntax of \cc blocks, connecting line 3 to line 7. }

\note<8>{I return to line 4, noting that \var t2/ holds the closure
  \mkclo[mapK1:]. I discuss the meaning of the \enter operator, and
  describe how the program ``enters'' the closure on the left with the
  argument on right. I use the next two slides to show that the body
  of \lab mapK1/ returns the closure \mkclo[mapK2:f], and that \var t3/
  will refer to that closure.}

\note<10>{The next two slides show |map| gathering its final argument
  and then executing. I reinforce the previous description of
  ``entering'' a closure. I connect the specification of \lab mapK2/
  to the value in \var t3/. I especially point out how \var f/ appears
  in \var t3/ and \lab mapK2/. I highlight that \lab mapK2/ does not
  return a closure, but rather immediately executes the \lab map/
  block. The result of \lab map/ gets bound to \var t4/ and returned.}

\begin{onlyenv}<7->
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}[t]{.45\hsize}
  \begin{AVerb}[gobble=4,numbers=left]
    \block main(xs):
      \vbinds t1<-\mkclo[toListK1:];
      \vbinds t2<-\balt{8}{\uline{\smash{\mkclo[mapK1:]}}}{\mkclo[mapK1:]};
      \vbinds \balt{10}{\uline{\smash{\var t3/}}}{t3}<-\balt{7,9}{\uline{\smash{\app t2*t1/}}}{\app t2*t1/};
      \vbinds \balt{12}{\uline{\smash{\var t4/}}}{t4}<-\balt{11}{\uline{\smash{\app t3*xs/}}}{\app t3*xs/};
      \return t4/
    \balt{8,9}{\uline{\smash{\ccblock mapK1()f:}}}{\ccblock mapK1()f:} \balt{10}{\uline{\smash{\mkclo[mapK2:f]}}}{\mkclo[mapK2:f]}
    \balt{11}{\uline{\smash{\ccblock mapK2(f)xs:}}}{\ccblock mapK2(f)xs:} \balt{12}{\uline{\smash{\goto map(f, xs)}}}{\goto map(f, xs)}
    \block map(f, xs): \ldots
  \end{AVerb}
\end{minipage} &
\begin{onlyenv}<7-10>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
> main xs = ({-"\uline{"-}map toList{-"}"-}) xs{-"\phantom{(}"-}
\end{minipage}
\end{onlyenv}\begin{onlyenv}<11,12>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
> main xs = {-"\uline{"-}(map toList) xs{-"}"-}{-"\phantom{(}"-}
\end{minipage}
\end{onlyenv}
\end{tabular*}
\end{onlyenv}
\end{frame}

\note{I am going to walk through the previous example again, because I want
to reinforce the notion of closures and how they work. This time, I will
show graphically how closures are allocated as \lab main/ executes. This sequence
will focus on the operations that occur when each statement is executed.

In the first slide, \var t1/ has been bound to \mkclo[toListK1:] and \var t2/ has
been bound to \mkclo[mapK1:]. This aren't very interseting because they don't capture
any variables. However, they work together on Line 4, causing \lab mapK1/ to execute
and return the value \mkclo[mapK2:f].}

\begin{frame}[fragile]
\vspace{12pt}
\note<1>{After Line 1 executes, \var t1/ is bound to the closure \mkclo[toListK1:]}
\begin{minipage}{.45\hsize}
  \begin{AVerb}[gobble=4,numbers=left]
    \block main(xs):
      \buncover{1}{\vbinds t1<-\mkclo[toListK1:];}
      \buncover{1,2}{\vbinds t2<-\mkclo[mapK1:];}\anchorF(t1)
      \buncover{1-3}{\vbinds t3<-\app t2*t1/;}\anchorF(t2)
      \vbinds t4<-\app t3*xs/;\anchorF(t3)
      \return t4/
    \ccblock mapK1()f: \mkclo[mapK2:f]
    \ccblock mapK2(f)xs: \goto map(f, xs)
    \block map(f, xs): \ldots
  \end{AVerb}
\end{minipage} 

\begin{tikzpicture}[overlay, remember picture]
  \node[invis, right=1in of t1,anchor=west] (nt1) {$\left[\var t1/: \mkclo[toListK1:]\right]$};
  \path let \p1 = (nt1.west),\p2 = (t2) in node[invis,anchor=west] (nt2) at (\x1,\y2) {$\left[\var t2/: \mkclo[mapK1:]\right]$};
  \draw [->] (nt1) to (t1);
  \draw [->] (nt2) to (t2);
\end{tikzpicture}

\begin{onlyenv}<2>\begin{tikzpicture}[overlay, remember picture]
  \path let \p1 = (nt1.west),\p2 = (t3) in node[invis,anchor=west] (nt3) at (\x1,\y2) {$\left[\var t3/: \mkclo[mapK2: t1]\right]$};
  \draw [->] (nt3) to (t3);
\end{tikzpicture}
\end{onlyenv}
\end{frame}

\begin{minipage}{.45\hsize}
  \begin{AVerb}[gobble=4,numbers=left]
    \block main(xs):
      \vbinds t1<-\mkclo[toListK1:];
      \vbinds t2<-\mkclo[mapK1:];
      \vbinds t3<-\app t2*t1/;
      \vbinds t4<-\app t3*xs/;
      \return t4/
    \ccblock toListK1()x: \goto toList(x)
    \block toList(x):  
      \vbinds nil<- \prim Nil();
      \vbinds cons<- \prim Cons(x,nil);
      \return cons/
    \ccblock mapK1()f: \mkclo[mapK2:f]
    \ccblock mapK2(f)xs: \goto map(f, xs)
    \block map(f, xs): \ldots
  \end{AVerb}
\end{minipage} 

\subsection{Side-Effects}
\begin{frame}
\vspace{12pt} \ldots 
\end{frame}
\subsection{Syntax}
\begin{frame}
\vspace{12pt} \ldots
\end{frame}

\section{Dataflow Analysis}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Control-Flow Graphs \& Basic Blocks}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Facts \& Lattices}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Rewriting}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{\Hoopl}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\end{comment}

\section{Uncurrying}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Motivation}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Facts, Lattice, Transfer Function}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Example: Uncurrying in a Block}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Example: Uncurrying |map|}
%% \begin{frame}{Uncurrying}\vspace{12pt}
%%   \begin{itemize}
%%   \item Uncurrying
%%     \begin{itemize}
%%     \item Partial Application
%%     \item Uncurrying within a block (\lab toInt/ example)
%%       \begin{itemize}
%%       \item Facts
%%       \item Step-by-step Transformation of \lab main/ 
%%       \end{itemize}
%%     \item Aside: use of multiple optimizations (dead code, inlining)
%%     \item Uncurrying |map|
%%       \begin{itemize}
%%       \item Original \cfg
%%       \item Development of facts \& the \cfg
%%       \end{itemize}
%%     \end{itemize}
%%   \end{itemize}
%% \end{frame}

\begin{comment}
\begin{frame}[fragile]{Uncurrying |map|}\vspace{12pt}
  \begin{tabular}{@@{}c}
    \begin{minipage}{\hsize}\begin{centering}
> main ns = map toList ns
> map f xs = case xs of
>   Cons x xs' -> Cons (f x) (map f xs')
>   Nil -> Nil 
> toList n = Cons n Nil
    \end{centering}\end{minipage} \\
    \begin{tabular}{@@{}lr}\begin{minipage}[t]{.55\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block main(ns): 
        \vbinds v227<-\mkclo[k203:];
        \vbinds v228<-\mkclo[k219:];
        \vbinds v229<-\app v227*v228/;
        \app v229 * ns/ 
      \ccblock k219()x: \goto b220(x)
      \block b220(x):\label{uncurry_global_toList_body}
        \vbinds v221<-\mkclo[Consclo2:];
        \vbinds v222<-\app v221*x/;
        \vbinds v223<-Nil;
        \app v222 * v223/ \label{uncurry_global_toList_body_end}
    \end{AVerb}
  \end{minipage} &
  \begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left,firstnumber=last]
      \ccblock k203()f: \mkclo[k204:f]
      \ccblock k204(f)xs: \goto caseEval216(xs, f)
      \block caseEval216(xs, f): \label{uncurry_global_map_body}
        \case xs;
          \valt Nil()->\goto altNil206();
          \valt Cons(x xs)->\goto altCons208(f, x, xs);
      \block altNil206(): Nil \label{uncurry_global_map_nil}
      \block altCons208(f, x, xs): \label{uncurry_global_map_cons}
        v209 <- \mkclo[Consclo2:]
        \vbinds v210<-\app f*x/; \label{uncurry_global_map_cons_fx}
        \vbinds v211<-\app v209*v210/;
        \vbinds v212<-\mkclo[k203:]; \label{uncurry_global_map_cons_map_start}
        \vbinds v213<-\app v212*f/;
        \vbinds v214<-\app v213*xs/; \label{uncurry_global_map_cons_map_end}
        \app v211 * v214/ \label{uncurry_global_map_cons_end}
    \end{AVerb}
  \end{minipage}\end{tabular} \\
  \end{tabular}
\end{frame}
\end{comment}

\note{This example illustrates uncurrying across blocks, but not across loops. I want
  to emphasize that this example alters the \cfg in interesting ways as the analysis
  proceeds.}

\begin{frame}[fragile]
\begin{comment}
  \begin{onlyenv}<1,4->\begin{tikzpicture}[remember picture]
    \node[stmt] (main) {\block main(ns):};
    \node[stmt,below=.3in of main] (caseEval216) {\block caseEval216(xs, f):};
    \node[stmt,below left=.6in and -0.5in of caseEval216] (altNil206) {\block altNil206():};
    \node[stmt,below right=.6in and -0.7in of caseEval216] (altCons208) {\block altCons208(f, x, xs):};
    \node[stmt, below=.6in of altCons208] (b220) {\block b220(x):};

    \draw [->] (caseEval216) to (altNil206);
    \draw [->] (caseEval216) to (altCons208);
  \end{tikzpicture}\end{onlyenv}

  \begin{onlyenv}<4->\begin{tikzpicture}[remember picture, overlay]
    \node[overlay,invis,below left=.15in and -.3in of caseEval216] () {$\emptyset$};
  \end{tikzpicture}\end{onlyenv}
\end{comment}

  \begin{onlyenv}<2->
    \begin{tikzpicture}
      \node[stmt] (caseEval216) {\block caseEval216(xs, f):};
      \node[stmt,below left=.6in and -0.5in of caseEval216] (altNil206) {\block altNil206():};
      \node[stmt,below right=.6in and -0.7in of caseEval216] (altCons208) {\block altCons208(f, x, xs):};
      \draw [->] (caseEval216) to (altNil206);
      \draw [->] (caseEval216) to (altCons208);
    \end{tikzpicture}
  \end{onlyenv}

  \begin{onlyenv}<2>
    \begin{AVerb}[gobble=6,numbers=left]
      \block caseEval216(xs, f): 
        \case xs;
          \valt Nil()->\goto altNil206();
          \valt Cons(x xs)->\goto altCons208(f, x, xs);
    \end{AVerb}
  \end{onlyenv}

  \begin{onlyenv}<3>
    \begin{AVerb}[gobble=6,numbers=left]
      \block caseEval216(\uline{xs}, \uline{f}): 
        \case xs;
          \valt Nil()->\goto altNil206();
          \valt Cons(x xs)->\goto altCons208(f, x, xs);
    \end{AVerb}
  \end{onlyenv}

\begin{comment}
  \begin{onlyenv}<4>\begin{tikzpicture}[remember picture, overlay]
    \node[overlay,invis,below right=.05in and -.1in of caseEval216] () {$\begin{array}{@@{}l}
        \{\var f/\,:\,\top\}, \{\var x/\,:\,\top\},\\
        \{\var xs/\,:\,\top\}\end{array}$};
  \end{tikzpicture}\end{onlyenv}

  \begin{onlyenv}<5>\begin{tikzpicture}[remember picture, overlay]
    \node[overlay,invis,below right=.07in and -.2in of main] () { $\{\var xs/\,:\,\top\}, \{\var f/\,:\,\mkclo[k219:]\unskip\}$};
    \node[overlay,invis,below right=.05in and -.1in of caseEval216] () {$\begin{array}{@@{}l}
        \{\var f/\,:\,\mkclo[k219:]\unskip\}, \{\var x/\,:\,\top\}, \\
        \{\var xs/\,:\,\top\}\end{array}$};

    \draw [->] (main) to (caseEval216);
  \end{tikzpicture}\end{onlyenv}
\end{comment}
\end{frame}

\begin{comment}
\begin{frame}[fragile]{Uncurrying |map|}\vspace{12pt}
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
\end{comment}

\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Example: Uncurrying a loop}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Related Work: Appel, Tarditi, Tolmach \& Oliva}
\begin{frame}\vspace{12pt} \ldots
\end{frame}

\begin{comment}

  \section{Conclusion}
  \begin{frame}\vspace{12pt} \ldots
  \end{frame}
  \subsection{Monadic  Optimizations}
  \begin{frame}\vspace{12pt} \ldots
  \end{frame}
  \subsection{Future Work}
  \begin{frame}\vspace{12pt} \ldots
  \end{frame}

\end{comment}

%% \subsection{Monadic Effects}

%% \subsection{Tails}

%% \subsection{Compilation}
%% %   \item Definition of |map|
%% \begin{frame}\vspace{12pt}
%% \begin{minipage}[t]{\hsize}\elimdisplayskip
%% > map :: (a -> b) -> [a] -> [b]{-"\phantom{(}"-}
%% > map f xs = case xs of
%% >   (x:xs') -> map (f x) xs'
%% >   [] -> []
%% >
%% > toList :: a -> [a]
%% > toList x = [x]
%% \end{minipage}
%% \end{frame}

%% \begin{frame}{Evaluating |map| (call-by-value)}\vspace{12pt}
%%   %  \item Evaluating |map| using call-by-value: |map toList [1,2,3]|
%%   \begin{onlyenv}<1>
%% > map toList [1,2] = case [1,2] of {-"\hfill\text{\it Definition of \mfun{map}.}"-}
%% >   (x:xs') -> toList x : map f xs'
%% >   [] -> []
%%   \end{onlyenv}

%%   \begin{onlyenv}<2>
%% > {-"\dots"-} = toList 1 : map f [2] {-"\hfill\text{\it ``Cons'' arm of \mfun{map}.}"-}
%%   \end{onlyenv}

%%   \begin{onlyenv}<3>
%% > {-"\dots"-} = [1] : map f [2] {-"\hfill\text{\it Definition of \mfun{toList}.}"-}
%%   \end{onlyenv}

%%   \begin{onlyenv}<4>
%% > {-"\dots"-} = [1] : case [2] of {-"\hfill\text{\it Definition of \mfun{map}.}"-}
%% >   (x:xs') -> toList x : map f xs'
%% >   [] -> []
%%   \end{onlyenv}

%%   \begin{onlyenv}<5>
%% > {-"\dots"-} = [1] : toList 2 : map f [] {-"\hfill\text{\it ``Cons'' arm of \mfun{map}.}"-}
%%   \end{onlyenv}

%%   \begin{onlyenv}<6>
%% > {-"\dots"-} = [1] : [2] : map f [] {-"\hfill\text{\it Definition of \mfun{toList}.}"-}
%%   \end{onlyenv}


%%   \begin{onlyenv}<7>
%% > {-"\dots"-} = [1] : [2] : case [] of {-"\hfill\text{\it Definition of \mfun{map}.}"-}
%% >   (x:xs') -> toList x : map f xs'
%% >   [] -> []
%%   \end{onlyenv}

%%   \begin{onlyenv}<8>
%% > {-"\dots"-} = [1] : [2] : [] {-"\hfill\text{\it ``Nil'' arm of \mfun{map}.}"-}
%%   \end{onlyenv}


%%   \begin{onlyenv}<9>
%% > {-"\dots"-} = [[1],[2]] {-"\hfill\text{\it Syntatic sugar.}"-}
%%   \end{onlyenv}

%%   %% \begin{itemize}
%%   %% \item Closures
%%   %% \end{itemize}
%% \end{frame}

%% \subsection{Hidden Effects in |toList|}
%% \begin{frame}\vspace{12pt}
%%   \frametitle<1>{Definition of |toList|}
%%   \begin{onlyenv}<1>
%% > toList :: a -> [a]
%% > toList x = [x] {-"\vphantom{\fbox{\mfun{Cons}}}"-}
%%   \end{onlyenv}

%%   \frametitle<2>{Removing Syntatic Sugar \ldots}
%%   \begin{onlyenv}<2>
%% > toList :: a -> [a]
%% > toList x = Cons x Nil {-"\vphantom{\fbox{\mfun{Cons}}}"-}
%%   \end{onlyenv}

%%   \frametitle<3>{Allocation!}
%%   \begin{onlyenv}<3>
%% > toList :: a -> [a]
%% > toList x = {-"\fbox{\ensuremath{"-}Cons x Nil{-"}}"-}
%%   \end{onlyenv}

%%   \frametitle<4>{Allocation!}
%%   \begin{onlyenv}<4>
%% > toList :: a -> [a]{-"\mathllap{\xout{\phantom{"-}[a]{-"}}}"-}
%% > toList x = {-"\fbox{\ensuremath{"-}Cons x Nil{-"}}"-}
%%   \end{onlyenv}

%%   \frametitle<5>{The real type of |toList|.}
%%   \begin{onlyenv}<5>
%% > toList :: a -> M [a]
%% > toList x = {-"\dots\phantom{\fbox{\ensuremath{"-}Cons x Nil{-"}}}"-}
%%   \end{onlyenv}

%%   \frametitle<6>{A monadic |toList|}
%%   \begin{onlyenv}<6>
%% > toList :: a -> M [a]
%% > toList x = do {-"\phantom{\fbox{\ensuremath{"-}Cons x Nil{-"}}}"-}
%% >   nil <- mkData Nil
%% >   cons <- mkData Cons x nil
%% >   return cons
%%   \end{onlyenv}
  
%% \end{frame}

%% \begin{frame}\vspace{12pt}
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
%% \end{frame}

%% \section{Dataflow Analysis}
%% \begin{frame}{Dataflow Analysis}\vspace{12pt}
%%   \begin{itemize}
%%   \item Control-Flow Graphs
%%   \item Basic Blocks
%%   \item Example Program \& Constant Propagation
%%   \item Facts and the Transfer Function
%%   \end{itemize}
  
%%   \begin{itemize}
%%   \item Hoopl
%%   \item Used in GHC
%%   \item Interleaved Analysis \& Rewriting
%%   \end{itemize}

%% \end{frame}

\end{document}
