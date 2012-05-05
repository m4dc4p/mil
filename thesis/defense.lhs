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
%\setbeamersize{text margin left=1.5em}
\usepackage{verbatim}
\AtBeginEnvironment{hscode}{\abovedisplayshortskip=0in%
  \abovedisplayskip=0in%
  \belowdisplayshortskip=0in%
  \belowdisplayskip=0in%
  \parskip=0pt}
\renewcommand{\hsnewpar}[1]{\parskip=0pt\parindent=0pt\par\noindent}
\def\hsline#1{\uline{\smash{#1}}}
\def\altline<#1>#2{\alt<#1>{\hsline{#2}}{#2}}
\def\inred{\color{red}}
\def\inL(#1){\ensuremath{\mfun{in}(\lab #1/)}}
\def\outL(#1){\ensuremath{\mfun{out}(\lab #1/)}}
\def\fct(#1:#2){\ensuremath{\{\var #1/\text{\,:\,}#2\unskip\}}}
\let\elimdisplayskip\relax
\newtoks\hstoks
\begin{document}\nomd\numbersoff

\begin{comment}
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
\note{The following sequence illustrates how I can turn a recursive
  call into a loop. I start by showing the definition of the program,
  then talk through the translation of each block. I want to build up
  the \cfg in pieces. The first slide shows the entire program. The next
shows the \mil block for \lab main/. }

\begin{frame}[fragile]{Uncurrying |map|}

\begin{onlyenv}<1-3>\begin{uncoverenv}<3>\begin{tikzpicture}
  \node[stmt] (main1) {\block main(ns):};
\end{tikzpicture}\end{uncoverenv}\end{onlyenv}

\note<2>{I point out that \lab main/ doesn't call any blocks, so
  therefore its \cfg node doesn't connect to anything.}

\begin{onlyenv}<1-3>
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}[t]{.5\hsize}
> {-"\altline<2,3>{"-}main ns{-"}"-} = map toList ns
> map f xs = case xs of
>   Cons x xs' -> 
>     Cons (f x) (map f xs')
>   Nil -> Nil 
> toList n = Cons n Nil
\end{minipage} & \begin{uncoverenv}<2-3>\begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block main(ns): 
        \vbinds v227<-\mkclo[k203:];
        \vbinds v228<-\mkclo[k219:];
        \vbinds v229<-\app v227*v228/;
        \app v229 * ns/ 
    \end{AVerb}
  \end{minipage}\end{uncoverenv}
\end{tabular*}
\end{onlyenv}

\note<3>{I do the same for \lab toList/.}

\begin{onlyenv}<4,5>\begin{uncoverenv}<5>\begin{tikzpicture}
  \node[stmt] (toList1) {\block toList(x):};
\end{tikzpicture}\end{uncoverenv}\end{onlyenv}

\begin{onlyenv}<4,5>
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}[t]{.5\hsize}
> main ns = map toList ns
> map f xs = case xs of
>   Cons x xs' -> 
>     Cons (f x) (map f xs')
>   Nil -> Nil 
> {-"\hsline{"-}toList n{-"}"-} = Cons n Nil
\end{minipage}& \begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block toList(x):
        \vbinds v221<-\mkclo[Consclo2:];
        \vbinds v222<-\app v221*x/;
        \vbinds v223<-Nil;
        \app v222 * v223/ 
    \end{AVerb}
  \end{minipage}
\end{tabular*}
\end{onlyenv} 

\note<5>{Since \lab map/ is pretty complicated, I reveal it
  in pieces. I start by looking at \lab map/ and showing that
  it calls two blocks, \lab nil/ and \lab cons/.}

\begin{onlyenv}<6-9>\begin{uncoverenv}<7-9>\begin{tikzpicture}
  \node[stmt] (map1) {\block map(f,xs):};
  \node[stmt,right=.3in of map1] (cons1) {\block cons(f, x, xs):};
  \node[stmt,left=.3in of map1] (nil1) {\block nil():};
  \draw [->] (map1) to (nil1);
  \draw [->] (map1) to (cons1);
\end{tikzpicture}\end{uncoverenv}\end{onlyenv}

\note<7>{\lab cons/ and \lab nil/ don't have any successors, so I 
go through them pretty quickly.}

\note<9>{Now I reveal the (initial) \cfg for the entire program. I note that
our compiler produces pretty bad code that doesn't take advantage of
obvious connectinos, such as between \lab cons/ and \lab map/, or between
\lab cons/ and \lab toList/.}

\begin{onlyenv}<6-9>
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}[t]{.5\hsize}
> main ns = map toList ns
> {-"\altline<6,7>{"-}map f xs{-"}"-} = case xs of
>   Cons x xs' -> 
>     {-"\altline<8>{"-}Cons (f x) (map f xs'){-"}"-}
>   Nil -> {-"\altline<9>{"-}Nil{-"}"-}
> toList n = Cons n Nil
\end{minipage} & \begin{onlyenv}<6,7>\begin{minipage}[t]{.4\hsize}
  \begin{AVerb}[gobble=6,numbers=left]
      \block map(f,xs): 
        \case xs;
          \valt Nil()->\goto nil();
          Cons x xs -> 
            \goto cons(f, x, xs)
    \end{AVerb}
\end{minipage}\end{onlyenv}\begin{onlyenv}<8>\begin{minipage}[t]{.4\hsize}
  \begin{AVerb}[gobble=6,numbers=left]
      \block cons(f, x, xs): 
        v209 <- \mkclo[Consclo2:]
        \vbinds v210<-\app f*x/; 
        \vbinds v211<-\app v209*v210/;
        \vbinds v212<-\mkclo[k203:]; 
        \vbinds v213<-\app v212*f/;
        \vbinds v214<-\app v213*xs/; 
        \app v211 * v214/ 
    \end{AVerb}
\end{minipage}\end{onlyenv}\begin{onlyenv}<9>\begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block nil(): Nil 
    \end{AVerb}
\end{minipage}\end{onlyenv}
\end{tabular*}
\end{onlyenv}

\begin{onlyenv}<10>\begin{centering}\begin{tikzpicture}
  \node[stmt] (main2) {\block main(ns):};
  \node[stmt,below=.3in of main2] (map2) {\block map(f,xs):};
  \node[stmt,right=.3in of map2] (cons2) {\block cons(f, x, xs):};
  \node[stmt,left=.3in of map2] (nil2) {\block nil():};
  \node[stmt,above=.3in of cons2] (toList2) {\block toList(x):};
  \draw [->] (map2) to (nil2);
  \draw [->] (map2) to (cons2);
\end{tikzpicture}

> main ns = map toList ns
> map f xs = case xs of
>   Cons x xs' -> Cons (f x) (map f xs')
>   Nil -> Nil 
> toList n = Cons n Nil
\end{centering}\end{onlyenv}
\end{frame}

\note{Now that I have shown the initial \cfg, I want to populate it
 with initial facts. Since only \lab map/ has a successor, we focus
 on \lab map/ first. I'ts pretty simple --- only everything is $\top$.}

\begin{frame}
\ldots
\end{frame}
\end{comment}

\note{To proceed, I need to connect \lab main/ to \lab map/. I will go through
  uncurrying within \lab main/.}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{tikzpicture}[remember picture]
    \node[stmt] (main3) {\block main(ns):};
    \node[stmt,below=.3in of main3] (map3) {\block map(f,xs):};
    \node[stmt,right=.3in of map3] (cons3) {\block cons(f, x, xs):};
    \node[stmt,left=.3in of map3] (nil3) {\block nil():};
    \node[stmt,above=.3in of cons3] (toList3) {\block toList(x):};
    \draw [->] (map3) to (nil3);
    \draw [->] (map3) to (cons3);
  \end{tikzpicture}

  \begin{onlyenv}<1-3>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nsa)
      \vbinds v227<-\mkclo[k203:];\anchorF(v227a) 
      \vbinds v228<-\mkclo[k219:];\anchorF(v228a)
      \vbinds v229<-\app\balt{3-}{{\inred{v227}}}{v227}*v228/;\anchorF(v229a) 
      \app v229 * ns/ 
    \ccblock k203()f: \mkclo[k204:f]
    \ccblock k204(f)xs: \goto map(f,xs)
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \end{onlyenv}

  \note<1>{Our first pass through \lab main/ produces facts about \var v227/,
    \var v228/ and \var v229/.}

  \begin{onlyenv}<2>\begin{tikzpicture}[overlay,remember picture]
    \node[fact, invis, right=0.25in of nsa, anchor=west] (fvnsa3) 
         {\fct(ns:\top)};
    \draw [->] (fvnsa3) to (nsa);
    \node[fact, invis, right=0.25in of v227a, anchor=west] (fv227a3) 
         {\fct(v227:{\mkclo[k203:]})};
    \node[fact, invis, right=0.25in of v228a, anchor=west] (fv228a3) 
         {\fct(v228:{\mkclo[k219:]})};
    \node[fact, invis, right=0.25in of v229a, anchor=west] (fv229a3) 
         {\fct(v229:\top)};
    \draw [->] (fv227a3) to (v227a);
    \draw [->] (fv228a3) to (v228a);
    \draw [->] (fv229a3) to (v229a);
  \end{tikzpicture}\end{onlyenv}%%

  \note<2>{I point out that \var v229/ is $\top$, but
    we can rewrite \app v227 * v228/ based on the facts gathered. This sequence connects
  the fact we have about \var v227/ with the result returned by the \cc block.}

  \begin{onlyenv}<3>\begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nsa, anchor=west] (fvnsa4) 
         {\fct(ns:\top)};
    \draw [->] (fvnsa4) to (nsa);
    \node[fact, invis, right=0.25in of v227a, anchor=west] (fv227a4) 
         {\fct(\inred v227:{\mkclo[k203:]})};
    \node[fact, invis, right=0.25in of v228a, anchor=west] (fv228a4) 
         {\fct(v228:{\mkclo[k219:]})};
    \node[fact, invis, right=0.25in of v229a, anchor=west] (fv229a4) 
         {\fct(v229:\top)};
    \draw [->] (fv228a4) to (v228a);
    \draw [->] (fv227a4) to (v227a);
    \draw [->] (fv229a4) to (v229a);
  \end{tikzpicture}\end{onlyenv}%%

  \begin{onlyenv}<4-6>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nsb)
      \vbinds v227<-\mkclo[k203:];\anchorF(v227b) 
      \vbinds v228<-\mkclo[k219:];\anchorF(v228b) 
      \llap{\ensuremath{\rightarrow} }\balt{4,5}{\vbinds v229<-\app {\inred{\mkclo[k203:]}}*v228/;}{\vbinds v229<-\inred{\mkclo[k204:v228]};}\anchorF(v229b) 
      \app v229 * ns/
    \balt{5}{\inred\ccblock k203()f:}{\ccblock k203()f:} \balt{6}{\inred\mkclo[k204:f]}{\mkclo[k204:f]}
    \ccblock k204(f)xs: \goto map(f,xs)
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \end{onlyenv}

  \begin{onlyenv}<4-6>\begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nsb, anchor=west] (fvnsa4) 
         {\fct(ns:\top)};
    \draw [->] (fvnsa4) to (nsb);
    \node[fact, invis, right=0.25in of v227b, anchor=west] (fv227a5) 
         {\balt{4}{\fct(\inred v227:{\mkclo[k203:]})}{\fct(v227:{\mkclo[k203:]})}};
    \node[fact, invis, right=0.25in of v228b, anchor=west] (fv228a5) 
         {\fct(v228:{\mkclo[k219:]})};
    \draw [->] (fv228a5) to (v228b);
    \draw [->] (fv227a5) to (v227b);
  \end{tikzpicture}\end{onlyenv}

  \note<6>{When I rewrite line 4, I get a new fact --- \var v229/
    holds \mkclo[k204:v228]. I now step through the same sequence as before,
    using the new fact to rewrite line 5.}
  \begin{onlyenv}<7,8>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nsc)
      \vbinds v227<-\mkclo[k203:];\anchorF(v227c)
      \vbinds v228<-\mkclo[k219:];\anchorF(v228c)
      \vbinds v229<-\mkclo[k204:v228];\anchorF(v229c)
      \app\balt{8}{{\inred{v229}}}{v229} * ns/
    \ccblock k203()f: \mkclo[k204:f]
    \ccblock k204(f)xs: \goto map(f,xs)
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \end{onlyenv}

  \begin{onlyenv}<7>\begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nsc, anchor=west] (fvnsa6) {\fct(ns:\top)};
    \draw [->] (fvnsa6) to (nsc);
    \node[fact, invis, right=0.25in of v227c, anchor=west] (fv227a6) 
         {\fct(v227:{\mkclo[k203:]})};
    \node[fact, invis, right=0.25in of v228c, anchor=west] (fv228a6) 
         {\fct(v228:{\mkclo[k219:]})};
    \node[fact, invis, right=0.25in of v229c, anchor=west] (fv229a6) 
         {\fct(v229:{\mkclo[k204:v228]})};
    \draw [->] (fv227a6) to (v227c);
    \draw [->] (fv228a6) to (v228c);
    \draw [->] (fv229a6) to (v229c);
  \end{tikzpicture}\end{onlyenv}

  \begin{onlyenv}<8>\begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nsc, anchor=west] (fvnsa7) {\fct(ns:\top)};
    \draw [->] (fvnsa7) to (nsc);
    \node[fact, invis, right=0.25in of v227c, anchor=west] (fv227a7) 
         {\fct(v227:{\mkclo[k203:]})};
    \node[fact, invis, right=0.25in of v228c, anchor=west] (fv228a7) 
         {\fct(v228:{\mkclo[k219:]})};
    \node[fact, invis, right=0.25in of v229c, anchor=west] (fv229a7) 
         {\fct(\inred v229:{\mkclo[k204:v228]})};
    \draw [->] (fv227a7) to (v227c);
    \draw [->] (fv228a7) to (v228c);
    \draw [->] (fv229a7) to (v229c);
  \end{tikzpicture}\end{onlyenv}

  \begin{onlyenv}<9,10>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nsd)
      \vbinds v227<-\mkclo[k203:];\anchorF(v227d)
      \vbinds v228<-\mkclo[k219:];\anchorF(v228d)
      \vbinds v229<-\mkclo[k204:v228];\anchorF(v229d)
      \app {\inred\mkclo[k204:v228]} * ns/
    \ccblock k203()f: \mkclo[k204:f]
    \balt{10}{{\inred\ccblock k204(f)xs: \goto map(f,xs)}}{\ccblock k204(f)xs: \goto map(f,xs)}
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \end{onlyenv}

  \begin{onlyenv}<9,10>\begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nsd, anchor=west] (fvnsa11) {\fct(ns:\top)};
    \draw [->] (fvnsa11) to (nsd);
    \node[fact, invis, right=0.25in of v227d, anchor=west] (fv227a11) 
         {\fct(v227:{\mkclo[k203:]})};
    \node[fact, invis, right=0.25in of v228d, anchor=west] (fv228a11) 
         {\fct(v228:{\mkclo[k219:]})};
    \node[fact, invis, right=0.25in of v229d, anchor=west] (fv229a11) 
         {\fct(v229:{\mkclo[k204:v228]})};
    \draw [->] (fv227a11) to (v227d);
    \draw [->] (fv228a11) to (v228d);
    \draw [->] (fv229a11) to (v229d);
  \end{tikzpicture}\end{onlyenv}

  \note<11>{With line 5 rewritten, the \cfg for the program changes.  \lab main/
    now connects to \lab map/. 

    Before moving on, I also point out that lines 2 and 4 are now
    dead, because \var 227/ and \var 229/ are no longer referenced and
    we can delete them. I explain that dead-code elimination is really
    a separate pass in the implementation, but the net result is the
    same.}
  \begin{onlyenv}<11-13>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nse)
      \balt{13}{\xout{\vbinds v227<-\mkclo[k203:];}}{\vbinds v227<-\mkclo[k203:];}\anchorF(v227e)
      \vbinds v228<-\mkclo[k219:];\anchorF(v228e)
      \balt{13}{\xout{\vbinds v229<-\mkclo[k204:v228];}}{\vbinds v229<-\mkclo[k204:v228];}\anchorF(v229e)
      \balt{11}{\inred\goto map(v228, ns)}{\goto map(v228, ns)}
    \ccblock k203()f: \mkclo[k204:f]
    \ccblock k204(f)xs: \balt{11}{\inred\goto map(f,xs)}{\goto map(f,xs)}
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \end{onlyenv}

  \begin{onlyenv}<11,12>\begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nse, anchor=west] (fvnsa8) {\fct(ns:\top)};
    \draw [->] (fvnsa8) to (nse);
    \node[fact, invis, right=0.25in of v227e, anchor=west] (fv227a8) 
         {\fct(v227:{\mkclo[k203:]})};
    \node[fact, invis, right=0.25in of v228e, anchor=west] (fv228a8) 
         {\fct(v228:{\mkclo[k219:]})};
    \node[fact, invis, right=0.25in of v229e, anchor=west] (fv229a8) 
         {\fct(v229:{\mkclo[k204:v228]})};
    \draw [->] (fv227a8) to (v227e);
    \draw [->] (fv228a8) to (v228e);
    \draw [->] (fv229a8) to (v229e);
  \end{tikzpicture}\end{onlyenv}

  \begin{onlyenv}<12>\begin{tikzpicture}[overlay, remember picture]
    \draw[color=red] [->] (main3) to (map3);
  \end{tikzpicture}\end{onlyenv}

  \begin{onlyenv}<13>\begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nse, anchor=west] (fvnsa9) {\fct(ns:\top)};
    \draw [->] (fvnsa9) to (nse);
    \node[fact, invis, right=0.25in of v228e, anchor=west] (fv228a9) {\fct(v228:{\mkclo[k219:]})};
    \draw [->] (fv228a9) to (v228e);
    \draw [->] (main3) to (map3);
  \end{tikzpicture}\end{onlyenv}

  \begin{onlyenv}<14>
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block main(ns): \anchorF(nsf)
        \vbinds v228<-\mkclo[k219:];\anchorF(v228f)
        \goto map(v228, ns)
    \ccblock k203()f: \mkclo[k204:f]
    \ccblock k204(f)xs: \goto map(f,xs)
    \ccblock k219()x: \goto toList(x)
    \end{AVerb}
  \end{onlyenv}

  \begin{onlyenv}<14>\begin{tikzpicture}[overlay,remember picture]
    \node[fact, invis, right=0.25in of nsf, anchor=west] (fvnsa10) {\fct(ns:\top)};
    \draw [->] (fvnsa10) to (nsf);
    \node[fact, invis, right=0.25in of v228f, anchor=west] (fv228a10) {\fct(v228:{\mkclo[k219:]})};
    \draw [->] (fv228a10) to (v228f);
    \draw [->] (main3) to (map3);
  \end{tikzpicture}
  \end{onlyenv}
\end{frame}

\note{I return to the \cfg, keeping \lab main/ on the screen, and show
  updated facts.}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{onlyenv}<1,2>
  \begin{tikzpicture}[remember picture]
    \node[stmt] (main4) {\block main(ns):};
    \node[stmt,below=.3in of main4] (map4) {\block map(f,xs):};
    \node[stmt,right=.3in of map4] (cons4) {\block cons(f, x, xs):};
    \node[stmt,left=.3in of map4] (nil4) {\block nil():};
    \node[stmt,above=.3in of cons4] (toList4) {\block toList(x):};

    \node[overlay,invis,below right=.07in and -.2in of main4] () 
         {\inL(map): \fct(f:{\mkclo[k219:]}), \fct(xs:\top)};

    \draw [->] (map4) to (nil4);
    \draw [->] (map4) to (cons4);
    \draw [->] (main4) to (map4);
  \end{tikzpicture}
  \end{onlyenv}
  \begin{onlyenv}<1>
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block main(ns): \anchorF(nsb1)
        \vbinds v228<-\mkclo[k219:]; \anchorF(v228b1)
        \goto map(v228, ns)
      \ccblock k203()f: \mkclo[k204:f]
      \ccblock k204(f)xs: \goto map(f,xs)
      \ccblock k219()x: \goto toList(x)
    \end{AVerb}
  \end{onlyenv}

  \note<1>{Now I show \lab map/. I annotate the two locations that
    generate facts --- the arguments to the block, and the 
    case statement.}
  \begin{onlyenv}<2>
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block map(f,xs): \anchorF(mapb1)
        \case xs;
          \valt Nil()->\goto nil(); 
          \valt Cons(\uline{x \anchorF(xb1)xs})->\goto cons(f, x, xs); 
    \end{AVerb}

    \begin{tikzpicture}[remember picture,overlay]
      \node[fact, invis, anchor=west] (fvmapb1) at ($(mapb1) + (0.25in,-0.1in)$) 
           {\fct(f:{\mkclo[k219:]}), \fct(xs:\top)};
      \node[fact, invis, anchor=west] (fvxb1) at ($(xb1) + (.25in,-.2in)$) 
           {\fct(x:\top), \fct(xs:\top)};
      \draw [->] (fvmapb1.west) to (mapb1);
      \draw [->] (fvxb1.west) to ($(xb1) -(0in,0.1in)$);
    \end{tikzpicture}
  \end{onlyenv}

  \note<2>{Now I show how in(cons) and in(nil) are generated from the facts
    passed through \lab map/. I emphasize that \var xs/ is actually new, and not
  the same \var xs/ passed in from \lab map/. I also talk about why \lab nil/
  gets no facts, because it takes no arguments.}

  \begin{onlyenv}<3>
    \begin{tikzpicture}
      \node[stmt] (main5) {\block main(ns):};
      \node[stmt,below=.3in of main5] (map5) {\block map(f,xs):};
      \node[stmt,right=.3in of map5] (cons5) {\block cons(f, x, xs):};
      \node[stmt,left=.3in of map5] (nil5) {\block nil():};
      \node[stmt,above=.3in of cons5] (toList5) {\block toList(x):};

      \node[overlay,invis,below right=.07in and -.2in of main5] () 
           {\inL(map): \fct(f:{\,\mkclo[k219:]}), \fct(x:\top)};

      \node[invis,below left=0.07in and -0.25in of cons5, anchor=north] () 
           {\inL(cons): \fct(\inred f:{\mkclo[k219:]}),
             \fct(\inred x:\top),
             \fct(\inred xs:\top)};
      
      \node[fact, invis, below left=0.07in and -.2in of main5] () {$\inL(nil)\text{:\ }\emptyset$};

      \draw [->] (map5) to (nil5);
      \draw [->] (map5) to (cons5);
      \draw [->] (main5) to (map5);
    \end{tikzpicture}
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block map(f,xs): \anchorF(mapb2)
        \case xs;
          \valt Nil()->\goto nil(); 
          \valt Cons(\uline{x \anchorF(xb2)xs})->\goto cons(f, x, xs); 
    \end{AVerb}
    \begin{tikzpicture}[remember picture,overlay]
      \node[fact, invis, anchor=west] (fvmapb2) at ($(mapb2) + (0.25in,-0.1in)$) 
           {\fct(\inred f:{\mkclo[k219:]}), \fct(xs:\top)};
      \node[fact, invis, anchor=west] (fvxb2) at ($(xb2) + (.25in,-.2in)$) 
           {\fct(\inred x:\top), \fct(\inred xs:\top)};
      \draw [->] (fvmapb2.west) to (mapb2);
      \draw [->] (fvxb2.west) to ($(xb2) -(0in,0.1in)$);
    \end{tikzpicture}
  \end{onlyenv}
\end{frame}

\note{Now I can finally show how to rewrite \lab cons/. I leave the facts
  as is on screen and bring up \lab cons/.}

\begin{frame}[fragile]{Uncurrying |map|}
    \begin{tikzpicture}
      \node[stmt] (main6) {\block main(ns):};
      \node[stmt,below=.3in of main6] (map6) {\block map(f,xs):};
      \node[stmt,right=.3in of map6] (cons6) {\block cons(f, x, xs):};
      \node[stmt,left=.3in of map6] (nil6) {\block nil():};
      \node[stmt,above=.3in of cons6] (toList6) {\block toList(x):};

      \node[fact,invis,below right=.07in and -.2in of main6] () 
           {\inL(map): \fct(f:{\mkclo[k219:]}), 
             \fct(xs:\top\})};

      \node[invis,below left=0.07in and -0.25in of cons6, anchor=north] () 
           {\inL(cons): \fct(f:{\mkclo[k219:]}),
             \fct(x:\top),
             \fct(xs:\top)};
      
      \node[fact, invis, below left=0.07in and -.2in of main6] () {$\inL(nil): \emptyset$};
      \draw [->] (map6) to (nil6);
      \draw [->] (map6) to (cons6);
      \draw [->] (main6) to (map6);
    \end{tikzpicture}
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consc1)
        v209 <- \mkclo[Consclo2:] \anchorF(v209c1)
        \vbinds v210<-\app f*x/; \anchorF(v210c1)
        \vbinds v211<-\app v209*v210/; \anchorF(v211c1)
        \vbinds v212<-\mkclo[k203:];  \anchorF(v212c1)
        \vbinds v213<-\app v212*f/; \anchorF(v213c1)
        \vbinds v214<-\app v213*xs/; \anchorF(v214c1)
        \app v211 * v214/ 
    \end{AVerb}

    \begin{tikzpicture}[remember picture,overlay]
      \node[fact, invis, right=0.25in of consc1, anchor=west] (fvconsc1) {\fct(f:{\mkclo[k219:]}), \fct(x:\top), \fct(xs:\top)};
      \node[fact, invis, right=0.25in of v209c1, anchor=west] (fvv209c1) {\fct(v209:\top)};
      \node[fact, invis, right=0.25in of v210c1, anchor=west] (fvv210c1) {\fct(v210:\top)};
      \node[fact, invis, right=0.25in of v211c1, anchor=west] (fvv211c1) {\fct(v211:\top)};
      \node[fact, invis, right=0.25in of v212c1, anchor=west] (fvv212c1) {\fct(v212:\top)};
      \node[fact, invis, right=0.25in of v213c1, anchor=west] (fvv213c1) {\fct(v213:\top)};
      \node[fact, invis, right=0.25in of v214c1, anchor=west] (fvv214c1) {\fct(v214:\top)};

      \draw [->] (fvconsc1) to (consc1);
      \draw [->] (fvv209c1) to (v209c1);
      \draw [->] (fvv210c1) to (v210c1);
      \draw [->] (fvv211c1) to (v211c1);
      \draw [->] (fvv212c1) to (v212c1);
      \draw [->] (fvv213c1) to (v213c1);
      \draw [->] (fvv214c1) to (v214c1);
    \end{tikzpicture}
  
\end{frame}

\begin{comment}
    %% \node[overlay,invis,below=.05in of cons4] () {\inL(cons):$\begin{array}{@@{}l}
    %%     \{\var f/\,:\,\top\}, \{\var x/\,:\,\top\},\\
    %%     \{\var xs/\,:\,\top\}\end{array}$};

  %% \begin{onlyenv}<1->\begin{tikzpicture}[overlay,remember picture]
  %%   \node[fact, right=0.25in of nsb1, anchor=west] (fvnsb1) {$\{\var ns/\,:\,\top\}$};
  %%   \draw [->] (fvnsb1) to (nsb);
  %%   \node[fact, right=0.25in of v228b1, anchor=west] (fv228b1) {$\{\var v228/\,:\,\mkclo[k219:]\unskip\}$};
  %%   \draw [->] (fv228b1) to (v228b1);
  %% \end{tikzpicture}
  \begin{onlyenv}<4->\begin{tikzpicture}[remember picture, overlay]
    \node[overlay,invis,below left=.15in and -.3in of caseEval216] () {$\emptyset$};
  \end{tikzpicture}\end{onlyenv}
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


    \begin{AVerb}[gobble=6,numbers=left]
      \block main(ns): 
        \vbinds v227<-\mkclo[k203:];
        \vbinds v228<-\mkclo[k219:];
        \vbinds v229<-\app v227*v228/;
        \app v229 * ns/ 
      \ccblock k219()x: \goto toList(x)
      \block toList(x):
        \vbinds v221<-\mkclo[Consclo2:];
        \vbinds v222<-\app v221*x/;
        \vbinds v223<-Nil;
        \app v222 * v223/ 
    \end{AVerb}
  \end{minipage} &
  \begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left,firstnumber=last]
      \ccblock k203()f: \mkclo[k204:f]
      \ccblock k204(f)xs: \goto map(f,xs)
      \block map(f,xs): 
        \case xs;
          \valt Nil()->\goto nil();
          \valt Cons(x xs)->\goto cons(f, x, xs);
      \block nil(): Nil 
      \block cons(f, x, xs): 
        v209 <- \mkclo[Consclo2:]
        \vbinds v210<-\app f*x/; 
        \vbinds v211<-\app v209*v210/;
        \vbinds v212<-\mkclo[k203:]; 
        \vbinds v213<-\app v212*f/;
        \vbinds v214<-\app v213*xs/; 
        \app v211 * v214/ 
    \end{AVerb}
\end{comment}


\begin{comment}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Example: Uncurrying a loop}
\begin{frame}\vspace{12pt} \ldots
\end{frame}
\subsection{Related Work: Appel, Tarditi, Tolmach \& Oliva}
\begin{frame}\vspace{12pt} \ldots
\end{frame}

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
