%&Pre_defense
\makeatletter\@@ifundefined{preambleloaded}{\input{pre_defense}}{}\makeatother
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\author[Justin Bailey]{Justin Bailey \\ \texttt{jgbailey@@codeslower.com}}
\institute{Portland State University}
\title{Using Dataflow Optimization Techniques with a Monadic Intermediate Language}
\date{\today}%\setbeameroption{show notes}
\begin{document}\nomd\numbersoff

\setbeamertemplate{navigation symbols}{}
\makeatletter\begin{frame}[plain]
\vfill\hbox{\kern-.5\beamer@@leftsidebar\vbox{\titlepage}}\vfill
\end{frame}\makeatother

%%\begin{comment}
\section{Introduction}
\begin{frame}{Introduction}
  \begin{itemize}
  \item Compiling Functional Programming Languages
  \item Dataflow Analysis
  \item Three-Address Code
  \end{itemize}
\end{frame}
\begin{frame}{Dataflow Analysis for Functional Languages?}
  \begin{itemize}
  \item Can we apply functional-language specific optimizations?
  \item Can we implement traditional dataflow-based optimizations?
  \end{itemize}
\end{frame}

\begin{frame}{Monadic Programming to the Rescue!}
  \begin{itemize}
  \item Simple control-flow
  \item Separate side-effecting computation from ``pure'' values
  \item Higher-order functions
  \end{itemize}
\end{frame}

\begin{frame}{\Mil: A Monadic Intermediate Language}
  \begin{itemize}
  \item Monadic: Haskell's |do| notation.
  \item Monadic: Segregated side-effects. 
  \item Dataflow: Basic blocks.
  \item Dataflow: Block scope.
  \item Dataflow: Based on three-address code.
  \end{itemize}
\end{frame}

\begin{frame}{Contributions}
  \begin{itemize}
  \item Applied the \emph{dataflow algorithm} to a
    functional language.
  \item Implemented \emph{uncurrying}, using the dataflow algorithm.
  \item Thorough exposition of the \hoopl library.
  \end{itemize}
\end{frame}
%%\end{comment}

%%\begin{comment}
\section{\Mil}
\subsection{Goals of \Mil}
\note{Now I want to talk about \Mil's purpose. Why a ``monadic''
  intermediate language?}
\begin{frame}{Goals of \Mil}
  \begin{itemize}
  \item Simplicity 
  \item Allocation \& Other Side-Effects
  \item Higher-Order Functions
  \end{itemize}
\end{frame}
\note{\Mil derives from Three-Address code, where every operation
  has at most two operands and one destination. I show how
  to represent a simple fraction in TLA.}
\begin{frame}[fragile]{Simplicity}
  \note<1>{Then I show how to represent the same expression using \Mil,
    showing how similar the two forms are.}
  \begin{centering}\begin{equation*}
    \frac{(b * c + d)}{2}
  \end{equation*}
  \end{centering}
  \begin{onlyenv}<2>\begin{itemize}
  \item Three-Address Code
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1em]
      t1 := b * c;
      t2 := t1 + d;
      t3 := t2 / 2;
    \end{AVerb}
  \end{itemize}\end{onlyenv}
  \begin{onlyenv}<3>\begin{itemize}
  \item \Mil
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1em]
      \vbinds t1<-\prim mul(b, c);
      \vbinds t2<-\prim add(t1, d);
      \vbinds t3<-\prim div(t2, 2);
    \end{AVerb}
  \end{itemize}\end{onlyenv}
\end{frame}
\note{\Mil separates side-effecting computation from
  pure values by placing all side-effecting operations
  in monadic \emph{tail} expressions.}
\begin{frame}[fragile]{Side-Effects}
\begin{onlyenv}<2->
    \begin{itemize}
    \item Closures\par
  \only<2->{\qquad\binds t1 <- \mkclo[k:x];}
  \only<4->{\item Data values\par}
  \only<4->{\qquad\binds t2<- Cons\ x\ xs;}
  \only<6->{\item Primitives\par}
  \only<6->{\qquad\binds t3<-\prim add(x, y);}
    \end{itemize}
\end{onlyenv}
\end{frame}

\note{\Mil is an \emph{intermediate} language, so it better be
  able to represent programs from a purely functional, statically typed
  language like Haskell or Habit. The following features mostly get us
  there. Type classes remain an unknown.}
\begin{frame}{Sufficiency}
  \begin{itemize}
  \item Higher-Order Functions
  \item Primitives 
  \item Data Values
  \end{itemize}
\end{frame}
%%\end{comment}

\begin{comment}
\subsection{Basics}
\note{I will explain \mil by example, using the program we will
  uncurry later. I show the example program which will illustrate
  various \mil features. I describe this simple program, making sure
  to note how we represent lists and the meaning of the terms |Cons|
  and |Nil|. I emphasize the data declaration and types are just for
  documentation here --- \mil is not a typed language.}

\begin{frame}[fragile]{\Mil by Example}
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}[t]{.5\hsize}
> data List a = Cons a (List a) | Nil
>
> main ns = map toList ns
> map f xs = case xs of
>   Cons x xs' -> 
>     Cons (f x) (map f xs')
>   Nil -> Nil 
> toList n = Cons n Nil
\end{minipage} 
\end{tabular*}
\end{frame}

\note{I start by showing the basic block for |main|. Every block
  starts with a label (a named location in the program). Each block
  specifies a set of arguments; those arguments are the only variables
  in scope at the beginning of the block.}

\begin{frame}[fragile]{Basic Blocks}
\note<1>{In this program \lab main/ represents a labeled location; 
  only the argument \var ns/ is in scope at the beginning of the block.}
\begin{tabular*}{\hsize}{l}
\begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block \balt{2}{\uline{main}}{main}(\balt{2}{\uline{ns}}{ns}): 
        \vbinds v227<-\mkclo[k203:];
        \vbinds v228<-\mkclo[k219:];
        \vbinds v229<-\app v227*v228/;
        \app v229 * ns/
    \end{AVerb}
  \end{minipage} \\\\ 
\begin{minipage}[t]{.5\hsize}
> main ns = map toList ns
\end{minipage}
\end{tabular*}
\end{frame}

\note{Every basic block consists of a series of
  \emph{statements}. Each statement binds a new variable on the left and
  evaluates a \term{tail} on the right.}
\begin{frame}[fragile]{Statements \& Tails}
\begin{tabular*}{\hsize}{l}
\begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block main(ns): 
        \vbinds v227<-\mkclo[k203:];\anchorF(v227g1)
        \vbinds v228<-\mkclo[k219:];\anchorF(v228g1)
        \vbinds v229<- v227\anchorF(v227l) \texttt{@@} v228\anchorF(v227r);\anchorF(v229g1)
        \app v229\anchorF(v229l) * ns\anchorF(v229r)/\anchorF(mtg1)
    \end{AVerb}
  \end{minipage} \\\\ 
\begin{minipage}[t]{.5\hsize}
> main ns = map toList ns
\end{minipage}
\end{tabular*}
\begin{onlyenv}<1>\begin{tikzpicture}[remember picture, overlay]
  \node[overlay] () at ($(v228g1) + (0.6in,0in)$) {$\left.\vphantom{
      \vcenter to 2\baselineskip{\hrule height1\baselineskip width0in depth1\baselineskip}}\right\}$
    \hbox to 0in{$\vcenter to 2\baselineskip{\vfill \it Binding \break Statements\par\vfill}$}};
\end{tikzpicture}\end{onlyenv}
\note<1>{Tails always appear on the \rhs of a binding statement,
  except at the end of a block. Tails implement side-effecting
  operations (to be described in more detail soon). Blocks end with
  either a \term{tail} term or \milres case/ statement (which we will
  see shortly).}
\begin{onlyenv}<2>\begin{tikzpicture}[remember picture, overlay]
  \node[fact,overlay, anchor=west] (fv228g1) at ($(v228g1) + (0.7in,0in)$) {\it Tails};
  \draw [->] (fv228g1) to (v227g1);
  \draw [->] (fv228g1) to (v228g1);
  \draw [->] (fv228g1) to (v229g1);
\end{tikzpicture}\end{onlyenv}
\note<2>{The tail \mkclo[k203:] creates a \emph{closure}. I define a
  closure as a data structure containing a label and an
  environment. The label indicates the block that should execute when
  the closure is ``entered''; the environment is a map from variables
  to values.  The block entered uses the environment to look up
  variables that do not appear in the block's argument list (i.e.,
  \emph{free variables}). In this case, the environment for each
  closure is empty.}
\frametitle<3>{Closures}\begin{onlyenv}<3>\begin{tikzpicture}[remember picture, overlay]
  \node[fact,overlay,text width=1in,anchor=west] (fv228g2) at ($(v228g1) + (0.7in,0in)$) {\it Closure\\ Allocation};
  \draw [->] (fv228g2) to (v227g1);
  \draw [->] (fv228g2) to (v228g1);
\end{tikzpicture}\end{onlyenv}
\note<3>{The ``enter'' operator implements function
  application. That is, the argument on the left refers to a
  closure. The function represented by the closure will be executed
  with the argument on the right.}
\frametitle<4->{Application}\begin{onlyenv}<4>\begin{tikzpicture}[remember picture, overlay]
  \node[fact,overlay,anchor=west] (fv227l1) at ($(v228g1) + (0.7in,-.5in)$) {\it Closure};
  \node[fact,overlay,anchor=west] (fv227r1) at ($(v228g1) + (0.7in,-0.25in)$) {\it Argument};
  \draw [->] (fv227l1.west) to (v227l.south west);
  \draw [->] (fv227r1.west) to (v227r.south);
\end{tikzpicture}\end{onlyenv}
\note<4>{On Line 5, we can infer that \var v229/ must be a closure value,
  because it is used in an \enter expression. As this code represents
|main|, this sequence evaluates |map toList ns|.}
\begin{onlyenv}<5>\begin{tikzpicture}[remember picture, overlay]
  \node[fact,overlay,anchor=west] (fv229l1) at ($(v228g1) + (0.7in,-.5in-\baselineskip)$) {\it Closure};
  \node[fact,overlay,anchor=west] (fv229r1) at ($(v228g1) + (0.7in,-0.25in-\baselineskip)$) {\it Argument};
  \draw [->] (fv229l1.west) to (v229l.south west);
  \draw [->] (fv229r1.west) to (v229r.south);
\end{tikzpicture}\end{onlyenv}
\end{frame}

\note{The allocations on lines 2 and 3 refer to \emph{\cc blocks}. A
  \cc block executes when a closure referring to that block is
  entered. A \cc block is always passed a closure and an argument. The
  \cc block defines the environment it expects in the closure.}

\begin{frame}[fragile]{\CC Blocks}
\begin{tabular*}{\hsize}{l}
\begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block main(ns): 
        \vbinds v227<-\mkclo[k203:];\anchorF(v227g3)
        \vbinds v228<-\mkclo[k219:];\anchorF(v228g3)
        \vbinds v229<-\app v227*v228/;\anchorF(v229g3)
        \app v229\anchorF(v229l) * ns\anchorF(v229r)/\anchorF(mtg3)

      \ccblock {k203\anchorF(k203g3)}(){\anchorF(k203eg3)f\anchorF(k203fg3)}: \mkclo[k204:f]
      \ccblock {\anchorF(k204g3)k204}(f){\anchorF(k204eg3)xs\anchorF(k204fg3)}: \ldots
      \ccblock {\anchorF(k219g3)k219}(){\anchorF(k219eg3)x\anchorF(k219xg3)}: \ldots
    \end{AVerb}
  \end{minipage} \\\\ 
\begin{minipage}[t]{.5\hsize}
> main ns = map toList ns
\end{minipage}
\end{tabular*}
\note<1>{The two tail expressions in main allocate closures that point
  to \lab k203/ and \lab k219/, respectively. Closures will only ever
  refer to \cc blocks.

  \Cc block specify the variables they expect to find in the environment
  when the block is entered. The two closures allocated have empty
  environments, as do their definitions. However, \lab k204/ expects 
  one variable, \var f/, in its environment.}
\begin{onlyenv}<2>\begin{tikzpicture}[remember picture, overlay]
  \node[fact,anchor=west, above right=.1in and 1in of k203fg3] (fvk203fg3) {\it Environment};
  \draw [->] (fvk203fg3) to (k203eg3.north west);
  \draw [->] (fvk203fg3) to (k204eg3.north west);
  \draw [->] (fvk203fg3) to (k219eg3.north west);
\end{tikzpicture}\end{onlyenv}
\end{frame}

\note{Now I want to illustrate how closures are allocated
  and used in \lab main/. \var v227/ and \var v228/ are bound
to the respective closures shown.}

\begin{frame}[fragile]{Application \& Closures}
  \begin{tabular*}{\hsize}{l}\begin{minipage}[t]{\hsize}
  \begin{AVerb}[gobble=4,numbers=left]
    \block main(ns): 
      \vbinds v227<-\mkclo[k203:];\anchorF(v227g4)
      \vbinds v228<-\mkclo[k219:];\anchorF(v228g4)
      \vbinds v229<-\app \anchorF(vapplg4)v227*\anchorF(vapprg4)v228/;\anchorF(v229g4)
      \app v229 * ns/

    \ccblock {\anchorF(k203g4)k203}(){f\anchorF(k203fg4)}: \mkclo[k204:f]\anchorF(k203tg4)
    \ccblock k204(f)xs: \balt{1-3}{\ldots}{\goto map(f, xs)}
    \ccblock k219()x: \balt{1-3}{\ldots}{\goto toList(x)}
  \end{AVerb}
  \end{minipage}\\\\ 
\begin{minipage}[t]{.5\hsize}
> main ns = map toList ns
\end{minipage}\end{tabular*}
  \begin{tikzpicture}[overlay, remember picture]
    \node[fact,right=.25in of v227g4,anchor=west] (fvv227g4) {$\left[\var v227/: \mkclo[k203:]\right]$};
    \path let \p1 = (fvv227g4.west),\p2 = (v228g4) in node[fact,anchor=west] (fvv228g4) at (\x1,\y2) {$\left[\var v228/: \mkclo[k219:]\right]$};
    \draw [->] (fvv227g4) to (v227g4);
    \draw [->] (fvv228g4) to (v228g4);
  \end{tikzpicture}
  \note<1>{When Line 4 executes, we ``enter'' the \cc block represented
    by \var v227/ (\lab k203/), with an empty environment and \var v228/
    bound to \var f/.}
  \begin{onlyenv}<2>\begin{tikzpicture}[overlay, remember picture]
    \draw [->] (vapplg4.south) to ($(k203g4) + (2em,1ex)$);
    \draw [->] (vapprg4.north) to (k203fg4);
    \end{tikzpicture}
  \end{onlyenv}
  \note<2>{Block \lab k203/ allocates a closure that points to \lab
    k204/ and that captures the argument, \var f/. The statement on
    line 4 binds \var v229/ to the closure value returned. Notice that
    the closure holds a reference to \var v228/ -- we use the local
    name of the value rather then the parameter name from the block.}
  \begin{onlyenv}<3>\begin{tikzpicture}[overlay, remember picture]
    \node[fact,right=.25in of v229g4,anchor=west] (fvv229g4) {$\left[\var v229/: \mkclo[k204:v228]\right]$};
    \draw [->] (fvv229g4) to (v229g4);
  \end{tikzpicture}\end{onlyenv}
  \note<3>{Now I reveal the body of \lab k204/ and \lab k219/. Now
    that we know what \cc block \var v229/ refers to, we can see that
    last line enters \lab k204/ and then does something new. I
    describe the syntax and meaning of ``jump'' or ``goto''
    statements.

    I note that \lab map/ and \lab toList/ are basic blocks just like
    \lab main/, meaning only the arguments passed to them are in scope
    at the beginning of each respective block.

    I also emphasize that the ``enter'' and ``jump'' statements are a
    lot like ordinary function calls, in that execution returns to the
    point from which the call was made after the block finishes
    executing.}
\end{frame}

\note{Now I can quickly show how \lab main/ implements evaluation of
  |map toList ns|.  I begin by rewriting |map toList ns| to |(map
  toList) ns|, noting that I am following a common strategy where
  multi-argument functions are treated as sequential applications of
  single-argument functions.}

\begin{frame}[fragile]{Evaluating |map toList ns|}
  \begin{tabular*}{\hsize}{l}\begin{minipage}[t]{\hsize}
  \begin{AVerb}[gobble=4,numbers=left]
    \block main(ns): 
      \vbinds v227<-\mkclo[k203:];\anchorF(v227g5)
      \vbinds v228<-\mkclo[k219:];\anchorF(v228g5)
      \vbinds v229<-\app v227*v228/;\anchorF(v229g5)
      \app v229 * ns/\anchorF(appg5)

    \ccblock k203()f: \mkclo[k204:f]\anchorF(k203tg5)
    \ccblock k204(f)xs: \goto map(f, xs)
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \end{minipage}\\\\ 
\begin{minipage}[t]{.5\hsize}
> main ns = ((map toList) ns)
\end{minipage}\end{tabular*}
\note<1>{In the following sequence I show how each line of \lab main/
  relates to an expression in the original program. At the end
  of the block, we've evaluated |map toList ns|!}
\begin{onlyenv}<2->\begin{tikzpicture}[remember picture, overlay]
  \node[fact,right=.25in of v227g5] (fv227g5) {|map|};
  \draw [->] (fv227g5) to (v227g5);
\end{tikzpicture}\end{onlyenv}\begin{onlyenv}<3->\begin{tikzpicture}[remember picture, overlay]
  \node[fact,right=.25in of v228g5] (fv228g5) {|toList|};
  \draw [->] (fv228g5) to (v228g5);
\end{tikzpicture}\end{onlyenv}
\begin{onlyenv}<4->\begin{tikzpicture}[remember picture, overlay]
  \node[fact,right=.25in of v229g5] (fv229g5) {|(map toList)|};
  \draw [->] (fv229g5) to (v229g5);
\end{tikzpicture}\end{onlyenv}
\begin{onlyenv}<5->\begin{tikzpicture}[remember picture, overlay]
  \node[fact,right=.25in of appg5] (fvappg5) {|((map toList) ns)|};
  \draw [->] (fvappg5) to (appg5);
\end{tikzpicture}\end{onlyenv}
\end{frame}

\note{Returning to the full example, I want to talk about the |map|
  function now; in particular, its use of the \milres case/
  statement. The case statement implements conditional branching
  in \mil.}
\begin{frame}[fragile]{Conditionals}
  \begin{tabular*}{\hsize}{l}\begin{minipage}[t]{\hsize}
  \begin{AVerb}[gobble=4,numbers=left]
    \block map(f, xs):
      \case xs\anchorF(disch1);
        \valt {Nil\anchorF(consh1)}()->\goto nil();\anchorF(alth1)
        \valt {Cons\anchorF(consh2)}(x xs)->\goto cons(f, x, xs);\anchorF(alth2)
    \end{AVerb}
  \end{minipage}\\\\ 
\begin{minipage}[t]{.5\hsize}
> map f xs = case xs of
>   Cons x xs' -> 
>     Cons (f x) (map f xs')
>   Nil -> Nil 
\end{minipage}\end{tabular*}
\note<1>{The \milres case/ statement examines its \emph{discriminant}
  (\var xs/ in this case) and compares the \emph{constructor} value
  found there to all \emph{alternatives} given. The first matching
  alternative will be executed. Alternatives always jump to another
  block; therefore, the block specified by the first matching
  alternative will be executed.}
\begin{onlyenv}<2>\begin{tikzpicture}[remember picture, overlay]
  \node[fact,above right=.2in and .5in of disch1, anchor=west] (fvdisch1) {\it Discriminant};
  \draw [->] (fvdisch1) to (disch1);
\end{tikzpicture}\end{onlyenv}
\begin{onlyenv}<3>\begin{tikzpicture}[remember picture, overlay]
  \node[fact,above right=.2in and .25in of disch1, anchor=west] (fvconsh1) {\it Constructors};
  \node[fact,above right=.1in and .25in of alth2, anchor=west] (fvalth1) {\it Alternatives};
  \draw [->] (fvconsh1) to (consh1);
  \draw [->] (fvconsh1) to (consh2);
  \draw [->] (fvalth1) to (alth1);
  \draw [->] (fvalth1) to (alth2);
\end{tikzpicture}\end{onlyenv}
\end{frame}
\end{comment}

%%\begin{comment}
\subsection{Related Work}
\begin{frame}{Related Work}
  \begin{itemize}
  \item \Mlj: Benton, Kennedy, \& Russell\footnote{``Compiling Standard ML to Java Bytecodes'' (1998).}
  \item Continuation-Passing Style\footnote{See Appel's ``Compiling with Continuations'' (1992).}
  \item Administrative-Normal Form: Flanagan, Sabry, Duba, and Felleisen\footnote{``The Essence of Compiling with Continuations'' (1993).}
  \end{itemize}
\end{frame}

\section{Dataflow Analysis}
\begin{frame}{Dataflow Analysis}
  \begin{itemize}
  \item Due to Kildall's ``A Unified Approach to Global Program Optimization'' (1973)
  \item Widely applied to imperative programming languages
  \end{itemize}
\end{frame}
\begin{frame}{Typical Dataflow Optimizations}
  \begin{itemize}
  \item Dead-code Elimination
  \item Constant Folding
  \item Lazy Code Motion
  \item For more, see Muchnick's ``Advanced compiler design and implementation'' (1997)
  \end{itemize}
\end{frame}
\subsection{Fundamentals}
\note{I give an abbreviated \mil program and its associated \cfg. I give
the definition of a ``basic block,'' as well.}
\begin{frame}[fragile]{Fundamentals: \Cfg{}s \& Basic Blocks}
  \hfil\begin{tikzpicture}
  \node[stmt] (b1) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b1():
        \vbinds f<-\mkclo[k1:];
        \vbinds g<-\mkclo[k3:];
        \goto b2(f, g)
    \end{AVerb}
  \end{minipage}};
  \node[stmt, below=.2in of b1] (b2) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b2 (f, g):
        \dots
        \goto b3(t, u, f)
    \end{AVerb}
    \end{minipage}};
  \node[stmt, below=.2in of b2] (b3) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b3 (t, u, f):
        \dots
        \goto b2(f, w)
    \end{AVerb}
    \end{minipage}};
    \draw [->] (b1) to (b2);
    \draw [->] (b2) to (b3);
    \draw [->] (b3.south) to ($(b3.south) + (0mm, -.25in)$) -|| ($(b2.west) + (-.25in, 0mm)$) to (b2.west);
  \end{tikzpicture}
\end{frame}
\note{Now I add some facts to the \cfg. I talk about in facts and out facts. I show
how the in facts from \lab b1/ propagate to \lab b2/.}
\begin{frame}[fragile]{Facts}
  \hfil\begin{tikzpicture}
  \node[stmt] (b1) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b1():
        \vbinds f<-\mkclo[k1:];
        \vbinds g<-\mkclo[k3:];
        \goto b2(f, g)
    \end{AVerb}
  \end{minipage}};
  \node[stmt, below=.2in of b1] (b2) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b2 (f, g):
        \dots
        \goto b3(t, u, f)
    \end{AVerb}
    \end{minipage}};
  \node[stmt, below=.2in of b2] (b3) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b3 (t, u, f):
        \dots
        \goto b2(f, w)
    \end{AVerb}
    \end{minipage}};
    \node[invis,overlay,right=.1in of b1,text width=1.5in] () {\outL(b1): \fct(f:\mkclo[k1:]), \fct(g:\mkclo[k3:])};
    \node[invis,overlay,right=.1in of b2,text width=1.5in] () {\inL(b2): \fct(f:\mkclo[k1:]), \fct(g:\mkclo[k3:])};
    \draw [->] (b1) to (b2);
    \draw [->] (b2) to (b3);
    \draw [->] (b3.south) to ($(b3.south) + (0mm, -.25in)$) -|| ($(b2.west) + (-.25in, 0mm)$) to (b2.west);
  \end{tikzpicture}
\end{frame}
\note{I point out that things are more complicated when a block has more than
  one predecessor, as in \lab b2/s case. I state that the facts are resolved 
using an analysis-specific ``meet'' operator. In this case, I show that the fact
about \var g/ conflicts, so we set \inL(b2)'s fact about \var g/ to $\top$.}
\begin{frame}[fragile]{Iteration}
  \hfil\begin{tikzpicture}
  \node[stmt] (b1) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b1():
        \vbinds f<-\mkclo[k1:];
        \vbinds g<-\mkclo[k3:];
        \goto b2(f, g)
    \end{AVerb}
  \end{minipage}};
  \node[stmt, below=.2in of b1] (b2) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b2 (f, g):
        \dots
        \goto b3(t, u, f)
    \end{AVerb}
    \end{minipage}};
  \node[stmt, below=.2in of b2] (b3) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b3 (t, u, f):
        \dots
        \goto b2(f, w)
    \end{AVerb}
    \end{minipage}};
    \node[invis,overlay,right=.1in of b1,text width=1.5in] () {\outL(b1): \fct(f:\mkclo[k1:]), \fct(g:\mkclo[k3:])};
    \node[invis,overlay,right=.1in of b2,text width=1.5in] () {\inL(b2): \fct(f:\mkclo[k1:]), \fct(g:\balt{2}{\top}{\mkclo[k3:]})};
    \node[fact,invis,left=.3in of b3.west,text width=.75in,anchor=east] () 
         {\outL(b3): \fct(f:\mkclo[k1:]), \fct(g:\mkclo[k4:v])};

%%    \node[invis,overlay,right=.1in of b3] () {\outL(b3): \fct(g:\mkclo[k4:v])};

    \draw [->] (b1) to (b2);
    \draw [->] (b2) to (b3);
    \draw [->] (b3.south) to ($(b3.south) + (0mm, -.25in)$) -|| ($(b2.west) + (-.25in, 0mm)$) to (b2.west);
  \end{tikzpicture}
\end{frame}

\subsection{\Hoopl}
\begin{frame}{\Hoopl: A Haskell Library for Dataflow Analysis}
  \begin{itemize}
  \item See ``Hoopl: A Modular, Reusable Library for Dataflow Analysis and Transformation'' by Ramsey, Dias, and Peyton Jones
    (2010)
  \item Used in the Glasgow Haskell Compiler
  \item Based on ``Composing Dataflow Analyses and Transformations'' by Lerner, Grove, and Chambers (2002)
  \end{itemize}
\end{frame}

\section{Uncurrying}
\begin{frame}{Uncurrying}
  \begin{itemize}
  \item Partial Application
  \item Uncurrying |map|
  \end{itemize}
\end{frame}
\note{I explain the |map| and |toList| functions in brief, then 
reveal the |mkLists| function.}
\begin{frame}{Partial Application}
> map f xs = case xs of
>   Cons x xs' -> Cons (f x) (map f xs')
>   Nil -> Nil
> toList x = Cons x Nil
\end{frame}
\note{|mkLists| is a partially applied function, in that
  it only provides one argument to |map|. The ``value'' of
|mkLists| is another function; that value must be applied.

Partial application is powerful, because I can easily define
specialized functions.}
\begin{frame}{Partial Application}
> mkLists = map toList 

> map f xs = case xs of
>   Cons x xs' -> Cons (f x) (map f xs')
>   Nil -> Nil
> toList x = Cons x Nil
\end{frame}
\note{However, partial application can have a cost. A naive
  compiler might generate inefficient code. For example, |main1| 
  and |main2| produce the same result, but |main2| might 
  execute slower (or allocate more memory).}
\begin{frame}{Partial Application}
> mkLists = map toList 

> main1 ns = map toList ns
> main2 ns = mkLists ns

> map f xs = case xs of
>   Cons x xs' -> Cons (f x) (map f xs')
>   Nil -> Nil
> toList x = Cons x Nil
\end{frame}

\note{The solution to this problem is \emph{uncurrying}. We
want to transform |main2| into |main1|. In this case, its
easy, but in other cases its not so simple.}

\subsection{Uncurrying |map|}
\note{The following example illustrates how I can turn a recursive
  call into a loop. I start by showing the definition of the example,
  then I talk through the translation of each block, building up
  the \cfg in pieces. After the \cfg has been defined, I apply uncurrying
  to each interesting block (\lab main/, \lab map/ and \lab cons/). I 
  rewrite the program as I go, illustrating each step. Finally, I summarize
  the benefits of my rewrite.

  The next slide begins the example by showing the example program.}
%%\end{comment}

%%\begin{comment}
\begin{frame}[fragile]{Uncurrying |map|}
\begin{uncoverenv}<3>\begin{tikzpicture}
  \node[stmt] (main1) {\block main(ns):};
\end{tikzpicture}\end{uncoverenv}
\note<2>{I point out that \lab main/ doesn't call any blocks, so
  therefore its \cfg node doesn't connect to anything.}
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}[t]{.5\hsize}
> {-"\altline<2,3>{"-}main ns{-"}"-} = map toList ns
> map f xs = case xs of
>   Cons x xs' -> 
>     Cons (f x) (map f xs')
>   Nil -> Nil 
> toList x = Cons x Nil
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
\end{frame}

\note{I do the same for \lab toList/.}

\begin{frame}[fragile]{Uncurrying |map|}
\begin{onlyenv}<1,2>\begin{uncoverenv}<2>\begin{tikzpicture}
  \node[stmt] (toList1) {\block toList(x):};
\end{tikzpicture}\end{uncoverenv}\end{onlyenv}

\begin{onlyenv}<1,2>
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}[t]{.5\hsize}
> main ns = map toList ns
> map f xs = case xs of
>   Cons x xs' -> 
>     Cons (f x) (map f xs')
>   Nil -> Nil 
> {-"\hsline{"-}toList x{-"}"-} = Cons x Nil
\end{minipage}& \begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block toList(x):
        \vbinds v221<-\mkclo[Cons1:];
        \vbinds v222<-\app v221*x/;
        \vbinds v223<-Nil;
        \app v222 * v223/ 
    \end{AVerb}
  \end{minipage}
\end{tabular*}
\end{onlyenv} 

\note<2>{Since \lab map/ is pretty complicated, I reveal it
  in pieces. I start by looking at \lab map/ and showing that
  it calls two blocks, \lab nil/ and \lab cons/.}
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
\begin{onlyenv}<1-4>\begin{uncoverenv}<2-4>\begin{tikzpicture}
  \node[stmt] (map1) {\block map(f,xs):};
  \node[stmt,right=.3in of map1] (cons1) {\block cons(f, x, xs):};
  \node[stmt,left=.3in of map1] (nil1) {\block nil():};
  \draw [->] (map1) to (nil1);
  \draw [->] (map1) to (cons1);
\end{tikzpicture}\end{uncoverenv}\end{onlyenv}

\note<2>{\lab cons/ and \lab nil/ don't have any successors, so I 
go through them pretty quickly.}

\note<4>{Now I reveal the (initial) \cfg for the entire program. I note that
our compiler produces pretty bad code that doesn't take advantage of
obvious connections, such as between \lab cons/ and \lab map/, or between
\lab cons/ and \lab toList/.}

\begin{onlyenv}<1-4>
\begin{tabular*}{\hsize}{@@{}ll}
\begin{minipage}[t]{.5\hsize}
> main ns = map toList ns
> {-"\altline<1,2>{"-}map f xs{-"}"-} = case xs of
>   Cons x xs' -> 
>     {-"\altline<3>{"-}Cons (f x) (map f xs'){-"}"-}
>   Nil -> {-"\altline<4>{"-}Nil{-"}"-}
> toList x = Cons x Nil
\end{minipage} & \begin{onlyenv}<1,2>\begin{minipage}[t]{.4\hsize}
  \begin{AVerb}[gobble=6,numbers=left]
      \block map(f,xs): 
        \case xs;
          \valt Nil()->\goto nil();
          Cons x xs -> 
            \goto cons(f, x, xs)
    \end{AVerb}
\end{minipage}\end{onlyenv}\begin{onlyenv}<3>\begin{minipage}[t]{.4\hsize}
  \begin{AVerb}[gobble=6,numbers=left]
      \block cons(f, x, xs): 
        \vbinds v209<-\mkclo[Cons1:];
        \vbinds v210<-\app f*x/; 
        \vbinds v211<-\app v209*v210/;
        \vbinds v212<-\mkclo[k203:]; 
        \vbinds v213<-\app v212*f/;
        \vbinds v214<-\app v213*xs/; 
        \app v211 * v214/ 
    \end{AVerb}
\end{minipage}\end{onlyenv}\begin{onlyenv}<4>\begin{minipage}[t]{.4\hsize}
    \begin{AVerb}[gobble=6,numbers=left]
      \block nil(): Nil 
    \end{AVerb}
\end{minipage}\end{onlyenv}
\end{tabular*}
\end{onlyenv}
\end{frame}

\begin{frame}{Uncurrying |map|}
\begin{tikzpicture}
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
> toList x = Cons x Nil
\end{frame}

\note{To proceed, I need to connect \lab main/ to \lab map/. I will go through
  uncurrying within \lab main/.}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{tikzpicture}
    \node[stmt] (main) {\block main(ns):};
    \node[stmt,below=.3in of main] (map) {\block map(f,xs):};
    \node[stmt,right=.3in of map] (cons) {\block cons(f, x, xs):};
    \node[stmt,left=.3in of map] (nil) {\block nil():};
    \node[stmt,above=.3in of cons] (toList) {\block toList(x):};
    \draw [->] (map) to (nil);
    \draw [->] (map) to (cons);
  \end{tikzpicture}
  \begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nsa)
      \vbinds v227<-\mkclo[k203:];\anchorF(v227a) 
      \vbinds v228<-\mkclo[k219:];\anchorF(v228a)
      \vbinds v229<-\app\balt{3-}{{\inred{v227}}}{v227}*v228/;\anchorF(v229a) 
      \app v229 * ns/ 
    \ccblock k203()f: \mkclo[k204:f]
    \ccblock k204(f)xs: \goto map(f,xs)
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
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
  \note<2>{I point out that \var v229/ is $\top$, but we can rewrite
    \app v227 * v228/ based on the facts gathered. This sequence
    connects the fact we have about \var v227/ with the result
    returned by the \cc block.}
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
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{tikzpicture}
    \node[stmt] (main) {\block main(ns):};
    \node[stmt,below=.3in of main] (map) {\block map(f,xs):};
    \node[stmt,right=.3in of map] (cons) {\block cons(f, x, xs):};
    \node[stmt,left=.3in of map] (nil) {\block nil():};
    \node[stmt,above=.3in of cons] (toList) {\block toList(x):};
    \draw [->] (map) to (nil);
    \draw [->] (map) to (cons);
  \end{tikzpicture}
  \begin{onlyenv}<1-3>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nsb)
      \vbinds v227<-\mkclo[k203:];\anchorF(v227b) 
      \vbinds v228<-\mkclo[k219:];\anchorF(v228b) 
      \balt{1,2}{\vbinds v229<-\app {\inred{\mkclo[k203:]}}*v228/;}{\vbinds v229<-\inred{\mkclo[k204:v228]};}\anchorF(v229b) 
      \app v229 * ns/
    \balt{2}{\inred\ccblock k203()f:}{\ccblock k203()f:} \balt{3}{\inred\mkclo[k204:f]}{\mkclo[k204:f]}
    \ccblock k204(f)xs: \goto map(f,xs)
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nsb, anchor=west] (fvnsa4) 
         {\fct(ns:\top)};
    \draw [->] (fvnsa4) to (nsb);
    \node[fact, invis, right=0.25in of v227b, anchor=west] (fv227a5) 
         {\balt{1}{\fct(v227:{{\inred\mkclo[k203:]}})}{\fct(v227:{\mkclo[k203:]})}};
    \node[fact, invis, right=0.25in of v228b, anchor=west] (fv228a5) 
         {\fct(v228:{\mkclo[k219:]})};
    \draw [->] (fv228a5) to (v228b);
    \draw [->] (fv227a5) to (v227b);
  \end{tikzpicture}\end{onlyenv}
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{tikzpicture}
    \node[stmt] (main) {\block main(ns):};
    \node[stmt,below=.3in of main] (map) {\block map(f,xs):};
    \node[stmt,right=.3in of map] (cons) {\block cons(f, x, xs):};
    \node[stmt,left=.3in of map] (nil3) {\block nil():};
    \node[stmt,above=.3in of cons] (toList) {\block toList(x):};
    \draw [->] (map) to (nil3);
    \draw [->] (map) to (cons);
  \end{tikzpicture}
  \note<2>{When I rewrite line 4, I get a new fact --- \var v229/
    holds \mkclo[k204:v228]. I now step through the same sequence as before,
    using the new fact to rewrite line 5.}
  \begin{onlyenv}<1,2>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nsc)
      \vbinds v227<-\mkclo[k203:];\anchorF(v227c)
      \vbinds v228<-\mkclo[k219:];\anchorF(v228c)
      \vbinds v229<-\mkclo[k204:v228];\anchorF(v229c)
      \app\balt{2}{{\inred{v229}}}{v229} * ns/
    \ccblock k203()f: \mkclo[k204:f]
    \ccblock k204(f)xs: \goto map(f,xs)
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \begin{onlyenv}<1>\begin{tikzpicture}[overlay, remember picture]
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
  \begin{onlyenv}<2>\begin{tikzpicture}[overlay, remember picture]
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
  \end{tikzpicture}\end{onlyenv}\end{onlyenv}
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{tikzpicture}
    \node[stmt] (main) {\block main(ns):};
    \node[stmt,below=.3in of main] (map3) {\block map(f,xs):};
    \node[stmt,right=.3in of map3] (cons) {\block cons(f, x, xs):};
    \node[stmt,left=.3in of map3] (nil) {\block nil():};
    \node[stmt,above=.3in of cons] (toList) {\block toList(x):};
    \draw [->] (map3) to (nil);
    \draw [->] (map3) to (cons);
  \end{tikzpicture}
  \begin{onlyenv}<1,2>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nsd)
      \vbinds v227<-\mkclo[k203:];\anchorF(v227d)
      \vbinds v228<-\mkclo[k219:];\anchorF(v228d)
      \vbinds v229<-\mkclo[k204:v228];\anchorF(v229d)
      \app {\inred\mkclo[k204:v228]} * ns/
    \ccblock k203()f: \mkclo[k204:f]
    \balt{2}{{\inred\ccblock k204(f)xs: \goto map(f,xs)}}{\ccblock k204(f)xs: \goto map(f,xs)}
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nsd, anchor=west] (fvnsa11) {\fct(ns:\top)};
    \draw [->] (fvnsa11) to (nsd);
    \node[fact, invis, right=0.25in of v227d, anchor=west] (fv227a11) 
         {\fct(v227:{\mkclo[k203:]})};
    \node[fact, invis, right=0.25in of v228d, anchor=west] (fv228a11) 
         {\fct(v228:{\mkclo[k219:]})};
    \node[fact, invis, right=0.25in of v229d, anchor=west] (fv229a11) 
         {\fct(v229:{{\inred \mkclo[k204:v228]}})};
    \draw [->] (fv227a11) to (v227d);
    \draw [->] (fv228a11) to (v228d);
    \draw [->] (fv229a11) to (v229d);
  \end{tikzpicture}\end{onlyenv}
\end{frame}

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
  \note<1>{With line 5 rewritten, the \cfg for the program changes.  \lab main/
    now connects to \lab map/. 

    Before moving on, I also point out that lines 2 and 4 are now
    dead, because \var 227/ and \var 229/ are no longer referenced and
    we can delete them. I explain that dead-code elimination is really
    a separate pass in the implementation, but the net result is the
    same.}
  \begin{onlyenv}<1-3>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nse)
      \balt{3}{\xout{\vbinds v227<-\mkclo[k203:];}}{\vbinds v227<-\mkclo[k203:];}\anchorF(v227e)
      \vbinds v228<-\mkclo[k219:];\anchorF(v228e)
      \balt{3}{\xout{\vbinds v229<-\mkclo[k204:v228];}}{\vbinds v229<-\mkclo[k204:v228];}\anchorF(v229e)
      \balt{1}{\inred\goto map(v228, ns)}{\goto map(v228, ns)}
    \ccblock k203()f: \mkclo[k204:f]
    \ccblock k204(f)xs: \balt{1}{\inred\goto map(f,xs)}{\goto map(f,xs)}
    \ccblock k219()x: \goto toList(x)
  \end{AVerb}
  \end{onlyenv}\begin{onlyenv}<1,2>\begin{tikzpicture}[overlay, remember picture]
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
  \end{tikzpicture}\end{onlyenv}\begin{onlyenv}<2>\begin{tikzpicture}[overlay, remember picture]
    \draw[color=red] [->] (main3) to (map3);
  \end{tikzpicture}\end{onlyenv}\begin{onlyenv}<3>\begin{tikzpicture}[overlay, remember picture]
    \node[fact, invis, right=0.25in of nse, anchor=west] (fvnsa9) {\fct(ns:\top)};
    \draw [->] (fvnsa9) to (nse);
    \node[fact, invis, right=0.25in of v228e, anchor=west] (fv228a9) {\fct(v228:{\mkclo[k219:]})};
    \draw [->] (fv228a9) to (v228e);
    \draw [->] (main3) to (map3);
  \end{tikzpicture}\end{onlyenv}\begin{onlyenv}<4>
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block main(ns): \anchorF(nsf)
        \vbinds v228<-\mkclo[k219:];\anchorF(v228f)
        \goto map(v228, ns)
      \ccblock k203()f: \mkclo[k204:f]
      \ccblock k204(f)xs: \goto map(f,xs)
      \ccblock k219()x: \goto toList(x)
    \end{AVerb}
  \end{onlyenv}\begin{onlyenv}<4>\begin{tikzpicture}[overlay,remember picture]
    \node[fact, invis, right=0.25in of nsf, anchor=west] (fvnsa10) {\fct(ns:\top)};
    \draw [->] (fvnsa10) to (nsf);
    \node[fact, invis, right=0.25in of v228f, anchor=west] (fv228a10) {\fct(v228:{\mkclo[k219:]})};
    \draw [->] (fv228a10) to (v228f);
    \draw [->] (main3) to (map3);
  \end{tikzpicture}\end{onlyenv}
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
           {\inL(map): \fct(f:{\mkclo[k219:]}), \fct(xs:\top)};

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

\note{Now I can finally show how to rewrite \lab cons/. I leave the
  facts as is on screen and bring up \lab cons/. I explain that \lab
  cons/ is pretty big so I'm going to hide the \cfg while working
  through the block. I leave the initial fact for \lab cons/'s
  arguments up throughout.}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{tikzpicture}
    \node[stmt] (main6) {\block main(ns):};
    \node[stmt,below=.3in of main6] (map6) {\block map(f,xs):};
    \node[stmt,right=.3in of map6] (cons6) {\block cons(f, x, xs):};
    \node[stmt,left=.3in of map6] (nil6) {\block nil():};
    \node[stmt,above=.3in of cons6] (toList6) {\block toList(x):};
    
    \node[fact,invis,below right=.07in and -.2in of main6] () 
         {\inL(map): \fct(f:{\mkclo[k219:]}), \fct(xs:\top)};

         \node[invis,below left=0.07in and -0.25in of cons6, anchor=north] () 
              {\inL(cons): \fct(f:{\mkclo[k219:]}),
                \fct(x:\top),
                \fct(xs:\top)};
              
              \node[fact, invis, below left=0.07in and -.2in of main6] () {$\inL(nil)\text{:\ } \emptyset$};
              \draw [->] (map6) to (nil6);
              \draw [->] (map6) to (cons6);
              \draw [->] (main6) to (map6);
  \end{tikzpicture}
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consd1)
        \vbinds v209<-\mkclo[Cons1:]; \anchorF(v209d1)
        \vbinds v210<-\app f*x/; \anchorF(v210d1)
        \vbinds v211<-\app v209*v210/; \anchorF(v211d1)
        \vbinds v212<-\mkclo[k203:]; \anchorF(v212d1)
        \vbinds v213<-\app v212*f/; \anchorF(v213d1)
        \vbinds v214<-\app v213*xs/; \anchorF(v214d1)
        \app v211 * v214/  
    \end{AVerb}
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{onlyenv}<1-2>
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consd1)
        \vbinds v209<-\mkclo[Cons1:]; \anchorF(v209d1)
        \vbinds v210<-\app f*x/; \anchorF(v210d1)
        \vbinds v211<-\app v209*v210/; \anchorF(v211d1)
        \vbinds v212<-\mkclo[k203:]; \anchorF(v212d1)
        \vbinds v213<-\app v212*f/; \anchorF(v213d1)
        \vbinds v214<-\app v213*xs/; \anchorF(v214d1)
        \app v211 * v214/  
    \end{AVerb}

    \begin{tikzpicture}[remember picture,overlay]
      \node[fact, invis, right=0.25in of consd1, anchor=west] (fvconsd1) {\fct(f:{\mkclo[k219:]}), \fct(x:\top), \fct(xs:\top)};
      \draw [->] (fvconsd1) to (consd1);
    \end{tikzpicture}
   \end{onlyenv}
    
  \note<1>{I show the fact for \var v209/.}

  \begin{onlyenv}<2>\begin{tikzpicture}[remember picture,overlay]
    \node[fact, invis, right=0.25in of v209d1, anchor=west] (fvv209d1) {\fct(v209:\mkclo[Cons1:])};
    \draw [->] (fvv209d1) to (v209d1);
    \end{tikzpicture}
  \end{onlyenv}

  \note<2>{Now I rewrite line 3, replacing \app f * x/ with a call
    to \lab toList/.  I begin by showing the definition of \lab
    k219/. I highlight the fact about \var f/ and rewrite in sequence.}
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{onlyenv}<1-3>
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consd2)
        \vbinds v209<-\mkclo[Cons1:]; \anchorF(v209d2)
        \vbinds v210<-\bonly{1}{\app{{\inred{}f}}*x/}\bonly{2}{\app{{\inred\mkclo[k219:]}}*x/}\bonly{3}{\inred\goto toList(x)}; \anchorF(v210d2)
        \vbinds v211<-\app v209*v210/; \anchorF(v211d2)
        \vbinds v212<-\mkclo[k203:]; \anchorF(v212d2)
        \vbinds v213<-\app v212*f/; \anchorF(v213d2)
        \vbinds v214<-\app v213*xs/; \anchorF(v214d2)
        \app v211 * v214/  
      \balt{2}{{\inred\ccblock k219()x:}}{\ccblock k219()x:} \bonly{3}{\inred}\goto toList(x)
    \end{AVerb}

    \begin{tikzpicture}[remember picture,overlay]
      \node[fact, invis, right=0.25in of consd2, anchor=west] (fvconsd2) 
           {\bonly{1}{\fct(\inred f:{\mkclo[k219:]})}%
             \bonly{2}{\fct(f:{{\inred\mkclo[k219:]}})}%
             \bonly{3}{\fct(f:{\mkclo[k219:]})}, \fct(x:\top), \fct(xs:\top)};
      \draw [->] (fvconsd2) to (consd2);

      \node[fact, invis, right=0.25in of v209d2, anchor=west] (fvv209d2) {\fct(v209:\mkclo[Cons1:])};
      \draw [->] (fvv209d2) to (v209d2);

    \end{tikzpicture}
  \end{onlyenv}

  \note<3>{Now I rewrite line 4, showing how I apply \lab Cons1/ to \var v210/ to
    replace \app v209 * v210/ with \mkclo[Cons2:v210]. At the end of the rewrite
    I get a new fact about \var v211/.}
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{onlyenv}<1-3>
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consd3)
        \vbinds v209<-\mkclo[Cons1:]; \anchorF(v209d3)
        \vbinds v210<-\goto toList(x); \anchorF(v210d3)
        \vbinds v211<-\bonly{1}{\app{{\inred{}v209}}*v210/}\bonly{2}{\app{{\inred{}\mkclo[Cons1:]}}*v210/}\bonly{3}{\inred\mkclo[Cons2:v210]}; \anchorF(v211d3)
        \vbinds v212<-\mkclo[k203:]; \anchorF(v212d3)
        \vbinds v213<-\app v212*f/; \anchorF(v213d3)
        \vbinds v214<-\app v213*xs/; \anchorF(v214d3)
        \app v211 * v214/  
      \balt{2}{{\inred\ccblock Cons1()a2:}}{\ccblock Cons1()a2:} \bonly{3}{\inred}\mkclo[Cons2:a2]
      \ccblock Cons2(a2)a1: Cons a2 a1
    \end{AVerb}

    \begin{tikzpicture}[remember picture,overlay]
      \node[fact, invis, right=0.25in of consd3, anchor=west] (fvconsd3) 
           {\fct(f:\mkclo[k219:]), \fct(x:\top), \fct(xs:\top)};
      \draw [->] (fvconsd3) to (consd3);

      \node[fact, invis, right=0.25in of v209d3, anchor=west] (fvv209d3) 
           {\bonly{1}{\fct({\inred v209}:\mkclo[Cons1:])}%
            \bonly{2}{\fct(v209:{{\inred\mkclo[Cons1:]}})}%
            \bonly{3}{\fct(v209:\mkclo[Cons1:])}};
      \draw [->] (fvv209d3) to (v209d3);
      \node[fact, invis, right=0.25in of v210d3, anchor=west] (fvv210d3) {\fct(v210:\top)};
      \draw [->] (fvv210d3) to (v210d3);
    \end{tikzpicture}
  \end{onlyenv}

  \note<3>{This sequence rewrites \lcapp map * (f * x) * xs/. Ultimately we
    turn line 7 into a \goto map() call rather than a function application.}
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{onlyenv}<1-6>
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consd4)
        \vbinds v209<-\mkclo[Cons1:]; \anchorF(v209d4)
        \vbinds v210<-\goto toList(x); \anchorF(v210d4)
        \vbinds v211<-\mkclo[Cons2:v210]; \anchorF(v211d4)
        \vbinds v212<-\mkclo[k203:]; \anchorF(v212d4) 
        \vbinds v213<-\bonly{1}{\app{{\inred{}v212}}*f/}\bonly{2}{\app{{\inred{}\mkclo[k203:]}}*f/}\bonly{3}{\inred\mkclo[k204:f]}\bonly{4-}{\mkclo[k204:f]}; \anchorF(v213d4)
        \vbinds v214<-\bonly{1-3}{\app v213*xs/}\bonly{4}{\app{{\inred{}v213}}*xs/}\bonly{5}{\app{{\inred{}\mkclo[k204:f]}}*xs/}\bonly{6}{\inred\goto map(f,xs)}; \anchorF(v214d4)
        \app v211 * v214/  
      \balt{2}{{\inred\ccblock k203()f:}}{\ccblock k203()f:} \bonly{3}{\inred}\mkclo[k204:f]
      \balt{5}{{\inred\ccblock k204(f)xs:}}{\ccblock k204(f)xs:} \bonly{6}{\inred}\goto map(f,xs)
    \end{AVerb}

    \begin{tikzpicture}[remember picture,overlay]
      \node[fact, invis, right=0.25in of consd4, anchor=west] (fvconsd4) 
           {\fct(f:\mkclo[k219:]), \fct(x:\top), \fct(xs:\top)};
      \draw [->] (fvconsd4) to (consd4);

      \node[fact, invis, right=0.25in of v209d4, anchor=west] (fvv209d4) 
           {\fct(v209:\mkclo[Cons1:])};
      \draw [->] (fvv209d4) to (v209d4);

      \node[fact, invis, right=0.25in of v210d4, anchor=west] (fvv210d4) {\fct(v210:\top)};
      \draw [->] (fvv210d4) to (v210d4);

      \node[fact, invis, right=0.25in of v211d4, anchor=west] (fvv211d4) {\fct(v211:\mkclo[Cons2:v210])};
      \draw [->] (fvv211d4) to (v211d4);

      \node[fact, invis, right=0.25in of v212d4, anchor=west] (fvv212d4) 
           {\bonly{1}{\fct(\inred v212:\mkclo[k203:])}%
             \bonly{2}{\fct(v212:{{\inred \mkclo[k203:]}})}%
             \bonly{3-}{\fct(v212:\mkclo[k203:])}};
      \draw [->] (fvv212d4) to (v212d4);

      \node[fact, invis, right=0.25in of v213d4, anchor=west] (fvv213d4) 
           {\bonly{1,2}{\fct(v213:\top)}%
             \bonly{3}{\inred\fct(v213:\mkclo[k204:f])}%
             \bonly{4}{\fct(\inred v213:\mkclo[k204:f])}%
             \bonly{5}{\fct(v213:{{\inred \mkclo[k204:f]}})}%
             \bonly{6-}{\fct(v213:\mkclo[k204:f])}};
      \draw [->] (fvv213d4) to (v213d4);

      \node[fact, invis, right=0.25in of v214d4, anchor=west] (fvv214d4) {\fct(v214:\top)};
      \draw [->] (fvv214d4) to (v214d4);
    \end{tikzpicture}
  \end{onlyenv}

  \note<6>{This rewrite turns the \enter at the end of the block into
    a direct data allocation. I note that my implementation does not
    currently perform this optimization, but only because I wanted to
    implement it as a more general application of monadic inlining,
    which I will get to later if there is time.}
\end{frame}


\begin{frame}[fragile]{Uncurrying |map|}
  \begin{onlyenv}<1-3>
    \begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consd5)
        \vbinds v209<-\mkclo[Cons1:]; \anchorF(v209d5)
        \vbinds v210<-\goto toList(x); \anchorF(v210d5)
        \vbinds v211<-\mkclo[Cons2:v210]; \anchorF(v211d5)
        \vbinds v212<-\mkclo[k203:]; \anchorF(v212d5) 
        \vbinds v213<-\mkclo[k204:f]; \anchorF(v213d5)
        \vbinds v214<-\goto map(f,xs); \anchorF(v214d5)
        \bonly{1}{\app{\inred{}v211} * v214/}\bonly{2}{\app{{\inred{}\mkclo[Cons2:v210]}} * v214/}\bonly{3}{\inred{}Cons v210 v214}
      \ccblock Cons1()a2: \mkclo[Cons2:a2]
      \balt{2}{{\inred\ccblock Cons2(a2)a1:}}{\ccblock Cons2(a2)a1:} \bonly{3}{\inred}Cons a2 a1
    \end{AVerb}

    \begin{tikzpicture}[remember picture,overlay]
      \node[fact, invis, right=0.25in of consd5, anchor=west] (fvconsd5) 
           {\fct(f:\mkclo[k219:]), \fct(x:\top), \fct(xs:\top)};
      \draw [->] (fvconsd5) to (consd5);

      \node[fact, invis, right=0.25in of v209d5, anchor=west] (fvv209d5) 
           {\fct(v209:\mkclo[Cons1:])};
      \draw [->] (fvv209d5) to (v209d5);

      \node[fact, invis, right=0.25in of v210d5, anchor=west] (fvv210d5) {\fct(v210:\top)};
      \draw [->] (fvv210d5) to (v210d5);

      \node[fact, invis, right=0.25in of v211d5, anchor=west] (fvv211d5) 
           {\bonly{1}{\fct(\inred v211:\mkclo[Cons2:v210])}%
             \bonly{2}{\fct(v211:{{\inred \mkclo[Cons2:v210]}})}%
             \bonly{3}{\fct(v211:\mkclo[Cons2:v210])}};
      \draw [->] (fvv211d5) to (v211d5);

      \node[fact, invis, right=0.25in of v212d5, anchor=west] (fvv212d5) 
           {\fct(v212:\mkclo[k203:])};
      \draw [->] (fvv212d5) to (v212d5);

      \node[fact, invis, right=0.25in of v213d5, anchor=west] (fvv213d5) 
           {\fct(v213:\mkclo[k204:f])};
      \draw [->] (fvv213d5) to (v213d5);

      \node[fact, invis, right=0.25in of v214d5, anchor=west] (fvv214d5) {\fct(v214:\top)};
      \draw [->] (fvv214d5) to (v214d5);
    \end{tikzpicture}
  \end{onlyenv}

  \note<3>{Now I show the original block and the rewritten block, flipping
    between the two to show how certain lines changed. On the last slide
    I eliminate dead code in the new block.}
\end{frame}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{onlyenv}<1>\begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): 
        \vbinds v209<-\mkclo[Cons1:];
        \vbinds v210<-\app f*x/; 
        \vbinds v211<-\app v209*v210/;
        \vbinds v212<-\mkclo[k203:]; 
        \vbinds v213<-\app v212*f/;
        \vbinds v214<-\app v213*xs/; 
        \app v211 * v214/ 
    \end{AVerb}
    \end{onlyenv}\begin{onlyenv}<2>\begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consd5)
        \vbinds v209<-\mkclo[Cons1:];
        \vbinds v210<-{\inred\goto toList(x)};
        \vbinds v211<-{\inred\mkclo[Cons2:v210]}; 
        \vbinds v212<-\mkclo[k203:]; 
        \vbinds v213<-{\inred\mkclo[k204:f]}; 
        \vbinds v214<-{\inred\goto map(f,xs)}; 
        \inred{Cons v210 v214}
    \end{AVerb}
    \end{onlyenv}\begin{onlyenv}<3>\begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consd5)
        \xout{\vbinds v209<-\mkclo[Cons1:];} 
        \vbinds v210<-\goto toList(x); 
        \xout{\vbinds v211<-\mkclo[Cons2:v210];}
        \xout{\vbinds v212<-\mkclo[k203:];}
        \xout{\vbinds v213<-\mkclo[k204:f];}
        \vbinds v214<-\goto map(f,xs);
        Cons v210 v214
    \end{AVerb}
    \end{onlyenv}\begin{onlyenv}<4>\begin{AVerb}[gobble=6,numbers=left,xleftmargin=1.5em]
      \block cons(f, x, xs): \anchorF(consd5)
        \vbinds v210<-\goto toList(x); 
        \vbinds v214<-\goto map(f,xs);
        Cons v210 v214
    \end{AVerb}
  \end{onlyenv}
\end{frame}

\note{Now I summarize the changes made to the program, showing 
  each block in succession. I keep the \cfg on screen to make
  the relations among blocks clear.}

\begin{frame}[fragile]{Uncurrying |map|}
  \begin{tikzpicture}[remember picture]
    \node[stmt] (main7) {\block main(ns):};
    \node[stmt,below=.3in of main7] (map7) {\block map(f,xs):};
    \node[stmt,right=.3in of map7] (cons7) {\block cons(f, x, xs):};
    \node[stmt,left=.3in of map7] (nil6) {\block nil():};
    \node[stmt,above=.3in of cons7] (toList7) {\block toList(x):};
    
    \draw [->] (map7) to (nil6);
    \draw [->] (map7) to (cons7);
  \end{tikzpicture}
  \begin{uncoverenv}<4->\vspace{8pt}
    \begin{tikzpicture}[remember picture, overlay]
      \draw[dashed] [->] (cons7.north) .. controls ($(cons7.north)!.3!(toList7.south) + (.1in,0in)$) and ($(cons7.north)!.6!(toList7.south) + (.1in,0in)$) .. (toList7.south);
      \draw[dashed] [->] (toList7.south) .. controls ($(cons7.north)!.6!(toList7.south) + (-.1in,0in)$) and ($(cons7.north)!.3!(toList7.south) + (-.1in,0in)$) .. (cons7.north);
      \draw[dashed] [->] (cons7.south) .. controls ($(cons7.south)!.3!(map7.south) + (0in,-.2in)$) and ($(cons7.south)!.6!(map7.south) + (0in,-.2in)$) .. (map7.south);
    \end{tikzpicture}
  \end{uncoverenv}
  \begin{onlyenv}<2->
    \begin{tikzpicture}[remember picture,overlay]
      \draw [->] (main7) to (map7);
    \end{tikzpicture}
  \end{onlyenv}
  \note<1>{I point out that the rewrite eliminated one closure and two
    applications. It also created a link from \lab main/ to \lab map/
    in \cfg, which allowed further rewrites.}
  \begin{onlyenv}<1>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nsa)
      \vbinds v227<-\mkclo[k203:];
      \vbinds v228<-\mkclo[k219:];
      \vbinds v229<-\app v227*v228/;
      \app v229 * ns/ 
  \end{AVerb}
  \end{onlyenv}\begin{onlyenv}<2>
    \begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block main(ns): \anchorF(nse)
      \xout{\vbinds v227<-\mkclo[k203:];} \anchorF(v227e1)
      \vbinds v228<-\mkclo[k219:];
      \xout{\vbinds v229<-\app v227*v228/;} \anchorF(v229e1)
      \goto map(v228, ns) \anchorF(mape1)
    \end{AVerb}
  \end{onlyenv}
  \note<2>{Now I show the rewrite to \lab cons/, in the
    same manner as \lab main/.}
  \begin{onlyenv}<3>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block cons(f, x, xs): \anchorF(consd1)
      \vbinds v209<-\mkclo[Cons1:]; 
      \vbinds v210<-\app f*x/; 
      \vbinds v211<-\app v209*v210/; 
      \vbinds v212<-\mkclo[k203:]; 
      \vbinds v213<-\app v212*f/; 
      \vbinds v214<-\app v213*xs/; 
      \app v211 * v214/  
    \end{AVerb}
  \end{onlyenv}
  \note<3>{Rewriting \lab cons/ eliminates two closures and four function
    applications. Two of those applications become calls to
    known functions (\lab toList/ and \lab map/). I note that the dashed lines
  indicate control-flow not visible to our algorithm, due to our \ast and 
  \hoopl's restriction on block shape.}
  \begin{onlyenv}<4>\begin{AVerb}[gobble=4,numbers=left,xleftmargin=1.5em]
    \block cons(f, x, xs): \anchorF(consd5)
      \xout{\vbinds v209<-\mkclo[Cons1:];} 
      \vbinds v210<-\goto toList(x); 
      \xout{\vbinds v211<-\app v209*v210/;}
      \xout{\vbinds v212<-\mkclo[k203:];}
      \xout{\vbinds v213<-\app v212*f/;}
      \vbinds v214<-\goto map(f,xs);
      Cons v210 v214 
    \end{AVerb}
  \end{onlyenv}
  \note<4>{I summarize the rewrite by showing the savings made. I note that
    not just uncurrying, but several other optimizations were necessary
    to achieve the savings shown. I also emphasize that this worked because
    \lab map/ was only used once in the program; additional uses of \lab map/
    would make the rewrite impossible (because \var f/ would not have a constant
    value). However, a heuristic which specialized each copy of \lab map/ would
    make the optimization possible in that case.}
  \begin{onlyenv}<5>
    \begin{itemize}
    \item One closure and two applications eliminated from \lab main/.
    \item Link from \lab main/ to \lab map/.
    \item Two closures and four function applications from \lab cons/.
    \item Link from \lab cons/ to \lab map/ and \lab toList/.
    \end{itemize}
  \end{onlyenv}
\end{frame}
%%\end{comment}

%%\begin{comment}
\subsection{Related Work}
\begin{frame}{Related Work}
\begin{itemize}
\item Appel: Uncurrying by pattern matching; ``Compiling with Continuations'' (1992)
\item Tarditi: Uncurrying in four passes; ``Design and Implementation of Code Optimizations for a Type-Directed Compiler for Standard ML'' (1996)
\item Tolmach \& Oliva: Automatic uncurrying; ``From ML to Ada: Strongly-typed Language Interoperability via Source Translation'' (1998)
\end{itemize}
\end{frame}
%%\end{comment}

\section{Conclusion}
\begin{frame}{Conclusion}
  \begin{itemize}
  \item Monadic Optimizations
  \item Contributions
  \end{itemize}
\end{frame}
\subsection{Monadic Optimizations}
\begin{frame}{Optimizing using the Monad Laws}
  \begin{itemize}
    \item {\it Left-Unit}
$$
|do { x <- return y; m }| \equiv\ |do { {-"\lamSubst{y}{x}\ "-} m}|
$$
    \item {\it Right-Unit}
$$
|do { x <- m; return x }| \equiv\ |do { m }|
$$
    \item {\it Associativity}
$$
|do { x <- do {y <- m; n}; o }| \equiv\ |do { y <- m; x <- n; o}|
$$
\item From Wadler's ``Monads for Functional Programming'' (1995)
  \end{itemize}
\end{frame}
\subsection{Contributions}
\begin{frame}{Dataflow Analysis \& \Mil}
  \begin{itemize}
    \item High-level functional programming; low-level details.
    \item Structured for dataflow analysis.
    \item Implemented other optimizations; for example, dead-code elimination.
  \end{itemize}
\end{frame}
\begin{frame}{Uncurrying}
  \begin{itemize}
  \item Implemented using the dataflow algorithm
  \item Able to uncurry across blocks and loops (with some caveats)
  \item Complete implementation described
  \end{itemize}
\end{frame}
\begin{frame}{\Hoopl}
  \begin{itemize}
  \item Thorough description of the library
  \item Simple, but complete, example implementation given
  \end{itemize}
\end{frame}

\begin{frame}[fragile]{Questions?}
Source code and paper available at \url{http://mil.codeslower.com}, or 
email me at \texttt{jgbailey@@codeslower.com}.
\end{frame}

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

%% \begin{comment}
%% \begin{frame}[fragile]{\Mil: Blocks}
%% \vspace{12pt}
%% \note[item]<1>{This sequence will connect a simple definition with a block of
%% \mil code. I will first illustrate ordinary blocks.

%% I start by removing the syntactic sugar to
%% show the real constructors.}
%% \begin{tabular*}{\hsize}{@@{}ll}
%% \begin{minipage}{.45\hsize}\elimdisplayskip\begin{onlyenv}<1>
%% > toList :: a -> [a]
%% > toList x = [x] {-"\strut"-}
%% \end{onlyenv}\begin{onlyenv}<2,3>
%% > toList :: a -> [a]
%% > toList x = Cons x Nil{-"\strut"-}
%% \end{onlyenv}\begin{onlyenv}<4>
%% > toList :: a -> [a]{-"\phantom{(}"-}
%% > toList x = Cons x {-"\uline{"-}Nil{-"}"-}
%% \end{onlyenv}\begin{onlyenv}<5>
%% > toList :: a -> [a]{-"\phantom{(}"-}
%% > toList x = {-"\uline{"-}Cons x Nil{-"}"-}
%% \end{onlyenv}\end{minipage} & \begin{minipage}{.45\hsize}\begin{uncoverenv}<3->
%%   \begin{AVerb}[gobble=4,numbers=left]
%%     \block toList(x):  
%%       \vbinds nil<- \balt{4}{\uline{\smash{\prim Nil()}}}{\prim Nil()};
%%       \vbinds cons<- \balt{5}{\uline{\smash{\prim Cons(x,nil)}}}{\prim Cons(x,nil)};
%%       \return cons/
%%   \end{AVerb}
%% \end{uncoverenv}\end{minipage}
%% \end{tabular*}


%% \note[item]<2>{Now I transform |toList| into a \mil block. I leave
%% both bits of code on the slide, so I can talk about the correspondances.

%% On the succeeding slides I connect each expression (Nil and Cons x Nil) to
%% the corresponding statement in the block.}
%% \end{frame}

%% \subsection{Closures \& Function Application}
%% \note{I define closures as a data structure with two properties: a
%%   pointer to some body of code and an environment -- a
%%   map that associates variables with values.

%%   To explain closures, I start by explaining free variables
%%   and environments. The first slide shows an expression with
%%   a free variable, |name|. I explain that the value of
%%   name must come from the environment, because it is 
%%   not given as an argument to any function shown.}

%% \begin{frame}[fragile]\vspace{12pt}
%% \begin{tabular*}{\hsize}{@@{}l}
%% \begin{minipage}{\hsize}\elimdisplayskip\begin{onlyenv}<1>
%% > putStrLn ("Hello, " ++ {-"\uline{"-}name{-"}"-} ++ "!"{-"\anchorF(nameVar)"-})
%% \end{onlyenv}\begin{onlyenv}<2>
%% > main {-"\uline{"-}name{-"}\strut"-} = 
%% >   putStrLn ("Hello, " ++ {-"\uline{"-}name{-"}"-}++ "!")
%% \end{onlyenv}\begin{onlyenv}<3-5>
%% > main {-"\uline{"-}name{-"}\strut"-} = do
%% >   let msg greeting = greeting ++ ", " ++ {-"\uline{"-}name{-"}"-} ++ "!"
%% >   {-"\anchorF(hello)"-}putStrLn (msg "Hello")
%% >   {-"\anchorF(nice)"-}putStrLn (msg "Nice to meet you")
%% \end{onlyenv}\begin{onlyenv}<6-9>
%% > main name{-"\strut"-} = do
%% >   let{-"\anchorF(msgDef)"-} msg greeting = greeting ++ ", " ++ name ++ "!"
%% >   {-"\anchorF(mapMsg)"-}mapM_ (putStrLn . msg{-"\anchorF(msgClo)"-} ) [{-"\anchorF(msg1)"-}"Hello",{-"\anchorF(msg2)"-}"Nice to meet you"] 
%% \end{onlyenv}\end{minipage}
%% \end{tabular*}

%% \note<1>{I explain that the value of |name| must be declared in some
%%   outer scope (at least, if we want the program to run). I now show
%%   |main|, which takes |name| as an argument. In this case, the environment
%%   contains |name| because it is argument to |main|.}

%% \note<2>{Now I define a local function, |msg|, explaining that I want
%%   to print different greetings. |msg| takes one argument, |greeting|, but |name|
%%   is free in |msg|.}

%% \note<3>{The next two slides show the environment for each invocation
%%   of |msg|. We assume |main| is invoked with the argument |"Justin"|, as shown
%%   on the right.}

%% \begin{onlyenv}<4>
%% \begin{tikzpicture}[remember picture,overlay]
%%   \path let \p1=(hello.west) in node[stmt, anchor=west] (ep1) at ($(\p1) + (0in, -1in)$) {\mfun{name}: |"Justin"|, \mfun{greeting}: |"Hello"|};
%%   \draw [->] (ep1.west) to ($(ep1.west) + (-.25in,0in)$) ||- (hello.west);
%% \end{tikzpicture}
%% \end{onlyenv}

%% \begin{onlyenv}<5>
%% \begin{tikzpicture}[remember picture, overlay]
%%   \path let \p1=(hello.west) in node[stmt, anchor=west] (ep2) at ($(\p1) + (0in, -1in)$) {\mfun{name}: |"Justin"|, \mfun{greeting}: |"Nice to meet you"|};
%%   \draw [->] (ep2.west) to ($(ep2.west) + (-.25in,0in)$) ||- (nice.west);
%% \end{tikzpicture}
%% \end{onlyenv}

%% \note<5>{Now I explain that I have talked about environments, I move
%%   to the second half: a pointer to some body of code. I rewrite the
%%   program to use |mapM_|. I explain that while previously we could
%%   think of |msg| as executing right away and building a string, we
%%   really can't anymore. Instead, it represents a delayed or suspended
%%   value that we need to supply more arguments to to get our string
%%   out.}

%% \note<6>{I now show the closure represented by |msg|. The ``hole''
%%   points to the function defintion; |name| exists in the environment
%%   (and does not change); |greeting| is shown to indicate that we don't
%%   have all the arguments yet.}

%% \begin{onlyenv}<7>
%% \begin{tikzpicture}[remember picture, overlay,node distance=0in]
%%   \path let \p1=(mapMsg.west) in node[stmt, anchor=west] (msgHole1) at ($(\p1) + (0in, -1in)$) {\strut\phantom{\textbullet}};
%%   \node[stmt, right=0in of msgHole1.east, anchor=west] (ep31) {\mfun{name}: |"Justin"|, \mfun{greeting}: ?};
%%   \draw [->] ($(msgClo.south) + (-.1in,-.1in)$) to (ep31.north);
%%   \draw [*->] (msgHole1.base) to ($(msgHole1.base) + (-.25in,0in)$) ||- ($(msgDef.base) + (-.25in,0in)$);
%% \end{tikzpicture}
%% \end{onlyenv}

%% \begin{onlyenv}<8>
%% \begin{tikzpicture}[remember picture, overlay,node distance=0in]
%%   \path let \p1=(mapMsg.west) in node[stmt, anchor=west] (msgHole2) at ($(\p1) + (0in, -1in)$) {\strut\phantom{\textbullet}};
%%   \node[stmt, right=0in of msgHole2.east, anchor=west] (ep32) {\mfun{name}: |"Justin"|, \mfun{greeting}: |"Hello"|};
%%   \draw [->] ($(msg1.south) + (.2in,-.1in)$) to (ep32.north);
%%   \draw [*->] (msgHole2.base) to ($(msgHole2.base) + (-.25in,0in)$) ||- ($(msgDef.base) + (-.25in,0in)$);
%% \end{tikzpicture}
%% \end{onlyenv}

%% \begin{onlyenv}<9>
%% \begin{tikzpicture}[remember picture, overlay,node distance=0in]
%%   \path let \p1=(mapMsg.west) in node[stmt, anchor=west] (msgHole3) at ($(\p1) + (0in, -1in)$) {\strut\phantom{\textbullet}};
%%   \node[stmt, right=0in of msgHole3.east, anchor=west] (ep33) {\mfun{name}: |"Justin"|, \mfun{greeting}: |"Nice to ..."|};
%%   \draw [->] ($(msg2.south) + (.5in,-.1in)$) to (ep33.north);
%%   \draw [*->] (msgHole3.base) to ($(msgHole3.base) + (-.25in,0in)$) ||- ($(msgDef.base) + (-.25in,0in)$);
%% \end{tikzpicture}
%% \end{onlyenv}

%% \end{frame}

%% \note{Now that I have defined closures, I want to explain
%%   closure-capturing blocks and the @@ operator in this sequence.

%% I start by showing a function that applies |map| to arguments, so I
%% can show how closures are built up and entered.}
%% \begin{frame}[fragile]
%% \vspace{12pt}
%% \begin{onlyenv}<1>
%% > main xs = map toList xs
%% \end{onlyenv}

%% \note<1>{Now I show the \mil code for main, next to the definition of |main|. I
%% want to illustrate the process of capturing arguments for |map|, while also
%% showing the syntax for creating closures and defining \cc blocks. I don't give
%% a lot of detail about the \mil code shown (yet).}

%% \note<2>{I start by rewriting |main| to show each function
%%   application. I motivate this rewrite by noting that I want to highlight
%%   \mil's support for \emph{curried} functions. I give a brief verbal definition of
%%   curried here and note I'll return to it later.}

%% \note<3>{Now I show that |main| starts by creating a closure referring to |toList|. This
%%   closure will be used by |map| to apply |toList| to its arguments. I do not reveal
%%   the definition of toList's \cc block yet.}

%% \note<4>{Now I need to do some hand-waving on why we create a closure 
%%   referring to |map|; I'll just say we create the closure for reasons to be 
%%   explained later.}

%% \begin{onlyenv}<2-6>
%% \begin{tabular*}{\hsize}{@@{}ll}
%% \begin{minipage}[t]{.45\hsize}
%%   \begin{AVerb}[gobble=4,numbers=left]
%%     \block main(xs):
%%       \vbinds t1<-\balt{4}{\uline{\smash{\mkclo[toListK1:]}}}{\mkclo[toListK1:]};
%%       \vbinds t2<-\balt{5}{\uline{\smash{\mkclo[mapK1:]}}}{\mkclo[mapK1:]};
%%       \vbinds t3<-\balt{6}{\uline{\smash{\app t2*t1/}}}{\app t2*t1/};
%%       \vbinds t4<-\app t3*xs/;
%%       \return t4/
%%     \ccblock toListK1()x: \ldots
%%     \ccblock mapK1()f: \mkclo[mapK2:f]
%%     \ccblock mapK2(f)xs: \goto map(f, xs)
%%     \block map(f, xs): \ldots
%%   \end{AVerb}
%% \end{minipage} &
%% \begin{onlyenv}<2>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
%% > main xs = map toList xs{-"\phantom{(}"-}
%% \end{minipage}
%% \end{onlyenv}\begin{onlyenv}<3>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
%% > main xs = (map toList) xs{-"\phantom{(}"-}
%% \end{minipage}
%% \end{onlyenv}\begin{onlyenv}<4>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
%% > main xs = (map {-"\uline{"-}toList{-"}"-}) xs{-"\phantom{(}"-}
%% \end{minipage}
%% \end{onlyenv}\begin{onlyenv}<5>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
%% > main xs = ({-"\uline{"-}map{-"}"-} toList) xs{-"\phantom{(}"-}
%% \end{minipage}
%% \end{onlyenv}\begin{onlyenv}<6>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
%% > main xs = ({-"\uline{"-}map toList{-"}"-}) xs
%% \end{minipage}
%% \end{onlyenv}
%% \end{tabular*}
%% \end{onlyenv}

%% \note<5>{The next slide shows |map| gathering its first argument, the first instance
%%   of function application so far. I underline the relevant portions in each
%% definition, but don't show the \cc blocks yet.}

%% \note<6>{Now I show the two \cc blocks for |map|. I explain how \var t3/ will hold
%%   \mkclo[mapK2:f] after the statement executes. I also state that the definition
%% of \lab toListK1/ isn't relevant yet, so I don't show it.}

%% \note<7>{The next slide will explain
%% the syntax of \cc blocks, connecting line 3 to line 7. }

%% \note<8>{I return to line 4, noting that \var t2/ holds the closure
%%   \mkclo[mapK1:]. I discuss the meaning of the \enter operator, and
%%   describe how the program ``enters'' the closure on the left with the
%%   argument on right. I use the next two slides to show that the body
%%   of \lab mapK1/ returns the closure \mkclo[mapK2:f], and that \var t3/
%%   will refer to that closure.}

%% \note<10>{The next two slides show |map| gathering its final argument
%%   and then executing. I reinforce the previous description of
%%   ``entering'' a closure. I connect the specification of \lab mapK2/
%%   to the value in \var t3/. I especially point out how \var f/ appears
%%   in \var t3/ and \lab mapK2/. I highlight that \lab mapK2/ does not
%%   return a closure, but rather immediately executes the \lab map/
%%   block. The result of \lab map/ gets bound to \var t4/ and returned.}

%% \begin{onlyenv}<7->
%% \begin{tabular*}{\hsize}{@@{}ll}
%% \begin{minipage}[t]{.45\hsize}
%%   \begin{AVerb}[gobble=4,numbers=left]
%%     \block main(xs):
%%       \vbinds t1<-\mkclo[toListK1:];
%%       \vbinds t2<-\balt{8}{\uline{\smash{\mkclo[mapK1:]}}}{\mkclo[mapK1:]};
%%       \vbinds \balt{10}{\uline{\smash{\var t3/}}}{t3}<-\balt{7,9}{\uline{\smash{\app t2*t1/}}}{\app t2*t1/};
%%       \vbinds \balt{12}{\uline{\smash{\var t4/}}}{t4}<-\balt{11}{\uline{\smash{\app t3*xs/}}}{\app t3*xs/};
%%       \return t4/
%%     \balt{8,9}{\uline{\smash{\ccblock mapK1()f:}}}{\ccblock mapK1()f:} \balt{10}{\uline{\smash{\mkclo[mapK2:f]}}}{\mkclo[mapK2:f]}
%%     \balt{11}{\uline{\smash{\ccblock mapK2(f)xs:}}}{\ccblock mapK2(f)xs:} \balt{12}{\uline{\smash{\goto map(f, xs)}}}{\goto map(f, xs)}
%%     \block map(f, xs): \ldots
%%   \end{AVerb}
%% \end{minipage} &
%% \begin{onlyenv}<7-10>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
%% > main xs = ({-"\uline{"-}map toList{-"}"-}) xs{-"\phantom{(}"-}
%% \end{minipage}
%% \end{onlyenv}\begin{onlyenv}<11,12>\begin{minipage}[t]{.45\hsize}\elimdisplayskip
%% > main xs = {-"\uline{"-}(map toList) xs{-"}"-}{-"\phantom{(}"-}
%% \end{minipage}
%% \end{onlyenv}
%% \end{tabular*}
%% \end{onlyenv}
%% \end{frame}

%% \note{I am going to walk through the previous example again, because I want
%% to reinforce the notion of closures and how they work. This time, I will
%% show graphically how closures are allocated as \lab main/ executes. This sequence
%% will focus on the operations that occur when each statement is executed.

%% In the first slide, \var t1/ has been bound to \mkclo[toListK1:] and \var t2/ has
%% been bound to \mkclo[mapK1:]. This aren't very interseting because they don't capture
%% any variables. However, they work together on Line 4, causing \lab mapK1/ to execute
%% and return the value \mkclo[mapK2:f].}


%% \begin{minipage}{.45\hsize}
%%   \begin{AVerb}[gobble=4,numbers=left]
%%     \block main(xs):
%%       \vbinds t1<-\mkclo[toListK1:];
%%       \vbinds t2<-\mkclo[mapK1:];
%%       \vbinds t3<-\app t2*t1/;
%%       \vbinds t4<-\app t3*xs/;
%%       \return t4/
%%     \ccblock toListK1()x: \goto toList(x)
%%     \block toList(x):  
%%       \vbinds nil<- \prim Nil();
%%       \vbinds cons<- \prim Cons(x,nil);
%%       \return cons/
%%     \ccblock mapK1()f: \mkclo[mapK2:f]
%%     \ccblock mapK2(f)xs: \goto map(f, xs)
%%     \block map(f, xs): \ldots
%%   \end{AVerb}
%% \end{minipage} 

%% \subsection{Side-Effects}
%% \begin{frame}
%% \vspace{12pt} \ldots 
%% \end{frame}
%% \subsection{Syntax}
%% \begin{frame}
%% \vspace{12pt} \ldots
%% \end{frame}

%% \begin{comment}
%%     \begin{tikzpicture}[remember picture,overlay]
%%       \node[fact, invis, right=0.25in of consd1, anchor=west] (fvconsd1) {\fct(f:{\mkclo[k219:]}), \fct(x:\top), \fct(xs:\top)};
%%       \draw [->] (fvconsd1) to (consd1);
%%       \node[fact, invis, right=0.25in of v209d1, anchor=west] (fvv209d1) {\fct(v209:\top)};
%%       \draw [->] (fvv209d1) to (v209d1);
%%       \node[fact, invis, right=0.25in of v210d1, anchor=west] (fvv210d1) {\fct(v210:\top)};
%%       \draw [->] (fvv210d1) to (v210d1);
%%       \node[fact, invis, right=0.25in of v211d1, anchor=west] (fvv211d1) {\fct(v211:\top)};
%%       \draw [->] (fvv211d1) to (v211d1);
%%       \node[fact, invis, right=0.25in of v212d1, anchor=west] (fvv212d1) {\fct(v212:\top)};
%%       \draw [->] (fvv212d1) to (v212d1);
%%       \node[fact, invis, right=0.25in of v213d1, anchor=west] (fvv213d1) {\fct(v213:\top)};
%%       \draw [->] (fvv213d1) to (v213d1);
%%       \node[fact, invis, right=0.25in of v214d1, anchor=west] (fvv214d1) {\fct(v214:\top)};
%%       \draw [->] (fvv214d1) to (v214d1);

%%     \end{tikzpicture}

%%     %% \node[overlay,invis,below=.05in of cons4] () {\inL(cons):$\begin{array}{@@{}l}
%%     %%     \{\var f/\,:\,\top\}, \{\var x/\,:\,\top\},\\
%%     %%     \{\var xs/\,:\,\top\}\end{array}$};

%%   %% \begin{onlyenv}<1->\begin{tikzpicture}[overlay,remember picture]
%%   %%   \node[fact, right=0.25in of nsb1, anchor=west] (fvnsb1) {$\{\var ns/\,:\,\top\}$};
%%   %%   \draw [->] (fvnsb1) to (nsb);
%%   %%   \node[fact, right=0.25in of v228b1, anchor=west] (fv228b1) {$\{\var v228/\,:\,\mkclo[k219:]\unskip\}$};
%%   %%   \draw [->] (fv228b1) to (v228b1);
%%   %% \end{tikzpicture}
%%   \begin{onlyenv}<4->\begin{tikzpicture}[remember picture, overlay]
%%     \node[overlay,invis,below left=.15in and -.3in of caseEval216] () {$\emptyset$};
%%   \end{tikzpicture}\end{onlyenv}
%%   \begin{onlyenv}<4>\begin{tikzpicture}[remember picture, overlay]
%%     \node[overlay,invis,below right=.05in and -.1in of caseEval216] () {$\begin{array}{@@{}l}
%%         \{\var f/\,:\,\top\}, \{\var x/\,:\,\top\},\\
%%         \{\var xs/\,:\,\top\}\end{array}$};
%%   \end{tikzpicture}\end{onlyenv}

%%   \begin{onlyenv}<5>\begin{tikzpicture}[remember picture, overlay]
%%     \node[overlay,invis,below right=.07in and -.2in of main] () { $\{\var xs/\,:\,\top\}, \{\var f/\,:\,\mkclo[k219:]\unskip\}$};
%%     \node[overlay,invis,below right=.05in and -.1in of caseEval216] () {$\begin{array}{@@{}l}
%%         \{\var f/\,:\,\mkclo[k219:]\unskip\}, \{\var x/\,:\,\top\}, \\
%%         \{\var xs/\,:\,\top\}\end{array}$};

%%     \draw [->] (main) to (caseEval216);
%%   \end{tikzpicture}\end{onlyenv}


%%     \begin{AVerb}[gobble=6,numbers=left]
%%       \block main(ns): 
%%         \vbinds v227<-\mkclo[k203:];
%%         \vbinds v228<-\mkclo[k219:];
%%         \vbinds v229<-\app v227*v228/;
%%         \app v229 * ns/ 
%%       \ccblock k219()x: \goto toList(x)
%%       \block toList(x):
%%         \vbinds v221<-\mkclo[Cons1:];
%%         \vbinds v222<-\app v221*x/;
%%         \vbinds v223<-Nil;
%%         \app v222 * v223/ 
%%       \ccblock Cons1()a2: \mkclo[Cons2:a2]
%%       \ccblock Cons2(a2)a1: Cons a2 a1
%%     \end{AVerb}
%%   \end{minipage} &
%%   \begin{minipage}[t]{.4\hsize}
%%     \begin{AVerb}[gobble=6,numbers=left,firstnumber=last]
%%       \ccblock k203()f: \mkclo[k204:f]
%%       \ccblock k204(f)xs: \goto map(f,xs)
%%       \block map(f,xs): 
%%         \case xs;
%%           \valt Nil()->\goto nil();
%%           \valt Cons(x xs)->\goto cons(f, x, xs);
%%       \block nil(): Nil 
%%       \block cons(f, x, xs): 
%%         \vbinds v209<-\mkclo[Cons1:];
%%         \vbinds v210<-\app f*x/; 
%%         \vbinds v211<-\app v209*v210/;
%%         \vbinds v212<-\mkclo[k203:]; 
%%         \vbinds v213<-\app v212*f/;
%%         \vbinds v214<-\app v213*xs/; 
%%         \app v211 * v214/ 
%%     \end{AVerb}
%% \end{comment}
\section{Appendix}
\subsection{Uncurrying Comparisons}
\begin{frame}[fragile]{Related Work: Appel}
\begin{minipage}{\hsize}
> f x = g x
> g x y = x + y
> main a b = f a b
\end{minipage}
\begin{minipage}{\hsize}
  \begin{AVerb}[gobble=4,numbers=left,xleftmargin=1em]
    \block main(a, b): \goto b208(a, b)
    \block b208(x, y):
      \vbinds v210<-\mkclo[plusclo1:x];
      \app v210 * y/
    \ccblock plusclo1(a2)a1: \prim plus(a2, a1)
    \block f(): \mkclo[k212:]
    \ccblock k212()x: \mkclo[k207:x]
    \block g(): \mkclo[k206:]
    \ccblock k206()x: \mkclo[k207:x]
    \ccblock k207(x)y: \goto b208(x, y)
  \end{AVerb}
\end{minipage}
\end{frame}
\begin{frame}[fragile]{Related Work: Tarditi}
\begin{minipage}{\hsize}
> g x y z = x + y + z
> h x y = g x y
> main s t u = h s t u
\end{minipage}
\begin{minipage}{\hsize}
  \begin{AVerb}[gobble=4,numbers=left,xleftmargin=1em]
    \block main(s, t, u): \goto b216(s, t, u)
    \block b216(x, y, z):
      \vbinds v219<-\mkclo[plusclo1:x];
      \vbinds v220<- \app v219*y/;
      \vbinds v221<- \mkclo[plusclo1:v220];
      \app v221 * z/
    \ccblock plusclo1(a2)a1: \prim plus(a2, a1)
    \ccblock g(): \mkclo[k213:]
    \ccblock k213()x: \mkclo[k214:x]
    \ccblock k214(x)y: \mkclo[k215:x, y]
    \ccblock h(): \mkclo[k207:]
    \ccblock k207()x: \mkclo[k208:x]
    \ccblock k208(x)y: \mkclo[k215:x, y]
    \ccblock k215(x, y)z: \goto b216(x, y, z)
  \end{AVerb}
\end{minipage} 
\end{frame}
\subsection{Example: Uncurrying with Loops}
\begin{frame}[fragile]{Original Program}
  \hfil\begin{tikzpicture}
  \node[stmt] (b1) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b1():
        \vbinds f<-\mkclo[k1:];
        \vbinds g<-\mkclo[k3:];
        \goto b2(f, g)
    \end{AVerb}
  \end{minipage}};
  \node[stmt, below=.2in of b1] (b2) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b2 (f, g):
        \vbinds t<-\app f*g/; 
        \vbinds u<-\app g*t/;
        \goto b3(t, u, f)
    \end{AVerb}
    \end{minipage}};
  \node[stmt, below=.2in of b2] (b3) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b3 (t, u, f):
        \vbinds v<-\app f*t/; 
        \vbinds w<-\mkclo[k4:v]; 
        \goto b2(f, w)
    \end{AVerb}
    \end{minipage}};
    \draw [->] (b1) to (b2);
    \draw [->] (b2) to (b3);
    \draw [->] (b3.south) to ($(b3.south) + (0mm, -.25in)$) -|| ($(b2.west) + (-.25in, 0mm)$) to (b2.west);
  \end{tikzpicture}
\end{frame}
\begin{frame}[fragile]{Initial Facts}
  \hfil\begin{tikzpicture}
  \node[stmt] (b1) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b1():
        \vbinds f<-\mkclo[k1:];
        \vbinds g<-\mkclo[k3:];
        \goto b2(f, g)
    \end{AVerb}
  \end{minipage}};
  \node[stmt, below=.2in of b1] (b2) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b2 (f, g):
        \vbinds t<-\app f*g/; 
        \vbinds u<-\app g*t/;
        \goto b3(t, u, f)
    \end{AVerb}
    \end{minipage}};
  \node[stmt, below=.2in of b2] (b3) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b3 (t, u, f):
        \vbinds v<-\app f*t/; 
        \vbinds w<-\mkclo[k4:v]; 
        \goto b2(f, w)
    \end{AVerb}
    \end{minipage}};
    \draw [->] (b1) to (b2);
    \draw [->] (b2) to (b3);
    \draw [->] (b3.south) to ($(b3.south) + (0mm, -.25in)$) -|| ($(b2.west) + (-.25in, 0mm)$) to (b2.west);

    \node[fact,invis,right=.1in of b1,text width=1.5in] () 
         {\outL(b1): \fct(f:\mkclo[k1:]), \fct(g:\mkclo[k3:])};
    \node[fact,invis,right=.1in of b2,text width=1.5in] () 
         {\inL(b2): \fct(f:\mkclo[k1:]), 
           \fct(g:\top)};
    \node[fact,invis,left=.3in of b3.west,text width=.75in,anchor=east] () 
         {\outL(b3): \fct(g:\mkclo[k4:v])};
  \end{tikzpicture}
\end{frame}
\begin{frame}[fragile]{Facts After Iteration}
  \hfil\begin{tikzpicture}
  \node[stmt] (b1) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b1():
        \vbinds f<-\mkclo[k1:];
        \vbinds g<-\mkclo[k3:];
        \goto b2(f, g)
    \end{AVerb}
  \end{minipage}};
  \node[stmt, below=.2in of b1] (b2) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b2 (f, g):
        \vbinds t<-\app f*g/; 
        \vbinds u<-\app g*t/;
        \goto b3(t, u, f)
    \end{AVerb}
    \end{minipage}};
  \node[stmt, below=.2in of b2] (b3) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b3 (t, u, f):
        \vbinds v<-\app f*t/; 
        \vbinds w<-\mkclo[k4:v]; 
        \goto b2(f, w)
    \end{AVerb}
    \end{minipage}};
    \draw [->] (b1) to (b2);
    \draw [->] (b2) to (b3);
    \draw [->] (b3.south) to ($(b3.south) + (0mm, -.25in)$) -|| ($(b2.west) + (-.25in, 0mm)$) to (b2.west);

    \node[fact,invis,right=.1in of b1,text width=1.5in] () 
         {\outL(b1): \fct(f:\mkclo[k1:]), \fct(g:\mkclo[k3:])};
    \node[fact,invis,right=.1in of b2,text width=1.5in] () 
         {\inL(b2): \fct(f:\mkclo[k1:]), 
           \fct(g:\top)};
    \node[invis,fact,right=.1in of b3,text width=1.5in] () 
         {\inL(b3): \fct(t:\mkclo[k2:g]), \fct(u:\top), \fct(f:\mkclo[k1:])};
    \node[fact,invis,left=.3in of b3.west,text width=.75in,anchor=east] () 
         {\outL(b3): \fct(f:\mkclo[k1:]), \fct(g:\mkclo[k4:v])};
  \end{tikzpicture}
\end{frame}
\begin{frame}[fragile]{Rewrite}
  \hfil\begin{tikzpicture}
  \node[stmt] (b1) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b1():
        \vbinds f<-\mkclo[k1:];
        \vbinds g<-\mkclo[k3:];
        \goto b2(f, g)
    \end{AVerb}
  \end{minipage}};
  \node[stmt, below=.2in of b1] (b2) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b2 (f, g):
        \vbinds t<-\mkclo[k2:g];
        \vbinds u<-\app g*t/;
        \goto b3(t, u, f)
    \end{AVerb}
    \end{minipage}};
  \node[stmt, below=.2in of b2] (b3) {\begin{minipage}{1in}
    \begin{AVerb}[gobble=6]
      \block b3 (t, u, f):
        \vbinds v<-\mkclo[k2:t];
        \vbinds w<-\mkclo[k4:v]; 
        \goto b2(f, w)
    \end{AVerb}
    \end{minipage}};
    \draw [->] (b1) to (b2);
    \draw [->] (b2) to (b3);
    \draw [->] (b3.south) to ($(b3.south) + (0mm, -.25in)$) -|| ($(b2.west) + (-.25in, 0mm)$) to (b2.west);

    \node[fact,invis,right=.1in of b1,text width=1.5in] () 
         {\outL(b1): \fct(f:\mkclo[k1:]), \fct(g:\mkclo[k3:])};
    \node[fact,invis,right=.1in of b2,text width=1.5in] () 
         {\inL(b2): \fct(f:\mkclo[k1:]), 
           \fct(g:\top)};
    \node[invis,fact,right=.1in of b3,text width=1.5in] () 
         {\inL(b3): \fct(t:\mkclo[k2:g]), \fct(u:\top), \fct(f:\mkclo[k1:])};
    \node[fact,invis,left=.3in of b3.west,text width=.75in,anchor=east] () 
         {\outL(b3): \fct(f:\mkclo[k1:]), \fct(g:\mkclo[k4:v])};
  \end{tikzpicture}
\end{frame}
\subsection{Future Work}
\begin{frame}{Future Work}
  \begin{itemize}
  \item Eliminating Thunks
  \item ``Push Through Cases''
  \end{itemize}
\end{frame}
\end{document}
