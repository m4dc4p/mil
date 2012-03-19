%&preamble
\input{nodocclass}\dodocclass
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\begin{document}
\numbersoff
\input{document.preamble}
\chapter{Conclusion \& Future Work}
\label{ref_chapter_conclusion}

\intent{Introduce our contributions.}  Our work applied the dataflow
algorithm to an area outside its traditional scope: functional
languages. We based our work on a \emph{monadic intermediate language}
(\mil) that supported high-level functional programming and exposed
certain low-level implementation details. We implemented our analysis
in Haskell using the \hoopl library; we also gave a thorough
description of how to implement dataflow-based optimizations using
\hoopl. We then demonstrated the utility of our work by using \hoopl
and \mil to create a novel implementation of the uncurrying
optimization. 

\intent{Signposts for chapter.} Though we choose the uncurrying
optimization to demonstrate our approach, several avenues of future
work remain.  We explore optimizations that take advantage of the
unique features of \mil in Section~\ref{conc_future_work}. We offer
some thoughts on the \hoopl library in
Section~\ref{conc_hoopl}. Section~\ref{conc_conc} offers our closing
thoughts.

\section{Future Work}
\label{conc_future_work}

This section describes optimizations that take particular advantage of
\mil's features. Sections~\ref{conc_inline_monadic} and
\ref{conc_deadcode} describe transformations based on the monadic
structure of \mil programs.  We extend uncurrying across \mil blocks
in Section~\ref{conc_uncurrying}, and discuss how to extend the same
optimization to thunks in Section~\ref{conc_thunks}.
Section~\ref{conc_cases} proposes a new analysis to eliminate
unnecessary allocations across \milres case/ statements.

\subsection{Inlining Monadic Code}
\label{conc_inline_monadic}
Figure~\ref{conc_fig_monad_laws} shows the \emph{monad laws}:
left-Unit, Right-Unit, and Associativity.  While these laws can be
interpreted as specifications of behavior, they can also be
interpreted as \emph{transformations}. 

\begin{myfig}
  \begin{math}
    \begin{aligned}
      |do { x <- return y; m }| & \equiv\ |do { {-"\lamSubst{y}{x}\ "-} m}| & \text{\it Left-Unit} & \quad\labeledeq{eq_left_unit} \\
      |do { x <- m; return x }| & \equiv\ |do { m }| & \text{\it Right-Unit} & \quad\labeledeq{eq_right_unit} \\
      \llap{|do { x <- do {y <- m; n}; o }|} & \equiv\ |do { y <- m; x <- n; o} |& \text{\it Associativity} & \quad\labeledeq{eq_assoc}
    \end{aligned}
  \end{math}
  \caption{The monad laws, as stated by Wadler
    \citeyearpar{Wadler1995}. The notation ``$\lamSubst{y}{x}\ m$''
    means that $y$ should be substituted for $x$ everywhere in $m$.  }
  \label{conc_fig_monad_laws}
\end{myfig}

For example, the following block binds
\var x/ to the value of \var y/, keeping both variables live between
the ``\binds x\ <-\ \return y/;'' and \goto l(x,y) statements:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b():
      \vbinds x<- \return y/;
      \dots
      \goto l(x, y)
  \end{AVerb}
\end{singlespace}

\noindent If no intervening statement binds \var x/ again, we can use
the Left-Unit law to replace all occurrences of \var x/ with \var y/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b():
      \vbinds x<- \return y/;
      $\dots$
      \goto l(y, y)
  \end{AVerb}
\end{singlespace}

\noindent Because we know \return y/ produces no side-effects, we can
eliminate the binding for \var x/. If variables represent registers,
this optimization reduces the number of registers used by the block and
makes it smaller: 

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b():
      $\dots$
      \goto l(y, y)
  \end{AVerb}
\end{singlespace}

The Right-Unit law shortens the ``tail'' of \mil blocks that end with a
\return/ statement. For example, Right-Unit can be used to transform the
following block:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b(\dots):
      \dots
      \vbinds x<- \app f*y/;
      \return x/
  \end{AVerb}
\end{singlespace}

\noindent into the shorter block:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b(\dots):
      \dots
      \app f * y/
  \end{AVerb}
\end{singlespace}

\noindent Not only does this tranformation eliminate a redundant
\milres return/ statement, it may also allow further optimizations. In
particular, if we know that the closure represented by \var f/ refers to
block \lab b/, our uncurrying optimization will tranform \app f * y/
into either a jump or an allocation.

The Associativity law provides an inlining mechanism for \mil
programs. The inner monadic computation mentioned on the right-hand
side of the law, |do { y <- m; n }|, can be an arbitrarily long monadic
program. All \mil blocks are monadic programs --- therefore, we can use
this law to inline almost any block. For example, consider these two blocks:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block compose(f, g, x): 
      \vbinds t1<- \app g*x/;
      \vbinds t2<- \app f*t1/;
      \return t2/ 

    \block main(a,b,c): 
      \vbinds x<- compose(a,b,c);
      \goto b(x)
  \end{AVerb}
\end{singlespace}

Equation~\eqref{eq_assoc} lets us inline \lab compose/ into \lab main/, as
long as we appropriately rename variables:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main(a,b,c): 
      \vbinds t1<- \app b*c/;
      \vbinds t2<- \app a*t1/;
      x <- \return t2/ 
      \goto b(x)
  \end{AVerb}
\end{singlespace}

\noindent Notice that we can now also apply Equation~\eqref{eq_left_unit}, eliminating
the use of \var x/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main(a,b,c): 
      \vbinds t1<- \app b*c/;
      \vbinds t2<- \app a*t1/;
      \goto b(t2)
  \end{AVerb}
\end{singlespace}

\Mil's syntax does not allow all monadic blocks to be inlined. \Mil
ensures that every block is also a basic block. A basic block cannot
branch to multiple destinations. Therefore, blocks that end in \milres
case/ statements cannot be inlined.

However, we can still transform around blocks that end in \milres
case/ statements. Consider the blocks \lab b1/, \lab t/ and \lab f/ in
the following program:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b1(a):
       \vbinds t1<- \goto b2(a);
       \dots
       \goto b3(t1)

    \block b2(a):
      \case a;
        \valt{}True()->\goto t(a);
        \valt{}False()->\goto f(a);

    \block t(\dots):
       \dots
       \return x/

    \block f(\dots):
       \dots
       \return x/
  \end{AVerb}
\end{singlespace}

\lab b1/ binds \var t1/ to the result of \lab b2/. \lab b2/ returns
the result of either block \lab t/ or \lab f/. Because \lab t/ and
\lab f/ do not end in a \milres case/ statement, we can move the code
that follows \var t1/'s binding in \lab b1/ to \lab t/ and \lab f/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b1(a):
       \goto b2(a)

    \block b2(a):
      \case a;
        \valt True()->\goto t(a);
        \valt False()->\goto f(a);

    \block t(a):
       \dots
       \vbinds t1<-\return x/;
       \goto b3(t1)

    \block f(\dots):
       \dots
       \vbinds t1<-\return x/;
       \goto b3(t1)
  \end{AVerb}
\end{singlespace}

\noindent This new program may be more efficient. For example, blocks
\lab t/ and \lab f/ end in tail calls, where before they ended in a
\return/. We can use the Left-Unit law to substitute \var x/ for \var
t1/ in \lab t/ and \lab f/ as well (which, in turn, allows us to
remove \var t1/'s binding in both blocks as it is no longer live). We may be able to
rewrite calls \lab b1/ to \lab b2/, and remove \lab b1/
altogether. Finally, the ``Push Through Cases'' optimization described
in Section~\ref{conc_cases} may be able to optimize \lab t/ and \lab
f/ even further.

\subsection{Dead-Code Elimination}
\label{conc_deadcode}

The Left-Unit law lets us eliminate a simple form of
dead-code, in which we can guarantee that the binding eliminated has
no observable side-effect. However, the law does not apply to any
monadic expression more complicated than |return x|. We treat
allocation as a monadic operation in MIL, but we cannot really observe
any side-effect of allocation (except our program may consume more
memory or run slower). Therefore we can eliminate any closure, thunk
or constructor allocation expressions that bind to a dead variable.

On Page~\pageref{uncurry_fig_compose}, we gave the \lamC definition of
|compose1|, which just captures the first argument to |compose|, and the
corresponding MIL code:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block compose1(): \mkclo[absBodyL208:]
    \ccblock absBodyL208()f: \goto absBlockL209(f)
    \block absBlockL209(f):
      \vbinds v210 <- \goto compose(); 
      \app v210 * f/ 
    
    \block compose(): \mkclo[absBodyL201:]
    \ccblock absBodyL201()f: \mkclo[absBodyL202:f]
  \end{AVerb}
\end{singlespace}

\noindent We can use the Associativity law (Equation~\eqref{eq_assoc} on
Page~\pageref{conc_inline_monadic}) to inline the allocation returned
by block \lab compose/ into block \lab absBlockL209/, giving us:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \dots
    \block absBlockL209(f):
      \vbinds v210 <- \mkclo[absBodyL201:]; 
      \app v210 * f/ 
    
    \block compose(): \mkclo[absBodyL201:]
    \ccblock absBodyL201()f: \mkclo[absBodyL202:f]
  \end{AVerb}
\end{singlespace}

\noindent Our uncurrying optimization then rewrites block \lab absBlockL209/ so it
directly returns the closure previously returned by \lab absBodyL201/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \dots
    \block absBlockL209(f):
      \vbinds v210 <- \mkclo[absBodyL201:]; 
      \mkclo[absBodyL202:f]
    
    \block compose(): \mkclo[absBodyL201:]
    \ccblock absBodyL201()f: \mkclo[absBodyL202:f]
  \end{AVerb}
\end{singlespace}

\noindent We can then apply dead-code elimination to remove the
allocation bound to \var v210/, since that variable is now dead.

\subsection{Uncurrying Across Blocks}
\label{conc_uncurrying}

Our uncurrying optimization only works within a single MIL
block. Extending the optimization across blocks seems obvious, but
presents several implementation challenges. Figure~\ref{conc_uncurry}
illustrates why. In Part~\subref{conc_uncurry_a}, |cap1| partially
applies |cap|, capturing |xs|. In turn, |cap1| is applied to |f| and
either |y| or |n| in the arms of the |case| statement. In
Part~\subref{conc_uncurry_b}, the \lab uncurry/ block creates the
closure represented by |cap1|. Tracing the usage of that closure
through \lab caseEval214/ shows that the two case arm blocks, \lab
altTrue208/ and \lab altFalse211/, eventually call \lab b205/ with the
value \var f/, \var t/ or \var f/ (respectively), and \var ys/.

\begin{myfig}
  \begin{tabular}{cc}
\begin{minipage}{3in}
> uncurry xs t y n f = 
>   let  cap ys g v = (g v) ys
>        cap1 = cap xs
>   in case t of 
>        True -> (cap1 f) y
>        False -> (cap1 f) n
\end{minipage} &
\begin{minipage}{3in}
   \begin{AVerb}[gobble=6]
      \block uncurry4 (t, f, y, n, xs):
        \vbinds cap1 <- \mkclo[k203:xs];
        \goto caseEval214(t, cap1, f, y, n)
      \ccblock k203(ys)g: \mkclo[k204: g, ys]
      \ccblock k204(g, ys)v: \mkclo[b205: g, v, ys]
      \block b205 (g, v, ys):
        \vbinds v206 <- \app g*v/;
        \app v206*ys/
      \block altTrue208(cap1, f, y):
        \vbinds v209 <- \app cap1*f/;
        \app v209*y/
      \block altFalse211(cap1, f, n):
        \vbinds v212 <- \app cap1*f/;
        \app v212*n/
      \block caseEval214 (t, cap1, f, y, n):
        \case t;
          \valt True()->\goto altTrue208(cap1, f, y);
          \valt False()->\goto altFalse211(cap1, f, n);
   \end{AVerb}
\end{minipage} \\\\
  \scap{conc_uncurry_a} & \scap{conc_uncurry_b}  
  \end{tabular}
  \caption{A program that illustrates challenges that occur when uncurrying across blocks.}
  \label{conc_uncurry}
\end{myfig}

Therefore, we could reasonably uncurry \lab altFalse211/ and
\lab altTrue208/ to call the block directly:

\begin{singlespace}
  \begin{AVerb}
    ...
    b205 (g, v, ys):
      v206 <- \app g*v/
      \app v206*ys/
    altTrue208 (cap1, f, y):
      b205(f, y, ?)
    altFalse211 (cap1, f, n):
      b205(f, n, ?)
  \end{AVerb}
\end{singlespace}

\noindent Unfortunately, as represented by the !+?+! symbol,
\lab altTrue208/ and \lab altFalse211/ do not have the \var ys/ argument
in scope that is expected by \lab b205/. That argument is captured
by \var cap1/. In order to bring it in scope, we need to rewrite the live
variables available to each block, starting from \lab caseEval214/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    ...
    b205 (g, v, ys):
      v206 <- \app g*v/
      \app v206*ys/
    altTrue208 (ys, f, y):
      b205(f, y, ys)
    altFalse211 (ys, f, n):
      b205(f, n, ys)
    caseEval214 (t, ys, f, y, n):
      case t of
        True -> altTrue208(ys, f, y)
        False -> altFalse211(ys, f, n)
  \end{AVerb}
\end{singlespace}

Rewriting blocks to track live variables in order to support this
optimization does not seem impossible, but it does seem tricky.

\subsection{Eliminating Thunks}
\label{conc_thunks}

Monadic thunks and closures share many characteristics. For example,
they both represent suspended computation, and they both capture an
environment of values. They also can be a source of inefficiency, as
well. Our compiler for \lamC to MIL produces many blocks the
immediately invoke some thunk. For example, the following \lamC
definition:

> main x = do
>   print x

\noindent compiles to this MIL code (in part):

\begin{singlespace}
  \begin{AVerb}
    \block printmon (a): \mkthunk[printbody: a]
    \block printbody (a): \prim print(a)

    \block main (x):
      \vbinds v206 <- \mkclo[printmon:];
      \vbinds v207 <- \app v206 * x/;
      \vbinds () <- \invoke v207/;
  \end{AVerb}
\end{singlespace}

\noindent The application \app v206 * x/ results in a thunk (\mkthunk
[printbody: a]) which is immediately invoked. A more efficient program
would bypass the allocation and instead directly invoke the monadic
action:

\begin{singlespace}
  \begin{AVerb}
    \block printmon (a): \mkthunk[printbody: a]
    \block printbody (a): \prim print(a)

    \block main (x):
      \vbinds v206 <- \mkclo[printmon:];
      \vbinds v207 <- \mkthunk[printbody: x];
      \vbinds () <- \invoke v207/;
  \end{AVerb}
\end{singlespace}

\noindent It seems our uncurrying analysis could be adapted to thunks in order to
implement such an optimization.

\subsection{Push Through Cases}
\label{conc_cases}

Functional language programs commonly implement a pattern of
\emph{construct/destruct}, where the program creates some value at one
point, and then inspects the value using case discrimination at
another point. Figure~\ref{conc_fig_cons_dest} shows one such
program. The |dec| function decrements a value, but only if the value
is greater than 0. It returns a |Maybe| value, indicating if the value
could be decremented or not. The |loop| function decrements |n| and
applies |f| to the result. When |dec n| returns |Nothing|, |loop|
stops executing.\footnote{This example is pretty contrived, but |dec|
  could be used for something more interesting, such as array bounds
  checks.}

\begin{myfig}
\begin{minipage}{\textwidth}
> dec :: Int -> Maybe Int
> dec i = if i > 0 
>          then Just (i - 1)
>          else Nothing

> loop :: Int -> (Int -> Int) -> Int
> loop n f = case dec n of
>   Just i -> loop (f i) f
>   Nothing -> f 0
\end{minipage}
\caption{A program that illustrates the \emph{construct/destruct} pattern.}
\label{conc_fig_cons_dest}
\end{myfig}

These two functions starkly illustrate the \emph{construct/destruct}
pattern. |loop| discriminates on the result of |dec n|, immediately
destructing the value created by |dec|. Figure~\ref{conc_fig_push1}
shows unoptimized MIL code for these two functions. \lab loop/
evaluates \goto dec(n) on Line~\ref{conc_fig_push1_goto_dec} and binds
the result to \var v215/. The \milres case/ statement on the next line
immediately \var v215/ apart, throwing away the allocated value just
created. This pattern introduces at least one allocation in every
invocation of |loop|.\footnote{A sufficiently clever compiler could
  put |Maybe| values into registers and avoid a heap allocation, of
  course. But, no compiler can be clever enough to cover all possible
  data types. We can always create one sufficiently large that a heap
  allocation must occur.}

\begin{myfig}
  \begin{minipage}{\textwidth}
    \begin{singlespace}
      \begin{AVerb}[gobble=8,numbers=left]
        \block loop(n, f):
           \vbinds v215<-\goto dec(n); \label{conc_fig_push1_goto_dec}
           \case v215;
              \valt{}Just(i)->\goto altJust(f, i);
              \valt{}Nothing()->\goto altNothing(f);
      
        \block dec(i): \label{conc_fig_push1_dec}
           \vbinds v233<-\prim gt(i, 0);
           \case v233;
              \valt{}True()->\goto altTrue(i);
              \valt{}False()->\goto altFalse();
      
        \block altNothing(f): \app{}f * 0/
      
        \block altJust(f, n):
           \vbinds v207<- \app f*n/;
           \goto loop(v207, f)
      
        \block altTrue(i):
           \vbinds v225<- \prim minus(i, 1);
           \prim Just(v225)
      
        \block altFalse(): \prim Nothing()
      \end{AVerb}
    \end{singlespace}
  \end{minipage}
  \caption{Initial form of our function.}
  \label{conc_fig_push1}
\end{myfig}

Inspecting the \lab dec/ block in Figure~\ref{conc_fig_push1} shows
that it evaluates a condition and branches to either \lab altTrue/ or
\lab altFalse/. We cannot directly inline \lab loop/ into \lab dec/,
because \lab loop/ ends with a \milres case/ statement. However, we
can move the body of \lab loop/ into each arm of the \milres case/
statement that ends \lab loop/.

Figure~\ref{conf_fig_push2} shows that we inline \lab dec/ into \lab
loop/, and then pushed the portion of \lab loop/ that followed the
statement \binds v215 <- \goto dec(n); into the \lab altTrue/ and \lab
altFalse/ blocks. For example, where \lab altFalse/ previously
contained one statement (\prim Nothing()), we now bind \var v215/ to
that value. In both blocks, the value bound is immediately destructed
by a \milres case/ statement. 
\begin{myfig}
  \begin{minipage}{\textwidth}
    \begin{singlespace}
      \begin{AVerb}[gobble=8]
        \block loop(n, f):
           \vbinds v233<-\prim gt(i, 0);
           \case v233;
              \valt{}True()->\goto altTrue(i, f, n);
              \valt{}False()->\goto altFalse(f, n);
      
        \block altTrue(i, f, n):
           \vbinds v225<-\prim minus(i, 1);
           \vbinds v215<-\prim Just(v225);
           \case v215;
              \valt{}Just(i)->\goto altJust(f, i);
              \valt{}Nothing()->\goto altNothing(f);
      
        \block altFalse(f, n): 
           \vbinds v215<-\prim Nothing();
           \case v215;
              \valt{}Just(i)->\goto altJust(f, n);
              \valt{}Nothing()->\goto altNothing(f);
    
        \block altNothing(f): \app{}f * 0/
      
        \block altJust(f, n):
           \vbinds v207<- \app f*n/;
           \goto loop(v207, f)
      
      \end{AVerb}
    \end{singlespace}
  \end{minipage}
  \caption{First transformation.}
  \label{conc_fig_push2}
\end{myfig}

A simple dataflow analysis (such as constant folding) of \lab altTrue/
and \lab altFalse/ in Figure~\ref{conc_fig_push2} would show that one
or the other branch in each case is never
taken. Figure~\ref{conf_fig_push3} shows how we could rewrite \lab
altTrue/ and \lab altFalse/, eliminating the allocation and
discrimination. This version of the program will perform no
allocations of |Maybe| values whatsoever, but we are still guaranteed
that |f| will not be applied to an index value less than 0.

\begin{myfig}
  \begin{minipage}{\textwidth}
    \begin{singlespace}
      \begin{AVerb}[gobble=8]
        \block loop(n, f):
           \vbinds v233<- \prim gt(i, 0);
           \case v233;
              \valt{}True()->\goto altTrue(i, f, n);
              \valt{}False()->\goto altFalse(f, n);
      
        \block altTrue(i, f, n):
           \vbinds v225<- \prim minus(i, 1);
           \goto altJust(f, v225)
      
        \block altFalse(f, n): 
           \goto altNothing(f)
    
        \block altNothing(f): \app{}f * 0/
      
        \block altJust(f, n):
           \vbinds v207<- \app f*n/;
           \goto loop(v207, f)
      \end{AVerb}
    \end{singlespace}
  \end{minipage}
  \caption{Final form of our function.}
\end{myfig}

%% \begin{myfig}
%%   \begin{tikzpicture}[>=stealth, node distance=.5in]\nomd
    
%%   \node[stmt] (loop) {
%%     \begin{minipage}{2.4in}
%%       \begin{AVerb}[gobble=8]
%%         \block loop(n, f):
%%           \vbinds v215<- \goto dec(n);
%%           \case v215;
%%             \valt{}Just(i)->\goto altJust(f, i);
%%             \valt{}Nothing()->\goto altNothing(f);
%%       \end{AVerb}
%%     \end{minipage}
%%   };

%%   \node[stmt, right=0.45in of loop] (dec) {
%%     \begin{minipage}{2.2in}
%%       \begin{AVerb}[gobble=8]
%%         \block dec(i):
%%           \vbinds v233<- \prim gt(i, 0);
%%           \case v233;
%%             \valt{}True()->\goto altTrue(i);
%%             \valt{}False()->\goto altFalse();
%%       \end{AVerb}
%%     \end{minipage}
%%   };

%%   \node[stmt, below right=0.35in and -1.15in of loop] (altNothing) {
%%     \begin{minipage}{\widthof{\block altNothing(f):}}
%%       \begin{AVerb}[gobble=8]
%%         \block altNothing(f):
%%            \app{}f * 0/
%%       \end{AVerb}
%%     \end{minipage}
%%   };

%%   \node[stmt, below left=0.35in and -1.15in of loop] (altJust) {
%%     \begin{minipage}{\widthof{\block altJust(f, n):\ \ \ }}
%%       \begin{AVerb}[gobble=8]
%%         \block altJust(f, n):
%%           \vbinds v207<- \app f*n/;
%%           \goto loop(v207, f)
%%       \end{AVerb}
%%     \end{minipage}
%%   };

%%   \node[stmt, below=0.35in of dec] (altTrue) {
%%     \begin{minipage}{\widthof{\block altTrue(i): \prim minus(i, 1)}}
%%       \begin{AVerb}[gobble=8]
%%         \block altTrue(i):
%%           \vbinds v225<- \prim minus(i, 1);
%%           \prim Just(v225)
%%       \end{AVerb}
%%     \end{minipage}
%%   };

%%   \node[stmt, below=0.35in of altTrue] (altFalse) {
%%     \begin{minipage}{\widthof{\block altFalse(): \prim Nothing()}}
%%       \begin{AVerb}[gobble=8]
%%         \block altFalse(): \prim Nothing()
%%       \end{AVerb}
%%     \end{minipage}
%%   };

%%   \draw [->] (loop.south) ||- ($(loop.south) - (0in,0.1in)$) -|| (altJust.north);
%%   \draw [->] (loop.south) ||- ($(loop.south) - (0in,0.1in)$) -|| (altNothing.north);
%%   \draw [->] (altJust.south) ||- ($(altJust.south) - (1in,0.3in)$) ||- (loop.west);
%%   \end{tikzpicture}
%% \end{myfig}

\section{Hoopl Refinements}
\label{conc_hoopl}

\intent{Summary of our Hoopl usage.} The Hoopl library played a
critical role in our work. The library presents a simple and powerful
interface for describing, analyzing and transforming CFGs. It allowed
us to explore a variety of optimizations that used dataflow analysis,
without the burden of implementing the dataflow algorithm ourselves.
Of course, by spending so much time with the library, we found some
areas where the library's interface left us struggling to bend our
algorithm to fit with Hoopl's view of dataflow analysis.

\subsection{Invasive Types}
\intent{Hoopl's use of |O| and |C| types requires your AST to support
  Hoopl from the beginning.} Hoopl uses the the |O| and |C| types
(described in Section~\ref{hoopl_sec_cfg}) to specify the shape of
each node in the \cfg; only nodes with compatible types can be
connected to each other. This design allows the compiler to enforce
some desirable properties; for example, a basic block will not contain
any nodes that can branch to more than one destination. Unfortunately,
this design requires that the |O| and |C| types be present on the
client AST. We found life much easier when we designed our AST with
Hoopl in mind from the beginning; otherwise, we found ourselves writing
a lot of code to transform between our existing AST and a nearly
identical, Hoopl-ized, version of the same.

``Smart'' constructors could be used to reduce the boilerplate
required when using Hoopl against an existing AST. For example,
consider the the AST given in Figure~\ref{hoopl_fig3} on
Page~\pageref{hoopl_fig3}. Instead of defining |CStmt| using GADTs,
imagine we defined |CStmtX| as a normal ADT and |CStmt| as a
|newtype|:

\begin{singlespace}
> data CStmtX = Entry Label |
>   Assign Var CExpr
>   {-"\dots"-}
>
> newtype CStmt o c = CStmt CStmtX
\end{singlespace}

\noindent To create Hoopl-ized values, we define a function for each constructor
(i.e., |Entry|, |Assign|, etc.) that both creates the correct |CStmtX| value and
parameterizes it by shape:

\begin{singlespace}
> entry :: Label -> CStmt O C
> entry l = CStmt (Entry l)
>
> assign :: Var -> CExpr -> CStmt O O
> assign v e = CStmt (Assign v e)
\end{singlespace}

However, this approach still requires that a fair amount of
boilerplate code be created. GADTs alleviate the problem somewhat
(since the compiler implements ``smart'' constructors for you), but
that does not help when working against an AST that cannot be
changed. Metaprogramming techniques using Template Haskell, combined
with one of the several generic programming libraries available to
Haskell may ultimately be the best approach here.

\subsection{Restricted Signatures}
\intent{Review of combinators for creating rewrite and transfer
  functions.} Hoopl does not specify transfer and rewrite functions
using simple function signatures. Instead, as detailed in
Section~\ref{hoopl_sec5}, Hoopl represents those functions using the
|BwdTransfer|, |BwdRewrite|, |FwdTransfer| and |FwdRewrite| types.
Client programs cannot directly create these values; instead, Hoopl
defines a function for creating each type: 

\begin{singlespace}
> mkFTransfer :: (forall e x . n e x -> f -> Fact x f) -> FwdTransfer n f
> mkBTransfer :: (forall e x . n e x -> Fact x f -> f) -> BwdTransfer n f      
> mkFRewrite :: FuelMonad m => 
>   (forall e x . n e x -> f -> m (Maybe (Graph n e x))) 
>   -> FwdRewrite m n f
> mkBRewrite :: FuelMonad m => 
>   (forall e x . n e x -> Fact x f -> m (Maybe (Graph n e x)))
>   -> BwdRewrite m n f
\end{singlespace}

\noindent As Hoopl does
not directly export the constructors for |FwdTransfer|, etc. this
scheme limits the signature of transfer and rewrite functions to
those shown above. 

\intent{Why the type signatures are too restrictive.} Unfortunately,
this scheme added some burden to our implementation. At several times
we wished that Hoopl allowed an accumulating parameter for
intermediate results in the signature of both transfer and rewrite
functions. Normally the |Fact| value should serve as an accumulator,
but it seems less than ideal to pollute the |Fact| value with
intermediate results that are only used within the transfer (or
rewrite) function.

\intent{Custom monad does allow arbitrary state, but the
  implementation cost is high.} Hoopl does allow the client program to
define a custom monad for using during rewrite, which does allow
intermediate results to be used. Implementing and using the monad
requires a modest amount of work: the client must make their monad an
instance of the |CheckpointMonad| class and use the |liftFuel|
function to lift custom monadic operations into the |FuelMonad|
class. Unfortunately, the custom monad still does not help with the
transfer function.

\intent{Summarize complaint.}  Earlier versions of the Hoopl library
allowed the client to return an arbitrary \emph{function} from the
transfer and rewrite functions. While that may have been too liberal,
we certainly wished for a slightly less restricted interface during
our work.

\section{Summary}
\label{conc_conc}

\intent{Review goals.} Kildall applied his dataflow algorithm to \textsc{algol
60}, an imperative, structured programming language. Most work in
dataflow analysis since then has focused on imperative programming
languages. We set out to explore the algorithm's use within the
context of a functional programming language; specifically, we hypothesized that,
by compiling to a monadic intermediate language, we could obtain a
basic-block structure that would be amiable to dataflow analysis. We
intended to implement optimizations drawn from the literature of
imperative and functional compilers, showing that the algorithm could
be applied in both contexts.

\intent{Contribution: MIL.} The monadic intermediate language
we described builds on a large body of work on monadic programming,
intermediate languages, and implementation techniques for functional
languages. While the overall concept is well-known, we believe MILs
still offers some novelty. MIL makes allocation explicit but still
offers high-level features like function application and case
discrimination. MIL programs, by design, consist of basic-block
elements. Of course, many intermediate languages consist of
basic-blocks, but MIL again combines that structure with a monadic
programming model, giving a ``pure'' flavor to low level operations.

\intent{Contributions: Hoopl.} Our work relied quite a bit on the
Hoopl library. Without it, we may not have even chosen this
research. While we did not contribute materially to Hoopl itself, this
work offers a significant amount of expository material describing
Hoopl, as well as at least one implementation of a non-trivial
optimization, that cannot be found elsewhere.

\intent{Contributions: Uncurrying.} Our work
contributes in several areas. Most importantly, we described
uncurrying in terms of dataflow analysis over our monadic intermediate
language. We did not find other work in this area, making us the first
to implement uncurrying over a MIL using dataflow analysis. In fact,
leaving aside our MIL, we did not find any other description of
uncurrying which used dataflow analysis. 

\intent{Summary \& Conclusion.}

\standaloneBib 

%% Some interaction with standalone makes the thesis break unless we
%% end with \noindent. The error is:
%%
%%   "You can't use `\\unskip' in vertical mode.\\sa@atenddocument
%%   ->\\unskip".
%%
\noindent\end{document}
