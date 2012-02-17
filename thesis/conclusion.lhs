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

\section{Hoopl Refinements}

\section{Future Work}

Many optimizations which use dataflow analysis to transform imperitave
programs exist (in particular, Muchnik \citeyearpar{Muchnick1998}
gives a broad survey). ``Future work'' could apply most of those to
MIL programs, but that would not make for interesting
reading. Instead, this section describes optimizations that take
particular advantage of our MIL program's structure. Some rely on the
monadic structure built into MIL; others extend our existing dataflow
analysis to more complicated transformations.

\subsection{Inlining Monadic Code}
\label{conc_inline_monadic}

Wadler gave the so-called \emph{monad laws} \citeyearpar{Wadler1995},
which state properties that all well-defined monads will obey. Figure
~\ref{conc_fig_monad_laws} gives the three laws: left-unit,
right-unit, and associativity.\footnote{Left-unit and right-unit can
  also be called left-identity and right-identity.} While these laws
can be interpreted as specifications of behavior, they can also be
interpreted as \emph{transformations}.

\begin{myfig}
  \begin{math}
    \begin{aligned}
      |do { x <- return y; m }| & \equiv\
      \begin{cases}
        |do { m }| & \text{when |x| is |y|.} \\
        |do { {-"\lamSubst{y}{x}\ "-} m}| & \text{otherwise.}
      \end{cases} & \text{\it Left-Unit} & \quad\labeledeq{eq_left_unit} \\
      |do { x <- m; return x }| & \equiv\ |do { m }| & \text{\it Right-Unit} & \quad\labeledeq{eq_right_unit} \\
      \llap{|do { x <- do {y <- m; n}; o }|} & \equiv\ |do { y <- m; x <- n; o} |& \text{\it Associativity} & \quad\labeledeq{eq_assoc}
    \end{aligned}
  \end{math}
  \caption{The monad laws, as stated by Wadler
    \citeyearpar{Wadler1995}. The notation ``$\lamSubst{y}{x}\ m$''
    means that $y$ should be substituted for $x$ everywhere in $m$.  }
  \label{conc_fig_monad_laws}
\end{myfig}

In fact, transformations of MIL programs using the monad laws can be
interpreted as optimizations. For example, the following block binds
\var x/ to the value of \var y/, keeping both variables live between
the ``\binds x\ <-\ \return y/;'' and \goto l(x,y) statements::

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b():
      \vbinds x <- \return y/;
      \dots
      \goto l(x, y)
  \end{AVerb}
\end{singlespace}

\noindent If no interverning statement binds \var x/ again, we can use
the Left-Unit law to replace all occurrences of \var x/ with \var y/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b():
      $\dots$
      \goto l(y, y)
  \end{AVerb}
\end{singlespace}

\noindent If variables represent registers, then this can reduce the number of registers used
in a given block of MIL code.

The Right-Unit law shortens the ``tail'' of MIL blocks that end with a
\return/ statement. For example, Right-Unit can be used to transform the
following MIL block:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block b(\dots):
      \dots
      \vbinds x <- \app f*y/;
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

The Associativity law provides an inlining mechanism for MIL
programs. The inner monadic computation mentioned on the right-hand
side of the law, |do { y <- m }|, can be an arbitrarily long monadic
program. All MIL blocks are monadic programs --- therefore, we can use
this law to inline almost any block. For example, consider these two blocks:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block compose(f, g, x): 
      \vbinds t1 <- \app g*x/;
      \vbinds t2 <- \app f*t1/;
      \return t2/ 

    \block main(a,b,c): 
      x <- compose(a,b,c)
      \goto b(x)
  \end{AVerb}
\end{singlespace}

Equation~\eqref{eq_assoc} lets us inline \lab compose/ into \lab main/, as
long as we appropriately rename variables:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main(a,b,c): 
      \vbinds t1 <- \app b*c/;
      \vbinds t2 <- \app a*t1/;
      x <- \return t2/ 
      \goto b(x)
  \end{AVerb}
\end{singlespace}

\noindent Notice we can now also apply Equation~\eqref{eq_left_unit}, eliminating
the use of \var x/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main(a,b,c): 
      \vbinds t1 <- \app b*c/;
      \vbinds t2 <- \app a*t1/;
      \goto b(t2)
  \end{AVerb}
\end{singlespace}

MIL blocks that end in \milres case/ statements cannot be
inlined, in general. The branching introduced by the \milres case/
prevents the block from begin inlined. To illustrate, consider
these two blocks:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}
    \block l1(a):
       \vbinds b <- \goto l2(a);
       \return b/

    \block l2(b):
      \case b;
        \valt{}True() -> \dots;
        \valt{}False() -> \dots;
  \end{AVerb}
\end{singlespace}

The block \lab l2/ cannot be inlined into the body of \lab l1/ because
our syntax does not allow a \milres case/ in the middle of a block. It
also breaks the fundamental model of each block being a basic block.

\subsection{Uncurrying Across Blocks}

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
>   let cap ys g v = (g v) ys
>       cap1 = cap xs
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
  \caption{}
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

\noindent Unfortuantely, as represetned by the !+?+! symbol,
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

\subsection{Dead-Code Elimination}

The Left-Unit (Equation~\eqref{eq_left_unit} on
Page~\pageref{eq_left_unit}) law lets us eliminate a simple form of
dead-code, in which we can guarantee that the binding eliminated has
no observable side-effect. However, the law does not apply to any
monadic expression more complicated than |return x|. We treat
allocation as a monadic operation in MIL, but we cannot really observe
any side-effect of allocation (except our program may consumre more
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

\noindent We can then apply dead-code eliminiation to remove the
allocation bound to \var v210/, since that variable is now dead.

\subsection{Push Through Cases}

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
  coures. But, no compiler can be clever enough to cover all possible
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
    \begin{singlespace}\correctspaceskip
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

\section{Summary}

\standaloneBib 

%% Some interaction with standalone makes the thesis break unless we
%% end with \noindent. The error is:
%%
%%   "You can't use `\\unskip' in vertical mode.\\sa@atenddocument
%%   ->\\unskip".
%%
\noindent\end{document}
