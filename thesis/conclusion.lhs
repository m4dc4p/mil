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
unique features of \mil in
Section~\ref{conc_future_work}. Section~\ref{conc_hoopl} describes
challenges we encountered using the \hoopl library, and give some
suggestions for improvements. Section~\ref{conc_conc} offers our
closing thoughts.

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

\Mil treats allocation as a monadic operation, but we cannot really
observe any side-effect of allocation. Therefore we can eliminate any
closure, thunk or constructor allocation that binds to a
dead variable.

For example, consider |compose1|, which just captures the first
argument to |compose|:

> compose1 f = compose f.

\noindent And the corresponding \mil code:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block compose1(): \mkclo[absBodyL208:]
    \ccblock absBodyL208()f: \goto absBlockL209(f)
    \block absBlockL209(f):
      \vbinds v210<- \goto compose(); 
      \app v210 * f/ 
    
    \block compose(): \mkclo[absBodyL201:]
    \ccblock absBodyL201()f: \mkclo[absBodyL202:f]
    \ccblock absBodyL202(f)g: \dots
  \end{AVerb}
\end{singlespace}

\noindent We can use the Associativity law to inline the allocation
returned by \lab compose/ into \lab absBlockL209/, giving
us:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block absBlockL209(f):
      \vbinds v210<- \mkclo[absBodyL201:]; 
      \app v210 * f/ 
  \end{AVerb}
\end{singlespace}

\noindent Our uncurrying optimization can now that the expression \app
v210 * f/ evaluates to \mkclo[absBodyL202:f] (because \var v210/ holds
the closure \mkclo[absBodyL201:]). We can replace \app v210 * f/ with
\mkclo[absBodyL202:f]:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block absBlockL209(f):
      \vbinds v210<- \mkclo[absBodyL201:]; 
      \mkclo[absBodyL202:f]
  \end{AVerb}
\end{singlespace}

\noindent After this rewrite, \var v210/ is no longer live. Because
closure allocation has no observable side-effect, we remove the
binding, eliminating one allocation:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block absBlockL209(f):
      \mkclo[absBodyL202:f]
  \end{AVerb}
\end{singlespace}

\noindent This optimization extends to thunk and data allocations. 

\subsection{Uncurrying Across Blocks}
\label{conc_uncurrying}

Our uncurrying optimization only works within a single \mil
block. Extending the optimization across blocks seems obvious, but
presents several implementation challenges, as
Figure~\ref{conc_uncurry} illustrates. 

\begin{myfig}
  \begin{tabular}{cc}
\begin{minipage}{3in}
> uncurry t f y n xs = 
>   let  cap ys g v = (g v) ys
>        cap1 = cap xs
>   in case t of 
>        True -> (cap1 f) y
>        False -> (cap1 f) n
\end{minipage} &
\begin{minipage}{3in}
   \begin{AVerb}[gobble=6]
      \block uncurry(t, f, y, n, xs):
        \vbinds cap1<- \mkclo[k203:xs];
        \goto caseEval214(t, cap1, f, y, n)
      \ccblock k203(ys)g: \mkclo[k204: g, ys]
      \ccblock k204(g, ys)v: \mkclo[b205: g, v, ys]
      \block b205(g, v, ys):
        \vbinds v206<- \app g*v/;
        \app v206 * ys/
      \block altTrue208(cap1, f, y):
        \vbinds v209<- \app cap1*f/;
        \app v209 * y/
      \block altFalse211(cap1, f, n):
        \vbinds v212<- \app cap1*f/;
        \app v212 * n/
      \block caseEval214(t, cap1, f, y, n):
        \case t;
          \valt True()->\goto altTrue208(cap1, f, y);
          \valt False()->\goto altFalse211(cap1, f, n);
   \end{AVerb}
\end{minipage} \\\\
  \scap{conc_uncurry_a} & \scap{conc_uncurry_b}  
  \end{tabular}
  \caption{A program that illustrates challenges that occur when
    uncurrying across blocks. Part~\subref{conc_uncurry_a} gives a
    \lamC definition; Part~\subref{conc_uncurry_b} shows its \mil
    equivalent. The |xs| argument to |cap| is live in each |case|
    alternative, but it is ``hidden'' in the closure created by
    |cap1|.}
  \label{conc_uncurry}
\end{myfig}

In Part~\subref{conc_uncurry_a}, |cap1| partially applies |cap| and
captures the |xs| argument to |uncurry|. Each case alternative
ultimately applies |cap1| to two arguments, resulting in the
evaulation of |cap|. Even though the |xs| argument to |cap| is not
syntactically present in either case arm, it is still live.

Part~\subref{conc_uncurry_b} shows how |xs| is hidden. The blocks \lab
altTrue208/ and \lab altFalse211/ represent the two different case
arms. The \var xs/ argument to \lab uncurry/ does not appear in either
block. However, the \var cap1/ argument that does appear in both holds
the closure \mkclo[k203:xs], illustrating that \var xs/ is present but
hidden. 

\lab altTrue208/ and \lab altFalse211/ both ultimately call block \lab
b205/.  We could try to rewrite \lab altFalse211/ and
\lab altTrue208/ to call \lab b205/ directly:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block altTrue208(cap1, f, y):
      \goto b205(f, y, ?)
    \block altFalse211(cap1, f, n):
      \goto b205(f, n, ?)
  \end{AVerb}
\end{singlespace}

\noindent Unfortunately, as shown by the !+?+! symbol, \lab
altTrue208/ and \lab altFalse211/ do not have the \var ys/ argument in
scope that is expected by \lab b205/. That argument should be \var
xs/, but it is hidden in the closure represented by \var cap1/. In
order to bring \var xs/ into scope, we need to rewrite the live
variables available to each block, starting from \lab uncurry/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block uncurry(t, f, y, n, xs):
      \goto caseEval214(t, xs, f, y, n)
    \block altTrue208(ys, f, y):
      \goto b205(f, y, ys)
    \block altFalse211(ys, f, n):
      \goto b205(f, n, ys)
    \block caseEval214(t, ys, f, y, n):
      \case t;
        \valt True()-> \goto altTrue208(ys, f, y);
        \valt False()-> \goto altFalse211(ys, f, n);
  \end{AVerb}
\end{singlespace}

\noindent Rewriting blocks to track live variables to support this
optimization does not seem impossible, but it does seem tricky.

\subsection{Eliminating Thunks}
\label{conc_thunks}

Monadic thunks and closures share many characteristics. For example,
they both represent suspended computation, and they both capture an
environment of values. They also can be a source of inefficiency, as
well. Our compiler for \lamC to \mil produces many blocks that
immediately invoke some thunk. For example, the following \lamC
definition reads a character and prints it to the screen:

\begin{singlespace}
> main x = do
>   c <- readChar 
>   print c
\end{singlespace}

\noindent Our compiler translates the program in this \mil code (in part):

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main():
      \vbinds v206<-\mkthunk[readCharbody:];
      \vbinds c<-\invoke v206/;
      \dots
    \block readCharbody(): \prim readChar()
  \end{AVerb}
\end{singlespace}

In this program, \lab main/ allocates a thunk pointing to
\lab readCharbody/ and binds it to \var v206/. The next line invokes
the thunk just constructed, binding the result to \var c/. A straightforward
adaption of our uncurrying optimization could transform this program
so it executes \lab readCharbody/ directly, instead of invoking the thunk:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main():
      \vbinds v206<-\mkthunk[readCharbody:];
      \vbinds c<-\goto readCharbody();
      \dots
  \end{AVerb}
\end{singlespace}

Of course, we can continue to apply furhter optimizations to the
program. Dead-code elimination would find that \var v206/ is no longer
live, letting us eliminate the allocation of the thunk:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main():
      \vbinds c<-\goto readCharbody();
      \dots
  \end{AVerb}
\end{singlespace}

\noindent The associativity law also lets inline the body of \lab readCharBody/
into \lab main/, removing an extra jump:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block main():
      \vbinds c<-\prim readChar();
      \dots
  \end{AVerb}
\end{singlespace}

\noindent While these last transformations do not relate directly to
eliminating thunks, they do show that each optimization tends to make
further optimizations possible.

\subsection{Push Through Cases}
\label{conc_cases}

Functional language programs commonly implement a pattern of
\emph{construct/destruct}, where the program constructs a value and
then inspects (or destructs) the value shortly
thereafter. Figure~\ref{conc_fig_cons_dest} shows one such
program. The |dec| function returns a |Maybe| value, indicating if its
argument could be decremented or not. The |loop| function
discriminates on the result of |dec n|, immediately throwing away the
|Maybe| value created by |dec|. The ``safe'' decrement implemented by |dec|
guarantees we will not apply |f| to values less than $0$.

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

Figure~\ref{conc_fig_push1} shows unoptimized \mil code for these two
functions. \lab loop/ evaluates \goto dec(n) on
Line~\ref{conc_fig_push1_goto_dec} and binds the result to \var
v215/. The \milres case/ statement on the next line immediately takes
\var v215/ apart, throwing away the allocated value just created. 

\begin{myfig}
  \begin{minipage}{\textwidth}
    \begin{singlespace}
      \begin{AVerb}[gobble=8,numbers=left]
        \block loop(n, f):
           \vbinds v215<-\goto dec(n); \label{conc_fig_push1_goto_dec}
           \case v215;
              \valt Just(i)->\goto altJust(f, i);
              \valt Nothing()->\goto altNothing(f);
      
        \block dec(i): \label{conc_fig_push1_dec}
           \vbinds v233<-\prim gt(i, 0);
           \case v233;
              \valt True()->\goto altTrue(i);
              \valt False()->\goto altFalse();
      
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
\lab altFalse/. As discussed in Section~\ref{conc_inline_monadic}, we
cannot directly inline \lab loop/ into \lab dec/, because \lab loop/
ends with a \milres case/ statement. However, we can move the body of
\lab loop/ into each arm of the \milres case/ statement that ends \lab
loop/.

We begin by inlining \lab dec/ into \lab loop/. Notice that the \milres case/ statement
now jumps to \lab altTrue/ and \lab altFalse/, where before it jumped to \lab altJust/ and
\lab altNothing/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block loop(n, f):
      \vbinds v233<-\prim gt(i, 0);
      \case v233;
        \valt True()->\goto altTrue(i, f, n);
        \valt False()->\goto altFalse(f, n);
  \end{AVerb}
\end{singlespace}

\noindent We also move the original case statement from \lab loop/ to
the end of \lab altTrue/ and \lab altFalse/. This transformation
requires that we bind the original result of \lab altTrue/ and \lab
altFalse/ to the variable that the original case statement inspected
(\var v215/). For example, \lab altTrue/ previously returned \prim
Just (v225); now, we bind \var v215/ to that value. In both blocks,
the value bound is immediately destructed by a \milres case/
statement:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block altTrue(i, f, n):
      \vbinds v225<-\prim minus(i, 1);
      \vbinds v215<-\prim Just(v225);
      \case v215;
        \valt Just(i)->\goto altJust(f, i);
        \valt Nothing()->\goto altNothing(f);
      
    \block altFalse(f, n): 
      \vbinds v215<-\prim Nothing();
      \case v215;
        \valt Just(i)->\goto altJust(f, n);
        \valt Nothing()->\goto altNothing(f);
  \end{AVerb}
\end{singlespace}

Dataflow analysis of \lab altTrue/ and \lab altFalse/ could show that
each block contains a case alternative that will never be
executed. For example, in \lab altTrue/, \var v215/ must always be a
\var Just/ value, and the \var Nothing/ alternative will never
execute. We can eliminate the case statement in both blocks and replace 
them with a jump. Notice that, in the \lab altTrue/ case, we need to
recognize that \var i/ in \var Just i/ is really \var v225/:

\begin{singlespace}\correctspaceskip
  \begin{AVerb}[gobble=4]
    \block altTrue(i, f, n):
      \vbinds v225<- \prim minus(i, 1);
      \vbinds v215<-\prim Just(v225);
      \goto altJust(f, v225)
      
    \block altFalse(f, n): 
      \vbinds v215<-\prim Nothing();
      \goto altNothing(f)

  \end{AVerb}
\end{singlespace}

Dead-code elimination would find that the bindings for \var v215/ in
both blocks is dead, and would eliminate the
allocation. Figure~\ref{conc_fig_push3} shows the final form of our
program, where we have eliminated the unnecessary allocation between
\lab dec/ and \lab loop/. This version of the program will perform no
allocations of |Maybe| values whatsoever, but we are still guaranteed
that |f| will not be applied to an index value less than $0$.

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

\section{\Hoopl Refinements}
\label{conc_hoopl}

\intent{Summary of our \hoopl usage.} The \hoopl library played a
critical role in our work. The library presents a simple and powerful
interface for describing, analyzing and transforming \cfgs. \Hoopl
allowed us to explore a variety of optimizations that used dataflow
analysis, without the burden of implementing the dataflow algorithm
from scratch.  Of course, by spending so much time with the library,
we found some areas where the library's interface left us struggling
to bend our algorithm to fit with \hoopl's view of dataflow
analysis. The following sections describe the issues we encountered,
and offer some possible solutions.

\subsection{Invasive Types}
\intent{\hoopl's use of |O| and |C| types requires your \ast to support
  \hoopl from the beginning.} \Hoopl uses the |O| and |C| types
(described on Page~\pageref{hoopl_sec_cfg}) to specify the shape of
each node in a \cfg; only nodes with compatible types can be connected
to each other. This design allows the compiler to enforce some
desirable properties; for example, a basic block will not contain any
nodes that can branch to more than one destination. Unfortunately,
this design also requires that the |O| and |C| types be present on the
client \ast. In preliminary work, we implemented an \ast without using
\hoopl's shape types. This choice reuiqred us to write a significant
amount of ``boilerplate'' to translate between our initial
representation and one that used \hoopl's desired types.

``Smart'' constructors could be used to reduce the boilerplate
required when using \hoopl against an existing \ast. For example,
consider the the \ast given in Figure~\ref{hoopl_fig3} on
Page~\pageref{hoopl_fig3}. Instead of defining |CStmt| using gadts,
imagine we defined |CStmtX| as a normal ADT and |CStmt| as a
|newtype|:

\begin{singlespace}
> data CStmtX = Entry Label |
>   Assign Var CExpr
>   {-"\dots"-}
>
> newtype CStmt o c = CStmt CStmtX
\end{singlespace}

\noindent To create \hoopl-ized values, we define a function for each
|CStmtX| constructor, parameterized by shape:

\begin{singlespace}
> entry :: Label -> CStmt O C
> entry l = CStmt (Entry l)
>
> assign :: Var -> CExpr -> CStmt O O
> assign v e = CStmt (Assign v e)
>
> {-"\dots"-}
\end{singlespace}

However, this approach still requires a fair amount of boilerplate
code. \Gadts alleviate the problem somewhat (since the compiler
implements ``smart'' constructors for you), but that does not help
when working against an \ast that cannot be changed. Metaprogramming
techniques using Template Haskell may ultimately be the best approach
here.

\subsection{Restricted Signatures}
\intent{Review of combinators for creating rewrite and transfer
  functions.} \Hoopl does not specify transfer and rewrite functions
using simple function signatures. Instead, as detailed in
Section~\ref{hoopl_sec5} (Page~\pageref{hoopl_sec5}), \hoopl
represents those functions using the |BwdTransfer|, |BwdRewrite|,
|FwdTransfer| and |FwdRewrite| types.  Client programs cannot directly
create these values; instead, \hoopl defines a function for creating
each type:

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

\intent{Why the type signatures are too restrictive.}  Unfortunately,
this scheme complicated our implementation at times. \Hoopl's type for
transfer functions only allows information to be stored in three
places: the client's \ast, the facts computed, and any values declared
in some scope external to the transfer function. Each of these
locations leads to different complications. 

To illustrate, imagine a forwards transfer function that analyzes a block
statement by statement (so it does not have access to an entire block
at once), but that also needs to know the label of the current block
being analyzed. \Hoopl requires that such a function have the signature:

> forall e x . n e x -> f -> Fact x f

\noindent We could store the label of the current block in the
client's \ast; that would mean each value of type |n| would need to
hold a label representing the current block. Possible, but burdensome
at least. The label of the current block could be part of the facts
computed. This works, but seems wasteful, as the label would not
matter outside each block, but it would be carried by all values of
type |f|. We could also capture the current label for the block in
some outer scope, but that seems to imply we would be applying \hoopl
to a single block at a time, which would not work for any inter-block
analysis.

\intent{Custom monad does allow arbitrary state, but the
  implementation cost is high.} A simple accumulating parameter on
transfer function would alleviate this issue. \Hoopl does allow the
client program to define a custom monad that will be used by the
rewrite functions, and that can give access to intermediate
results. Unfortunately, the custom monad still does not help with the
transfer function.

\intent{Summarize complaint.}  Earlier versions of the \hoopl library
allowed the client to return an arbitrary \emph{function} from the
transfer and rewrite functions. While that may have been too liberal,
we certainly wished for a slightly less restricted interface during
our work.

\section{Summary}
\label{conc_conc}

\intent{Review goals.} Kildall applied his dataflow algorithm to
\algol, an imperative, structured programming language. Most work in
dataflow analysis since then has focused on imperative programming
languages. We set out to explore the algorithm's use within the
context of a functional programming language; specifically, we
hypothesized that, by compiling to a monadic intermediate language, we
could obtain a basic-block structure that would be ameniable to
dataflow analysis. We intended to implement optimizations drawn from
the literature of imperative and functional compilers, showing that
the algorithm could be applied in both contexts.

\intent{Contribution: \mil.} The monadic intermediate language
we described builds on a large body of work on monadic programming,
intermediate languages, and implementation techniques for functional
languages. While the overall concept is well-known, we believe \mil
offers some novelty. \Mil makes allocation explicit but still
offers high-level features like function application and case
discrimination. \Mil programs, by design, consist of basic-block
elements. Of course, many intermediate languages consist of
basic-blocks, but \mil again combines that structure with a monadic
programming model, giving a ``pure'' flavor to low-level operations.

\intent{Contributions: \hoopl.} Our work made significant use of the
\hoopl library. Without it, we may not have even pursued this
research. While we did not contribute materially to \hoopl itself, this
work offers a significant amount of expository material describing
\hoopl, as well as at least one implementation of a non-trivial
optimization that cannot be found elsewhere.

\intent{Contributions: Uncurrying.} Our work contributes in several
areas. Most importantly, we described uncurrying in terms of dataflow
analysis. We did not find other work in this area, and so we believe
that we are the first to implement uncurrying using dataflow analysis.

\standaloneBib 

%% Some interaction with standalone makes the thesis break unless we
%% end with \noindent. The error is:
%%
%%   "You can't use `\\unskip' in vertical mode.\\sa@atenddocument
%%   ->\\unskip".
%%
\noindent\end{document}
