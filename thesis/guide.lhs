%&preamble
\input{nodocclass}\dodocclass
%include polycode.fmt
%include lineno.fmt
%include subst.fmt
\begin{document}
\fancyhf{}
\numbersoff
\input{document.preamble}

\section*{Thesis Style Guide}

This document specifies the typographic guidelines followed for various
elements in the thesis. 

\section*{Abbreviations}
Abbreviations such as \mil and \cfg appear in small caps. When an
acronym starts a sentence, its first letter is capitalized (e.g.,
``\Mil'').

Abbreviations in section and chapter headings in the body text, which are always
in Helvetica (a sans-serif font) should not
appear in small caps. For example, ``\textsf{MIL}'' instead of ``\textsf{\textsc{mil}}.''

New terms are written in italic type when they are first
introduced. For example, ``The \emph{dataflow algorithm} defines a
general approach to program analysis\dots''. Abbreviations
are introduced by writing them after the term: ``A \emph{control-flow graph}
(\cfg) \dots''

\section*{Numbers}
Chapter, Section, Page and Figure references use old-style numerals:
0, 1, 2, 3, etc.  Line numbers are also old-style.

Superscripts, subscripts, and footnotes use ``normal'' numerals: $0,
1, 2, 3,$ etc.  Numbers in mathematical expressions are normal (e.g.,
``$x = 10$, '' not ``$x = $\ 10'').  Indexed variables (e.g., $B_1$,
$t_1$, etc.) also use normal numerals.

\section*{Syntax}
\Mil program fragments appear in typewriter font: \binds x <- \goto readChar();,
\lab main/, \block print(x):, etc. \lamC program fragments use italic
font: \lcdef compose (f,g,x)=\lcapp f * (g * x)/;.

\Mil program blocks that appear in display text are
single-spaced. Block headers (e.g., \block foo(a,b,c):) are not
indented, but lines in blocks are indented two spaces. Continued lines
or case alternatives always indent two spaces from their parent:

\begin{singlespace}\correctspaceskip
\begin{AVerb}[gobble=2]
  \block foo(a,b,c): \hfill\textrm{\emph{(block header)}}\hskip.5\hsize
    \vbinds f<-\return x/; \hfill\textrm{\emph{(subsequent lines)}}\hskip.5\hsize
    \hfill\textrm{\vdots}\hskip.5\hsize
    \case z;
      \valt T()->\goto foo(); \hfill\textrm{\emph{(case alternative)}}\hskip.5\hsize
      \dots
\end{AVerb}
\end{singlespace}

\lamC programs are also always single-spaced. They are also indented a paragraph indent:

\begin{singlespace}
> main x = do
>   c <- readChar
>   print c
\end{singlespace}

\end{document}
