\documentclass[12pt]{report}
%include polycode.fmt
\begin{document}
%{
%format t_1 = "\ensuremath{t_1}"
%format t_2 = "\ensuremath{t_2}"
\begin{math}
  \begin{array}{rlr}
    \termrule def:\term f/\ a_1\ \ldots\ a_n\ =\ \term term/:(Definitions)/ \\
    \termrule term:\term C/\ t_1\ \ldots\ t_n:(ADTs)/ \\
    \termcase |case t of|:(Case Discrimination)/ \\
    & \qquad\mathit{C}_1\ a_1\ \ldots\ a_n \rightarrow t_1 \\
    & \qquad\dots \\
    & \qquad\mathit{C}_n\ a_1\ \ldots\ a_n \rightarrow t_n \\
    \termcase |let a = t_1 in t_2|:(Let)/ \\
    \termcase |do { a <- t_1; t; }|:(Bind)/ \\
    \termcase \lamAbs{x}{t}:(Abstraction)/ \\ 
    \termcase \term t_1/\ \term t_2/:(Application)/ \\
    \termcase a:(Variables)/ \\
    \termcase \term p^*/:(Primitives)/ \\\\
    & \multicolumn{2}{l}{\hbox to 5in{\vbox{\disableparspacing %%
          5in;\parfillskip=0pt plus 1fil\relax where\ $t, t_1, \ldots, t_n$ are terms, $a, a_1, \ldots,
          a_n$ are variables, $C,\allowbreak C_1,\allowbreak \ldots,\allowbreak C_n$ are constructor
          names, $p$ names a primitive and $f$ names a definition.}}}
  \end{array}
\end{math}
%}
\end{document}
