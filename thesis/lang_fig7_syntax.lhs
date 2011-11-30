\documentclass[12pt]{report}
%include polycode.fmt
\begin{document}
\begin{minipage}{5.1in}
  \begin{align*}
    \term name/\ a_1\ \ldots\ a_n\ &:= \term term/ & \syntaxrule(Top-level Definitions)/ \\
    \termrule term:\term C/\ t_1\ \ldots\ t_n:(ADTs)/ \\
    \termcase |case|\ \term t/\ |of|:(Case Discrimination)/ \\
    & \qquad\mathit{C}_1\ a_1\ a_2\ \ldots\ a_n \rightarrow t, n \ge 0 \\
    %% & \qquad\mathit{C}_2\ b_1\ b_2\ \ldots\ b_n \rightarrow t_2, n \ge 0 \\
    %% & \qquad\ldots \\
    \termcase a, b:(Variables)/ \\
    \termcase \lamAbs{x}{t_1}:(Abstraction)/ \\ 
    \termcase \term t_1/\ \term t_2/:(Application)/ \\
  \end{align*}
\end{minipage}
\end{document}
