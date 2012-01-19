\iffalse
%include polycode.fmt
\fi
\begin{tikzpicture}[>=stealth, node distance=.55in]

  \node[stmt] (start) {|Entry l|\labelNode{hoopl_lst4_start}}; %%  :: CStmt C O
  \node[labelfor=start] () {\refNode{hoopl_lst4_start}};
  \node[right=.1in of start.east, overlay] () {|:: CStmt C O|};

  \node[stmt,
    below of=start] (assignc) {|Assign "c" (Const 4)|\labelNode{hoopl_lst4_assignc}}; %%  :: CStmt O O
  \node[labelfor=assignc] () {\refNode{hoopl_lst4_assignc}};
  \node[right=.1in of assignc.east, overlay] () {|:: CStmt O O|};

  \node[stmt,
    below of=assignc] (assigna1) {|Assign "a" (Add (Var "c") (Const 1))|\labelNode{hoopl_lst4_assigna1}}; %%  :: CStmt O O|
  \node[labelfor=assigna1] () {\refNode{hoopl_lst4_assigna1}};
  \node[right=.1in of assigna1.east, overlay] () {|:: CStmt O O|};

  \node[stmt,
    below of=assigna1] (print) {|Call "printf" [String "%d", Var "c"]|\labelNode{hoopl_lst4_print}}; %%  :: CStmt O O
  \node[labelfor=print] () {\refNode{hoopl_lst4_print}};
  \node[right=.1in of print.east, overlay] () {|:: CStmt O O|};

  \node[stmt,
    below of=print] (assigna2) {|Assign "a" (Add (Var "c") (Const 2))|\labelNode{hoopl_lst4_assigna2}}; %%  :: CStmt O O
  \node[labelfor=assigna2] () {\refNode{hoopl_lst4_assigna2}};
  \node[right=.1in of assigna2.east, overlay] () {|:: CStmt O O|};

  \node[stmt,
    below of=assigna2] (return) {|Return|\labelNode{hoopl_lst4_return}}; %%  :: CStmt O C
  \node[labelfor=return] () {\refNode{hoopl_lst4_return}};
  \node[right=.1in of return.east, overlay] () {|:: CStmt C O|};

  \draw [->>] (start) to (assignc);
  \draw [->] (assignc) to (assigna1);
  \draw [->] (assigna1) to (print);
  \draw [->] (print) to (assigna2);
  \draw [->>] (assigna2) to (return);

\end{tikzpicture}

