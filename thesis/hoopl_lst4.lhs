%include polycode.fmt
\begin{minipage}{3in}
  \begin{tikzpicture}[>=stealth, node distance=.5in]

    \node[stmt] (start) {|Entry l :: CStmt C O|\labelNode{hoopl_lst4_start}};
    \node[labelfor=start] () {\refNode{hoopl_lst4_start}};

    \node[stmt,
      below of=start] (assignc) {|Assign "c" (Const 4) :: CStmt O O|\labelNode{hoopl_lst4_assignc}};
    \node[labelfor=assignc] () {\refNode{hoopl_lst4_assignc}};

    \node[stmt,
      below of=assignc] (assigna1) {|Assign "a" (Add (Var "c") (Const 1)) :: CStmt O O|\labelNode{hoopl_lst4_assigna1}};
    \node[labelfor=assigna1] () {\refNode{hoopl_lst4_assigna1}};

    \node[stmt,
      below of=assigna1] (print) {|Call "printf" [String "%d", Var "c"] :: CStmt O O|\labelNode{hoopl_lst4_print}};
    \node[labelfor=print] () {\refNode{hoopl_lst4_print}};

    \node[stmt,
      below of=print] (assigna2) {|Assign "a" (Add (Var "c") (Const 2)) :: CStmt O O|\labelNode{hoopl_lst4_assigna2}};
    \node[labelfor=assigna2] () {\refNode{hoopl_lst4_assigna2}};

    \node[stmt,
      below of=assigna2] (return) {|Return :: CStmt O C|\labelNode{hoopl_lst4_return}};
    \node[labelfor=return] () {\refNode{hoopl_lst4_return}};

    \draw [->>] (start) to (assignc);
    \draw [->] (assignc) to (assigna1);
    \draw [->] (assigna1) to (print);
    \draw [->] (print) to (assigna2);
    \draw [->>] (assigna2) to (return);

  \end{tikzpicture}
\end{minipage}

