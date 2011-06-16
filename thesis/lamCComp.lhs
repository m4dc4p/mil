%% Rules for compiling LambdaCase to MIL
%include polycode.fmt
\begin{singlespace}
  \begin{longtable}{m{2.5in}l@@{\vline\hspace{.1in}}m{3.5in}}
    \caption{Compilation rules from \lamC to MIL.} \\
    \hline \\
    \endfirsthead
    \caption{Compilation rules from \lamC to MIL \emph{(cont'd)}} \\
    \hline \\
    \endhead
    \\ \hline \multicolumn{3}{r}{\emph{Continued on next page}}
    \endfoot 
    \\ \hline
    \endlastfoot

    \multicolumn{3}{c}{\emph{Variables}} \\ \\[-.5em]
    \begin{minipage}[t]{2in}
      \begin{AVerb}
\compMILE{v} = return v
      \end{AVerb}
    \end{minipage} & & We return the value of the variable given. \\ \\

    \multicolumn{3}{c}{\emph{Application}} \\ \\[-.5em]
    \begin{SaveVerbatim}[commandchars=\\\{\},codes={\catcode`\_8\catcode`\$3\catcode`\^7},numberblanklines=false]{MILApp}
t$_1$ $\Leftarrow$ \compMILV{f}
t$_2$ $\Leftarrow$ \compMILV{g}
t$_1$ @@ t$_2$
    \end{SaveVerbatim}
    {\compMILE{|f g|}
       \ =\hfil\break\phantom{\tt\ \ }\BUseVerbatim[baseline=c]{MILApp}} & & \\ \\

    \multicolumn{3}{c}{\emph{Abstraction}} \\ \\[-.5em]
    \newbox\boxLAbsA
    \setbox\boxLAbsA=\hbox{|\y -> t|}
    \begin{SaveVerbatim}[commandchars=\\\{\},codes={\catcode`\_8\catcode`\$3\catcode`\^7},numberblanklines=false]{MILAbs1}
k k$_1$ \{fv$_1$,\dots,fv$_m$\}

k$_1$ \{fv$_1$,\dots,fv$_m$\} x = 
  \compMILE{\box\boxLAbsA}
    \end{SaveVerbatim}
    {\compMILE{|\x -> (\y -> t)|} 
      \ = \hfil\break\phantom{\tt\ \ }\BUseVerbatim[baseline=c]{MILAbs1}} & & \\ \\

    \begin{SaveVerbatim}[commandchars=\\\{\},codes={\catcode`\_8\catcode`\$3\catcode`\^7},numberblanklines=false]{MILAbs2}
k k$_1$ \{fv$_1$,\dots,fv$_m$\}

k$_1$ \{fv$_1$,\dots,fv$_m$\} x = 
  b$_1$(fv$_1$,\dots,fv$_m$, x)

b$_1$(fv$_1$,\dots,fv$_m$, x) = 
  \compMILE{t}
    \end{SaveVerbatim}
    {\compMILE{|\x -> t|} 
      \ = \hfil\break\phantom{\tt\ \ }\BUseVerbatim[baseline=c]{MILAbs2}} & & \\ \\

    \multicolumn{3}{c}{\emph{Constructors}} \\ \\[-.5em]
%% lhs2tex formatting directives that make numbers into subscripts
%format x_1
%format x_n
    \begin{minipage}[t]{2in}
      \begin{AVerb}
\compMILE{C x_1 \dots x_n} = 
  t$_1$ $\Leftarrow$ \compMILV{|x_1|}
  \dots
  t$_n$ $\Leftarrow$ \compMILV{|x_n|}
  C t$_1$ \dots t$_n$
      \end{AVerb}
    \end{minipage} & & We create a data value with tag #C# and fields $x_1$ to $x_n$. If $n$ is zero, no
    arguments are present and the data value has no fields. \\ \\

    \multicolumn{3}{c}{\emph{Case}} \\ \\[-.5em]
  \newbox\boxLCCase%%
  \setbox\boxLCCase=\hbox{\texths%%
%format a_1
%format a_n
%format t_1
> case t of
>   C a_1 {-"\dots"-} a_n -> b
>   {-"\dots"-}
}%%
\begin{SaveVerbatim}[commandchars=\\\{\},codes={\catcode`\_8\catcode`\$3\catcode`\^7},numberblanklines=false]{MILCase}
t$_1$ $\Leftarrow$ \compMILE{t}
case t$_1$ of
  C a$_1$ $\dots$ a$_n$ $\to$
    b$_1$(fv$_1$,$\dots$,fv$_m$,a$_1$,$\dots$,a$_n$)
  \dots

b$_1$(fv$_1$,$\dots$,fv$_m$,a$_1$,$\dots$,a$_n$) = 
  \compMILE{b}
\end{SaveVerbatim}
    {\compMILE{\box\boxLCCase}\nobreak\ = \hfil\break
      \phantom{\tt\ \ }\BUseVerbatim[baseline=c]{MILCase}} & & We
    assign the result of evaluating |t| (an arbitrary term) to a
    compiler temporary, \texttt{t$_1$}. We compile the body of the case arm,
    |b|, to a block, \texttt{b$_1$}. The MIL #case# arm jumps immediately to
    the compiled block \texttt{b$_1$}. Free variables (represented by
    \texttt{fv$_1$,\dots,fv$_m$}) and those bound by the arm
    (\texttt{a$_1$,$\dots$,a$_n$}) are passed to \texttt{b$_1$}. We only show one
    arm here, but many can be present. \\ \\

  \label{mil_tbl1}
  \end{longtable}
\end{singlespace}
