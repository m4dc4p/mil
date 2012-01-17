%include polycode.fmt
\begin{myfig}\disableoverfull
  \begin{minipage}{\hsize}\disableoverfull
> data FwdPass m n f = FwdPass	{
>     fp_lattice :: DataflowLattice f
>   , fp_transfer :: FwdTransfer n f
>   , fp_rewrite :: FwdRewrite m n }

> data BwdPass m n f = BwdPass {
>     bp_lattice :: DataflowLattice f
>   , bp_transfer :: BwdTransfer n f
>   , bp_rewrite :: BwdRewrite m n f }

> analyzeAndRewriteFwd :: (CheckpointMonad m, NonLocal n, LabelsPtr entries) => 
>   FwdPass m n f 
>   -> MaybeC e entries 
>   -> Graph n e x 
>   -> Fact e f 
>   -> m (Graph n e x, FactBase f, MaybeO x f)

> analyzeAndRewriteBwd :: (CheckpointMonad m, NonLocal n, LabelsPtr entries) => 
>   BwdPass m n f 
>   -> MaybeC e entries 
>   -> Graph n e x 
>   -> Fact x f 
>   -> m (Graph n e x, FactBase f, MaybeO e f)
  \end{minipage}
  \caption{Hoopl's types and functions used to execute backwards and
    forwards analysis and transformation. |BwdPass| and |FwdPass|
    package the client program's definition of lattice, transfer
    function, and rewrite function. Except for direction,
    |analyzeAndRewriteFwd| and |analyzeAndRewriteBwd| behave the same;
    they execute the optimization defined by the client program.}
  \label{hoopl_fig14}
\end{myfig}
