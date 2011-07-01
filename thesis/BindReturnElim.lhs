> {-# LANGUAGE GADTs #-}
> module BindReturnElim (bindReturn)
>   
> where 
>     
> import Compiler.Hoopl
> import MIL

This optimization eliminates a combination that appears frequently at the end
of a MIL block: a bind followed immediately by a return. For example:

b(...):
  ...
  a <- m
  return a

Can be transformed (by the left-identity monad law) into:

b(...):
  ....
  m

We will implement this optimization by recursing over each block in
the program, looking for the pattern above and rewriting it.  We
recurse to eliminate chains for bind/return paris, such as:

b(...):
  a <- m
  b <- return a
  c <- return b
  return c

Which is successively transformed into:

b(...):
  a <- m
  b <- return a
  return b

==> 

b(...):
  a <- m
  return a

Finally becoming

b(...): m


Note that to optimize slightly, |rewriteBlock| reverses the order of
the middle statements (i.e., the |bind| statements), so we can use
pattern-matching rather than the |last| function to get the final
|bind| statement.

> rewriteBlock :: [StmtM O O] -> StmtM O C -> ProgM O C
> rewriteBlock = rw . reverse
>   where
>     rw :: [StmtM O O] -> StmtM O C -> ProgM O C
>     rw (Bind v t:bs) (Done n l (Return v')) 
>       | v == v' = rw bs (Done n l t)
>     rw binds done = mkMiddles (reverse binds) <*> mkLast done

To rewrite all the blocks, we break each block in the program into a tuple containing 
then entry statement, a list of middle statements, and the final exit statemnet. We apply |rewriteBlock| to the appropriate values and reconsstruct the block. We then fold all the blocks together to reconstruct the entire program.

> bindReturn :: ProgM C C -> ProgM C C
> bindReturn (GMany _ blocks _) = 
>   let allBlocks :: LabelMap (Block StmtM C C) -> [(MaybeC C (StmtM C O), [StmtM O O], MaybeC C (StmtM O C))]
>       allBlocks = map blockToNodeList' . mapElems
>       rwB :: (MaybeC C (StmtM C O), [StmtM O O], MaybeC C (StmtM O C)) -> ProgM C C
>       rwB (JustC entry, binds, JustC done) = mkFirst entry <*> rewriteBlock binds done
>   in foldr (|*><*|) emptyClosedGraph . map rwB . allBlocks $ blocks

We do not catch certain situations that we could optimize, such as a
bind/return pair separated by "pure" computations:

  a <- m
  x <- C a b c
  return a

Where |x <- C a b c| is a pure statement (i.e., it could be a
primitive call as well). However, to be a valid transformation, the
intervening statements must be dead code. They cannot have side
effects and any values created cannot be used. We rely on dead-code
eliminatino to clean up the program before attemping bind/return
elimination, and therefore we don't worry about this case here.