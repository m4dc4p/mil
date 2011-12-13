> {-# LANGUAGE GADTs, RankNTypes #-}
>
> module InlineReturn (inlineReturn)
>
> where
>
> import Control.Monad.State (State, execState, modify, gets)
> import Text.PrettyPrint 
> import Data.List (sort, (\\), elemIndex)
> import Data.Maybe (fromMaybe, isJust, catMaybes, fromJust)
> import Data.Map (Map, (!))
> import qualified Data.Map as Map
> import Data.Set (Set)
> import qualified Data.Set as Set
> import Debug.Trace
> 
> import Compiler.Hoopl
> 
> import Util
> import MIL
>
> -- Goto/Return elimination
> -- When a Goto jumps to a block that immediately calls a primitive, or
> -- returns a value, we inline the block:
> --
> --  L1: return r
> --   ...
> --  L2: v <- goto l1 (x)
> -- ==>
> --  L2: v <- return x
> --
> -- Bind/subst elimination can take care of the return left over.
> 
> -- | Blocks we can inline will be stored in the map, by 
> -- label/name. 
> type ReturnPrimBlocks = Map Dest (Tail, Env)
> 
> -- | Indicates what kind of instruction can be inlined
> -- from a block. 
> type ReturnType = Maybe (Tail, Env)
> 
> -- | Inline blocks that immediately return a
> -- tail. Closure entry blocks are NOT inlined
> -- because they need to capture an argument. Only
> -- BlockEntry blocks can be considered.
> inlineReturn :: ProgM C C -> ProgM C C
> inlineReturn body = 
>     runSimple $ do
>       -- First we find all the blocks which we
>       -- could inline
>       (_, f, _) <- analyzeAndRewriteBwd bwdAnalysis (JustC labels) body (initial bwdAnalysis)
>       let returnBlocks = Map.fromList . map toDest . filter (isJust . snd) .  mapToList $ f
>           toDest (l, Just f) = (fromJust (labelToDest body l), f)
>       -- Turn our facts into a proper map of Dest -> Fact, then
>       -- use those facts to rewrite and inline.
>       (body', _, _) <- analyzeAndRewriteBwd (bwdRewrite returnBlocks) (JustC labels) body (initial (bwdRewrite returnBlocks))
>       return body'
>   where              
>     labels = entryLabels body
>     initial :: BwdPass SimpleFuelMonad Stmt a -> FactBase a
>     initial bwd = mkFactBase (bp_lattice bwd) (zip labels (repeat (fact_bot (bp_lattice bwd))))
>     bwdRewrite :: ReturnPrimBlocks -> BwdPass SimpleFuelMonad Stmt EmptyFact
>     bwdRewrite returnBlocks = BwdPass { bp_lattice = rewriteLattice
>                                       , bp_transfer = mkBTransfer noOpTrans
>                                       , bp_rewrite = inlineReturnRewrite returnBlocks }
>     rewriteLattice :: DataflowLattice EmptyFact
>     rewriteLattice = DataflowLattice { fact_name = "Goto/Return"
>                                      , fact_bot = ()
>                                      , fact_join = extend}
>     bwdAnalysis :: BwdPass SimpleFuelMonad Stmt ReturnType
>     bwdAnalysis = BwdPass { bp_lattice = analysisLattice
>                           , bp_transfer = inlineReturnTransfer 
>                           , bp_rewrite = noBwdRewrite }
>     analysisLattice = DataflowLattice { fact_name = "Goto/Return"
>                                       , fact_bot = Nothing
>                                       , fact_join = extend }
>     extend :: (Eq a) => JoinFun a
>     extend _ (OldFact old) (NewFact new) = (changeIf (old /= new), new)   
> 
> inlineReturnTransfer :: BwdTransfer Stmt ReturnType
> inlineReturnTransfer = mkBTransfer bw
>   where
>     bw :: Stmt e x -> Fact x ReturnType -> ReturnType
>     bw (Done _ _ t) f = Just (t, [])
>     bw block@(BlockEntry _ _ args) (Just (t, _)) = Just (t, args)
>     bw _ _ = Nothing
> 
> inlineReturnRewrite :: FuelMonad m => ReturnPrimBlocks -> BwdRewrite m Stmt EmptyFact
> inlineReturnRewrite blocks = iterBwdRw (mkBRewrite rewriter)
>   where
>     rewriter :: FuelMonad m => forall e x. Stmt e x -> Fact x EmptyFact -> m (Maybe (ProgM e x))
>     rewriter (Bind v (Goto dest vs)) _ = 
>       case dest `Map.lookup` blocks of
>         Just (t, succEnv) -> return (Just (mkMiddle (Bind v (renameTail (mkRenamer vs succEnv) t))))
>         _ -> return Nothing
>     rewriter (Done n label (Goto dest@(_, l) vs)) _ =
>       case dest `Map.lookup` blocks of
>         Just (t, succEnv) -> return (Just (mkLast (Done n label (renameTail (mkRenamer vs succEnv) t))))
>         _ -> return Nothing
>     rewriter _ _ = return Nothing
