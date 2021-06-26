------------------------------------------------------------------------------------
-- PatriciaTree properties, these properties do not depend on the graph instance
-- Used to proof the preconditions of the PatricaGraph
------------------------------------------------------------------------------------

module Proofs.PatriciaTreeProperties where

open import InductiveGraph
open import PatriciaTree

open import Haskell.Prim
open import Haskell.Prelude
open import Haskell.Data.List
open import Haskell.Data.Maybe
open import Haskell.Data.Tuple

open import GHC.Tuple

open import IntMap hiding (foldlWithKey')
open import IntMap as IM hiding (foldlWithKey')

open import Proofs.Proof
open import Proofs.ListProperties
open import Proofs.MaybeProperties
open import Proofs.GeneralProperties
open import Proofs.IntMapProperties
open import Proofs.TupleProperties

-- | Finding a node in the graph is not dependent on edges.
--   So, if an edge is deleted all nodes are still part of the graph.
propFindingNodesNotDependentOnEdgesDelete : (lk : Node) -> (n : Node) -> (preds : IntMap (List b)) -> (succs : IntMap (List b)) -> (intMap : GraphRep a b) -> isJust (IM.lookup lk (clearSucc (clearPred intMap n succs) n preds)) ≡ isJust (IM.lookup lk intMap)
propFindingNodesNotDependentOnEdgesDelete lk n preds@(Map []) succs@(Map []) intMap@(Map []) = refl
propFindingNodesNotDependentOnEdgesDelete lk n preds@(Map (p ∷ ps)) succs@(Map []) intMap@(Map []) = refl
propFindingNodesNotDependentOnEdgesDelete lk n preds@(Map []) succs@(Map (s ∷ ss)) intMap@(Map []) = refl
propFindingNodesNotDependentOnEdgesDelete lk n preds@(Map []) succs@(Map []) intMap@(Map (m ∷ ms)) = refl
propFindingNodesNotDependentOnEdgesDelete lk n preds@(Map (p ∷ ps)) succs@(Map (s ∷ ss)) intMap@(Map []) = refl
propFindingNodesNotDependentOnEdgesDelete lk n preds@(Map []) succs@(Map (s ∷ ss)) intMap@(Map (m ∷ ms)) =
  begin
    isJust (IM.lookup lk (clearSucc (clearPred intMap n succs) n preds))
  =⟨⟩
    isJust (IM.lookup lk (differenceWith (λ grV edgeV → Just (clearPredHelper n grV edgeV)) intMap succs))
  =⟨ propLookUpDifferenceWithJust lk (clearPredHelper n) intMap succs ⟩
    isJust (IM.lookup lk intMap)
  ∎
propFindingNodesNotDependentOnEdgesDelete lk n preds@(Map (p ∷ ps)) succs@(Map []) intMap@(Map (m ∷ ms)) =
  begin
    isJust (IM.lookup lk (clearSucc (clearPred intMap n succs) n preds))
  =⟨⟩
    isJust (IM.lookup lk (differenceWith (λ grV edgeV → Just (clearSuccHelper n grV edgeV)) intMap preds))
  =⟨ propLookUpDifferenceWithJust lk (clearSuccHelper n) intMap preds ⟩
    isJust (IM.lookup lk intMap)
  ∎
propFindingNodesNotDependentOnEdgesDelete lk n preds@(Map (p ∷ ps)) succs@(Map (s ∷ ss)) intMap@(Map (m ∷ ms)) = 
  begin
    isJust (IM.lookup lk (clearSucc (clearPred intMap n succs) n preds))
  =⟨⟩
    isJust (IntMap.lookup lk (differenceWith (λ grV edgeV → Just (clearSuccHelper n grV edgeV)) (differenceWith (λ grV edgeV → Just (clearPredHelper n grV edgeV)) intMap succs) preds))
  =⟨ propLookUpDifferenceWithJustTwice lk  (clearSuccHelper n) (clearPredHelper n) intMap preds succs ⟩
    isJust (IM.lookup lk intMap)
  ∎

-- | Finding a node in the graph is not dependent on edges.
--   So, if an edge is inserted all nodes are still part of the graph.
propFindingNodesNotDependentOnEdgesInsert : (lk : Node) -> (n : Node) -> (np : Node) -> (ns : Node) -> (preds : IntMap (List b)) -> (succs : IntMap (List b)) -> (cxt' : Context' a b) -> (intMap : GraphRep a b) -> isJust (IM.lookup lk (addPred (addSucc intMap n np preds) n ns succs)) ≡ isJust (IM.lookup lk intMap)
propFindingNodesNotDependentOnEdgesInsert lk n np ns preds@(Map []) succs@(Map []) cxt' intMap@(Map []) = refl
propFindingNodesNotDependentOnEdgesInsert lk n np ns preds@(Map (p ∷ ps)) succs@(Map []) cxt' intMap@(Map []) = refl
propFindingNodesNotDependentOnEdgesInsert lk n np ns preds@(Map []) succs@(Map (s ∷ ss)) cxt' intMap@(Map []) = refl
propFindingNodesNotDependentOnEdgesInsert lk n np ns preds@(Map []) succs@(Map []) cxt' intMap@(Map (m ∷ ms)) = refl
propFindingNodesNotDependentOnEdgesInsert lk n np ns preds@(Map (p ∷ ps)) succs@(Map (s ∷ ss)) cxt' intMap@(Map []) = refl
propFindingNodesNotDependentOnEdgesInsert lk n np ns preds@(Map []) succs@(Map (s ∷ ss)) cxt' intMap@(Map (m ∷ ms)) =
  begin
    isJust (IM.lookup lk (addPred (addSucc intMap n np preds) n ns succs))
  =⟨⟩
    isJust (IntMap.lookup lk (differenceWith (λ grV edgeV → Just (combinePredds n grV edgeV)) intMap succs))
  =⟨ propLookUpDifferenceWithJust lk (combinePredds n) intMap succs ⟩
    isJust (IM.lookup lk intMap)
  ∎
propFindingNodesNotDependentOnEdgesInsert lk n np ns preds@(Map (p ∷ ps)) succs@(Map []) cxt' intMap@(Map (m ∷ ms)) =
  begin
    isJust (IM.lookup lk (addPred (addSucc intMap n np preds) n ns succs))
  =⟨⟩
    isJust (IntMap.lookup lk (differenceWith (λ grV edgeV → Just (combineSuccs n grV edgeV)) intMap preds))
  =⟨ propLookUpDifferenceWithJust lk (combineSuccs n) intMap preds ⟩
    isJust (IM.lookup lk intMap)
  ∎
propFindingNodesNotDependentOnEdgesInsert lk n np ns preds@(Map (p ∷ ps)) succs@(Map (s ∷ ss)) cxt' intMap@(Map (m ∷ ms)) =
  begin
    isJust (IM.lookup lk (addPred (addSucc intMap n np preds) n ns succs))
  =⟨⟩
    isJust (IntMap.lookup lk (differenceWith (λ grV edgeV → Just (combinePredds n grV edgeV)) (differenceWith (λ grV edgeV → Just (combineSuccs n grV edgeV)) intMap preds) succs))
  =⟨ propLookUpDifferenceWithJustTwice lk  (combinePredds n) (combineSuccs n) intMap succs preds ⟩
    isJust (IM.lookup lk intMap)
  ∎

-- | Getting the fst of a patriciaLabNode is a node
propFstPatriciaLabNodeIsNode : (n : Node) -> (ctx : Context' a b) -> n ≡ fst (patriciaLabNode (n , ctx))
propFstPatriciaLabNodeIsNode n (_ , l , _) = refl

-- | Looking up a node in a map is the same as looking up the node in the map converted to patriciaLabNodes
propLookUpIntMapEquivElemLabNodes : (n : Node) -> (vctxs : List (Node × Context' a b)) -> isJust (IntMap.lookup n (Map vctxs)) ≡ elem ⦃ iFoldableList ⦄ n (Haskell.Prelude.map fst (Haskell.Prelude.map patriciaLabNode vctxs))
propLookUpIntMapEquivElemLabNodes n [] = refl
propLookUpIntMapEquivElemLabNodes n (m@(k , cxt) ∷ ms) =
  begin
    isJust (IM.lookup n (Map ((k , cxt) ∷ ms)))
  =⟨⟩
    isJust (if n == k then Just cxt else IntMap.lookup n (Map ms))
  =⟨ propIsJustIfThenElse (n == k) cxt (IntMap.lookup n (Map ms)) ⟩
    (n == k || isJust (IntMap.lookup n (Map ms)))
  =⟨ cong (λ x -> (n == k || x)) (propLookUpIntMapEquivElemLabNodes n ms) ⟩
    (n == k || elem ⦃ iFoldableList ⦄ n (Haskell.Prelude.map fst (Haskell.Prelude.map patriciaLabNode ms)))
  =⟨⟩
    elem ⦃ iFoldableList ⦄ n (k ∷ Haskell.Prelude.map fst (Haskell.Prelude.map patriciaLabNode ms))
  =⟨ cong (λ x -> elem ⦃ iFoldableList ⦄ n (x ∷ Haskell.Prelude.map fst (Haskell.Prelude.map patriciaLabNode ms))) (propFstPatriciaLabNodeIsNode k cxt) ⟩
    elem ⦃ iFoldableList ⦄ n (fst (patriciaLabNode (k , cxt)) ∷ Haskell.Prelude.map fst (Haskell.Prelude.map patriciaLabNode ms))
  =⟨⟩
    elem ⦃ iFoldableList ⦄ n (Haskell.Prelude.map fst (Haskell.Prelude.map patriciaLabNode (m ∷ ms)))
  ∎

-- | Checking if a maybe context supplied to matchGrLookUp isJust is the same as checking if the maybe context isJust
propIsJustMatchGraphMaybe : (n : Node) -> (cxt : Maybe (Context' a b)) -> (ms : IntMap (Context' a b)) -> isJust (fst (matchGrLookUp n ms cxt)) ≡ isJust cxt
propIsJustMatchGraphMaybe n Nothing (Map ms) = refl
propIsJustMatchGraphMaybe n (Just (p , label , s)) (Map ms) = refl

-- | Checking if a maybe context supplied to matchGrLookUp' isJust is the same as checking if the maybe context isJust
propIsJustMatchGraphMaybe' : (n : Node) -> (cxt : Maybe (Context' a b)) -> (ms : IntMap (Context' a b)) -> isJust (fst (matchGrLookUp' n ms cxt)) ≡ isJust cxt
propIsJustMatchGraphMaybe' n Nothing (Map ms) = refl
propIsJustMatchGraphMaybe' n (Just (p , label , s)) (Map ms) = refl

-- | When only checking if the context is a just, matchGrLookUp and matchGrLookUp' are equivalent
propIsJustMatchLookupEquivmatchGrLookUp' : (n : Node) -> (grep : GraphRep a b) -> (mcxt : Maybe (Context' a b)) -> isJust (fst (matchGrLookUp n grep mcxt)) ≡ isJust (fst (matchGrLookUp' n grep mcxt))
propIsJustMatchLookupEquivmatchGrLookUp' n intMap mcxt = 
  begin
    isJust (fst (matchGrLookUp n intMap mcxt))
  =⟨ propIsJustMatchGraphMaybe n mcxt intMap ⟩
    isJust mcxt
  =⟨ sym (propIsJustMatchGraphMaybe' n mcxt intMap) ⟩
    isJust (fst (matchGrLookUp' n intMap mcxt))
  ∎
