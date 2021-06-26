module PatriciaGraph where

open import InductiveGraph

open import Haskell.Prim
open import Haskell.Prelude
open import Haskell.Data.List
open import Haskell.Data.Maybe
open import Haskell.Data.Tuple
open import Haskell.Data.Bifunctor

open import GHC.Tuple

open import PatriciaTree

open import IntMap hiding (foldlWithKey')
open import IntMap as IM hiding (foldlWithKey')

open import Proofs.Proof
open import Proofs.ListProperties
open import Proofs.MaybeProperties
open import Proofs.GeneralProperties
open import Proofs.IntMapProperties
open import Proofs.TupleProperties
open import Proofs.PatriciaTreeProperties

open Bifunctor ⦃ ... ⦄


open Graph ⦃ ... ⦄
open DynGraph ⦃ ... ⦄

instance
  -- | These instances depend on each other, Agda doesn't see that the instances are terminating.
  {-# TERMINATING #-}
  iGraphPatriciaGr : Graph PatriciaGr
  iDynGraphPatriciaGr : DynGraph PatriciaGr

data NonEmptyPatriciaGraph {a b : Set} : PatriciaGr a b → Set where
  instance itsNonEmpty : ∀ {x xs} → NonEmptyPatriciaGraph (Gr (Map (x ∷ xs)))

propUpdatingContextKeepsNodesHelper : (cxt : Context a b) -> (nUpdate : Node) -> (nKeep : Node) -> (grab : PatriciaGr a b) ->  ⦃ _ : IsTrue (nodeInContext nUpdate cxt) ⦄ -> ⦃ _ : IsTrue (gelem nKeep grab) ⦄ -> gelem ⦃ iGraphPatriciaGr ⦄ nKeep (cxt & (snd (match ⦃ iGraphPatriciaGr ⦄ nUpdate grab))) ≡ true

instance
  iDynGraphPatriciaGr .super = iGraphPatriciaGr

  iDynGraphPatriciaGr ._&_ = patriciaMerge
  
  iDynGraphPatriciaGr .propUpdatingContextKeepsNodes = propUpdatingContextKeepsNodesHelper

------------------------------------------------------------------
-- PatriciaTree properties required by the graph
------------------------------------------------------------------

-- | Checking if both nodes of the ledge are in a list of lnodes is
--   equivalent to checking if the nodes of the ledge are in the Graph
--   after inserting all nodes from the list of nodes into an empty graph
propLEdgeNodesInLNodeListEquivLEdgeNodesInGrahp : {a : Set} -> {b : Set} -> (lns : List (LNode a)) -> (le : LEdge b) -> (nodeInLNodeList (fst₃ le) lns && nodeInLNodeList (snd₃ le) lns) ≡ edgeNodesGelem ⦃ iGraphPatriciaGr ⦄ le (insNodes ⦃ iDynGraphPatriciaGr ⦄ lns (Gr (Map [])))

-- | Checking all nodes of a list of ledges are in a list of lnodes is
--   equivalent to checking if all nodes of a list of ledgse are in the Graph
--   after inserting all nodes from the list of nodes into an empty graph
propAllLEdgeNodesInLNodeListEquivAllLEdgeNodesInGrahp : (lns : List (LNode a)) -> (les : List (LEdge b)) -> Haskell.Prelude.map (λ le → nodeInLNodeList (fst₃ le) lns && nodeInLNodeList (snd₃ le) lns) les ≡ Haskell.Prelude.map (λ le → edgeNodesGelem ⦃ iGraphPatriciaGr ⦄ le (insNodes ⦃ iDynGraphPatriciaGr ⦄ lns (Gr (Map [])))) les
propAllLEdgeNodesInLNodeListEquivAllLEdgeNodesInGrahp lns [] = refl
propAllLEdgeNodesInLNodeListEquivAllLEdgeNodesInGrahp lns (le ∷ les) =
  begin
    Haskell.Prelude.map (λ le → nodeInLNodeList (fst₃ le) lns && nodeInLNodeList (snd₃ le) lns) (le ∷ les)
  =⟨⟩
    (nodeInLNodeList (fst₃ le) lns && nodeInLNodeList (snd₃ le) lns) ∷ Haskell.Prelude.map (λ le₁ → nodeInLNodeList (fst₃ le₁) lns && nodeInLNodeList (snd₃ le₁) lns) les
  =⟨ cong (λ x -> x ∷ Haskell.Prelude.map (λ le₁ → nodeInLNodeList (fst₃ le₁) lns && nodeInLNodeList (snd₃ le₁) lns) les) (propLEdgeNodesInLNodeListEquivLEdgeNodesInGrahp lns le) ⟩ 
    (edgeNodesGelem le (insNodes lns (Gr (Map [])))) ∷ Haskell.Prelude.map (λ le₁ → nodeInLNodeList (fst₃ le₁) lns && nodeInLNodeList (snd₃ le₁) lns) les
  =⟨ cong (λ x -> (edgeNodesGelem le (insNodes lns (Gr (Map [])))) ∷ x ) (propAllLEdgeNodesInLNodeListEquivAllLEdgeNodesInGrahp lns les) ⟩
    (edgeNodesGelem le (insNodes lns (Gr (Map [])))) ∷ Haskell.Prelude.map (λ le → edgeNodesGelem le (insNodes lns (Gr (Map [])))) les
  =⟨⟩
    Haskell.Prelude.map (λ le → edgeNodesGelem le (insNodes lns (Gr (Map [])))) (le ∷ les)
    ∎

instance 
  iGraphPatriciaGr .Graph.empty = Gr IM.empty

  iGraphPatriciaGr .isEmpty (Gr g)  = IM.null g

  iGraphPatriciaGr .match           = matchGr

  iGraphPatriciaGr .mkGraph lns les ⦃ allContained ⦄ = insEdges les (insNodes lns (Gr IM.empty)) ⦃ subst (All IsTrue) ( propAllLEdgeNodesInLNodeListEquivAllLEdgeNodesInGrahp lns les ) allContained ⦄

  iGraphPatriciaGr .labNodes (Gr g) = patriciaLabNodes g

  iGraphPatriciaGr .matchAny = matchAnyDefault

  iGraphPatriciaGr .noNodes = noNodesDefault

  iGraphPatriciaGr .nodeRange = nodeRangeDefault

  iGraphPatriciaGr .labEdges (Gr g) = IM.toList g >>= (λ {(node , (_ , _ , s)) ->
                                      IM.toList s >>= (λ {(next , labels) ->
                                        labels >>= (λ {label ->
                                          return (node , next , label)
                                          })
                                        })
                                      })

  ---------------------------------
  -- Properties
  ---------------------------------

  iGraphPatriciaGr .propGraphAndLabNodesSameNodes n (Gr (Map [])) = refl
  iGraphPatriciaGr .propGraphAndLabNodesSameNodes n (Gr g@(Map (m ∷ ms))) =
    begin
      gelem n (Gr g)
    =⟨⟩
      isJust (fst (matchGr n (Gr (Map (m ∷ ms)))))
    =⟨⟩
      isJust (fst (matchGrLookUp n (Map (m ∷ ms)) (IM.lookup n (Map (m ∷ ms)))))
    =⟨ propIsJustMatchGraphMaybe n (IM.lookup n (Map (m ∷ ms))) (Map (m ∷ ms)) ⟩
      isJust (IM.lookup n (Map (m ∷ ms)))
    =⟨ propLookUpIntMapEquivElemLabNodes n ((m ∷ ms)) ⟩
      elem ⦃ iFoldableList ⦄ n (Haskell.Prelude.map fst (patriciaLabNodes (Map (m ∷ ms))))
    =⟨⟩
      elem ⦃ iFoldableList ⦄ n (Haskell.Prelude.map fst (Graph.labNodes iGraphPatriciaGr (Gr (Map (m ∷ ms)))))
    ∎

  iGraphPatriciaGr .propEmptyGraphIsEmptyLabNodes (Gr (Map [])) = refl
  iGraphPatriciaGr .propEmptyGraphIsEmptyLabNodes (Gr (Map (m ∷ ms))) = refl

------------------------------------------------------------------
-- PatriciaTree properties required by the graph continued
------------------------------------------------------------------

-- | Checking if a node is part of the patrica graph is the same as checking if the node is in the IntMap.
propGelemEquivIsJustLookUp : (n : Node) -> (ms : IntMap (Context' a b)) -> gelem ⦃ iGraphPatriciaGr ⦄ n (Gr ms) ≡ isJust (IntMap.lookup n ms)
propGelemEquivIsJustLookUp n (Map []) = refl
propGelemEquivIsJustLookUp n (Map (m ∷ ms)) =
  begin
    gelem ⦃ iGraphPatriciaGr ⦄ n (Gr (Map (m ∷ ms)))
  =⟨⟩
    isJust (fst (matchGr n (Gr (Map (m ∷ ms)))))
  =⟨⟩
    isJust (fst (matchGrLookUp n (Map (m ∷ ms)) (IntMap.lookup n (Map (m ∷ ms)))))
  =⟨ propIsJustMatchGraphMaybe n (IntMap.lookup n (Map (m ∷ ms))) (Map (m ∷ ms)) ⟩
    isJust (IntMap.lookup n (Map (m ∷ ms)))
  ∎

-- | When a node is looked up, the node and context are removed from the IntMap.
--   So, this is equivalent to deleting the node directly from the IntMap.
propIsJustLookUpSndMatchEquivDelete : {a : Set} -> {b : Set} -> (nKeep : Node) -> (n : Node) -> (grMap : GraphRep a b) -> isJust (IM.lookup nKeep (snd (matchGrLookUp' n grMap (IntMap.lookup n grMap)))) ≡ isJust (IM.lookup nKeep (IM.delete n grMap))
propIsJustLookUpSndMatchEquivDelete nKeep n (Map []) = refl
propIsJustLookUpSndMatchEquivDelete {a} {b} nKeep n grMap@(Map (km@(k , m) ∷ ms)) =
  begin
    isJust (IM.lookup nKeep (snd (matchGrLookUp' n grMap (IntMap.lookup n grMap))))
  =⟨⟩ 
    isJust (IM.lookup nKeep (snd (matchGrLookUp' n (Map (km ∷ ms)) (if n == k then Just m else IM.lookup n (Map ms)))))
  =⟨ helper (IM.lookup n (Map (km ∷ ms))) {refl} ⟩
    isJust (IM.lookup nKeep (IM.delete n grMap))
  ∎
    where
      helper : (mcxt : Maybe (Context' a b)) -> {eq : mcxt ≡ (IM.lookup n grMap)} -> isJust (IM.lookup nKeep (snd (matchGrLookUp' n grMap (IntMap.lookup n grMap)))) ≡ isJust (IM.lookup nKeep (IM.delete n grMap))
      helper Nothing {eq} =
        begin
          isJust (IM.lookup nKeep (snd (matchGrLookUp' n grMap (IntMap.lookup n grMap))))
        =⟨ cong (λ x -> isJust (IM.lookup nKeep (snd (matchGrLookUp' n grMap x)))) (sym eq) ⟩
          isJust (IM.lookup nKeep (snd (matchGrLookUp' n grMap Nothing)))
        =⟨⟩
          isJust (IM.lookup nKeep grMap)
        =⟨ cong (λ x -> isJust (IM.lookup nKeep x)) ((sym (propDeleteNotElemEquivInit n grMap ⦃ subst IsFalse (trans (propIsJustNothing {a}) (cong (λ x -> isJust x) eq)) itsFalse ⦄))) ⟩
          isJust (IM.lookup nKeep (IM.delete n grMap))
        ∎
      helper (Just (Map neIns , l , Map neOuts)) {eq} =
        begin
          isJust (IM.lookup nKeep (snd (matchGrLookUp' n grMap (IntMap.lookup n grMap))))
        =⟨ cong (λ x -> isJust (IM.lookup nKeep (snd (matchGrLookUp' n (Map (km ∷ ms)) x)))) (sym eq) ⟩
          isJust (IM.lookup nKeep (snd (matchGrLookUp' n (Map (km ∷ ms)) (Just (Map neIns , l , Map neOuts)))))
        =⟨⟩
          isJust (IM.lookup nKeep (clearSucc (clearPred (IM.delete n grMap) n (IM.delete n (Map neOuts))) n (IM.delete n (Map neIns))))
        =⟨ propFindingNodesNotDependentOnEdgesDelete nKeep n (IM.delete n (Map neIns)) (IM.delete n (Map neOuts)) (IM.delete n grMap) ⟩
          isJust (IM.lookup nKeep (IM.delete n grMap))
        ∎

-- | Checking if a node is an element of a context merged with a context, can be split
--   into checking if the node is part of the context or part of the graph.
propMergingSplit : (cxt : Context a b) -> (nKeep : Node) -> (grMap : GraphRep a b) -> isJust (IM.lookup nKeep (patriciaMerge' cxt (snd (matchGrLookUp (sndContext cxt) grMap (IntMap.lookup (sndContext cxt) grMap))))) ≡ (nKeep == (sndContext cxt) || isJust (IM.lookup nKeep (snd (matchGrLookUp' (sndContext cxt) grMap (IntMap.lookup (sndContext cxt) grMap)))))
propMergingSplit cxt@(_,_,_,_ eIn v l eOut) nKeep grMap =
  begin
    isJust (IM.lookup nKeep (patriciaMerge' (_,_,_,_ eIn v l eOut) (snd (matchGrLookUp v grMap (IntMap.lookup v grMap)))))
  =⟨ cong (λ x -> isJust (IM.lookup nKeep (patriciaMerge' (_,_,_,_ eIn v l eOut) x))) propMatchGrLookUpPrime ⟩
    isJust (IM.lookup nKeep (patriciaMerge' (_,_,_,_ eIn v l eOut) (Gr g')))
  =⟨⟩
    isJust (IM.lookup nKeep (addPred (addSucc (IM.insert v (preds , l , succs) g') v np preds) v ns succs))
  =⟨ propFindingNodesNotDependentOnEdgesInsert nKeep v np ns preds succs (preds , l , succs) (IM.insert v (preds , l , succs) g') ⟩
    isJust (IM.lookup nKeep (IM.insert v (preds , l , succs) g'))
  =⟨ propLookUpSplit nKeep v (preds , l , succs) g' ⟩
    (nKeep == v || isJust (IM.lookup nKeep g'))
  =⟨⟩
    (nKeep == v || isJust (IM.lookup nKeep (snd (matchGrLookUp' v grMap (IntMap.lookup v grMap)))))
  ∎
    where
      g' = snd (matchGrLookUp' v grMap (IntMap.lookup v grMap))
      propMatchGrLookUpPrime : snd (matchGrLookUp v grMap (IntMap.lookup v grMap)) ≡ Gr g'
      propMatchGrLookUpPrime =
        begin
          snd (matchGrLookUp v grMap (IntMap.lookup v grMap))
        =⟨⟩
          snd (second (λ x -> Gr x) (matchGrLookUp' v grMap (IntMap.lookup v grMap)))
        =⟨ propConstructorWrapSecond (λ x -> Gr x)  (matchGrLookUp' v grMap (IntMap.lookup v grMap)) ⟩
          Gr (snd (matchGrLookUp' v grMap (IntMap.lookup v grMap)))
        =⟨⟩
          Gr g'
        ∎
      nppreds = fromAdjCounting eIn
      np = fst nppreds
      preds = snd nppreds
      nssuccs = fromAdjCounting eOut
      ns = fst nssuccs
      succs = snd nssuccs

-- | Updating a context keeps al nodes. This helper function is required. 
--   The PatriciaGr instance is not fully in scope when implementing the proof directly in the instance.
propUpdatingContextKeepsNodesHelper {a} {b} cxt@(_,_,_,_ eIn v l eOut) nUpdate nKeep (Gr intMap) ⦃ updateInContext ⦄ ⦃ nKeepGelem ⦄ =
  begin
    gelem nKeep (cxt & (snd (match nUpdate (Gr intMap))))
  =⟨⟩
    gelem nKeep (patriciaMerge cxt (snd (match nUpdate (Gr intMap))))
  =⟨⟩
    isJust (fst (match nKeep (patriciaMerge cxt (snd (match nUpdate (Gr intMap))))))
  =⟨ cong (λ x -> isJust (fst (match nKeep (patriciaMerge (_,_,_,_ eIn v l eOut) (snd (match x (Gr intMap))))))) (sameNodeIsEq' nUpdate v ⦃ updateInContext ⦄) ⟩
    isJust (fst (match nKeep (patriciaMerge (_,_,_,_ eIn v l eOut) (snd (match v (Gr intMap))))))
  =⟨⟩
    isJust (fst (matchGrLookUp nKeep (patriciaMerge' (_,_,_,_ eIn v l eOut) (snd (match v (Gr intMap)))) oldmcxt))
  =⟨ propIsJustMatchGraphMaybe nKeep oldmcxt (patriciaMerge' (_,_,_,_ eIn v l eOut) (snd (match v (Gr intMap)))) ⟩
    isJust (IM.lookup nKeep (patriciaMerge' (_,_,_,_ eIn v l eOut) (snd (matchGrLookUp v intMap (IntMap.lookup v intMap)))))
  =⟨ propMergingSplit (_,_,_,_ eIn v l eOut) nKeep intMap ⟩
    (nKeep == v || isJust (IM.lookup nKeep (snd (matchGrLookUp' v intMap (IntMap.lookup v intMap)))))
  =⟨ cong (λ x -> (nKeep == v || x)) (propIsJustLookUpSndMatchEquivDelete nKeep v intMap) ⟩
    (nKeep == v || isJust (IM.lookup nKeep (IM.delete v intMap)))
  =⟨ propElemWithDelete nKeep v intMap ⦃ subst IsTrue (sym (propIsTrueEquivTrue (isJust (IM.lookup nKeep intMap)) ⦃ subst IsTrue (trans (sym (propIsTrueEquivTrue (gelem nKeep (Gr intMap)) ⦃ nKeepGelem ⦄ )) (propGelemEquivIsJustLookUp nKeep intMap)) itsTrue ⦄ )) itsTrue ⦄ ⟩
    true
  ∎
    where
      oldmcxt : Maybe (Context' a b)
      oldmcxt = (IM.lookup nKeep (patriciaMerge' (_,_,_,_ eIn v l eOut) (snd (matchGrLookUp v intMap (IntMap.lookup v intMap)))))

------------------------------------------------------
-- Simple versions of inserting nodes
-- They are used for proofing and are equivalent
-- to the original functions as proofed below.
------------------------------------------------------
insNodeSimple' : LNode a -> GraphRep a b -> GraphRep a b
insNodeSimple' vl intMap = IM.insert (fst vl) (Map [] , (snd vl) , Map []) intMap

insNodeSimple : LNode a -> PatriciaGr a b -> PatriciaGr a b
insNodeSimple (v , l) (Gr intMap) = Gr (insNodeSimple' (v , l) intMap)

insNodesSimple : List (LNode a) -> PatriciaGr a b -> PatriciaGr a b
insNodesSimple lns g = (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) g

propInsNodeInsNodeSimpleEquiv : (ln : LNode a) -> (gr : PatriciaGr a b) -> insNode ln gr ≡ insNodeSimple ln gr
propInsNodeInsNodeSimpleEquiv (n , l) (Gr (Map [])) = refl
propInsNodeInsNodeSimpleEquiv (n , l) (Gr (Map (m ∷ ms))) = refl

propInsNodesInsNodesSimpleEquiv : (lns : List (LNode a)) -> (gr : PatriciaGr a b) -> (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) gr ≡ (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) gr
propInsNodesInsNodesSimpleEquiv [] (Gr (Map ms)) = refl
propInsNodesInsNodesSimpleEquiv (ln@(n , l) ∷ lns) gr@(Gr (Map ms)) =
  begin
    (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode (ln ∷ lns)) (Gr (Map ms))
  =⟨⟩
    (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms)))
  =⟨ propInsNodesInsNodesSimpleEquiv lns (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms))) ⟩
    (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms)))
  =⟨⟩
    (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple (ln ∷ lns)) (Gr (Map ms))
  ∎

-- | The list of nodes is equivalent to the list of key value pairs of the IntMap mapped to the key.
propNodesIsMapFst : (gr : PatriciaGr a b) -> nodes gr ≡ Haskell.Prelude.map fst (IM.toList (getMap gr))
propNodesIsMapFst (Gr (Map [])) = refl
propNodesIsMapFst gr@(Gr (Map (m@(k , v) ∷ ms))) =
  begin
    nodes (Gr (Map (m ∷ ms)))
  =⟨ cong (λ x -> x ∷ nodes (Gr (Map (ms)))) (sym (propFstPatriciaLabNodeIsNode k v)) ⟩
    k ∷ nodes (Gr (Map (ms)))
  =⟨ cong (λ x -> k ∷ x) (propNodesIsMapFst (Gr (Map ms))) ⟩
    k ∷ Haskell.Prelude.map fst ms
  =⟨⟩
    Haskell.Prelude.map fst (m ∷ ms)
  ∎

-- | The list of nodes is equivalent to the list of key value pairs of the IntMap mapped to the key.
--   When adding an extra node / key this still holds.
propNodesEquivKeys : (lns : List (LNode a)) -> (gr : PatriciaGr a b) -> nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) gr) ≡ Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) (getMap gr)))
propNodesEquivKeys [] (Gr (Map [])) = refl
propNodesEquivKeys [] gr@(Gr (Map ms@(_ ∷ _))) =
  begin
    nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple []) (Gr (Map ms)))
  =⟨⟩
    nodes (Gr (Map ms))
  =⟨ propNodesIsMapFst (Gr (Map ms)) ⟩
    Haskell.Prelude.map fst ms
  =⟨⟩
    Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' []) (Map ms)))
  ∎
propNodesEquivKeys (ln@(n , l) ∷ lns) (Gr (Map ms)) =
  begin
    nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple (ln ∷ lns)) (Gr (Map ms)))
  =⟨⟩
    nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms))))
  =⟨ propNodesEquivKeys lns  (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms))) ⟩
    Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) (Map ((n , (Map [] , l , Map [])) ∷ ms))))
  =⟨⟩
    Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' (ln ∷ lns)) (Map ms)))
  ∎

-- | In the PatriciaGraph, nodes that at the front of the graph are also at the front of the list of nodes.
propHeadNodesEquivGraphNode : (lk : Node) -> (ln : LNode a) -> (lns : List (LNode a)) -> elem lk (nodes ⦃ iGraphPatriciaGr ⦄ {a} {b} ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map (((fst ln) , (Map [] , (snd ln) , Map [])) ∷ []))))) ≡ elem lk ((fst ln) ∷ nodes ⦃ iGraphPatriciaGr ⦄ {a} {b} ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map []))))
propHeadNodesEquivGraphNode lk ln [] = refl
propHeadNodesEquivGraphNode lk (v , l) lns@(_ ∷ _) =
  begin
    elem ⦃ iFoldableList ⦄ lk (nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map ((v , (Map [] , l , Map [])) ∷ [])))))
  =⟨ cong (λ x -> elem ⦃ iFoldableList ⦄ lk (nodes ⦃ iGraphPatriciaGr ⦄ x)) (propInsNodesInsNodesSimpleEquiv lns ((Gr (Map ((v , (Map [] , l , Map [])) ∷ []))))) ⟩
    elem ⦃ iFoldableList ⦄ lk (nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) (Gr (Map ((v , (Map [] , l , Map [])) ∷ [])))))
  =⟨ cong (λ x -> elem ⦃ iFoldableList ⦄ lk x) (propNodesEquivKeys lns (Gr (Map ((v , (Map [] , l , Map [])) ∷ [])))) ⟩
    elem ⦃ iFoldableList ⦄ lk (Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) (Map ((v , (Map [] , l , Map [])) ∷ [])))))
  =⟨ propElemInsertElemMap lk v l lns ⟩
    elem ⦃ iFoldableList ⦄ lk (v ∷ Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) (Map []))))
  =⟨ cong (λ x -> elem ⦃ iFoldableList ⦄ lk (v ∷ x)) (sym (propNodesEquivKeys lns (Gr (Map [])))) ⟩
    elem ⦃ iFoldableList ⦄ lk (v ∷ nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) (Gr (Map []))))
  =⟨ cong (λ x -> elem ⦃ iFoldableList ⦄ lk (v ∷ nodes ⦃ iGraphPatriciaGr ⦄ x)) (sym (propInsNodesInsNodesSimpleEquiv lns (Gr (Map [])))) ⟩
    elem ⦃ iFoldableList ⦄ lk (v ∷ nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map []))))
  ∎

-- | Inserting nodes, matching and checking if the returned context is dependent on the IntMap.
propIsJustMatchGrInsertEquivMatchGrLookUp'Insert : (v : Node ) -> (lns : List (LNode a)) -> (pgr : PatriciaGr a b) -> isJust (fst (matchGr v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) pgr))) ≡ isJust (fst (matchGrLookUp' v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) (getMap pgr)) (IM.lookup v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) (getMap pgr)))))
propIsJustMatchGrInsertEquivMatchGrLookUp'Insert v [] (Gr (Map [])) = refl
propIsJustMatchGrInsertEquivMatchGrLookUp'Insert v [] pgr@(Gr intMap@(Map (_ ∷ _))) =
  begin
    isJust (fst (matchGr v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple []) pgr)))
  =⟨⟩
    isJust (fst (matchGrLookUp v intMap (IntMap.lookup v intMap)))
  =⟨ propIsJustMatchLookupEquivmatchGrLookUp' v intMap (IntMap.lookup v intMap) ⟩
    isJust (fst (matchGrLookUp' v intMap (IntMap.lookup v intMap)))
  =⟨⟩
    isJust (fst (matchGrLookUp' v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' []) (getMap pgr)) (IM.lookup v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' []) (getMap pgr)))))
  ∎
propIsJustMatchGrInsertEquivMatchGrLookUp'Insert v (ln@(k , l) ∷ lns) (Gr (Map ms)) =
  begin
    isJust (fst (matchGr v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple (ln ∷ lns)) (Gr (Map ms)))))
  =⟨⟩
    isJust (fst (matchGr v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) (Gr (Map ((k , (Map [] , l , Map [])) ∷ ms))))))
  =⟨ propIsJustMatchGrInsertEquivMatchGrLookUp'Insert v lns (Gr (Map ((k , (Map [] , l , Map [])) ∷ ms))) ⟩
    isJust (fst (matchGrLookUp' v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) (Map ((k , (Map [] , l , Map [])) ∷ ms))) (IM.lookup v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) (Map ((k , (Map [] , l , Map [])) ∷ ms))))))
  =⟨⟩
    isJust (fst (matchGrLookUp' v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' (ln ∷ lns)) (Map ms)) (IM.lookup v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' (ln ∷ lns)) (Map ms)))))
  ∎

-- | Checking if a node is an element of the list of nodes after inserting nodes,
--   is equivalent to checking if the node is an element of the graph after inserting nodes.
propElemNodesEquivGelemInsertedNodes : (v : Node ) -> (lns : List (LNode a)) -> (pgr : PatriciaGr a b) -> elem v (nodes ⦃ iGraphPatriciaGr ⦄ {a} {b} ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) pgr)) ≡ gelem v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) pgr)
propElemNodesEquivGelemInsertedNodes v lns pgr@(Gr intMap@(Map ms)) =
  begin
    elem v (nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) pgr))
  =⟨ cong (λ x -> elem v (nodes ⦃ iGraphPatriciaGr ⦄ x)) (propInsNodesInsNodesSimpleEquiv lns pgr) ⟩
    elem v (nodes ⦃ iGraphPatriciaGr ⦄ ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) pgr))
  =⟨ cong (λ x -> elem ⦃ iFoldableList ⦄ v x) (propNodesEquivKeys lns pgr) ⟩
    elem v (Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns)intMap)))
  =⟨ propElemEquivLookUp v lns intMap ⟩
    isJust (IM.lookup v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) intMap))
  =⟨ sym (propIsJustMatchGraphMaybe' v (IM.lookup v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) intMap)) ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) intMap)) ⟩
    isJust (fst (matchGrLookUp' v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) intMap) (IM.lookup v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns) intMap))))
  =⟨ sym (propIsJustMatchGrInsertEquivMatchGrLookUp'Insert v lns pgr) ⟩
    isJust (fst (matchGr v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) pgr)))
  =⟨⟩
    isJust (fst (match v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns) pgr)))
  =⟨ cong (λ x -> isJust (fst (match v x))) (sym (propInsNodesInsNodesSimpleEquiv lns pgr)) ⟩
    isJust (fst (match v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) pgr)))
  =⟨⟩
    gelem v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) pgr)
  ∎

-- | Checking if a node is an element of an empty graph is equivalent to false.
propGelemEmpty : {a : Set} -> {b : Set} -> (n : Node) -> gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} n (iGraphPatriciaGr .Graph.empty) ≡ false
propGelemEmpty {a} {b} n =
  begin
    gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} n (iGraphPatriciaGr .Graph.empty)
  =⟨⟩
    gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} n (Gr IM.empty)
  =⟨⟩
    isJust (fst (match ⦃ iGraphPatriciaGr ⦄ {a} {b} n (Gr IM.empty)))
  =⟨⟩
    isJust (fst (matchGr {a} {b} n (Gr IM.empty)))
  =⟨⟩
    false
  ∎

-- | Checking if a node is in a node list is the same as inserting
--   all nodes from the node list into an empty graph and checking if
--   the node is in the list of nodes produced from the graph.
propNodeElemLNodeListEquivNodeElemGraphNodes : {a : Set} -> {b : Set} -> (n : Node) -> (lns : List (LNode a)) -> elem n (Haskell.Prelude.map fst (lns)) ≡ elem n (nodes ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr {a} {b} (Map []))))
propNodeElemLNodeListEquivNodeElemGraphNodes v [] = refl
propNodeElemLNodeListEquivNodeElemGraphNodes v (ln@(n , l) ∷ lns) =
  begin
    elem v (Haskell.Prelude.map fst (ln ∷ lns))
  =⟨⟩
    elem v (n ∷ Haskell.Prelude.map fst lns)
  =⟨⟩
    foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (n ∷ Haskell.Prelude.map fst lns)
   =⟨⟩
    (v == n || foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (Haskell.Prelude.map fst lns))
  =⟨ cong (λ x -> (v == n || x )) (propNodeElemLNodeListEquivNodeElemGraphNodes v lns) ⟩
    (v == n || foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (nodes ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map [])))))
  =⟨⟩
    foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (n ∷ nodes ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map []))))
  =⟨ (sym (propHeadNodesEquivGraphNode v ln lns)) ⟩
    foldMap ⦃ iFoldableList ⦄ ⦃ MonoidDisj ⦄ (v ==_) (nodes ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map ((n , (Map [] , l , Map [])) ∷ [])))))
  =⟨⟩
    elem v (nodes ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map ((n , (Map [] , l , Map [])) ∷ [])))))
  =⟨⟩
    elem v (nodes ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode (ln ∷ lns)) (Gr (Map []))))
  ∎

-- | Checking if a node is in a node list is the same as inserting
--   all nodes from the node list into an empty graph and checking if
--   the node is gelem.
propNodeInLNodeListEquivNodeInGraph : {a : Set} -> {b : Set} -> (n : Node) -> (lns : List (LNode a)) -> elem n (Haskell.Prelude.map fst lns) ≡ gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} n (insNodes ⦃ iDynGraphPatriciaGr ⦄ lns (Gr (Map [])))
propNodeInLNodeListEquivNodeInGraph v [] = refl
propNodeInLNodeListEquivNodeInGraph v (ln@(n , l) ∷ lns) =
  begin
    elem v (Haskell.Prelude.map fst (ln ∷ lns))
  =⟨ propNodeElemLNodeListEquivNodeElemGraphNodes v (ln ∷ lns) ⟩
    elem v (nodes ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map ((n , (Map [] , l , Map [])) ∷ [])))))
  =⟨ propElemNodesEquivGelemInsertedNodes v lns (Gr (Map ((n , (Map [] , l , Map [])) ∷ []))) ⟩
    gelem v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map ((n , (Map [] , l , Map [])) ∷ []))))
  =⟨⟩
    gelem v ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) ((_&_ (_,_,_,_ [] n l [])) (Gr (Map []))))
  =⟨⟩
    gelem v (_∘_ (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (_&_ (_,_,_,_ [] n l [])) (Gr (Map [])))
  =⟨⟩
    gelem v (flip _∘_ (_&_ (_,_,_,_ [] n l [])) (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns) (Gr (Map [])))
  =⟨⟩
    gelem v (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode (ln ∷ lns) (Gr (Map [])))
  =⟨⟩
    gelem v (foldl (flip insNode) (Gr (Map [])) (ln ∷ lns))
  =⟨ cong (λ x -> (gelem v x)) (propFodlEquivFodl' (flip insNode) (Gr (Map [])) (ln ∷ lns)) ⟩
    gelem v (Haskell.Data.List.foldl' (flip insNode) (Gr (Map [])) (ln ∷ lns))
  =⟨⟩
    gelem v (insNodes ⦃ iDynGraphPatriciaGr ⦄ (ln ∷ lns) (Gr (Map [])))
  ∎

-- | This function needs to be implemented below the graph instance.
-- propLEdgeNodesInLNodeListEquivLEdgeNodesInGrahp : {a : Set} -> {b : Set} -> (lns : List (LNode a)) -> (le : LEdge b) -> (nodeInLNodeList (fst₃ le) lns && nodeInLNodeList (snd₃ le) lns) ≡ edgeNodesGelem ⦃ iGraphPatriciaGr ⦄ le (insNodes ⦃ iDynGraphPatriciaGr ⦄ lns (Gr (Map [])))
propLEdgeNodesInLNodeListEquivLEdgeNodesInGrahp {a} {b} [] (v , w , l) =
  begin
    false
  =⟨⟩
    (false && false)
  =⟨ cong₂ (λ x y -> x && y) (propGelemEmpty {a} {b} v) (propGelemEmpty {a} {b} w) ⟩
    (gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} v (foldl (flip insNode) (Gr (Map [])) []) && gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} w (foldl (flip insNode) (Gr (Map [])) []))
  =⟨ cong (λ x -> (gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} v x && gelem w x)) (propFodlEquivFodl' (flip insNode) (Gr (Map [])) []) ⟩
    (gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} v (Haskell.Data.List.foldl' (flip insNode) (Gr (Map [])) []) && gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} w (Haskell.Data.List.foldl' (flip insNode) (Gr (Map [])) []))
  =⟨⟩
    (gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} v (insNodes ⦃ iDynGraphPatriciaGr ⦄ [] (Gr (Map []))) && gelem ⦃ iGraphPatriciaGr ⦄ {a} {b} w (insNodes ⦃ iDynGraphPatriciaGr ⦄ [] (Gr (Map []))))
  ∎
propLEdgeNodesInLNodeListEquivLEdgeNodesInGrahp (ln@(n , l) ∷ lns) le@(v , w , _) =
  begin
    (nodeInLNodeList (fst₃ le) (ln ∷ lns) && nodeInLNodeList (snd₃ le) (ln ∷ lns))
  =⟨⟩
    (elem v (Haskell.Prelude.map fst (ln ∷ lns))) && (elem w (Haskell.Prelude.map fst (ln ∷ lns)))
  =⟨ cong₂ (λ x y -> x && y) (propNodeInLNodeListEquivNodeInGraph v (ln ∷ lns)) (propNodeInLNodeListEquivNodeInGraph w (ln ∷ lns)) ⟩
    (gelem v (insNodes (ln ∷ lns) (Gr (Map []))) && gelem w (insNodes (ln ∷ lns) (Gr (Map []))))
  =⟨⟩
    edgeNodesGelem le (insNodes (ln ∷ lns) (Gr (Map [])))
  ∎
