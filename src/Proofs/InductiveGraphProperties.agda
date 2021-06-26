-- https://github.com/haskell/fgl/blob/master/test/Data/Graph/Inductive/Graph/Properties.hs#L37
module Proofs.InductiveGraphProperties where

open import Proofs.Proof
open import Proofs.ListProperties

open import Haskell.Prelude
open import Haskell.Prim
open import Prelude
open import Haskell.Data.List
open import Haskell.Data.Maybe

open import InductiveGraph
open import InductiveGraphProperties

open Graph ⦃ ... ⦄
open DynGraph ⦃ ... ⦄
open GraphProperties ⦃ ... ⦄
open DynGraphProperties ⦃ ... ⦄

----------------------------------------------------------------------
-- Laws from Marting Erwigs paper
----------------------------------------------------------------------
propGmapFusion : ⦃ _ : DynGraph gr ⦄ -> (grab : gr a b) -> (f : (Context a b -> Context c d)) -> (g : (Context a b -> Context a b)) -> (gmap f (gmap g grab)) ≡ gmap (f ∘ g) grab
propGmapFusion = {!   !}

propGmapUnit : ⦃ _ : DynGraph gr ⦄ ->  (grab : gr a b) -> gmap id grab ≡ id grab
propGmapUnit = {!   !}

-- ----------------------------------------------------------------------
-- Self defined properties
-- ----------------------------------------------------------------------

-- | NewNodes should return the amount of nodes that are asked
--   Doesn't depend on a custom implementation of Graph, since it doesn't matter
--   what nodeRange returns.
propNewNodesCorrectAmount : ⦃ _ : Graph gr ⦄ -> (grab : gr a b) -> (n : Int) -> ⦃ IsNonNegativeInt n ⦄ -> length (newNodes n grab) ≡ n
propNewNodesCorrectAmount = {!   !}

-- propInsEdgeKeepsNodes : ⦃ _ : DynGraph gr ⦄ -> (le : LEdge b) -> (grab : gr a b) -> ⦃ _ : IsTrue (edgeNodesGelem le grab) ⦄ -> edgeNodesGelem le grab ≡ edgeNodesGelem le (insEdge le grab)
-- propInsEdgeKeepsNodes {gr} {b} {a} le@(v , w , l) g ⦃ isContained ⦄ =
--   begin
--     edgeNodesGelem le g
--   =⟨⟩
--     gelem v g && gelem w g
--   =⟨ propIsTrueIsJustTrue (edgeNodesGelem le g) ⟩
--     true
--   =⟨ cong (λ x -> true && x) (sym (propWIng')) ⟩
--     true && gelem w (cxt & snd (match v g))
--   =⟨ cong (λ x -> x && gelem w (cxt & snd (match v g))) (sym (propVIng')) ⟩
--     gelem v (cxt & snd (match v g)) && gelem w (cxt & snd (match v g))
--   =⟨⟩
--     gelem v (insEdge le g) && gelem w (insEdge le g)
--   =⟨⟩
--     edgeNodesGelem le (insEdge le g)
--   ∎
--   where
--     mcxtg' = match v g
--     mcxt = fst mcxtg'
--     prlasu = fromJust mcxt ⦃ subst IsTrue (sym (propIsTrueAndTrueFst (gelem v g) (gelem w g) ⦃ isContained ⦄)) itsTrue ⦄
--     pr = fst₄ prlasu
--     la = third₄ prlasu
--     su = fourth₄ prlasu
--     cxt : Context a b
--     cxt = (_,_,_,_ pr v la ((l , w) ∷ su))
--     g' : gr a b
--     g' = snd (match v g)
--     propEdgeNodeVInCxt : elem v (nodesFromContext cxt) ≡ true
--     propEdgeNodeVInCxt =
--       begin
--         elem v (nodesFromContext cxt)
--       =⟨⟩
--         elem v (nodesFromContext (_,_,_,_ pr v la ((l , w) ∷ su)))
--       =⟨⟩
--         elem v (v ∷ w ∷ map snd su)
--       =⟨⟩
--         (if v == v then true else elem v (w ∷ map snd su))
--       =⟨ cong (λ x -> if x then true else elem v (w ∷ map snd su)) (sameNodeIsEq v) ⟩
--         true
--       ∎
--     propEdgeNodeWInCxt : elem w (nodesFromContext cxt) ≡ true
--     propEdgeNodeWInCxt =
--       begin
--         elem w (nodesFromContext cxt)
--       =⟨⟩
--         elem w (nodesFromContext (_,_,_,_ pr v la ((l , w) ∷ su)))
--       =⟨⟩
--         elem w (v ∷ w ∷ map snd su)
--       =⟨⟩
--         (if w == v then true else elem w (w ∷ map snd su))
--       =⟨ propIfSwitchBool (w == v) ⟩
--         (if w /= v then elem w (w ∷ map snd su) else true)
--       =⟨ cong (λ x -> if x then elem w (w ∷ map snd su) else true) (difNodeIsDif w v) ⟩
--         (if false then elem w (w ∷ map snd su) else true)
--       =⟨⟩
--         true
--       ∎
--     propVIng' : gelem v (cxt & g') ≡ true
--     propVIng' =
--       begin
--         gelem v (cxt & g')
--       =⟨ trans (sym (propAddingContextAddsNodes cxt v g')) propEdgeNodeVInCxt ⟩
--         true
--       ∎
--     propWIng' : gelem w (cxt & g') ≡ true
--     propWIng' =
--       begin
--         gelem w (cxt & g')
--       =⟨ trans (sym (propAddingContextAddsNodes cxt w g')) propEdgeNodeWInCxt ⟩
--         true
--       ∎

-- ----------------------------------------------------------------------
-- QuickCheck properties
-- Provable if some other properties are known.
-- ----------------------------------------------------------------------

-- | Insert a node for every label in the list, but don't add any new
--   edges. Uses nodes that are not contained in the graph
--   Since insNodes depends on insNode it should be possible to prove these
--   properties knowing that the insNode properties are correct
propInsNodes : ⦃ _ : DynGraphProperties gr ⦄ -> ⦃ _ : Eq a ⦄ -> (lns : List (LNode a)) -> (grab : gr a b) -> equalLists (labNodes (insNodes lns grab)) (lns ++ (labNodes grab)) ≡ true
propInsNodes [] g = propEqualLists (labNodes (insNodes [] g))
-- propInsNodes (ln ∷ []) g =
--     begin
--         equalLists (labNodes (insNodes (ln ∷ []) g)) ((ln ∷ []) ++ (labNodes g))
--     =⟨⟩
--         equalLists (labNodes (insNode ln g)) (ln ∷ (labNodes g))
--     =⟨ propInsNode ln g ⟩
--         true
--     ∎
-- propInsNode : equalLists (labNodes (insNode ln grab)) (ln ∷ (labNodes grab)) ≡ true
propInsNodes (ln ∷ lns) g =
    begin
        equalLists (labNodes (insNodes (ln ∷ lns) g)) (ln ∷ lns ++ (labNodes g))
    =⟨⟩
        equalLists (labNodes (foldl' (flip insNode) g (ln ∷ lns))) (ln ∷ lns ++ (labNodes g))
    =⟨ cong (λ x -> equalLists (labNodes x) (ln ∷ lns ++ (labNodes g))) (sym (propFodlEquivFodl' (flip insNode) g (ln ∷ lns))) ⟩
        equalLists (labNodes (foldl (flip insNode) g (ln ∷ lns))) (ln ∷ lns ++ (labNodes g))
    =⟨⟩
        equalLists (labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode (ln ∷ lns) g)) (ln ∷ lns ++ (labNodes g))
    =⟨ {!   propEqualListsEquiv₁ !} ⟩
        equalLists (ln ∷ labNodes (foldl (flip insNode) g lns)) (ln ∷ lns ++ (labNodes g))
    =⟨ cong (λ x -> equalLists (ln ∷ labNodes x) (ln ∷ lns ++ (labNodes g))) (propFodlEquivFodl' (flip insNode) g lns) ⟩
        equalLists (ln ∷ labNodes (foldl' (flip insNode) g lns)) (ln ∷ lns ++ (labNodes g))
    =⟨⟩
        equalLists (ln ∷ labNodes (insNodes lns g)) (ln ∷ lns ++ (labNodes g))
    =⟨ propEqualListsSameHead ln (labNodes (insNodes lns g)) (lns ++ (labNodes g)) ⟩
        equalLists (labNodes (insNodes lns g)) (lns ++ (labNodes g))
    =⟨ propInsNodes lns g ⟩
        true
    ∎

propInsNodesNoAddedEdges : ⦃ _ : DynGraphProperties gr ⦄ -> ⦃ _ : Ord b ⦄ -> (lns : List (LNode a)) -> (grab : gr a b) -> ⦃ _ : All (λ ln -> IsFalse (gelem (fst ln) grab)) lns ⦄ -> equalLists (labEdges (insNodes lns grab)) (labEdges grab) ≡ true
propInsNodesNoAddedEdges = {!   !}

-- | Insert an edge for every label in the list.  Multiple edges and
--   loops allowed.
--   Since insEdges depends on insEdge it should be possible to prove this
--   properties knowing that the insEdge property is correct
propInsEdges : ⦃ _ : DynGraphProperties gr ⦄ -> ⦃ _ : Ord b ⦄ -> (les : List (LEdge b)) -> (grab : gr a b) -> ⦃ _ : All IsTrue (map (λ le -> edgeNodesGelem le grab) les) ⦄ -> equalLists (labEdges (insEdges les grab)) (les ++ (labEdges grab)) ≡ true
propInsEdges = {!   !}

-- | Test deleting multiple edges.
--   Since delEdges depends on delEdge it should be possible to prove these
--   prroperties knowing that the delEdge properties are correct
propDelEdges : ⦃ _ : DynGraphProperties gr ⦄ ->  (es : List Edge) -> (grab : gr a b) -> all (λ e -> not (elem e (edges (delEdges es grab)))) es ≡ true
propDelEdges = {!   !}

propDelEdgesGelemNode : ⦃ _ : DynGraphProperties gr ⦄ ->  (es : List Edge) -> (grab : gr a b) -> all (λ e -> (all (λ n -> not (nodeInEdge n e)) (nodes (delEdges es grab)))) es ≡ true
propDelEdgesGelemNode = {!   !}

-- | Filter properties
--   Both properties depend on labnfilter, so if propLabnfilterTrue holds,
--   then these properties should also hold. 
-- | Tests `nfilter` with a function accepting all nodes.
propNfilterTrue : ⦃ _ : DynGraphProperties gr ⦄ -> ⦃ Eq a ⦄ -> ⦃ Eq b ⦄ -> (grab : gr a b) -> (nfilter (const true) grab) ≡ grab
propNfilterTrue = {!   !}
-- | Tests `labnfilter` with a function accepting all nodes.
propLabfilterTrue : ⦃ _ : DynGraphProperties gr ⦄ -> ⦃ Eq a ⦄ -> ⦃ Eq b ⦄ -> (grab : gr a b) -> (labfilter (const true) grab) ≡ grab
propLabfilterTrue = {!   !}

-- -----------------------------------------------------------------------------
-- Miscellaneous

-- | Ensure the edge projection functions work as intended.
propEdgeProjections : ⦃ Eq b ⦄ -> (le : LEdge b) -> 
    toLEdge (toEdge le) (edgeLabel le) ≡ le
propEdgeProjections le@(v , w , l) = 
    begin
        toLEdge (toEdge le) (edgeLabel le)
    =⟨⟩
        toLEdge (v , w) l
    =⟨⟩
        le
    ∎
