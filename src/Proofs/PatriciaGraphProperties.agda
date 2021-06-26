-----------------------------------------
-- Module that implements the Graph
-- properties of the PatriciaTree
-----------------------------------------
module Proofs.PatriciaGraphProperties where

open import InductiveGraph
open import InductiveGraphProperties
open import PatriciaTree
open import PatriciaGraph

open import Haskell.Prim
open import Haskell.Prelude renaming (error to error')
open import Haskell.Data.List
open import Haskell.Data.Maybe
open import Haskell.Data.Tuple
open import Haskell.Data.Bifunctor

open import IntMap hiding (foldlWithKey')
open import IntMap as IM hiding (foldlWithKey')

open import Proofs.Proof
open import Proofs.InductiveGraphPropertiesDefault
open import Proofs.ListProperties
open import Proofs.IntMapProperties


open Graph ⦃ ... ⦄
open GraphProperties ⦃ ... ⦄
open DynGraph ⦃ ... ⦄
open DynGraphProperties ⦃ ... ⦄


propInsNodesSimpleMoveGr : (lns : List (Key × a)) -> (intMap : GraphRep a b) -> labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns (Gr intMap)) ≡ labNodes (Gr (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns intMap))
propInsNodesSimpleMoveGr [] intMap@(Map ms) = refl
propInsNodesSimpleMoveGr (ln@(n , l) ∷ lns) intMap@(Map ms) = 
  begin
    labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple (ln ∷ lns) (Gr (Map ms)))
  =⟨⟩
    labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms))))
  =⟨ propInsNodesSimpleMoveGr lns (Map ((n , (Map [] , l , Map [])) ∷ ms)) ⟩
    labNodes (Gr (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns (Map ((n , (Map [] , l , Map [])) ∷ ms))))
  =⟨⟩
    labNodes (Gr (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' (ln ∷ lns) (Map ms)))
  ∎


instance
    iGraphPropertiesGr : GraphProperties PatriciaGr
    iDynGraphPropertiesGr : DynGraphProperties PatriciaGr


instance
  ---------------------------------
  -- Graph Properties
  ---------------------------------
  iGraphPropertiesGr .super = iGraphPatriciaGr

  iGraphPropertiesGr .propNodeCount = propNodeCountDefault

  iGraphPropertiesGr .propNodeRange = propNodeRangeDefault

  iGraphPropertiesGr .propMkGraphNodes = {!   !}
  iGraphPropertiesGr .propMkGraphEdges = {!   !}
  iGraphPropertiesGr .propMatchNodeRemoved = {!   !}
  iGraphPropertiesGr .propMatchEdgesRemoved = {!   !}
  iGraphPropertiesGr .propMatchAny = {!   !}
  iGraphPropertiesGr .propNewNodesReallyNew = {!   !}
  iGraphPropertiesGr .propUfoldAllNodees = {!   !}
  iGraphPropertiesGr .propAllNodesGelem = {!   !}
  iGraphPropertiesGr .propGelemInNodes = {!   !}
  iGraphPropertiesGr .propHasNeighborAdj = {!   !}
  iGraphPropertiesGr .propHasLEdge = {!   !}

instance
  ---------------------------------
  -- DynamicGraph Properties
  ---------------------------------
  iDynGraphPropertiesGr .super = iDynGraphPatriciaGr

  iDynGraphPropertiesGr .propMerge = {!   !}

  iDynGraphPropertiesGr .propInsNode ln@(n , l) (Gr (Map ms)) =
    begin
      equalLists (labNodes (insNode ln (Gr (Map ms)))) (ln ∷ (labNodes (Gr (Map ms))))
    =⟨⟩
      equalLists (labNodes (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms)))) (ln ∷ (labNodes (Gr (Map ms))))
    =⟨⟩
      equalLists (ln ∷ labNodes (Gr (Map ms))) (ln ∷ (labNodes (Gr (Map ms))))
    =⟨ propEqualLists (ln ∷ labNodes (Gr (Map ms))) ⟩
      true
    ∎

  -- propInsNodes' : ⦃ _ : Eq a ⦄ -> (lns : List (LNode a)) -> (grab : gr a b) -> equalLists (labNodes (insNodes lns grab)) (lns ++ (labNodes grab)) ≡ true
  iDynGraphPropertiesGr .propInsNodes' [] g@(Gr (Map ms)) = 
    begin
      equalLists (labNodes (insNodes [] g)) ([] ++ (labNodes g))
    =⟨⟩
      equalLists (labNodes g) (labNodes g)
    =⟨ propEqualLists (labNodes g) ⟩
      true
    ∎
  -- insNodes vs g = foldl' (flip insNode) g vs
  iDynGraphPropertiesGr .propInsNodes' (ln@(n , l) ∷ lns) g@(Gr (Map ms)) =
    begin
      equalLists (labNodes (insNodes (ln ∷ lns) g)) (ln ∷ lns ++ labNodes g)
    =⟨⟩
      equalLists (labNodes (foldl' (flip insNode) g (ln ∷ lns))) (ln ∷ lns ++ labNodes g)
    =⟨ cong (λ x -> equalLists (labNodes x) (ln ∷ lns ++ labNodes g)) (sym (propFodlEquivFodl' (flip insNode) g (ln ∷ lns))) ⟩
      equalLists (labNodes (foldl (flip insNode) g (ln ∷ lns))) (ln ∷ lns ++ labNodes g)
    =⟨⟩
      equalLists (labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode (ln ∷ lns) g)) (ln ∷ lns ++ labNodes g)
    =⟨⟩
      equalLists (labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms ))))) (ln ∷ lns ++ labNodes g)
    =⟨ cong (λ x -> equalLists (labNodes x) (ln ∷ lns ++ labNodes g)) (propInsNodesInsNodesSimpleEquiv lns (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms )))) ⟩
      equalLists (labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns (Gr (Map ((n , (Map [] , l , Map [])) ∷ ms ))))) (ln ∷ lns ++ labNodes g)
    =⟨ cong (λ x -> equalLists x (ln ∷ lns ++ labNodes g)) (propInsNodesSimpleMoveGr lns (Map ((n , (Map [] , l , Map [])) ∷ ms ))) ⟩
      equalLists (labNodes (Gr (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns (Map ((n , (Map [] , l , Map [])) ∷ ms ))))) (ln ∷ lns ++ labNodes g)
    =⟨⟩
      equalLists (Haskell.Prelude.map patriciaLabNode (IM.toList (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns (Map ((n , (Map [] , l , Map [])) ∷ ms ))))) (ln ∷ lns ++ Haskell.Prelude.map patriciaLabNode (IM.toList (getMap g)))
    =⟨ propEqualListsEquiv₁ (Haskell.Prelude.map patriciaLabNode (IM.toList (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns (Map ((n , (Map [] , l , Map [])) ∷ ms ))))) (ln ∷ lns ++ Haskell.Prelude.map patriciaLabNode (IM.toList (getMap g))) (ln ∷ Haskell.Prelude.map patriciaLabNode (IM.toList (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns (Map ms)))) ⦃ subst IsTrue (sym (propEqualListInsertEqualListMap ln patriciaLabNode lns (Map ms))) itsTrue ⦄ ⟩
      equalLists (ln ∷ Haskell.Prelude.map patriciaLabNode (IM.toList (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns (Map ms)))) (ln ∷ lns ++ Haskell.Prelude.map patriciaLabNode (IM.toList (getMap g)))
    =⟨⟩
      equalLists (ln ∷ labNodes (Gr (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns (Map ms)))) (ln ∷ lns ++ labNodes g)
    =⟨ propEqualListsSameHead ln (labNodes (Gr (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns (Map ms)))) (lns ++ labNodes g) ⟩
      equalLists (labNodes (Gr (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple' lns (Map ms)))) (lns ++ labNodes g)
    =⟨ cong (λ x -> equalLists x (lns ++ labNodes g)) (sym (propInsNodesSimpleMoveGr lns (Map ms ))) ⟩
      equalLists (labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns (Gr (Map ms )))) (lns ++ labNodes g)
    =⟨⟩
      equalLists (labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNodeSimple lns g)) (lns ++ labNodes g)
    =⟨ cong (λ x -> equalLists (labNodes x) (lns ++ labNodes g)) (sym (propInsNodesInsNodesSimpleEquiv lns g)) ⟩
      equalLists (labNodes (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ insNode lns g)) (lns ++ labNodes g)
    =⟨⟩
      equalLists (labNodes (foldl (flip insNode) g lns)) (lns ++ labNodes g)
    =⟨ cong (λ x -> equalLists (labNodes x) (lns ++ labNodes g)) (propFodlEquivFodl' (flip insNode) g lns) ⟩
      equalLists (labNodes (foldl' (flip insNode) g lns)) (lns ++ labNodes g)
    =⟨⟩
      equalLists (labNodes (insNodes lns g)) (lns ++ labNodes g)
    =⟨ propInsNodes' lns g ⟩
      true
    ∎

  iDynGraphPropertiesGr .propInsNodeNoAddedEdges = {!   !}
  iDynGraphPropertiesGr .propInsEdge le g = {!   !}
  iDynGraphPropertiesGr .propDelNode = {!   !}
  iDynGraphPropertiesGr .propDelNodeRemovedEdges = {!   !}
  iDynGraphPropertiesGr .propDelNodes = {!   !}
  iDynGraphPropertiesGr .propDelNodesRemovedEdges = {!   !}
  iDynGraphPropertiesGr .propDelEdge = {!   !}
  iDynGraphPropertiesGr .propDelEdgeGelemNode = {!   !}
  iDynGraphPropertiesGr .propDelLEdge = {!   !}
  iDynGraphPropertiesGr .propDelAllLEdge = {!   !}
  iDynGraphPropertiesGr .propBuildGr = {!   !}
  iDynGraphPropertiesGr .propGfiltermapId = {!   !}
  iDynGraphPropertiesGr .propLabnfilterTrue = {!  !}