module Proofs.InductiveGraphPropertiesDefault where

open import Proofs.Proof
open import Proofs.ListProperties

open import Haskell.Prelude
open import Haskell.Prim
open import Prelude
open import Haskell.Data.List
open import Haskell.Data.Maybe

open import InductiveGraph

open Graph ⦃ ... ⦄

----------------------------------------------------------------------
-- Default QuickCheck properties

-- | Ensure that the default definition of 'noNodes' is equal to the
--   the number of nodes in labNodes
propNodeCountDefault : ⦃ _ : Graph gr ⦄ -> (grab : gr a b) -> 
    noNodesDefault grab ≡ length (nodes grab)
propNodeCountDefault g =
    begin
        noNodesDefault g
    =⟨⟩
        length (labNodes g)
    =⟨ mapGivesSameLength (labNodes g) ⟩
        length (map fst (labNodes g))
    =⟨⟩
        length (nodes g)
    ∎

-- | Ensure that the definition of 'nodeRange' matches the default
--   implementation.
propNodeRangeDefault : ⦃ _ : Graph gr ⦄ -> (grab : gr a b) -> ⦃ nonEmptyInstance : IsFalse (isEmpty grab) ⦄ -> 
    nodeRangeDefault grab ≡ (minimum (nodes grab) ⦃ getNonEmptyNodes grab nonEmptyInstance ⦄ , maximum (nodes grab) ⦃ getNonEmptyNodes grab nonEmptyInstance ⦄)
propNodeRangeDefault g ⦃ nonEmptyInstance ⦄ = refl

