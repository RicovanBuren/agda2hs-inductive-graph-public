module Proofs.IntMapProperties where

open import IntMap as IM

open import Haskell.Prim
open import Haskell.Prelude
open import Haskell.Data.Maybe
open import Proofs.Proof
open import Proofs.GeneralProperties
open import Proofs.ListProperties

postulate
    -- | Inserting and deleting the same key does not change the keys contained in the IntMap.
    propDeleteInsertSame : (lk : Key) -> (ik : Key) -> (v : a) -> (intMap : IntMap a) -> IM.lookup lk (IM.insert ik v (IM.delete ik intMap)) ≡ IM.lookup lk intMap

    -- | Deleting a key from the IntMap that is not contained in the IntMap produces an equivalent IntMap.
    propDeleteNotElemEquivInit : (dk : Key) -> (intMap : IntMap a) -> ⦃ IsFalse (isJust (IM.lookup dk intMap)) ⦄ -> IM.delete dk intMap ≡ intMap

    -- | If the lookup key is contained in the IntMap then the lookup key should be equivalent to the deleted key (dk) or be contained in the IntMap even if dk is deleted.
    propElemWithDelete : (lk : Key) -> (dk : Key) -> (intMap : IntMap a) -> ⦃ IsTrue (isJust (IM.lookup lk intMap)) ⦄ -> (lk == dk || isJust (IM.lookup lk (IM.delete dk intMap))) ≡ true

    -- | Looking up a key in a map where a new key is inserted should be equivalent to checking if the key is equivalent to the inserted key or is contained in the IntMap without inserting the key.
    propLookUpSplit : (lk : Key) -> (ik : Key) -> (v : a) -> (intMap : IntMap a) -> isJust (IM.lookup lk (IM.insert ik v intMap)) ≡ (lk == ik || isJust (IM.lookup lk intMap))

    -- | Calling differenceWith with a function that always returns a Just should not change the keys.
    propLookUpDifferenceWithJust : (lk : Key) -> (f : a -> b -> a) -> (intMap₁ : IntMap a) -> (intMap₂ : IntMap b) -> isJust (IM.lookup lk (differenceWith (λ v₁ v₂ -> Just (f v₁ v₂)) intMap₁ intMap₂)) ≡ isJust (IM.lookup lk intMap₁)

    -- | Calling differenceWith twice with functions that always returns a Just should not change the keys.
    propLookUpDifferenceWithJustTwice : (lk : Key) -> (f₁ : a -> b -> a) -> (f₂ : a -> c -> a) -> (intMap₁ : IntMap a) -> (intMap₂ : IntMap b) -> (intMap₃ : IntMap c) -> isJust (IM.lookup lk (differenceWith (λ v₁ v₂ → Just (f₁ v₁ v₂) ) (differenceWith (λ v₁ v₂ → Just (f₂ v₁ v₂)) intMap₁ intMap₃) intMap₂)) ≡ isJust (IM.lookup lk intMap₁)

    -- | Inserting a key with a value and checking if a key (lk) is contained is the same as checking if lk is an element of the list of keys with the added key prepended. getting al the keys and prepending the added key should be equivalent.
    --   In this implementation of IntMap key an value pairs are always prepended to the existing map.
    propElemInsertElemMap : {b : Set} -> (lk : Key) -> (k : Key) -> (l : a) -> (lns : List (Key × a)) -> elem ⦃ iFoldableList ⦄ lk (Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ (λ kv m -> IM.insert (fst kv) (Map {b} [] , (snd kv) , Map {b} []) m) lns) (Map ((k , (Map [] , l , Map [])) ∷ []))))) ≡ elem ⦃ iFoldableList ⦄ lk (k ∷ Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ (λ kv m -> IM.insert (fst kv) (Map {b} [] , (snd kv) , Map {b} []) m) lns) (Map []))))

    -- | Just like the propElemInsertElemMap the IntMap should not care about the order so added key value pairs can be prepended to the labeled keys list.
    propEqualListInsertEqualListMap : ⦃ _ : Eq a ⦄ -> {b : Set} -> (kl : Key × a) -> (mapf : ((Key × (IntMap b × a × IntMap b)) -> (Key × a))) -> (lns : List (Key × a)) -> (intMap : IntMap (IntMap b × a × IntMap b)) -> equalLists (Haskell.Prelude.map mapf (IM.toList (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ (λ kv m -> IM.insert (fst kv) (Map {b} [] , (snd kv) , Map {b} []) m) lns (Map (((fst kl) , (Map [] , (snd kl) , Map [])) ∷ (IM.toList intMap)))))) (kl ∷ Haskell.Prelude.map mapf (IM.toList (foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ (λ kv m -> IM.insert (fst kv) (Map {b} [] , (snd kv) , Map {b} []) m) lns intMap))) ≡ true

    -- | Checking if a key is an element of the list of keys should be equivalent to checking if the key is contained in the IntMap.
    propElemEquivLookUp : (lk : Key) -> (lns : List (Key × a)) -> (intMap : IntMap (IntMap b × a × IntMap b)) -> elem lk (Haskell.Prelude.map fst (IM.toList ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ (λ kv m -> IM.insert (fst kv) (Map [] , (snd kv) , Map []) m) lns) intMap))) ≡ isJust (IM.lookup lk ((foldMap ⦃ iFoldableList ⦄ ⦃ MonoidEndoᵒᵖ ⦄ (λ kv m -> IM.insert (fst kv) (Map [] , (snd kv) , Map []) m) lns) intMap))