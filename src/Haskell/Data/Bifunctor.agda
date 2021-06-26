module Haskell.Data.Bifunctor where

open import Haskell.Prim
open import Haskell.Prelude

variable
    p : Set -> Set -> Set

-- | A bifunctor is a type constructor that takes
-- two type arguments and is a functor in /both/ arguments. That
-- is, unlike with 'Functor', a type constructor such as 'Either'
-- does not need to be partially applied for a 'Bifunctor'
-- instance, and the methods in this class permit mapping
-- functions over the 'Left' value or the 'Right' value,
-- or both at the same time.
--
-- Formally, the class 'Bifunctor' represents a bifunctor
-- from @Hask@ -> @Hask@.
--
-- Intuitively it is a bifunctor where both the first and second
-- arguments are covariant.
--
-- You can define a 'Bifunctor' by either defining 'bimap' or by
-- defining both 'first' and 'second'.
--
-- If you supply 'bimap', you should ensure that:
--
-- @'bimap' 'id' 'id' ≡ 'id'@
--
-- If you supply 'first' and 'second', ensure:
--
-- @
-- 'first' 'id' ≡ 'id'
-- 'second' 'id' ≡ 'id'
-- @
--
-- If you supply both, you should also ensure:
--
-- @'bimap' f g ≡ 'first' f '.' 'second' g@
--
-- These ensure by parametricity:
--
-- @
-- 'bimap'  (f '.' g) (h '.' i) ≡ 'bimap' f h '.' 'bimap' g i
-- 'first'  (f '.' g) ≡ 'first'  f '.' 'first'  g
-- 'second' (f '.' g) ≡ 'second' f '.' 'second' g
-- @
--
-- @since 4.8.0.0
record Bifunctor (p : Set -> Set -> Set) : Set₁ where
    field
        bimap : (a -> b) -> (c -> d) -> p a c -> p b d

        -- | Map over both arguments at the same time.
        --
        -- @'bimap' f g ≡ 'first' f '.' 'second' g@
        --
        -- ==== __Examples__
        -- >>> bimap toUpper (+1) ('j', 3)
        -- ('J',4)
        --
        -- >>> bimap toUpper (+1) (Left 'j')
        -- Left 'J'
        --
        -- >>> bimap toUpper (+1) (Right 3)
        -- -- Right 4
        -- bimap : (a -> b) -> (c -> d) -> p a c -> p b d
        -- bimap f g = first f ∘ second g


        -- | Map covariantly over the first argument.
        --
        -- @'first' f ≡ 'bimap' f 'id'@
        --
        -- ==== __Examples__
        -- >>> first toUpper ('j', 3)
        -- ('J',3)
        --
        -- >>> first toUpper (Left 'j')
        -- Left 'J'
        first : (a -> b) -> p a c -> p b c

        -- | Map covariantly over the second argument.
        --
        -- @'second' ≡ 'bimap' 'id'@
        --
        -- ==== __Examples__
        -- >>> second (+1) ('j', 3)
        -- ('j',4)
        --
        -- >>> second (+1) (Right 3)
        -- Right 4
        second : (b -> c) -> p a b -> p a c

open Bifunctor ⦃ ... ⦄

firstDefault : ⦃ Bifunctor p ⦄ -> (a -> b) -> p a c -> p b c
firstDefault f = bimap f id

secondDefault : ⦃ Bifunctor p ⦄ -> (b -> c) -> p a b -> p a c
secondDefault = bimap id

-- | @since 4.8.0.0
instance
    {-# TERMINATING #-}
    iBifunctor× : Bifunctor _×_
    iBifunctor× .bimap f g (a , b) = (f a , g b)
    iBifunctor× .first = firstDefault
    iBifunctor× .second = secondDefault

-- | @since 4.8.0.0
instance 
    {-# TERMINATING #-}
    iBifunctor×× : {x1 : Set} -> Bifunctor ((_×_×_) x1)
    iBifunctor×× .bimap f g (x1 , a , b) = (x1 , f a , g b)
    iBifunctor×× .first = firstDefault
    iBifunctor×× .second = secondDefault