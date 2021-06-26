module CommonSubset where
{-# FOREIGN AGDA2HS {-# LANGUAGE LambdaCase #-} #-}

open import Agda.Builtin.List public
open import Agda.Builtin.Nat

open import Haskell.Prim
open import Haskell.Prim.Tuple
open import Haskell.Prim.Bool
open import Haskell.Prim.Int
open import Haskell.Prim.Maybe
open import Haskell.Prim.List
open import Haskell.Prim.Ord

justANumber : Nat
justANumber = 1
{-# COMPILE AGDA2HS justANumber #-}

append : {a : Set} -> a -> List a -> List a
append x xs = x ∷ []
{-# COMPILE AGDA2HS append #-}

append' : {A : Set} -> A -> List A -> List A
append' x xs = x ∷ []
-- {-# COMPILE AGDA2HS append' #-} Does not compile correctly, capitalized type generalizations are invalid Haskell

pow : Nat -> Nat -> Nat
pow b 0 = 0
pow b (suc x) = b + pow b x
-- {-# COMPILE AGDA2HS pow #-} Does not compile correctly

-- Not defined in agda but is defined in haskell
length : {a : Set} -> List a -> Nat
length [] = 0
length (x ∷ xs) = 1 + length xs

safeHead : {a : Set} -> List a -> Maybe a
safeHead [] = Nothing
safeHead (x ∷ xs) = Just x
{-# COMPILE AGDA2HS safeHead #-}

boolToNat : Bool -> Nat
boolToNat b = if b then 1 else 0
{-# COMPILE AGDA2HS boolToNat #-}

whereTest : Nat
whereTest = test
    where
        test : Nat  -- Function type is a must
        test = 1
{-# COMPILE AGDA2HS whereTest #-}

whereTestType : {a : Set} -> List a -> Maybe a
whereTestType {a} xs = helper xs
    where
        helper : List a -> Maybe a
        helper [] = Nothing
        helper (x ∷ []) = Just x
        helper ( x ∷ _ ) = Nothing
{-# COMPILE AGDA2HS whereTestType #-}

whereTestType' : {a : Set} -> List a -> Maybe a
whereTestType' {a} xs = helper xs
    where
        helper : List a -> Maybe a
        helper [] = Nothing
        helper (x ∷ []) = Just x
        helper ( x ∷ ys ) = helper ys
{-# COMPILE AGDA2HS whereTestType' #-}

caseTest : Bool -> Nat
caseTest b = case b of
    λ { (true) → 1
      ; (false) → 0}
{-# COMPILE AGDA2HS caseTest #-}



caseWhereTest : Bool -> Nat
caseWhereTest b = case b of
    λ { (true) → one       
      ; (false) → z}
    where
        one : Nat
        one = 1
        z : Nat
        z = 0
-- {-# COMPILE AGDA2HS caseWhereTest #-} Does not compile, "Pattern matching lambdas must take a single argument"

whereCaseTest : Bool -> Nat
whereCaseTest b = test
    where
        test = case b of
            λ { (true) → 1       
            ; (false) → 0}
{-# COMPILE AGDA2HS whereCaseTest #-}

recordLambdaTest : (Bool -> Nat)
recordLambdaTest = λ { true -> 1 ; false -> 2 }
{-# COMPILE AGDA2HS recordLambdaTest #-}

parenthesisTest : Nat
parenthesisTest = 10 - (2 + 3)
{-# COMPILE AGDA2HS parenthesisTest #-}

parenthesisTest' : Nat
parenthesisTest' = _-_ 10 $ 2 + 3
{-# COMPILE AGDA2HS parenthesisTest' #-}

parenthesisTest'' : Nat
parenthesisTest'' = sub 10 (2 + 3)
    where
        sub : Nat -> Nat -> Nat
        sub = _-_
{-# COMPILE AGDA2HS parenthesisTest'' #-}

parenthesisTest''' : Nat
parenthesisTest''' = _-_ 10 (2 + 3)
{-# COMPILE AGDA2HS parenthesisTest''' #-}


-- Tests if @ works correctly
insertByTest        : { a : Set } -> (a -> a -> Ordering) -> a -> List a -> List a
insertByTest _ x [] = x ∷ []
insertByTest cmp x ys@(y ∷ ys')
    = case cmp x y of
        λ   { GT -> y ∷ insertByTest cmp x ys'
            ; _  -> x ∷ ys}
{-# COMPILE AGDA2HS insertByTest #-}

shadowTest : { a : Set } -> List a -> Maybe a
shadowTest {a} xs = shadow xs
    where
        shadow : List a -> Maybe a
        shadow [] = Nothing
        shadow (x ∷ xs) = Just x
{-# COMPILE AGDA2HS shadowTest #-}

-- Types
Node = Int
{-# COMPILE AGDA2HS Node #-}

-- | Labeled node
LNode : Set -> Set
LNode a = (Node × a)
{-# COMPILE AGDA2HS LNode #-}

data Node' : Set where
  node   : Int -> Node'
-- {-# COMPILE AGDA2HS Node' #-} Doesn't compile correctly

ifElseTest : Bool
ifElseTest = if true then false
    else (
        if true then false else true
    )
{-# COMPILE AGDA2HS ifElseTest #-}

wherewhere : Bool
wherewhere = where1
    where
        where1 = where2
            where
                where2 = true
{-# COMPILE AGDA2HS wherewhere #-}

splitDefTest : Bool -> List (Bool)

someFunction : Bool
someFunction = true

splitDefTest n = withMatch n
    where
        withMatch : Bool -> List (Bool)
        withMatch v = v ∷ v ∷ []
-- {-# COMPILE AGDA2HS splitDefTest #-} -- Doesn't compile because the definition and implementation are split