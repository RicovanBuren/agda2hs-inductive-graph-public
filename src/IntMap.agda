------------------------------------------------------------------------
-- A watered down version of the Haskell Data.Map library using Int as Key
--
-- Maps from Int to values, based on lists
-- This modules provides a simpler map interface, without a dependency
-- between the key and value types.
------------------------------------------------------------------------


module IntMap where

open import Prelude
open import Haskell.Prim 
open import Haskell.Prelude hiding (null) hiding (toList) hiding (lookup) renaming (map to listMap) renaming (foldr to foldableFoldr)
open import Haskell.Data.List renaming (delete to listDelete) --renaming (foldl' to listFoldl')

{--------------------------------------------------------------------
  Map
--------------------------------------------------------------------}
Key = Int


-- | A Map from keys @k@ to values @a@. 
data IntMap (a : Set) : Set where
    Map : List (Key × a) -> IntMap a

private
  getKey : (Key × a) -> Key
  getKey (k , _) = k

  getValue : (Key × a) -> a
  getValue (_ , v) = v

empty : IntMap a
empty = Map []

null : IntMap a -> Bool
null (Map []) = true
null (Map (_ ∷ _)) = false

size : IntMap a -> Int
size (Map xs) = length xs

insert : Key -> a -> IntMap a -> IntMap a
insert k v (Map xs) = Map ((k , v) ∷ xs)

fromList : List (Key × a) -> IntMap a
fromList xs = Map xs

toList : IntMap a -> List (Key × a)
toList (Map xs) = xs

lookupAndKey : Key -> IntMap a -> Maybe (Key × a)
lookupAndKey k (Map []) = Nothing
lookupAndKey k (Map (xv@(x , v) ∷ xs)) = if k == x then Just xv else lookupAndKey k (Map xs)

lookup : Key -> IntMap a -> Maybe a
lookup k (Map []) = Nothing
lookup k (Map (xv@(x , v) ∷ xs)) = if k == x then Just v else lookup k (Map xs)

delete : Key -> IntMap a -> IntMap a
delete k (Map []) = Map []
delete k (Map (xv@(x , v) ∷ xs)) = if k == x then Map (xs) else Map (xv ∷ toList (delete k (Map xs)))

mapWithKey : (Key -> a -> b) -> IntMap a -> IntMap b
mapWithKey f (Map []) = Map []
mapWithKey f (Map ((x , v) ∷ xs)) = Map ((x , f x v)  ∷ toList (mapWithKey f (Map xs)))

map : (a -> b) -> IntMap a -> IntMap b
map f = mapWithKey (λ _ x -> f x)

private
  keyComp : (Key -> Key -> Bool) -> (Key × a) -> (Key × a) -> (Key × a)
  keyComp comp xv₁@(x₁ , _) xv₂@(x₂ , _) = if comp x₁ x₂ then xv₁ else xv₂

minViewWithKey : IntMap a -> Maybe ((Key × a) × IntMap a)
minViewWithKey {a} (Map []) = Nothing
minViewWithKey {a} m@(Map xs@(_ ∷ _)) = Just (minkv , (delete (getKey minkv) m))
  where
    minkv = foldr1 (keyComp _<=_) xs

maxViewWithKey : IntMap a -> Maybe ((Key × a) × IntMap a)
maxViewWithKey {a} (Map []) = Nothing
maxViewWithKey {a} m@(Map xs@(_ ∷ _)) = Just (maxkv , (delete (getKey maxkv) m))
  where
    maxkv = foldr1 (keyComp _>=_) xs

-- | Difference with a combining function.
--
-- > let f al ar = if al == "b" then Just (al ++ ":" ++ ar) else Nothing
-- > differenceWith f (fromList [(5, "a"), (3, "b")]) (fromList [(5, "A"), (3, "B"), (7, "C")])
-- >     == singleton 3 "b:B"
--
-- This function is terminating because it will always be called with next, where the first map is always one constructor less
-- and if the first map is empty, the function terminates.
{-# TERMINATING #-}
differenceWith : (a -> b -> Maybe a) -> IntMap a -> IntMap b -> IntMap a
differenceWith f (Map []) _ = (Map [])
differenceWith f (Map (kv@(k , v) ∷ xs)) m2 = case lookupAndKey k m2 of
                                              λ { Nothing -> Map (kv ∷ (toList next))
                                                ; (Just (k2 , v2)) -> case f v v2 of
                                                    λ { Nothing -> next
                                                      ; (Just fv) -> Map ((k , fv) ∷ (toList next))}
                                                }
  where
    next = differenceWith f (Map xs) m2

-- | Insert with a combining function.
-- @'insertWithKey' f key value mp@ 
-- will insert the pair (key, value) into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert @f key new_value old_value@.
--
-- > let f key new_value old_value = (show key) ++ ":" ++ new_value ++ "|" ++ old_value
-- > insertWithKey f 5 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "5:xxx|a")]
-- > insertWithKey f 7 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a"), (7, "xxx")]
-- > insertWithKey f 5 "xxx" empty                         == singleton 5 "xxx"
insertWithKey : (Key -> a -> a -> a) -> Key -> a -> IntMap a -> IntMap a
insertWithKey f k x m = case lookupAndKey k m of
                        λ { Nothing -> insert k x m
                          ; (Just (_ , vm)) -> insert k (f k x vm) m}

-- right-biased insertion, used by 'union'
-- | /O(min(n,W))/. Insert with a combining function.
-- @'insertWith' f key value mp@ 
-- will insert the pair (key, value) into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert @f new_value old_value@.
--
-- > insertWith (++) 5 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "xxxa")]
-- > insertWith (++) 7 "xxx" (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a"), (7, "xxx")]
-- > insertWith (++) 5 "xxx" empty                         == singleton 5 "xxx"

insertWith : (a -> a -> a) -> Key -> a -> IntMap a -> IntMap a
insertWith f k x t = insertWithKey (λ _ x' y' -> f x' y') k x t     

-- | Update a value at a specific key with the result of the provided function.
-- When the key is not
-- a member of the map, the original map is returned.
--
-- > adjust ("new " ++) 5 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "new a")]
-- > adjust ("new " ++) 7 (fromList [(5,"a"), (3,"b")]) == fromList [(3, "b"), (5, "a")]
-- > adjust ("new " ++) 7 empty                         == empty

adjust : (a -> a) -> Key -> IntMap a -> IntMap a
adjust f k (Map []) = Map []
adjust f k (Map (xv@(x , v) ∷ xs)) =  if k == x then Map ((k , f v) ∷ xs) 
                                      else Map (xv ∷ toList (adjust f k (Map xs)))

foldr : (Key -> a -> b -> b) -> b -> IntMap a -> b
foldr f z (Map []) = z
foldr f z (Map ((k , v) ∷ xs)) = foldr f (f k v z) (Map xs)

foldWithKey : (Key -> a -> b -> b) -> b -> IntMap a -> b
foldWithKey = foldr

-- foldl' is not strict!
-- foldl' : (a -> Key -> b -> a) -> a -> IntMap b -> a
-- foldl' f z (Map []) = z
-- foldl' f z (Map ((k , v) ∷ xs)) = f (foldl' f z (Map xs)) k v

-- foldlWithKey' is not strict!
foldlWithKey' : (a -> Key -> b -> a) -> a -> IntMap b -> a
foldlWithKey' f z (Map []) = z
foldlWithKey' f z (Map ((k , v) ∷ xs)) = f (foldlWithKey' f z (Map xs)) k v

foldlStrict : (a -> b -> a) -> a -> (List b) -> a
foldlStrict = foldl'

-- | Build a map from a list of key\/value pairs with a combining function. See also fromAscListWithKey'.
--
-- > fromListWith (++) [(5,"a"), (5,"b"), (3,"b"), (3,"a"), (5,"a")] == fromList [(3, "ab"), (5, "aba")]
-- > fromListWith (++) [] == empty

fromListWithKey : (Key -> a -> a -> a) -> List (Key × a) -> IntMap a 
fromListWithKey {a} f xs = foldlStrict ins empty xs
  where
    ins : IntMap a -> (Key × a) -> IntMap a
    ins t (k , x) = insertWithKey f k x t

-- | Create a map from a list of key\/value pairs with a combining function. See also 'fromAscListWith'.
--
-- > fromListWith (++) [(5,"a"), (5,"b"), (3,"b"), (3,"a"), (5,"a")] == fromList [(3, "ab"), (5, "aba")]
-- > fromListWith (++) [] == empty

fromListWith : (a -> a -> a) -> List (Key × a) -> IntMap a 
fromListWith f xs = fromListWithKey (λ _ x y -> f x y) xs



{--------------------------------------------------------------------
  Eq 
--------------------------------------------------------------------}
-- This function terminates because both m1 and m2 will become smaller in every iteration
instance
  {-# TERMINATING #-}
  iEqIntMap : ⦃ Eq a ⦄ -> Eq (IntMap a)
  iEqIntMap {a} ._==_ m1 m2 = if size m1 /= size m2 then false
                          else helper m1 m2
    where
      helper : IntMap a -> IntMap a -> Bool
      helper (Map []) (Map []) = true
      helper (Map []) _ = false
      helper (Map (kv1@(k1 , v1) ∷ xs)) m2 = case lookupAndKey k1 m2 of
                                            λ { Nothing -> false
                                              ; (Just kv2) -> if kv1 == kv2
                                                              then helper (Map xs) (delete k1 m2)
                                                              else false
                                              } 

{--------------------------------------------------------------------
  Functor 
--------------------------------------------------------------------}
instance
  iFunctorIntMap : Functor IntMap
  iFunctorIntMap .fmap = map

{--------------------------------------------------------------------
  Ord 
--------------------------------------------------------------------}
instance
  iOrdIntMap : ⦃ Ord a ⦄ -> Ord (IntMap a)
  iOrdIntMap = ordFromCompare (λ m1 m2 -> compare (toList m1) (toList m2) )

