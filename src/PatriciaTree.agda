-- | An implementation of 'Data.Graph.Inductive.Graph.Graph'
--   using big-endian patricia tree (i.e. "Data.IntMap").

module PatriciaTree where
{-# FOREIGN AGDA2HS
  import Data.Graph.Inductive.Graph

  import           Control.Applicative (liftA2)
  import           Data.IntMap         as IntMap
  import           Data.List           (foldl', sort)
  import           Data.Maybe          (fromMaybe)
  import           Data.Tuple          (swap)

  import Data.Bifunctor
#-}


open import InductiveGraph

open import Haskell.Prim
open import Haskell.Prelude
open import Haskell.Data.List
open import Haskell.Data.Maybe
open import Haskell.Data.Tuple
open import Haskell.Data.Bifunctor

open import GHC.Tuple

open import IntMap hiding (foldlWithKey')
open import IntMap as IM hiding (foldlWithKey')

open Bifunctor ⦃ ... ⦄

----------------------------------------------------------------------
-- GRAPH REPRESENTATION
----------------------------------------------------------------------
Context' : Set -> Set -> Set
Context' a b = (IntMap (List b) × a × IntMap (List b))
{-# COMPILE AGDA2HS Context' #-}


GraphRep : Set -> Set -> Set
GraphRep a b = IntMap (Context' a b)
{-# COMPILE AGDA2HS GraphRep #-}

-- newtype Gr a b = Gr (GraphRep a b)
data PatriciaGr (a : Set) (b : Set) : Set where
    Gr : GraphRep a b -> PatriciaGr a b
{-# COMPILE AGDA2HS PatriciaGr #-}

UGr = PatriciaGr (Tuple []) (Tuple [])
{-# COMPILE AGDA2HS UGr #-}

getMap : PatriciaGr a b -> GraphRep a b
getMap (Gr m) = m
{-# COMPILE AGDA2HS getMap #-}

----------------------------------------------------------------------
-- CLASS INSTANCES
----------------------------------------------------------------------

instance
    iEqGr : ⦃ Ord a ⦄ -> ⦃ Ord b ⦄ -> Eq (PatriciaGr a b)
    iEqGr ._==_  (Gr g1) (Gr g2) = fmap sortAdj g1 == fmap sortAdj g2
        where
            sortAdj : ⦃ Ord a ⦄ -> ⦃ Ord b ⦄ -> (IntMap (List a) × b × IntMap (List a)) -> (IntMap (List a) × b × IntMap (List a))
            sortAdj (p , n , s) = (fmap sort p , n , fmap sort s)
{-# COMPILE AGDA2HS iEqGr #-}

----------------------------------------------------------------------
-- UTILITIES to be able to define the Graph instance
----------------------------------------------------------------------
clearSuccHelper : Node -> Context' a b -> List b -> Context' a b
clearSuccHelper v (ps , l , ss) _ = let ss' = IM.delete v ss
                                    in (ps , l , ss')
{-# COMPILE AGDA2HS clearSuccHelper #-}

clearSucc : {a : Set} -> {b : Set} -> GraphRep a b -> Node -> IM.IntMap (List b) -> GraphRep a b
clearSucc g v succs@(Map []) = g
clearSucc g v succs@(Map (s ∷ ss)) = IM.differenceWith (λ grV edgeV -> Just (clearSuccHelper v grV edgeV)) g succs
{-# COMPILE AGDA2HS clearSucc  #-}

clearPredHelper : Node -> Context' a b -> List b -> Context' a b
clearPredHelper v (ps , l , ss) _ = let ps' = IM.delete v ps
                                    in (ps' , l , ss)
{-# COMPILE AGDA2HS clearPredHelper #-}

clearPred : {a : Set} -> {b : Set} -> GraphRep a b -> Node -> IM.IntMap (List b) -> GraphRep a b
clearPred g v preds@(Map []) = g
clearPred g v preds@(Map (s ∷ ss)) = IM.differenceWith (λ grV edgeV -> Just (clearPredHelper v grV edgeV)) g preds
{-# COMPILE AGDA2HS clearPred #-}

-- A version of @++@ where order isn't important, so @xs ++ [x]@
-- becomes @x:xs@.  Used when we have to have a function of type @[a]
-- -> [a] -> [a]@ but one of the lists is just going to be a single
-- element (and it isn't possible to tell which).
addLists : List a -> List a -> List a
addLists (a ∷ []) as  = a ∷ as
addLists as  (a ∷ []) = a ∷ as
addLists xs  ys  = xs ++ ys
{-# COMPILE AGDA2HS addLists #-}

-- We use differenceWith to modify a graph more than bulkThreshold times,
-- and repeated insertWith otherwise.
-- This is not used
bulkThreshold : Int
bulkThreshold = 5
{-# COMPILE AGDA2HS bulkThreshold #-}

foldlWithKey' : (a -> IM.Key -> b -> a) -> a -> IntMap b -> a
foldlWithKey' = IM.foldlWithKey'
{-# COMPILE AGDA2HS foldlWithKey' #-}

combineSuccs : Node -> Context' a b -> List b -> Context' a b
combineSuccs v (ps , l' , ss) l = let ss' = IM.insertWith addLists v l ss
                                  in (ps , l' , ss')
{-# COMPILE AGDA2HS combineSuccs #-}

addSucc : GraphRep a b -> Node -> Int -> IM.IntMap (List b) -> GraphRep a b
addSucc {a} {b} g0 v numAdd (Map []) = g0
addSucc {a} {b} g0 v numAdd (Map (m ∷ ms)) = IM.differenceWith (λ grV edgeV -> Just (combineSuccs v grV edgeV)) g0 (Map (m ∷ ms))
{-# COMPILE AGDA2HS addSucc  #-}

combinePredds : Node -> Context' a b -> List b -> Context' a b
combinePredds v (ps , l' , ss) l =  let ps' = IM.insertWith addLists v l ps
                                    in (ps' , l' , ss)
{-# COMPILE AGDA2HS combinePredds #-}

addPred : GraphRep a b -> Node -> Int -> IM.IntMap (List b) -> GraphRep a b
addPred {a} {b} g0 v _ (Map []) = g0
addPred {a} {b} g0 v _ (Map (m ∷ ms)) = IM.differenceWith (λ grV edgeV -> Just (combinePredds v grV edgeV)) g0 (Map (m ∷ ms))
{-# COMPILE AGDA2HS addPred #-}

toAdj : IntMap (List b) -> Adj b
toAdj = concatMap expand ∘ IM.toList
  where
    expand : (b × List a) -> List (a × b)
    expand (n , ls) = Haskell.Prelude.map (flip _,_ n) ls
{-# COMPILE AGDA2HS toAdj #-}

fromAdj : Adj b -> IntMap (List b)
fromAdj = IM.fromListWith addLists ∘ Haskell.Prelude.map (second (_∷ []) ∘ swap)
{-# COMPILE AGDA2HS fromAdj #-}

data PatriciaFromListCounting (a : Set) : Set where
  FromListCounting : Int -> (IntMap a) -> PatriciaFromListCounting a
  --deriving (Eq, Show, Read)
{-# COMPILE AGDA2HS PatriciaFromListCounting #-}

getFromListCounting : PatriciaFromListCounting a -> (Int × IntMap a)
getFromListCounting (FromListCounting i m) = (i , m)
{-# COMPILE AGDA2HS getFromListCounting #-}

fromListWithKeyCounting : (Int -> a -> a -> a) -> List (Int × a) -> (Int × IntMap a)
fromListWithKeyCounting {a} f = getFromListCounting ∘ Haskell.Data.List.foldl' ins (FromListCounting 0 IM.empty)
  where
    ins : PatriciaFromListCounting a -> (Key × a) -> PatriciaFromListCounting a
    ins (FromListCounting i t) (k , x) = FromListCounting (i + 1) (IM.insertWithKey f k x t)
{-# COMPILE AGDA2HS fromListWithKeyCounting #-}

fromListWithCounting : (a -> a -> a) -> List (Int × a) -> (Int × IntMap a)
fromListWithCounting f = fromListWithKeyCounting (λ _ x y -> f x y)
{-# COMPILE AGDA2HS fromListWithCounting #-}

fromAdjCounting : { b : Set} -> Adj b -> (Int × IntMap (List b))
fromAdjCounting = fromListWithCounting addLists ∘ Haskell.Prelude.map (second (_∷ []) ∘ swap)
{-# COMPILE AGDA2HS fromAdjCounting #-}

matchGrLookUp' : Node -> GraphRep a b -> Maybe (Context' a b) -> Decomp GraphRep a b
matchGrLookUp' n g Nothing = (Nothing , g)
matchGrLookUp' n g (Just (p , label , s)) = let g1 = IM.delete n g
                                                p' = IM.delete n p
                                                s' = IM.delete n s
                                                g2 = clearPred g1 n s'
                                                g3 = clearSucc g2 n p'
                                            in (Just (_,_,_,_ (toAdj p') n label (toAdj s)) , g3)
{-# COMPILE AGDA2HS matchGrLookUp'   #-}

matchGrLookUp : Node -> GraphRep a b -> Maybe (Context' a b) -> Decomp PatriciaGr a b
matchGrLookUp n g cxt = second (λ x -> Gr x) (matchGrLookUp' n g cxt)
{-# COMPILE AGDA2HS matchGrLookUp #-}

matchGr : {a : Set} -> {b : Set} -> Node -> PatriciaGr a b -> Decomp PatriciaGr a b
matchGr node (Gr g) = matchGrLookUp node g (IM.lookup node g)
{-# COMPILE AGDA2HS matchGr #-}

patriciaLabNode : {a : Set} -> {b : Set} -> (Node × (Context' a b)) -> LNode a
patriciaLabNode (n , (_ , l , _)) = (n , l)
{-# COMPILE AGDA2HS patriciaLabNode #-}

patriciaLabNodes : {a : Set} {b : Set} -> GraphRep a b -> List (LNode a)
patriciaLabNodes g = Haskell.Prelude.map patriciaLabNode (IM.toList g)
{-# COMPILE AGDA2HS patriciaLabNodes #-}

patriciaMerge' : Context a b -> PatriciaGr a b -> GraphRep a b
patriciaMerge' (_,_,_,_ p v l s) (Gr g) = let nppreds = fromAdjCounting p
                                              np = fst nppreds
                                              preds = snd nppreds
                                              nssuccs = fromAdjCounting s
                                              ns = fst nssuccs
                                              succs = snd nssuccs
                                              g1 = IM.insert v (preds , l , succs) g
                                              g2 = addSucc g1 v np preds
                                          in addPred g2 v ns succs
{-# COMPILE AGDA2HS patriciaMerge' #-}

patriciaMerge : Context a b -> PatriciaGr a b -> PatriciaGr a b
patriciaMerge cxt g = Gr (patriciaMerge' cxt g)
{-# COMPILE AGDA2HS patriciaMerge #-}

----------------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------------

toContext : Node -> Context' a b -> Context a b
toContext v (ps , a , ss) = (_,_,_,_ (toAdj ps) v a (toAdj ss))
{-# COMPILE AGDA2HS toContext #-}

fromContext : Context a b -> Context' a b
fromContext (_,_,_,_ ps _ a ss) = (fromAdj ps , a , fromAdj ss)
{-# COMPILE AGDA2HS fromContext #-}

----------------------------------------------------------------------
-- OVERRIDING FUNCTIONS
----------------------------------------------------------------------

-- {-# RULES
--       "insNode/Data.Graph.Inductive.PatriciaTree"  insNode = fastInsNode
--   #-}
fastInsNode : LNode a -> PatriciaGr a b -> PatriciaGr a b
fastInsNode (v , l) (Gr g) = seq g' (Gr g')
  where
    g' = IM.insert v (IM.empty , l , IM.empty) g
{-# COMPILE AGDA2HS fastInsNode #-}

-- {-# RULES
--       "insEdge/Data.Graph.Inductive.PatriciaTree"  insEdge = fastInsEdge
--   #-}
fastInsEdge : LEdge b -> PatriciaGr a b -> PatriciaGr a b
fastInsEdge {b} {a} (v , w , l) (Gr g) = seq g2 (Gr g2)
  where
    addS' : Context' a b -> Context' a b
    addS' (ps , l' , ss) = (ps , l' , IM.insertWith addLists w (l ∷ []) ss)
    addP' : (IntMap (List b) × a × IntMap (List b)) -> (IntMap (List b) × a × IntMap (List b))
    addP' (ps , l' , ss) = (IM.insertWith addLists v (l ∷ []) ps , l' , ss)

    g1 = IM.adjust addS' v g
    g2 = IM.adjust addP' w g1
{-# COMPILE AGDA2HS fastInsEdge #-}

-- {-# RULES
--       "gmap/Data.Graph.Inductive.PatriciaTree"  gmap = fastGMap
--   #-}
fastGMap : (Context a b -> Context c d) -> PatriciaGr a b -> PatriciaGr c d
fastGMap {a} {b} {c} {d} f (Gr g) = Gr (IM.mapWithKey f' g)
  where
    f' : Node -> Context' a b -> Context' c d
    f' = ((fromContext ∘ f) ∘_ ) ∘ toContext
{-# COMPILE AGDA2HS fastGMap #-}

-- {-# RULES
--       "nmap/Data.Graph.Inductive.PatriciaTree"  nmap = fastNMap
--   #-}
fastNMap : (a -> c) -> PatriciaGr a b -> PatriciaGr c b
fastNMap {a} {c} {b} f (Gr g) = Gr (IM.map f' g)
  where
    f' : Context' a b -> Context' c b
    f' (ps , a , ss) = (ps , f a , ss)
{-# COMPILE AGDA2HS fastNMap #-}

-- {-# RULES
--       "emap/Data.Graph.Inductive.PatriciaTree"  emap = fastEMap
--   #-}
fastEMap : (b -> c) -> PatriciaGr a b -> PatriciaGr a c
fastEMap {b} {c} {a} f (Gr g) = Gr (IM.map f' g)
  where
    f' : Context' a b -> Context' a c
    f' (ps , a , ss) = (IM.map (Haskell.Prelude.map f) ps , a , IM.map (Haskell.Prelude.map f) ss)
{-# COMPILE AGDA2HS fastEMap #-}

-- {-# RULES
--       "nemap/Data.Graph.Inductive.PatriciaTree"  nemap = fastNEMap
--   #-}
fastNEMap : (a -> c) -> (b -> d) -> PatriciaGr a b -> PatriciaGr c d
fastNEMap {a} {c} {b} {d} fn fe (Gr g) = Gr (IM.map f' g)
  where
    f' : Context' a b -> Context' c d
    f' (ps , a , ss) = (IM.map (Haskell.Prelude.map fe) ps , fn a , IM.map (Haskell.Prelude.map fe) ss)
{-# COMPILE AGDA2HS fastNEMap #-}

instance
    iBifunctorPatriciaGr : Bifunctor PatriciaGr
    iBifunctorPatriciaGr .bimap = fastNEMap
    iBifunctorPatriciaGr .first = fastNMap
    iBifunctorPatriciaGr .second = fastEMap
{-# COMPILE AGDA2HS iBifunctorPatriciaGr #-}



