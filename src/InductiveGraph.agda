-- https://hackage.haskell.org/package/fgl-5.7.0.3/docs/Data-Graph-Inductive-Graph.html
-- {-# OPTIONS --allow-unsolved-metas #-}
module InductiveGraph where
{-# FOREIGN AGDA2HS {-# LANGUAGE LambdaCase #-} #-}
{-# FOREIGN AGDA2HS
import           Control.Arrow (first)
import           Data.Function (on)
import           qualified Data.IntSet   as IntSet
import           Data.List     (delete, foldl', groupBy, sort, sortBy, (\\))
import           Data.Maybe    (fromMaybe, isJust, fromJust)

-- Used to create lists, since the [l..r] syntactic sugar is not part of agda
createList :: Int -> Int -> [Int]
createList l r = [l..r]
#-}

-- import           Control.Arrow (first)
-- import           Data.Function (on)
-- import qualified Data.IntSet   as IntSet

open import Haskell.Data.List
open import Haskell.Data.Maybe
open import Haskell.Data.Function
-- open import Haskell.Data.IntSet

open import GHC.Tuple

open import Proofs.Proof
open import Proofs.ListProperties
open import Proofs.GeneralProperties

open import Prelude
open import Haskell.Prelude hiding (suc) renaming (error to error')
open import Haskell.Prim
open import Haskell.Prim.Tuple


variable
  gr : Set -> Set -> Set

postulate
  -- | The implicit argument ensures that an a can actually be constructed
  error : String -> {x : a} -> a

-- | Unlabeled node
Node = Int
{-# COMPILE AGDA2HS Node #-}

-- | Labeled node
LNode : Set -> Set
LNode a = (Node × a)
{-# COMPILE AGDA2HS LNode #-}

-- | Quasi-unlabeled node
UNode = LNode (Tuple [])
{-# COMPILE AGDA2HS UNode #-}

-- | Unlabeled edge
Edge = (Node × Node)
{-# COMPILE AGDA2HS Edge #-}
-- | Labeled edge
LEdge : Set -> Set
LEdge b = (Node × Node × b)
{-# COMPILE AGDA2HS LEdge #-}
-- | Quasi-unlabeled edge
UEdge = LEdge (Tuple [])
{-# COMPILE AGDA2HS UEdge #-}

-- | Unlabeled path
Path = List Node
{-# COMPILE AGDA2HS Path #-}

-- | Labeled path
data LPath (a : Set) : Set where
    LP : List (LNode a) -> LPath a
{-# COMPILE AGDA2HS LPath #-}

-- instance (Show a) => Show (LPath a) where
--   show (LP xs) = show xs
-- instance
--   iShowLPath : ⦃ Show a ⦄ → Show (LPath a)
--   iShowLPath .show (LP x) = show x
 
-- instance (Eq a) => Eq (LPath a)
instance
    iEqLPath : ⦃ Eq a ⦄ → Eq (LPath a)
    iEqLPath ._==_ (LP [])              (LP [])                 = true
    iEqLPath ._==_ (LP (( _ , x) ∷ _ )) (LP (( _ , y) ∷ _ ))    = x == y
    iEqLPath ._==_ (LP _)               (LP _)                  = false   
{-# COMPILE AGDA2HS iEqLPath #-}

-- instance (Ord a) => Ord (LPath a) where
--   compare (LP [])        (LP [])        = EQ
--   compare (LP ((_,x):_)) (LP ((_,y):_)) = compare x y
--   compare _ _ = error "LPath: cannot compare two empty paths"
instance
    iOrdLPath : ⦃ Ord a ⦄ → Ord (LPath a)
    iOrdLPath = ordFromCompare λ where
        (LP [])             (LP [])             -> EQ
        (LP ((_ , x) ∷ _))  (LP ((_ , y) ∷ _))  -> compare x y
        (LP [])             (LP ((_ , _) ∷ _))  -> LT
        (LP ((_ , x) ∷ _))  (LP [])             -> GT
        -- _               _                     -> {!   !} -- error "LPath: cannot compare two empty paths"
-- {-# COMPILE AGDA2HS iOrdLPath #-} -- agda2hs doesn't support pattern match in where clause
{-# FOREIGN AGDA2HS
instance (Ord a) => Ord (LPath a) where
  compare (LP [])        (LP [])        = EQ
  compare (LP ((_,x):_)) (LP ((_,y):_)) = compare x y
  compare _ _ = error "LPath: cannot compare two empty paths"
#-}


-- | Quasi-unlabeled path
UPath = List UNode
{-# COMPILE AGDA2HS UPath #-}

-- | Labeled links to or from a 'Node'.
Adj : Set -> Set
Adj b = List (b × Node)
{-# COMPILE AGDA2HS Adj #-}

-- | Links to the 'Node', the 'Node' itself, a label, links from the 'Node'.
--
--   In other words, this captures all information regarding the
--   specified 'Node' within a graph.
Context : Set -> Set -> Set
Context a b = _×_×_×_ (Adj b) Node a (Adj b)

{-# FOREIGN AGDA2HS
type Context a b = (Adj b , Node, a , Adj b)
#-}
-- {-# COMPILE AGDA2HS Context #-}

MContext : Set -> Set -> Set
MContext a b = Maybe (Context a b)
{-# COMPILE AGDA2HS MContext #-}
-- | 'Graph' decomposition - the context removed from a 'Graph', and the rest of the 'Graph'.
Decomp : (Set -> Set -> Set) -> Set -> Set -> Set
Decomp g a b = (MContext a b × g a b)
{-# COMPILE AGDA2HS Decomp #-}
-- | The same as 'Decomp', only more sure of itself.
GDecomp : (Set -> Set -> Set) -> Set -> Set -> Set
GDecomp g a b = (Context a b × g a b)
{-# COMPILE AGDA2HS GDecomp #-}

-- | Unlabeled context.
UContext = (List Node × Node × List Node)
{-# COMPILE AGDA2HS UContext #-}
-- | Unlabeled decomposition.
UDecomp : Set -> Set
UDecomp g = (Maybe UContext × g)
{-# COMPILE AGDA2HS UDecomp #-}


fst₃ : {b : Set} -> LEdge b -> Node
fst₃ (x , _ , _) = x
{-# COMPILE AGDA2HS fst₃ #-}

snd₃ : {b : Set} -> LEdge b -> Node
snd₃ (_ , x , _) = x
{-# COMPILE AGDA2HS snd₃ #-}

fstContext : Context a b -> Adj b
fstContext (_,_,_,_ x _ _ _) = x
{-# COMPILE AGDA2HS fstContext #-}

sndContext : Context a b -> Node
sndContext (_,_,_,_ _ x _ _) = x
{-# COMPILE AGDA2HS sndContext #-}

thirdContext : Context a b -> a
thirdContext (_,_,_,_ _ _ x _ ) = x
{-# COMPILE AGDA2HS thirdContext #-}

fouthContext : Context a b -> Adj b
fouthContext (_,_,_,_ _ _ _ x) = x
{-# COMPILE AGDA2HS fouthContext #-}

-- | Add a label to an edge.
toLEdge : Edge -> b -> LEdge b
toLEdge (v , w) l = (v , w , l)
{-# COMPILE AGDA2HS toLEdge #-}

labUNodes : List Node -> List UNode
labUNodes = map (flip _,_ [])
{-# COMPILE AGDA2HS labUNodes #-}

labUEdges : List Edge -> List UEdge
labUEdges = map (λ e -> toLEdge e [])
{-# COMPILE AGDA2HS labUEdges #-}

nodeInLNodeList : Node -> List (LNode a) -> Bool
nodeInLNodeList _ [] = false
nodeInLNodeList v (x ∷ xs) = elem v (map fst (x ∷ xs))

nodeInNodeList : Node -> List Node -> Bool
nodeInNodeList _ [] = false
nodeInNodeList v (x ∷ xs) = nodeInLNodeList v (labUNodes (x ∷ xs))

record Graph gr : Set₁ where
    -- {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-}
    field
        -- | An empty 'Graph'.
        empty : gr a b
        -- | True if the given 'Graph' is empty.
        isEmpty : gr a b -> Bool

        -- | Decompose a 'Graph' into the 'MContext' found for the given node and the remaining 'Graph'.
        match : Node -> gr a b -> Decomp gr a b

        -- | Create a 'Graph' from the list of 'LNode's and 'LEdge's.
        --
        --   For graphs that are also instances of 'DynGraph', @mkGraph ns
        --   es@ should be equivalent to @('insEdges' es . 'insNodes' ns)
        --   'empty'@.
        mkGraph : (lns : List (LNode a)) -> (les : List (LEdge b)) -> ⦃ All IsTrue (map (λ le -> nodeInLNodeList (fst₃ le) lns && nodeInLNodeList (snd₃ le) lns ) les ) ⦄ -> gr a b

        -- | A list of all 'LNode's in the 'Graph'.
        labNodes : gr a b -> List (LNode a)

        -- | Decompose a graph into the 'Context' for an arbitrarily-chosen 'Node'
        matchAny : (grab : gr a b) -> ⦃ IsFalse (isEmpty grab) ⦄ -> GDecomp gr a b

        -- | The number of 'Node's in a 'Graph'.
        noNodes : gr a b -> Int

        -- | The minimum and maximum 'Node' in a 'Graph'.
        nodeRange : (grab : gr a b) -> ⦃ IsFalse (isEmpty grab) ⦄ -> (Node × Node)

        -- | A list of all 'LEdge's in the 'Graph'.
        labEdges : gr a b -> List (LEdge b)

        ---------------------------------
        -- Properties
        ---------------------------------

        -- | The property that the graph and the labNodes share the same nodes
        {propGraphAndLabNodesSameNodes} : (n : Node) -> (grab : gr a b) -> isJust (fst (match n grab)) ≡ elem n (map fst (labNodes grab))

        -- | The property that an empty graph has no nodes and a nonempty graph does contain nodes
        {propEmptyGraphIsEmptyLabNodes} : (grab : gr a b) -> isEmpty grab ≡ null (labNodes grab)
-- {-# COMPILE AGDA2HS Graph #-}


{-# FOREIGN AGDA2HS
class Graph gr where
  {-# MINIMAL empty, isEmpty, match, mkGraph, labNodes #-}

  -- | An empty 'Graph'.
  empty     :: gr a b

  -- | True if the given 'Graph' is empty.
  isEmpty   :: gr a b -> Bool

  -- | Decompose a 'Graph' into the 'MContext' found for the given node and the
  -- remaining 'Graph'.
  match     :: Node -> gr a b -> Decomp gr a b

  -- | Create a 'Graph' from the list of 'LNode's and 'LEdge's.
  --
  --   For graphs that are also instances of 'DynGraph', @mkGraph ns
  --   es@ should be equivalent to @('insEdges' es . 'insNodes' ns)
  --   'empty'@.
  mkGraph   :: [LNode a] -> [LEdge b] -> gr a b

  -- | A list of all 'LNode's in the 'Graph'.
  labNodes  :: gr a b -> [LNode a]

  -- | Decompose a graph into the 'Context' for an arbitrarily-chosen 'Node'
  -- and the remaining 'Graph'.
  matchAny  :: gr a b -> GDecomp gr a b
  matchAny = matchAnyDefault

  -- | The number of 'Node's in a 'Graph'.
  noNodes   :: gr a b -> Int
  noNodes = noNodesDefault

  -- | The minimum and maximum 'Node' in a 'Graph'.
  nodeRange :: gr a b -> (Node,Node)
  nodeRange = nodeRangeDefault

  -- | A list of all 'LEdge's in the 'Graph'.
  labEdges  :: gr a b -> [LEdge b]
  labEdges = labEdgesDefault
#-}


open Graph ⦃ ... ⦄


-- | List all 'Node's in the 'Graph'.
nodes : ⦃ Graph gr ⦄ -> {a : Set} -> {b : Set} -> gr a b -> List Node
nodes = map fst ∘ labNodes
{-# COMPILE AGDA2HS nodes #-}

---------------------------------
-- Helper properties
---------------------------------
propEmptyGraphIsEmptyNodes : ⦃ _ : Graph gr ⦄ -> (grab : gr a b) -> 
    isEmpty grab ≡ null (nodes grab)
propEmptyGraphIsEmptyNodes g =
    begin
        isEmpty g
    =⟨ propEmptyGraphIsEmptyLabNodes g ⟩
        null (labNodes g)
    =⟨ propNullMap (labNodes g) ⟩
        null (map fst (labNodes g))
    =⟨⟩
        null ((map fst ∘ labNodes) g)
    =⟨⟩
        null (nodes g)
    ∎

getNonEmptyLabNodes : ⦃ _ : Graph gr ⦄ -> (grab : gr a b) -> IsFalse (isEmpty grab) -> NonEmpty (labNodes grab)
getNonEmptyLabNodes g neg = let isFalseProof = subst IsFalse (propEmptyGraphIsEmptyLabNodes g) neg
                            in nullImpliesNonEmpty (labNodes g) isFalseProof

getNonEmptyNodes : ⦃ _ : Graph gr ⦄ -> (grab : gr a b) -> IsFalse (isEmpty grab) -> NonEmpty (nodes grab)
getNonEmptyNodes g neg =    let isFalseProof = subst IsFalse (propEmptyGraphIsEmptyNodes g) neg
                            in nullImpliesNonEmpty (nodes g) isFalseProof

getJustMatch : ⦃ _ : Graph gr ⦄ -> (n : Node) -> (grab : gr a b) -> IsTrue (elem n (map fst (labNodes grab))) -> IsTrue (isJust (fst (match n grab)))
getJustMatch v g trueMap =  subst IsTrue (sym (propGraphAndLabNodesSameNodes v g)) trueMap
                            
---------------------------------
-- Default implementations
---------------------------------
matchAnyDefault : ⦃ iGraph : Graph gr ⦄ -> (grab : gr a b) ->
  ⦃ IsFalse (isEmpty grab) ⦄ ->
  GDecomp gr a b
matchAnyDefault {gr} {a} {b} g ⦃ nonEmptyInstance ⦄ = withMatch (fst (head (labNodes g) ⦃ getNonEmptyLabNodes g nonEmptyInstance ⦄)) {refl}
  where
    withMatch : (n : Int) -> {eq : (fst (head (labNodes g) ⦃ getNonEmptyLabNodes g nonEmptyInstance ⦄)) ≡ n} -> GDecomp gr a b
    withMatch v {eq} =  let
                          jcg' = match v g
                          maybec = fst jcg'
                          c = fromMaybe (error "Match Exception, Empty Graph" { fromJust maybec ⦃
                                let headProof = headIsContained (labNodes g) ⦃ getNonEmptyLabNodes g nonEmptyInstance ⦄
                                    congFunction = λ x -> elem x (map fst (labNodes g))
                                in getJustMatch v g (subst IsTrue (trans (sym headProof) (cong congFunction eq)) itsTrue) 
                              ⦄ }) maybec
                          g' = snd jcg'
                        in (c , g')
{-# COMPILE AGDA2HS matchAnyDefault #-}

-- | 'True' if the 'Node' is present in the 'Graph'.
gelem : ⦃ Graph gr ⦄ -> {a : Set} -> {b : Set} -> Node -> gr a b -> Bool
gelem v = isJust ∘ fst ∘ match v
{-# COMPILE AGDA2HS gelem #-}

-- | The number of 'Node's in a 'Graph'.
noNodesDefault : ⦃ Graph gr ⦄ -> gr a b -> Int
noNodesDefault = length ∘ labNodes
{-# COMPILE AGDA2HS noNodesDefault #-}

-- | The minimum and maximum 'Node' in a 'Graph'.
nodeRangeDefault : ⦃ iGraph : Graph gr ⦄ -> (grab : gr a b) -> ⦃ IsFalse (isEmpty grab) ⦄ -> (Node × Node)
-- nodeRangeDefault g ⦃ nonEmptyInstance ⦄ = helper (labNodes g) ⦃ getNonEmptyLabNodes g nonEmptyInstance ⦄ 
--   where
--     -- helper : (as : List Node) -> ⦃ NonEmptyGraph as ⦄ -> (Node × Node)
--     helper : (as : List (LNode a)) -> ⦃ NonEmpty as ⦄ -> (Node × Node)
--     helper (x ∷ xs) = (minimum (map fst (x ∷ xs)) ⦃ itsNonEmpty ⦄ , maximum (map fst (x ∷ xs)) ⦃ itsNonEmpty ⦄)
-- nodeRangeDefault g ⦃ nonEmptyInstance ⦄ = (minimum (map fst (labNodes g)) ⦃ nonEmptyListImpliesNonEmptyMap (labNodes g) (getNonEmptyLabNodes g nonEmptyInstance) ⦄ , maximum (map fst (labNodes g)) ⦃ nonEmptyListImpliesNonEmptyMap (labNodes g) (getNonEmptyLabNodes g nonEmptyInstance) ⦄)
nodeRangeDefault g ⦃ nonEmptyInstance ⦄ = (minimum (nodes g) ⦃ getNonEmptyNodes g nonEmptyInstance ⦄ , maximum (nodes g) ⦃ getNonEmptyNodes g nonEmptyInstance ⦄)
{-# COMPILE AGDA2HS nodeRangeDefault #-}

-- | Fold a function over the graph by recursively calling 'match'.
{-# TERMINATING #-}
ufold : ⦃ Graph gr ⦄ -> (Context a b -> c -> c) -> c -> (grab : gr a b) -> c
ufold {gr} {a} {b} {c} f u g = withMatch (isEmpty g) {refl}
  where
    withMatch : (bo : Bool) -> {eq : isEmpty g ≡ bo} -> c
    withMatch true {eq} = u
    withMatch false {eq} =  let c'g' = matchAny g ⦃ subst IsFalse (sym eq) itsFalse ⦄
                                c' = fst c'g'
                                g' = snd c'g'
                            in  f c' (ufold f u g')
{-# COMPILE AGDA2HS ufold #-}

-- | A list of all 'LEdge's in the 'Graph'.
labEdgesDefault : ⦃ Graph gr ⦄ -> gr a b -> List (LEdge b)
labEdgesDefault g = ufold (λ {(_,_,_,_ _ v _ s) -> (map (λ {(l , w) -> (v , w , l)} ) s ++_)}) [] g
{-# COMPILE AGDA2HS labEdgesDefault #-}

-- | Check if the nodes from the edges are in the graph
edgeNodesGelem : ⦃ _ : Graph gr ⦄ -> {b : Set} -> (le : LEdge b) -> (grab : gr a b) -> Bool
edgeNodesGelem (v , w , _) g = gelem v g && gelem w g
{-# COMPILE AGDA2HS edgeNodesGelem #-}

nodeInContext : Node -> Context a b -> Bool
nodeInContext n (_,_,_,_ _ v _ _) = n == v

record DynGraph gr : Set₁ where
    field
        overlap ⦃ super ⦄ : Graph gr
        -- | Merge the 'Context' into the 'DynGraph'.
        --
        --   Context adjacencies should only refer to either a Node already
        --   in a graph or the node in the Context itself (for loops).
        --
        --   Behaviour is undefined if the specified 'Node' already exists
        --   in the graph.
        _&_ : Context a b -> gr a b -> gr a b      

        ---------------------------------
        -- Properties
        ---------------------------------

        -- | Updating a context should not remove nodes
        {propUpdatingContextKeepsNodes} : (cxt : Context a b) -> (nUpdate : Node) -> (nKeep : Node) -> (grab : gr a b) -> ⦃ _ : IsTrue (nodeInContext nUpdate cxt) ⦄ -> ⦃ _ : IsTrue (gelem nKeep grab) ⦄ -> gelem nKeep (cxt & (snd (match nUpdate grab))) ≡ true

-- {-# COMPILE AGDA2HS DynGraph #-}

{-# FOREIGN AGDA2HS
class (Graph gr) => DynGraph gr where
  -- | Merge the 'Context' into the 'DynGraph'.
  --
  --   Context adjacencies should only refer to either a Node already
  --   in a graph or the node in the Context itself (for loops).
  --
  --   Behaviour is undefined if the specified 'Node' already exists
  --   in the graph.
  (&) :: Context a b -> gr a b -> gr a b
#-}

open DynGraph ⦃ ... ⦄

----------------------------------------------------------------------
-- UTILITIES
----------------------------------------------------------------------

-- auxiliary functions used in the implementation of the
-- derived class members
--
_∘∶_ : (c -> d) -> (a -> b -> c) -> a -> b -> d
-- f .: g = \x y->f (g x y)
-- f .: g = (f .) . g
-- (.:) f = ((f .) .)
-- (.:) = (.) (.) (.)
_∘∶_ = _∘_ ∘ _∘_
{-# COMPILE AGDA2HS _∘∶_ #-}

flip2 : (a × b) -> (b × a)
flip2 (x , y) = (y , x)
{-# COMPILE AGDA2HS flip2 #-}

-- projecting on context elements
--
context1l' : Context a b -> Adj b
context1l' (_,_,_,_ p v _ s) = p ++ filter ((_== v) ∘ snd) s
{-# COMPILE AGDA2HS context1l' #-}

context4l' : Context a b -> Adj b
context4l' (_,_,_,_ p v _ s) = s ++ filter ((_== v) ∘ snd) p
{-# COMPILE AGDA2HS context4l' #-}

mcontext : ⦃ Graph gr ⦄ -> gr a b -> Node -> MContext a b
mcontext = fst ∘∶ flip match
{-# COMPILE AGDA2HS mcontext #-}

context1l : ⦃ Graph gr ⦄ -> gr a b -> Node -> Adj b
context1l = maybe [] context1l' ∘∶ mcontext
{-# COMPILE AGDA2HS context1l #-}

context4l : ⦃ Graph gr ⦄ -> gr a b -> Node -> Adj b
context4l = maybe [] context4l' ∘∶ mcontext
{-# COMPILE AGDA2HS context4l #-}

-- | The number of nodes in the graph.  An alias for 'noNodes'.
order : ⦃ Graph gr ⦄ -> gr a b -> Int
order = noNodes
{-# COMPILE AGDA2HS order #-}

-- | The number of edges in the graph.
--
--   Note that this counts every edge found, so if you are
--   representing an unordered graph by having each edge mirrored this
--   will be incorrect.
--
--   If you created an unordered graph by either mirroring every edge
--   (including loops!) or using the @undir@ function in
--   "Data.Graph.Inductive.Basic" then you can safely halve the value
--   returned by this.
size : ⦃ Graph gr ⦄ -> gr a b -> Int
size = length ∘ labEdges
{-# COMPILE AGDA2HS size #-}


-- | Map a function over the graph by recursively calling 'match'.
gmap :  ⦃ DynGraph gr ⦄ -> (Context a b -> Context c d) -> gr a b -> gr c d
gmap f = ufold (λ c -> (f c &_)) empty
{-# COMPILE AGDA2HS gmap #-}
--{-# NOINLINE [0] gmap #-}

-- | Map a function over the 'Node' labels in a graph.
nmap :  ⦃ DynGraph gr ⦄ -> (a -> c) -> gr a b -> gr c b
nmap f = gmap (λ {(_,_,_,_ p v l s) -> (_,_,_,_ p v (f l) s)})
{-# COMPILE AGDA2HS nmap #-}
-- {-# NOINLINE [0] nmap #-}

-- | Map a function over the 'Edge' labels in a graph.
emap : ⦃ DynGraph gr ⦄ -> (b -> c) -> gr a b -> gr a c
emap {gr} {b} {c} {a} f = gmap lambdaFunction
  where
    map1 : (b -> c) -> List (b × d) -> List (c × d)
    map1 g = map (first g)
    lambdaFunction : Context a b -> Context a c
    lambdaFunction (_,_,_,_ p v l s) = (_,_,_,_ (map1 f p) v l (map1 f s))
{-# COMPILE AGDA2HS emap #-}
-- {-# NOINLINE [0] emap #-}

-- | Map functions over both the 'Node' and 'Edge' labels in a graph.
nemap : ⦃ DynGraph gr ⦄ -> (a -> c) -> (b -> d) -> gr a b -> gr c d
nemap {gr} {a} {c} {b} {d} fn fe = gmap lambdaFunction
  where
    fe' = map (first fe)
    lambdaFunction : Context a b -> Context c d
    lambdaFunction (_,_,_,_ p v l s) = (_,_,_,_ (fe' p) v (fn l) (fe' s))
{-# COMPILE AGDA2HS nemap #-}
-- {-# NOINLINE [0] nemap #-}

-- | Drop the label component of an edge.
toEdge : {b : Set} -> LEdge b -> Edge
toEdge (v , w , _) = (v , w)
{-# COMPILE AGDA2HS toEdge #-}

-- | List all 'Edge's in the 'Graph'.
edges : ⦃ Graph gr ⦄ -> gr a b -> List Edge
edges = map toEdge ∘ labEdges
{-# COMPILE AGDA2HS edges #-}

-- | The label in an edge.
edgeLabel : {b : Set} -> LEdge b -> b
edgeLabel (_ , _ , l) = l
{-# COMPILE AGDA2HS edgeLabel #-}

-- | List N available 'Node's, i.e. 'Node's that are not used in the 'Graph'.
newNodes : ⦃ Graph gr ⦄ -> Int -> gr a b -> List Node
newNodes {gr} {a} {b} i g = withMatch (isEmpty g) {refl}
  where
    withMatch : (bo : Bool) -> {eq : isEmpty g ≡ bo} -> List Node
    withMatch true {eq} = createList 0 (i - 1) --[0..i-1] 
    withMatch false {eq} = createList (n + 1) (n + i) --[n+1..n+i]
      where
        n = snd (nodeRange g ⦃ subst IsFalse (sym eq) itsFalse ⦄)
{-# COMPILE AGDA2HS newNodes #-}

-- | Insert a 'LNode' into the 'Graph'.
insNode : ⦃ DynGraph gr ⦄ -> {a : Set} -> LNode a -> gr a b -> gr a b
insNode (v , l) = ((_,_,_,_ [] v l [] ) &_)
{-# COMPILE AGDA2HS insNode #-}
-- {-# NOINLINE [0] insNode #-}

-- | Insert a 'LEdge' into the 'Graph'. Both nodes of the edge must be contained
insEdge : ⦃ iDynGraph : DynGraph gr ⦄ -> (le : LEdge b) -> (grab : gr a b) ->
  ⦃ _ : IsTrue (edgeNodesGelem le grab) ⦄ ->
  gr a b
insEdge {gr} {b} {a} (v , w , l) g ⦃ isContained ⦄ = 
  let
    mcxtg' = match v g
    mcxt = fst mcxtg'
    g' = snd mcxtg'
    prlasu = fromJust mcxt ⦃ subst IsTrue (sym (propIsTrueAndTrueFst (gelem v g) (gelem w g) ⦃ isContained ⦄)) itsTrue ⦄
    pr = fstContext prlasu
    la = thirdContext prlasu
    su = fouthContext prlasu
  in (_,_,_,_ pr v la ((l , w) ∷ su)) & g'

{-# COMPILE AGDA2HS insEdge #-}
-- {-# NOINLINE [0] insEdge #-}

-- | Property that guarantees that inserting an edges does not delete nodes
propInsOtherEdgeKeepsNodes : ⦃ _ : DynGraph gr ⦄ -> (le : LEdge b) -> (leNext : LEdge b) -> (grab : gr a b) -> ⦃ leTrue : IsTrue (edgeNodesGelem le grab) ⦄ -> ⦃ leNextTrue : IsTrue (edgeNodesGelem leNext grab) ⦄ -> edgeNodesGelem leNext grab ≡ edgeNodesGelem leNext (insEdge le grab)
propInsOtherEdgeKeepsNodes {gr} {b} {a} le@(v , w , l) leNext@(vNext , wNext , lNext) g ⦃ isContained ⦄ ⦃ isContainedNext ⦄  =
  begin
    edgeNodesGelem leNext g
  =⟨⟩
    gelem vNext g && gelem wNext g
  =⟨ propIsTrueIsJustTrue (edgeNodesGelem leNext g) ⟩
    true
  =⟨ cong (λ x -> true && x) (sym addingContextKeepsNodesWNext) ⟩
    true && gelem wNext (cxt & g')
  =⟨ cong (λ x -> x && gelem wNext (cxt & g')) (sym addingContextKeepsNodesVNext) ⟩
    gelem vNext (cxt & g') && gelem wNext (cxt & g')
  =⟨⟩
    gelem vNext (insEdge le g) && gelem wNext (insEdge le g)
  =⟨⟩
    edgeNodesGelem leNext (insEdge le g)
  ∎
  where
    mcxtg' = match v g
    mcxt = fst mcxtg'
    prlasu = fromJust mcxt ⦃ subst IsTrue (sym (propIsTrueAndTrueFst (gelem v g) (gelem w g) ⦃ isContained ⦄)) itsTrue ⦄
    pr = fstContext prlasu
    la = thirdContext prlasu
    su = fouthContext prlasu
    cxt : Context a b
    cxt = (_,_,_,_ pr v la ((l , w) ∷ su))
    g' : gr a b
    g' = snd (match v g)
    propEdgeNodeVInCxt : nodeInContext v cxt ≡ true
    propEdgeNodeVInCxt = sameNodeIsEq v
    addingContextKeepsNodesVNext : gelem vNext (cxt & g') ≡ true
    addingContextKeepsNodesVNext = propUpdatingContextKeepsNodes cxt v vNext g ⦃ subst IsTrue (sym (sameNodeIsEq v)) itsTrue ⦄ ⦃ subst IsTrue (sym (propIsTrueAndTrueFst (gelem vNext g) (gelem wNext g) ⦃ isContainedNext ⦄)) itsTrue ⦄
    addingContextKeepsNodesWNext : gelem wNext (cxt & g') ≡ true
    addingContextKeepsNodesWNext = propUpdatingContextKeepsNodes cxt v wNext g ⦃ subst IsTrue (sym (sameNodeIsEq v)) itsTrue ⦄ ⦃ subst IsTrue (sym (propIsTrueAndTrueSnd (gelem vNext g) (gelem wNext g) ⦃ isContainedNext ⦄)) itsTrue ⦄

-- | Remove multiple 'Node's from the 'Graph'.
delNodes : ⦃ Graph gr ⦄ -> List Node -> gr a b -> gr a b
delNodes vs g = foldl' (snd ∘∶ flip match) g vs
{-# COMPILE AGDA2HS delNodes #-}

-- | Remove a 'Node' from the 'Graph'.
delNode : ⦃ Graph gr ⦄ -> Node -> gr a b -> gr a b
delNode v = delNodes (v ∷ [])
{-# COMPILE AGDA2HS delNode #-}

-- | Remove an 'Edge' from the 'Graph'.
--
--   NOTE: in the case of multiple edges, this will delete /all/ such
--   edges from the graph as there is no way to distinguish between
--   them.  If you need to delete only a single such edge, please use
--   'delLEdge'.
delEdge : ⦃ DynGraph gr ⦄ -> Edge -> gr a b -> gr a b
delEdge (v , w) g = case match v g of
                    λ { (Nothing , _) -> g
                      ; (Just (_,_,_,_ p v' l s) , g') -> (_,_,_,_ p v' l (filter (λ section -> not ((snd section) == w)) s )) & g' }
{-# COMPILE AGDA2HS delEdge #-}

delLEdgeBy : ⦃ DynGraph gr ⦄ -> ((b × Node) -> Adj b -> Adj b) -> LEdge b -> gr a b -> gr a b
delLEdgeBy f (v , w , b) g = case match v g of
                                λ { (Nothing , _)          -> g
                                  ; (Just (_,_,_,_ p v' l s) , g') -> (_,_,_,_ p v' l (f (b , w) s)) & g' }
{-# COMPILE AGDA2HS delLEdgeBy #-}

-- | Remove an 'LEdge' from the 'Graph'.
--
--   NOTE: in the case of multiple edges with the same label, this
--   will only delete the /first/ such edge.  To delete all such
--   edges, please use 'delAllLedge'.
delLEdge : ⦃ DynGraph gr ⦄ -> ⦃ Eq b ⦄ -> LEdge b -> gr a b -> gr a b
delLEdge = delLEdgeBy delete
{-# COMPILE AGDA2HS delLEdge #-}

-- | Remove all edges equal to the one specified.
delAllLEdge : ⦃ DynGraph gr ⦄ -> ⦃ Eq b ⦄ -> LEdge b -> gr a b -> gr a b
delAllLEdge = delLEdgeBy (filter ∘ _/=_)
{-# COMPILE AGDA2HS delAllLEdge #-}

-- | Insert multiple 'LNode's into the 'Graph'.
insNodes : ⦃ DynGraph gr ⦄ -> {a : Set} -> List (LNode a) -> gr a b -> gr a b
insNodes vs g = foldl' (flip insNode) g vs
{-# COMPILE AGDA2HS insNodes #-}
--{-# INLINABLE insNodes #-}

-- | Property that guarantees that inserting multiple edges keeps all nodes
propInsEdgeKeepsAllNodes : ⦃ iDynGraph : DynGraph gr ⦄ -> (es : List (LEdge b)) -> (e : LEdge b) -> (grab : gr a b) -> ⦃ _ : All IsTrue (map (λ le -> edgeNodesGelem le grab) es) ⦄ -> ⦃ _ : IsTrue (edgeNodesGelem e grab) ⦄ -> map (λ le → edgeNodesGelem le grab) es ≡ map (λ le -> edgeNodesGelem le (insEdge e grab)) es
propInsEdgeKeepsAllNodes [] insE g = refl
propInsEdgeKeepsAllNodes (e ∷ es) insE g ⦃ allCons ⦃ i = i ⦄ ⦃ is = is ⦄ ⦄ ⦃ insEContained ⦄ =
  begin
    map (λ le → edgeNodesGelem le g) (e ∷ es)
  =⟨⟩
    (edgeNodesGelem e g) ∷ (map (λ le → edgeNodesGelem le g) es)
  =⟨ cong (λ x -> x ∷ (map (λ le → edgeNodesGelem le g) es) ) (propInsOtherEdgeKeepsNodes insE e g ⦃ insEContained ⦄ ⦃ i ⦄) ⟩
    (edgeNodesGelem e (insEdge insE g)) ∷ (map (λ le → edgeNodesGelem le g) es)
  =⟨ cong ((λ x -> (edgeNodesGelem e (insEdge insE g)) ∷ x)) (propInsEdgeKeepsAllNodes es insE g ⦃ is ⦄ ⦃ insEContained ⦄) ⟩
    (edgeNodesGelem e (insEdge insE g)) ∷ (map (λ le -> edgeNodesGelem le (insEdge insE g)) es)
  =⟨⟩
    map (λ le -> edgeNodesGelem le (insEdge insE g)) (e ∷ es)
  ∎

-- | Insert multiple edges into the graph
insEdges : ⦃ iDynGraph : DynGraph gr ⦄ -> (les : List (LEdge b)) -> (grab : gr a b) -> 
  ⦃ _ : All IsTrue (map (λ le -> edgeNodesGelem le grab) les) ⦄ ->
  gr a b
insEdges [] g = g
insEdges {gr} {b} {a} les@(e ∷ es) g ⦃ allCons ⦃ i = i ⦄ ⦃ is = is ⦄ ⦄ = withMatch (edgeNodesGelem e g) ⦃ i ⦄ {refl}
  where
    withMatch : (bo : Bool) -> ⦃ IsTrue bo ⦄ -> {eq : (edgeNodesGelem e g) ≡ bo} -> gr a b
    withMatch true {eq} = insEdges es (insEdge e g ⦃ i ⦄) ⦃ let  -- propInsEdgeKeepsNodesListAllIsTrue : All IsTrue (map (λ le → edgeNodesGelem le g) es) ≡ All IsTrue (map (λ le -> edgeNodesGelem le (insEdge e g)) es)
                                                                propInsEdgeKeepsNodesListAllIsTrue = propAllTrueWithPropIsAllTrue (map (λ le → edgeNodesGelem le g) es) (map (λ le -> edgeNodesGelem le (insEdge e g)) es) (propInsEdgeKeepsAllNodes es e g ⦃ is ⦄ ⦃ i ⦄) ⦃ is ⦄
                                                            in propImpliesProp is propInsEdgeKeepsNodesListAllIsTrue
                                                          ⦄
{-# COMPILE AGDA2HS insEdges #-}
--{-# INLINABLE insEdges #-}


-- | Remove multiple 'Edge's from the 'Graph'.
delEdges : ⦃ DynGraph gr ⦄ -> List Edge -> gr a b -> gr a b
delEdges es g = foldl' (flip delEdge) g es
{-# COMPILE AGDA2HS delEdges #-}

-- | Build a 'Graph' from a list of 'Context's.
--
--   The list should be in the order such that earlier 'Context's
--   depend upon later ones (i.e. as produced by @'ufold' (:) []@).
buildGr : ⦃ DynGraph gr ⦄ -> List (Context a b) -> gr a b
buildGr = foldr _&_ empty
{-# COMPILE AGDA2HS buildGr #-}

-- | Property that checking if an edge is an element of a node list is
--   is equivalent to the same edge with a label
propNodeInNodeListEquivNodeInLNodeList : (ns : List Node) -> (es : List Edge) -> map (λ e -> nodeInNodeList (fst e) ns && nodeInNodeList (snd e) ns ) es ≡ map (λ le -> nodeInLNodeList (fst₃ le) (labUNodes ns) && nodeInLNodeList (snd₃ le) (labUNodes ns) ) (labUEdges es) 
propNodeInNodeListEquivNodeInLNodeList [] [] = refl
propNodeInNodeListEquivNodeInLNodeList [] (e ∷ es) =
  begin
    map (λ e -> nodeInNodeList (fst e) [] && nodeInNodeList (snd e) [] ) (e ∷ es)
  =⟨⟩
    false ∷ map (λ e -> nodeInNodeList (fst e) [] && nodeInNodeList (snd e) [] ) es
  =⟨ cong (λ x -> false ∷ x) (propNodeInNodeListEquivNodeInLNodeList [] es) ⟩
    false ∷ map (λ le -> nodeInLNodeList (fst₃ le) (labUNodes []) && nodeInLNodeList (snd₃ le) (labUNodes []) ) (labUEdges es)
  =⟨⟩
    map (λ le -> nodeInLNodeList (fst₃ le) (labUNodes []) && nodeInLNodeList (snd₃ le) (labUNodes []) ) (labUEdges (e ∷ es))
  ∎
propNodeInNodeListEquivNodeInLNodeList (n ∷ ns) [] = refl
propNodeInNodeListEquivNodeInLNodeList (n ∷ ns) (e@(v , w) ∷ es) =
  begin
    map (λ e -> nodeInNodeList (fst e) (n ∷ ns) && nodeInNodeList (snd e) (n ∷ ns) ) (e ∷ es)
  =⟨⟩
    (nodeInNodeList (fst e) (n ∷ ns) && nodeInNodeList (snd e) (n ∷ ns)) ∷ map (λ e -> nodeInNodeList (fst e) (n ∷ ns) && nodeInNodeList (snd e) (n ∷ ns) ) es
  =⟨⟩
    (nodeInLNodeList (fst₃ {Tuple []} (toLEdge e [])) (labUNodes (n ∷ ns)) && nodeInLNodeList (snd₃ {Tuple []} (toLEdge e [])) (labUNodes (n ∷ ns))) ∷ map (λ e -> nodeInNodeList (fst e) (n ∷ ns) && nodeInNodeList (snd e) (n ∷ ns) ) es
  =⟨ cong (λ x -> (nodeInLNodeList (fst₃ {Tuple []} (toLEdge e [])) (labUNodes (n ∷ ns)) && nodeInLNodeList (snd₃ {Tuple []} (toLEdge e [])) (labUNodes (n ∷ ns))) ∷ x ) (propNodeInNodeListEquivNodeInLNodeList (n ∷ ns) es) ⟩
    (nodeInLNodeList (fst₃ {Tuple []} (toLEdge e [])) (labUNodes (n ∷ ns)) && nodeInLNodeList (snd₃ {Tuple []} (toLEdge e [])) (labUNodes (n ∷ ns))) ∷ map (λ le -> nodeInLNodeList (fst₃ le) (labUNodes (n ∷ ns)) && nodeInLNodeList (snd₃ le) (labUNodes (n ∷ ns))) (map (λ e -> toLEdge e []) es)
  =⟨⟩
    map (λ le -> nodeInLNodeList (fst₃ le) (labUNodes (n ∷ ns)) && nodeInLNodeList (snd₃ le) (labUNodes (n ∷ ns))) (labUEdges (e ∷ es))
  ∎

-- | Build a quasi-unlabeled 'Graph'.
mkUGraph : ⦃ Graph gr ⦄ -> (ns : List Node) -> (es : List Edge) -> ⦃ All IsTrue (map (λ e -> nodeInNodeList (fst e) ns && nodeInNodeList (snd e) ns ) es ) ⦄ -> gr (Tuple []) (Tuple [])
mkUGraph vs es ⦃ allContained ⦄ = mkGraph (labUNodes vs) (labUEdges es) ⦃ subst (All IsTrue) (propNodeInNodeListEquivNodeInLNodeList vs es) allContained ⦄

{-# COMPILE AGDA2HS mkUGraph #-}

-- | Build a graph out of the contexts for which the predicate is
-- satisfied by recursively calling 'match'.
gfiltermap : ⦃ DynGraph gr ⦄ -> (Context a b -> MContext c d) -> gr a b -> gr c d
gfiltermap f = ufold (maybe id _&_ ∘ f) empty
{-# COMPILE AGDA2HS gfiltermap #-}

-- | Returns the subgraph only containing the labelled nodes which
-- satisfy the given predicate.
labnfilter : ⦃ Graph gr ⦄ -> (LNode a -> Bool) -> gr a b -> gr a b
labnfilter p gr = delNodes (map fst ∘ filter (not ∘ p) $ labNodes gr) gr
{-# COMPILE AGDA2HS labnfilter #-}

-- | Returns the subgraph only containing the nodes which satisfy the
-- given predicate.
nfilter : ⦃ DynGraph gr ⦄ -> (Node -> Bool) -> gr a b -> gr a b
nfilter f = labnfilter (f ∘ fst)
{-# COMPILE AGDA2HS nfilter #-}

-- | Returns the subgraph only containing the nodes whose labels
-- satisfy the given predicate.
labfilter : ⦃ DynGraph gr ⦄ -> (a -> Bool) -> gr a b -> gr a b
labfilter f = labnfilter (f ∘ snd)
{-# COMPILE AGDA2HS labfilter #-}

-- | Returns the subgraph induced by the supplied nodes.
-- subgraph : ⦃ DynGraph gr ⦄ -> List Node -> gr a b -> gr a b
-- subgraph vs = let vs' = fromList vs
--               in nfilter (λ { k -> member k vs' })
-- | Removed the intSet dependency
subgraph : ⦃ DynGraph gr ⦄ -> List Node -> gr a b -> gr a b
subgraph vs = nfilter (λ k -> elem k vs)
{-# COMPILE AGDA2HS subgraph #-}

-- | Find the context for the given 'Node'.  Causes an error if the 'Node' is
-- not present in the 'Graph'.
context : ⦃ _ : Graph gr ⦄ -> (grab : gr a b) -> (n : Node) -> ⦃ IsTrue (gelem n grab) ⦄ ->  Context a b
context g v ⦃ itsContained ⦄ = fromMaybe (error  ("Match Exception, Node: " ++ show v) { fromJust (fst (match v g)) ⦃ itsContained ⦄ }  ) (fst (match v g))
-- context g v = fromMaybe' (fst (match v g)) (error' { i = {! isJust (fst (match v g)) ≡ true  !} } ("Match Exception, Node: " ++ show v))
-- context : ⦃ _ : Graph gr ⦄ -> (grab : gr a b) -> (n : Node) -> ⦃ IsTrue (gelem n grab) ⦄ ->  Context a b
-- context g v = fromMaybe' (fst (match v g)) (λ _ → error ("Match Exception, Node: " ++ show v))
{-# COMPILE AGDA2HS context #-}

-- | The label in a 'Context'.
lab' : Context a b -> a
lab' (_,_,_,_ _ _ l _) = l
{-# COMPILE AGDA2HS lab' #-}

-- | Find the label for a 'Node'.
lab : ⦃ Graph gr ⦄ -> gr a b -> Node -> Maybe a
lab g v = fmap lab' ∘ fst $ match v g
{-# COMPILE AGDA2HS lab #-}

lneighbors' : Context a b -> Adj b

lneighbors : ⦃ Graph gr ⦄ -> gr a b -> Node -> Adj b
-- | All labelled links coming into or going from a 'Context'.
lneighbors' (_,_,_,_ p _ _ s) = p ++ s
{-# COMPILE AGDA2HS lneighbors' #-}
-- | Find the labelled links coming into or going from a 'Context'.
lneighbors = maybe [] lneighbors' ∘∶ mcontext
{-# COMPILE AGDA2HS lneighbors #-}

-- | Find the neighbors for a 'Node'.
neighbors : ⦃ Graph gr ⦄ -> gr a b -> Node -> List Node
neighbors = map snd ∘∶ lneighbors
{-# COMPILE AGDA2HS neighbors #-}

-- | Find all 'Node's that have a link from the given 'Node'.
suc : ⦃ Graph gr ⦄ -> gr a b -> Node -> List Node
suc = map snd ∘∶ context4l
{-# COMPILE AGDA2HS suc #-}

-- | Find all 'Node's that link to to the given 'Node'.
pre : ⦃ Graph gr ⦄ -> gr a b -> Node -> List Node
pre = map snd ∘∶ context1l
{-# COMPILE AGDA2HS pre #-}

-- | Find all 'Node's that are linked from the given 'Node' and the label of
-- each link.
lsuc : ⦃ Graph gr ⦄ -> gr a b -> Node -> List (Node × b)
lsuc = map flip2 ∘∶ context4l
{-# COMPILE AGDA2HS lsuc #-}

-- -- | Find all 'Node's that link to the given 'Node' and the label of each link.
lpre : ⦃ Graph gr ⦄ -> gr a b -> Node -> List (Node × b)
lpre = map flip2 ∘∶ context1l
{-# COMPILE AGDA2HS lpre #-}

-- | Find all outward-bound 'LEdge's for the given 'Node'.
out : ⦃ Graph gr ⦄ -> gr a b -> Node -> List (LEdge b)
out g v = map (λ { (l , w) -> (v , w , l) }) (context4l g v)
{-# COMPILE AGDA2HS out #-}

-- -- | Find all inward-bound 'LEdge's for the given 'Node'.
inn : ⦃ Graph gr ⦄ -> gr a b -> Node -> List (LEdge b)
inn g v = map (λ { (l , w)->(w , v , l) }) (context1l g v)
{-# COMPILE AGDA2HS inn #-}

-- | The outward-bound degree of the 'Node'.
outdeg : ⦃ Graph gr ⦄ -> gr a b -> Node -> Int
outdeg = length ∘∶ context4l
{-# COMPILE AGDA2HS outdeg #-}

-- | The inward-bound degree of the 'Node'.
indeg : ⦃ Graph gr ⦄ -> gr a b -> Node -> Int
indeg  = length ∘∶ context1l
{-# COMPILE AGDA2HS indeg #-}

-- | The degree of a 'Context'.
deg' : Context a b -> Int
deg' (_,_,_,_ p _ _ s) = length p + length s
{-# COMPILE AGDA2HS deg' #-}

-- | The degree of the 'Node'.
deg : ⦃ iGraph : Graph gr ⦄ -> (grab : gr a b) -> (n : Node) -> ⦃ IsTrue (gelem n grab) ⦄ -> Int
deg g v = deg' (context g v)
{-# COMPILE AGDA2HS deg #-}

-- | The 'Node' in a 'Context'.
node' : Context a b -> Node
node' (_,_,_,_ _ v _ _) = v
{-# COMPILE AGDA2HS node' #-}

-- | The 'LNode' from a 'Context'.
labNode' : Context a b -> LNode a
labNode' (_,_,_,_ _ v l _) = (v , l)
{-# COMPILE AGDA2HS labNode' #-}

-- | All 'Node's linked to or from in a 'Context'.
neighbors' : Context a b -> List Node
neighbors' (_,_,_,_ p _ _ s) = map snd p ++ map snd s
{-# COMPILE AGDA2HS neighbors' #-}

-- | All 'Node's linked to in a 'Context'.
suc' : Context a b -> List Node
suc' = map snd ∘ context4l'
{-# COMPILE AGDA2HS suc' #-}

-- | All 'Node's linked from in a 'Context'.
pre' : Context a b -> List Node
pre' = map snd ∘ context1l'
{-# COMPILE AGDA2HS pre' #-}

-- | All 'Node's linked from in a 'Context', and the label of the links.
lsuc' : Context a b -> List (Node × b)
lsuc' = map flip2 ∘ context4l'
{-# COMPILE AGDA2HS lsuc' #-}

-- | All 'Node's linked from in a 'Context', and the label of the links.
lpre' : Context a b -> List (Node × b)
lpre' = map flip2 ∘ context1l'
{-# COMPILE AGDA2HS lpre' #-}

-- | All outward-directed 'LEdge's in a 'Context'.
out' : Context a b -> List (LEdge b)
out' (_,_,_,_ a v b c) = map (λ { (l , w) -> (v , w , l) }) (context4l' (_,_,_,_ a v b c))
{-# COMPILE AGDA2HS out' #-}

-- | All inward-directed 'LEdge's in a 'Context'.
inn' : Context a b -> List (LEdge b)
inn' (_,_,_,_ a v b c) = map (λ { (l , w) -> (w , v , l) }) (context1l' (_,_,_,_ a v b c))
{-# COMPILE AGDA2HS inn' #-}

-- | The outward degree of a 'Context'.
outdeg' : Context a b -> Int
outdeg' = length ∘ context4l'
{-# COMPILE AGDA2HS outdeg' #-}

-- | The inward degree of a 'Context'.
indeg' : Context a b -> Int
indeg' = length ∘ context1l'
{-# COMPILE AGDA2HS indeg' #-}

-- | Checks if there is a directed edge between two nodes.
hasEdge : ⦃ Graph gr ⦄ -> gr a b -> Edge -> Bool
hasEdge gr (v , w) = elem w (suc gr v)
{-# COMPILE AGDA2HS hasEdge #-}

-- | Checks if there is an undirected edge between two nodes.
hasNeighbor : ⦃ Graph gr ⦄ -> gr a b -> Node -> Node -> Bool
hasNeighbor gr v w = elem w (neighbors gr v)
{-# COMPILE AGDA2HS hasNeighbor #-}

-- | Checks if there is a labelled edge between two nodes.
hasLEdge : ⦃ Graph gr ⦄ -> ⦃ Eq b ⦄ -> gr a b -> LEdge b -> Bool
hasLEdge gr (v , w , l) = elem (w , l) (lsuc gr v)
{-# COMPILE AGDA2HS hasLEdge #-}

-- | Checks if there is an undirected labelled edge between two nodes.
hasNeighborAdj : ⦃ Graph gr ⦄ -> ⦃ Eq b ⦄ -> gr a b -> Node -> (b × Node) -> Bool
hasNeighborAdj gr v a = elem a (lneighbors gr v)
{-# COMPILE AGDA2HS hasNeighborAdj #-}

----------------------------------------------------------------------
-- GRAPH EQUALITY
----------------------------------------------------------------------
-- Newtype wrapper just to test for equality of multiple edges.  This
-- is needed because without an Ord constraint on `b' it is not
-- possible to guarantee a stable ordering on edge labels.
data GroupEdges b : Set where
    GEs : LEdge (List b) -> GroupEdges b
    -- deriving (Show, Read)
{-# COMPILE AGDA2HS GroupEdges #-}

slabNodes : ⦃ Graph gr ⦄ -> gr a b -> List (LNode a)
slabNodes = sortBy (on compare fst) ∘ labNodes
{-# COMPILE AGDA2HS slabNodes #-}

glabEdges : ⦃ Graph gr ⦄ -> gr a b -> List (GroupEdges b)
glabEdges = map (GEs ∘ groupLabels)
            ∘ groupBy (on _==_ toEdge)
            ∘ sortBy (on compare toEdge)
            ∘ labEdges
    where
        groupLabels : List (LEdge b) -> LEdge (List b)
        groupLabels [] = (0 , 0 , [])
        groupLabels les@(x ∷ xs) = toLEdge (toEdge (head les)) (map edgeLabel les)
{-# COMPILE AGDA2HS glabEdges #-}

eqLists : ⦃ Eq a ⦄ -> List a -> List a -> Bool
eqLists xs ys = null (xs \\ ys) && null (ys \\ xs)
-- OK to use \\ here as we want each value in xs to cancel a *single*
-- value in ys.
{-# COMPILE AGDA2HS eqLists #-}

instance 
    groupEdgesEq : ⦃ Eq b ⦄ -> Eq (GroupEdges b)
    groupEdgesEq ._==_ (GEs (v1 , w1 , bs1)) (GEs (v2 , w2 , bs2))  = v1 == v2
                                                                    && w1 == w2
                                                                    && eqLists bs1 bs2
{-# COMPILE AGDA2HS groupEdgesEq #-}

equal : ⦃ Eq a ⦄ -> ⦃ Eq b ⦄ -> ⦃ Graph gr ⦄ -> gr a b -> gr a b -> Bool
equal g g' = slabNodes g == slabNodes g' && glabEdges g == glabEdges g'
-- This assumes that nodes aren't repeated (which shouldn't happen for
-- sane graph instances).  If node IDs are repeated, then the usage of
-- slabNodes cannot guarantee stable ordering.
{-# COMPILE AGDA2HS equal #-}

----------------------------------------------------------------------
-- PRETTY PRINTING
----------------------------------------------------------------------

-- | Pretty-print the graph.  Note that this loses a lot of
--   information, such as edge inverses, etc.
-- prettify : ⦃ DynGraph gr ⦄ -> ⦃ Show a ⦄ -> ⦃ Show b ⦄ -> gr a b -> String
-- prettify g = {!   !} -- foldr (showsContext ∘ context g) id (nodes g) ""
--   where
--     showsContext : { a1 a2 a3 a4 : Set } -> ⦃ Show a1 ⦄ -> ⦃ Show a2 ⦄ -> ⦃ Show a3 ⦄ -> ⦃ Show a4 ⦄ -> (a × a1 × a2 × a3) -> (a4 -> List Char) -> a4 -> String
--     showsContext (_ , n , l , s) sg = shows n ∘ (':' ∷_) ∘ shows l
--                                 ∘ showString "->" ∘ shows s
--                                 ∘ ('\n' ∷_) ∘ sg
-- prettify : ⦃ DynGraph gr ⦄ -> ⦃ Show a ⦄ -> ⦃ Show b ⦄ -> gr a b -> String
-- prettify g with inspect (isEmpty g)
-- prettify g    | true  with≡ eq = ""
-- prettify g    | false with≡ eq = foldr (λ first second -> {!   !} ) id (nodes g) ""
--   where
--     showsContext : { a1 a2 a3 a4 : Set } -> ⦃ Show a1 ⦄ -> ⦃ Show a2 ⦄ -> ⦃ Show a3 ⦄ -> ⦃ Show a4 ⦄ -> (a × a1 × a2 × a3) -> (a4 -> List Char) -> a4 -> String
--     showsContext (_ , n , l , s) sg = shows n ∘ (':' ∷_) ∘ shows l
--                                 ∘ showString "->" ∘ shows s
--                                 ∘ ('\n' ∷_) ∘ sg

-- postulate
--   IO : Set -> Set

-- postulate
--   putStr : String → IO ⊤

-- -- | Pretty-print the graph to stdout.
-- prettyPrint : ⦃ DynGraph gr ⦄ -> ⦃ Show a ⦄ -> ⦃ Show b ⦄ -> gr a b -> IO ⊤
-- prettyPrint = putStr ∘ prettify


----------------------------------------------------------------------
-- Ordered Graph
----------------------------------------------------------------------

-- | OrdGr comes equipped with an Ord instance, so that graphs can be
--   used as e.g. Map keys.
data OrdGraph (gr : Set -> Set -> Set) ( a b : Set) : Set where
  OrdGr : gr a b -> OrdGraph gr a b
--   deriving (Read,Show)
{-# COMPILE AGDA2HS OrdGraph #-}

instance
  {-# TERMINATING #-}
  iEqOrdGraph : ⦃ Graph gr ⦄ -> ⦃ Ord a ⦄ -> ⦃ Ord b ⦄ -> Eq (OrdGraph gr a b)
  
  iOrdGraph : ⦃ Graph gr ⦄ -> ⦃ Ord a ⦄ -> ⦃ Ord b ⦄ -> Ord (OrdGraph gr a b)
  iOrdGraph {gr} {a} {b} = ordFromCompare λ { (OrdGr g1) (OrdGr g2)  -> (((on compare (sort ∘ labNodes)) g1 g2) <> ((on compare (sort ∘ labEdges)) g1 g2)) }
    -- where
    --   lambdaFunction : OrdGraph gr a b ->  OrdGraph gr a b -> Ordering
    --   lambdaFunction (OrdGr g1) (OrdGr g2) = (((on compare (sort ∘ labNodes)) g1 g2) <> ((on compare (sort ∘ labEdges)) g1 g2))

  iEqOrdGraph ._==_ g1 g2 = compare g1 g2 == EQ
{-# COMPILE AGDA2HS iEqOrdGraph #-}
-- {-# COMPILE AGDA2HS iOrdGraph #-}
{-# FOREIGN AGDA2HS
instance (Graph gr, Ord a, Ord b) => Ord (OrdGraph gr a b) where
  compare (OrdGr g1) (OrdGr g2) = on compare (sort . labNodes) g1 g2 <> on compare (sort . labEdges) g1 g2
#-}
