module InductiveGraphProperties where

open import Proofs.Proof
open import Proofs.ListProperties

open import Haskell.Prelude
open import Haskell.Prim
open import Prelude
open import Haskell.Data.List
open import Haskell.Data.Maybe

open import InductiveGraph

open Graph ⦃ ... ⦄
open DynGraph ⦃ ... ⦄

---------------------------------
-- Helper functions
---------------------------------
getNodes : List (LNode a) -> List Node
getNodes lvs = map (fst) lvs

getEdges : List (LEdge b) -> List Edge
getEdges les = map (λ {(l , r , _) -> (l , r) }) les

getNodeFromGDecomp : ⦃ Graph gr ⦄ -> GDecomp gr a b -> Node
getNodeFromGDecomp gdecomp = node' (fst gdecomp)

gDecompToDecomp : ⦃ Graph gr ⦄ -> GDecomp gr a b -> Decomp gr a b
gDecompToDecomp (c , g) = (Just c), g

getContextFromMatch : ⦃ _ : Graph gr ⦄ -> (v : Node) -> (grab : gr a b)  -> ⦃ IsTrue (gelem v grab) ⦄ -> Context a b
getContextFromMatch v g = fromJust (fst (match v g))

getGraphFromMatch : ⦃ _ : Graph gr ⦄ -> Node -> gr a b -> gr a b
getGraphFromMatch v g = snd (match v g)

nodeInEdge : ⦃ _ : Graph gr ⦄ -> Node -> Edge -> Bool
nodeInEdge n (l , r) = n == l || n == r

nodeInLEdge : ⦃ _ : Graph gr ⦄ -> Node -> LEdge b -> Bool
nodeInLEdge n (l , r , _) = nodeInEdge n (l , r)

record GraphProperties gr : Set₁ where
    field
        overlap ⦃ super ⦄ : Graph gr
        -- propNodeCount : (grab : gr a b) -> noNodes grab ≡ noNodesDefault grab
        propNodeCount : (grab : gr a b) -> noNodes grab ≡ length (nodes grab)

        -- | Ensure that the definition of 'nodeRange' matches the default
        --   implementation.
        propNodeRange : (grab : gr a b) -> ⦃ nonEmptyInstance : IsFalse (isEmpty grab) ⦄ -> nodeRange grab ≡ (minimum (nodes grab) ⦃ getNonEmptyNodes grab nonEmptyInstance ⦄ , maximum (nodes grab) ⦃ getNonEmptyNodes grab nonEmptyInstance ⦄)

        -- | Make sure that a graph created with specified nodes contains
        --   those nodes (and only those nodes)
        propMkGraphNodes : ⦃ _ : Eq a ⦄ -> (lns : List (LNode a)) -> (les : List (LEdge b)) ->  ⦃ _ : All IsTrue (map (λ le -> nodeInLNodeList (fst₃ le) lns && nodeInLNodeList (snd₃ le) lns ) les ) ⦄ -> equalLists (labNodes (mkGraph lns les)) lns ≡ true

        -- | Make sure that a graph created with specified edges contains
        --   those edges (and only those edges)
        propMkGraphEdges : ⦃ _ : Eq b ⦄ -> (lns : List (LNode a)) -> (les : List (LEdge b)) ->  ⦃ _ : All IsTrue (map (λ le -> nodeInLNodeList (fst₃ le) lns && nodeInLNodeList (snd₃ le) lns ) les ) ⦄ -> equalLists (labEdges (mkGraph lns les)) les ≡ true

        -- | The resultant graph shouldn't matter on the order of nodes and
        --   edges provided.
        --   This is already proved by propMkGraphNodes and propMkGraphEdges, 
        --   since they don't rely on the order
        
        -- | Ensure that when a node is matched, it is indeed removed from the
        --   resulting graph.
        --   propMatch is split in two, one checks if the node is removed, the other checks if the edges are removed.
        propMatchNodeRemoved : (n : Node) -> (grab : gr a b) -> isJust (fst (match n grab)) ≡ not (gelem n (snd (match n grab)))
        propMatchEdgesRemoved : ⦃ _ : Eq b ⦄ -> (n : Node) -> (grab : gr a b) -> disjointLists ((out grab n) ++ (inn grab n)) (labEdges (snd (match n grab))) ≡ true

        -- | Ensure that 'matchAny' is valid by verifying that it achieves the
        --   same result as matching for that node specifically.
        propMatchAny : (grab : gr a b) -> ⦃ _ : IsFalse (isEmpty grab) ⦄ -> gDecompToDecomp (matchAny grab) ≡ match (getNodeFromGDecomp (matchAny grab)) grab

        -- | newNodes should return Nodes that aren't already in the graph.
        propNewNodesReallyNew : (grab : gr a b) -> (n : Int) -> ⦃ IsNonNegativeInt n ⦄ -> disjointLists (nodes grab) (newNodes n grab) ≡ true

        -- | ufold should create a Context for each node.
        propUfoldAllNodees : (grab : gr a b) -> sort (ufold (_∷_ ∘ node') [] grab) ≡ sort (nodes grab)

        -- | All nodes should indeed be elements of the graph.
        propAllNodesGelem : (grab : gr a b) -> all (λ n -> gelem n grab) (nodes grab) ≡ true

        -- | If a potential 'Node' is 'gelem' then it should also be in the
        --   output of 'nodes'.
        propGelemInNodes : (grab : gr a b) -> (n : Node) -> gelem n grab ≡ elem n (nodes grab)

        -- | Check that having a labelled edge in a graph is equivalent to
        -- 'hasNeighborAdj' reporting that the edge is there.
        propHasNeighborAdj : ⦃ _ : Eq b ⦄ -> (grab : gr a b) -> (v : Node) -> (w : Node) -> (l : b) -> any ⦃ iFoldableList ⦄ (λ n -> elem ⦃ iFoldableList ⦄ n ((v , w , l) ∷ (w , v , l) ∷ [])) (labEdges grab) ≡ (hasNeighborAdj grab v (l , w) && hasNeighborAdj grab w (l , v))

        -- | Check that having a labelled edge in a graph is equivalent to
        -- 'hasLEdge' reporting that the edge is there.
        propHasLEdge : ⦃ _ : Eq b ⦄ -> (grab : gr a b) -> (e : LEdge b) -> (elem ⦃ iFoldableList ⦄ e (labEdges grab)) ≡ hasLEdge grab e



record DynGraphProperties gr : Set₁ where
    field
        overlap ⦃ super ⦄ : DynGraph gr
        -- | Ensure that matching and then merging using '&' produces the
        --   original graph again.
        --
        --   In the quickcheck tests it isn't possible to generate an
        --   arbitrary 'Context' to test against; 'propMatch' \"proves\"
        --   that matching is valid, so if merging produces the original graph
        --   again then it must be valid as well.
        --   When proving properties we can use an arbitrary context. We only need to make sure that the node is in th Graph
        propMerge : (n : Node) -> (grab : gr a b) -> ⦃ _ : IsFalse (isEmpty grab) ⦄ -> ⦃ _ : IsTrue (gelem n grab) ⦄ -> (getContextFromMatch n grab) & (getGraphFromMatch n grab) ≡ grab

        -- | 'insNode' inserts a single node and doesn't add or delete any
        --   edges. Uses a node that is not contained in the graph
        propInsNode : ⦃ _ : Eq a ⦄ -> (ln : LNode a) -> (grab : gr a b) -> equalLists (labNodes (insNode ln grab)) (ln ∷ (labNodes grab)) ≡ true

        propInsNodeNoAddedEdges : ⦃ _ : Eq b ⦄ -> (ln : LNode a) -> (grab : gr a b) -> ⦃ _ : IsFalse (gelem (fst ln) grab) ⦄ -> (labEdges (insNode ln grab)) ≡ (labEdges grab)

        propInsNodes' : ⦃ _ : Eq a ⦄ -> (lns : List (LNode a)) -> (grab : gr a b) -> equalLists (labNodes (insNodes lns grab)) (lns ++ (labNodes grab)) ≡ true

        -- | Test inserting an edge.  This could possibly be a multiple edge
        --   or loop.
        propInsEdge : ⦃ _ : Eq b ⦄ -> (le : LEdge b) -> (grab : gr a b) -> ⦃ _ : IsTrue (edgeNodesGelem le grab) ⦄ -> equalLists (labEdges (insEdge le grab)) (le ∷ (labEdges grab)) ≡ true
    

        -- | Delete a node, and ensure there are no edges
        --   referencing that node afterwards.
        propDelNode : (n : Node) -> (grab : gr a b) -> gelem n (delNode n grab) ≡ false

        propDelNodeRemovedEdges : (n : Node) -> (grab : gr a b) -> all (λ le -> not (nodeInLEdge n le) ) (labEdges (delNode n grab)) ≡ true

        -- | Test deleting a sub-set of nodes.
        propDelNodes : (ns : List Node) -> (grab : gr a b) -> all (λ n -> not (gelem n (delNodes ns grab))) ns ≡ true

        propDelNodesRemovedEdges : (ns : List Node) -> (grab : gr a b) -> all (λ le -> (all (λ n -> not (nodeInLEdge n le)) ns) ) (labEdges (delNodes ns grab)) ≡ true

        -- | Delete an edge, and ensure that the nodes from that
        --   edge are still there (if that edge was present in the graph to
        --   start with).
        propDelEdge : (e : Edge) -> (grab : gr a b) -> elem e (edges (delEdge e grab)) ≡ false

        propDelEdgeGelemNode : (e : Edge) -> (grab : gr a b) -> all (λ n -> not (nodeInEdge n e)) (nodes (delEdge e grab)) ≡ true

        -- | Add a 'LEdge' then delete it; the resulting graph should be the
        --   same as the original graph.
        propDelLEdge : ⦃ _ : Eq b ⦄ -> (le : LEdge b) -> (grab : gr a b) -> ⦃ _ : IsTrue (edgeNodesGelem le grab) ⦄ -> delLEdge le (insEdge le grab) ≡ grab

        -- | Test deleting all labelled edges equal to the specified one removes all those edges
        propDelAllLEdge : ⦃ _ : Eq b ⦄ -> (le : LEdge b) -> (grab : gr a b) -> elem ⦃ iFoldableList ⦄ le (labEdges (delAllLEdge le grab)) ≡ false

        -- | 'buildGr' re-creates the original graph after 'ufold' obtains all
        --   the contexts.
        propBuildGr :  ⦃ Eq a ⦄ -> ⦃ Eq b ⦄ -> (grab : gr a b) -> buildGr (ufold _∷_ [] grab) ≡ grab

        -- | Tests `gfiltermap` with a function accepting all contexts.
        propGfiltermapId : ⦃ Eq a ⦄ -> ⦃ Eq b ⦄ -> (grab : gr a b) -> (gfiltermap Just grab) ≡ grab

        -- | Tests `labnfilter` with a function accepting all nodes.
        propLabnfilterTrue :  ⦃ Eq a ⦄ -> ⦃ Eq b ⦄ -> (grab : gr a b) -> (labnfilter (const true) grab) ≡ grab

        -- | The subgraph induced by a list of nodes should contain exactly
        -- the nodes from this list, as well as all edges between these nodes.
        -- Not implemented
        -- valid_subgraph :: (DynGraph gr, Ord b) => gr a b -> Gen Bool
        -- valid_subgraph gr = do
        --   vs <- sublistOf $ nodes gr
        --   let sg = subgraph vs gr
        --       svs = S.fromList vs
        --       subedges = filter (\(v,w,_) -> v `S.member` svs && w `S.member` svs) $ labEdges gr
        --   return $ sort (nodes sg) == sort vs && sort (labEdges sg) == sort subedges