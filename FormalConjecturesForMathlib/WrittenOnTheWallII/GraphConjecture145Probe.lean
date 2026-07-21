import FormalConjectures.WrittenOnTheWallII.GraphConjecture145
import FormalConjecturesForMathlib.WrittenOnTheWallII.GraphConjecture142Proof

open Classical SimpleGraph

#check Finset.exists_mem_eq_inf'
#check Finset.inf'_mem
#check Finset.inf'_le
#check Finset.le_inf'
#check SimpleGraph.exists_walk_of_dist_ne_zero
#check SimpleGraph.exists_walk_of_dist_eq
#check SimpleGraph.Walk.dropLast
#check SimpleGraph.Walk.IsPath.dropLast
#check SimpleGraph.Walk.IsPath.induce_support_isTree
#check SimpleGraph.Walk.IsPath.support_toFinset_card
#check SimpleGraph.Walk.support_toFinset_card
#check SimpleGraph.Walk.adj_penultimate
#check SimpleGraph.Walk.IsPath.chordless
#check SimpleGraph.dist_eq_length_of_geodesic
#check SimpleGraph.exists_geodesic
#check SimpleGraph.eccSet_maxEccentricityVertices_add_one_le_diam_splice
#check SimpleGraph.diam_add_one_le_largestInducedTreeSize_splice
#check SimpleGraph.IsTree.card_le_largestInducedTreeSize_splice
#check SimpleGraph.Walk.IsPath.induce_union_isTree_of_unique_attachment
#check SimpleGraph.connected_iff_ediam_ne_top
#check SimpleGraph.dist_le_diam
#check SimpleGraph.exists_pair_dist_eq_diam
#check SimpleGraph.mem_maxEccentricityVertices_iff
#check SimpleGraph.maxEccentricityVertices_nonempty_splice
#check SimpleGraph.exists_eccSet_witness_splice
