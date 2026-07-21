import WOW146.GraphConjecture146Proof
import FormalConjectures.WrittenOnTheWallII.GraphConjecture145

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture145

#check Finset.inf'_mem
#check Finset.inf'_le
#check Finset.le_inf'
#check SimpleGraph.Walk.exists_adj_adj_not_adj_ne
#check SimpleGraph.Walk.chordless_of_length_eq_dist
#check SimpleGraph.IsIndepSet.card_le_indepNum
#check SimpleGraph.induce_adj
#check SimpleGraph.mem_neighborSet
#check SimpleGraph.graphSquareRadius_eq
#check SimpleGraph.radius_le_eccent
#check SimpleGraph.exists_edist_eq_eccent_of_finite
#check ENat.toNat_le_toNat
#check SimpleGraph.dist_eq_one_iff_adj
#check SimpleGraph.Connected.exists_path_of_dist
#check SimpleGraph.Walk.adj_getVert_succ
#check SimpleGraph.Walk.getVert_zero
#check SimpleGraph.Walk.getVert_length
#check SimpleGraph.Walk.getVert_inj
#check SimpleGraph.Walk.IsPath.getVert_injective
