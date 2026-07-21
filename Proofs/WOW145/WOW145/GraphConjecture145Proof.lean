/-
Copyright 2026 Dominic Dabish.
Licensed under the Apache License, Version 2.0.
-/

import WOW146.ExceptionalTheorem
import FormalConjectures.WrittenOnTheWallII.GraphConjecture145

open Classical
open SimpleGraph
open WrittenOnTheWallII.GraphConjecture145

namespace WOW145

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
variable {G : SimpleGraph α}

#check Finset.inf'_mem
#check Finset.exists_mem_eq_inf'
#check Finset.inf'_le
#check Finset.le_inf'
#check SimpleGraph.indepNeighborsCard
#check SimpleGraph.IsIndepSet.card_le_indepNum
#check SimpleGraph.indepNum_eq_one_iff
#check SimpleGraph.radius_ne_zero_of_nontrivial
#check ENat.toNat_eq_zero
#check SimpleGraph.graphSquareRadius_eq
#check WOW146.exceptional_six_vertex_induced_tree
#check SimpleGraph.eccSet_periphery_add_one_le_diam
#check SimpleGraph.diam_succ_le_largestInducedTreeSize

end WOW145
