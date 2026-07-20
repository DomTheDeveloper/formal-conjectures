/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import WOWII.ZZGraphConjecture314Core

/-!
The finite C5 core of the nonbipartite family in WOWII Graph Conjecture 314.
-/

namespace WrittenOnTheWallII.GraphConjecture314

open Classical SimpleGraph

private instance totalDominationDecidable (T : Finset (Fin 5)) :
    Decidable (IsTotalDominatingSet (cycleGraph 5) T) := by
  unfold IsTotalDominatingSet
  infer_instance

private instance minimalTotalDominationDecidable (T : Finset (Fin 5)) :
    Decidable (IsMinimalTotalDominatingSet (cycleGraph 5) T) := by
  unfold IsMinimalTotalDominatingSet
  infer_instance

/-- Every minimal total dominating set of the 5-cycle has three vertices.

This is checked by kernel reduction over the finite type `Fin 5`; it does not
invoke generated native code and remains compatible with the strict proof
audit. -/
lemma cycleGraph_five_minimalTDS_card_eq_three
    (S : Finset (Fin 5))
    (hS : IsMinimalTotalDominatingSet (cycleGraph 5) S) :
    S.card = 3 := by
  decide +revert

/-- In particular, the 5-cycle is well totally dominated. -/
lemma cycleGraph_five_isWellTotallyDominated :
    IsWellTotallyDominated (cycleGraph 5) := by
  intro S T hS hT
  rw [cycleGraph_five_minimalTDS_card_eq_three S hS,
    cycleGraph_five_minimalTDS_card_eq_three T hT]

end WrittenOnTheWallII.GraphConjecture314
