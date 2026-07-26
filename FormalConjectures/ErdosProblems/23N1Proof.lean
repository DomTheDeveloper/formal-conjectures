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

import FormalConjectures.ErdosProblems.«23»

/-!
# Kernel enumeration of the five-vertex case of Erdős Problem 23
-/

namespace Erdos23

/-- Every triangle-free graph on five vertices can be made bipartite by deleting at most one edge. -/
@[category test, AMS 5]
theorem erdos_23_n1_kernel :
    ∀ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 → ∃ (H : SimpleGraph (Fin 5)),
      H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 1 := by
  decide +kernel

/-- The five-cycle witnesses that the one-edge bound is sharp. -/
@[category test, AMS 5]
theorem erdos_23_n1_tight_kernel :
    ∃ (G : SimpleGraph (Fin 5)), G.CliqueFree 3 ∧ ∀ (H : SimpleGraph (Fin 5)),
      H ≤ G → H.IsBipartite → 1 ≤ (G.edgeFinset \ H.edgeFinset).card := by
  decide +kernel

#print axioms erdos_23_n1_kernel
#print axioms erdos_23_n1_tight_kernel

end Erdos23
