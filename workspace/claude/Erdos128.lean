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

import FormalConjectures.Util.ProblemImports

/-!
# Resolution of the formal statement of Erdős Problem 128

`FormalConjectures/ErdosProblems/128.lean` states:

```
theorem erdos_128 :
    answer(sorry) ↔ ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (V' : Set V),
      2 * V'.ncard + 1 ≥ Fintype.card V →
        50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2 → ¬ G.CliqueFree 3
```

The intended problem (erdosproblems.com/128) asks: if EVERY induced subgraph
on at least `n/2` vertices has more than `n²/50` edges, must `G` contain a
triangle?  The density condition must be a universally quantified *hypothesis*.
As formalized, `∀ V', hyp₁ → hyp₂ → ¬CliqueFree` instead says: if there
EXISTS one large dense induced subgraph, then `G` has a triangle.  That is
elementarily false: a single edge on two vertices is already a counterexample
(`V' = univ` is "large" and "dense" for `n = 2`, but there is no triangle).
So the formal statement is resolved by `answer(False)` while the intended
problem remains open.
-/

namespace Erdos128Resolution

/-- The right-hand side of the formalized Erdős 128 is false, witnessed by the
single-edge graph on two vertices. -/
theorem erdos_128_rhs_false :
    ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V) (V' : Set V),
      2 * V'.ncard + 1 ≥ Fintype.card V →
        50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2 → ¬ G.CliqueFree 3) := by
  intro h
  -- the single edge on two vertices, with `V' = univ`
  have hcard : 2 * (Set.univ : Set (Fin 2)).ncard + 1 ≥ Fintype.card (Fin 2) := by
    simp [Set.ncard_univ]
  have hedge : ((⊤ : SimpleGraph (Fin 2)).induce Set.univ).edgeSet.Nonempty := by
    refine ⟨s(⟨0, Set.mem_univ _⟩, ⟨1, Set.mem_univ _⟩), ?_⟩
    rw [SimpleGraph.mem_edgeSet]
    simp [Subtype.ext_iff]
  have hdense : 50 * ((⊤ : SimpleGraph (Fin 2)).induce Set.univ).edgeSet.ncard >
      Fintype.card (Fin 2) ^ 2 := by
    have h1 : 0 < ((⊤ : SimpleGraph (Fin 2)).induce Set.univ).edgeSet.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr hedge
    simp only [Fintype.card_fin]
    omega
  have htriangle := h (Fin 2) ⊤ Set.univ hcard hdense
  -- but a two-vertex graph has no triangle
  exact htriangle (SimpleGraph.cliqueFree_of_card_lt (by simp))

end Erdos128Resolution
