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
# Core definition for WOWII Graph Conjecture 314

The proof chain and catalog theorem both depend on the largest induced-path
invariant.  Keeping it in this dependency-light module lets the catalog theorem
import its completed proof without a circular import.
-/

open Classical

namespace WrittenOnTheWallII.GraphConjecture314

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The size of a largest induced path of `G`, represented as the supremum of
the cardinalities of induced subgraphs that are trees of maximum degree two. -/
noncomputable def largestInducedPathSize (G : SimpleGraph α) [DecidableRel G.Adj] : ℕ :=
  sSup { n | ∃ s : Finset α,
    s.card = n ∧
    (G.induce (s : Set α)).IsTree ∧
    ∀ v : (s : Set α), (G.induce (s : Set α)).degree v ≤ 2 }

end WrittenOnTheWallII.GraphConjecture314
