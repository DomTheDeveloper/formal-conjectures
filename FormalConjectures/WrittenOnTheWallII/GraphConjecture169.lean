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
module

public import FormalConjecturesUtil

/-!
# Written on the Wall II, conjecture 169

A connected graph with at least two vertices admits the proposed lower bound on the number
of leaves of a spanning tree. With a leaf defined by degree one, the singleton is the unique
exception. The colour-class estimate is related to Theorem 3 of DeLaViña and Waller (2008).

[Ermelinda DeLaViña, Written on the Wall II](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json).
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture169

open Finset SimpleGraph

variable {V : Type*}

/-- Vertices at even graph distance from `r`, including `r` itself. -/
noncomputable def evenSide [Fintype V] (G : SimpleGraph V) (r : V) : Finset V :=
  univ.filter fun v => G.dist v r % 2 = 0

/-- Number of degree-one vertices. -/
noncomputable def leafCount [Fintype V] (T : SimpleGraph V) : ℕ := by
  classical
  exact (univ.filter fun v => T.degree v = 1).card

/-- The largest leaf count over all trees on `V` whose edges belong to `G`. -/
noncomputable def maxLeafCount [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {k | ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree ∧ k = leafCount T}

set_option linter.style.formal_proof_palomar false in
/-- The spanning-tree leaf bound in Graffiti.pc conjecture 169 holds exactly when a
nonempty finite connected graph has at least two vertices. All distances are in the input graph. -/
@[category research solved, AMS 5, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/ProofPlaygrond/blob/969f70657d579c9c82e2f1592a653e8a0ad3c89a/proofs/graffiti-138-169/Graffiti169.lean#L192-L207"]
theorem conjecture169 [Fintype V] [Nonempty V] {G : SimpleGraph V} (hG : G.Connected) :
    (1 + ((univ.sup' univ_nonempty fun r => (evenSide G r).card) -
          (univ.inf' univ_nonempty fun r => (evenSide G r).card)) ≤ maxLeafCount G) ↔
      1 < Fintype.card V := by
  sorry

end WrittenOnTheWallII.GraphConjecture169
