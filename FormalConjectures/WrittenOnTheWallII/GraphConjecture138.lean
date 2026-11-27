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
# Written on the Wall II, conjecture 138

A proposed lower bound on the order of a longest induced path fails for a 19-vertex tree.

[Ermelinda DeLaViña, Written on the Wall II](https://www.uhd.edu/academics/sciences/mathematics-statistics/wowii/files/conjectures.json).
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture138

open SimpleGraph

/-- In the square, distinct vertices are adjacent if they are one or two steps apart. -/
def square {V : Type*} (H : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ (H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm)
    (fun ⟨z, e, f⟩ => Or.inr ⟨z, f.symm, e.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] : DecidableRel (square H).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ (_ ∨ ∃ z, H.Adj _ z ∧ H.Adj z _)))

def MaxDeg {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) : Prop :=
  ∀ w, H.degree w ≤ H.degree v

/-- Distances of all distinct pairs of maximum-degree vertices in a graph. -/
def pairDistances {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] : Set ℕ :=
  {d | ∃ x y, x ≠ y ∧ MaxDeg H x ∧ MaxDeg H y ∧ H.dist x y = d}

open scoped Classical in
noncomputable def uniqueFlag {V : Type*} [Fintype V] (H : SimpleGraph V) : ℕ :=
  if ∃! S : Finset V, H.IsMaximumIndepSet S then 1 else 0

def inducedPathOrders {V : Type*} (H : SimpleGraph V) : Set ℕ :=
  {k | ∃ (x y : V) (p : H.Walk x y), p.IsPath ∧ p.IsChordless ∧ p.length + 1 = k}

set_option linter.style.formal_proof_palomar false in
/-- Graffiti.pc conjecture 138 is false. In the finite counterexample the longest induced path
has 17 vertices, the maximum independent set is unique, and the minimum distance between
distinct maximum-degree vertices in the square graph is 6. The proposed bound is 18. -/
@[category research solved, question, AMS 5, formal_proof using lean4 at
  "https://github.com/DomTheDeveloper/ProofPlaygrond/blob/969f70657d579c9c82e2f1592a653e8a0ad3c89a/proofs/graffiti-138-169/WOWII138.lean#L196-L212"]
theorem conjecture138 :
    ¬ ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      H.Connected → ∀ d, IsLeast (pairDistances (square H)) d →
        ∃ k ∈ inducedPathOrders H, (2 + uniqueFlag H) * d ≤ k := by
  sorry

end WrittenOnTheWallII.GraphConjecture138
