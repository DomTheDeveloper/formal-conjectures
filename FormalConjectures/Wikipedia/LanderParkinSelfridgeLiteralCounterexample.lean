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

import FormalConjectures.Wikipedia.LanderParkinAndSelfridgeConjecture

/-!
# Counterexample to the literal Lander–Parkin–Selfridge declaration

The catalog theorem quantifies over all natural numbers `n` and `m`, although its
prose requires positive numbers of summands. Taking both index types to be empty
makes the two power sums equal, while `k = 1` makes the claimed bound false.
-/

namespace LanderParkinSelfridge

/-- The catalog declaration is false because it permits two empty sums. -/
@[category research solved, AMS 11]
theorem lander_parkin_selfridge_false :
    ¬ (∀ (k n m : ℕ) (x : Fin n → ℕ) (y : Fin m → ℕ),
      (∀ i, 0 < x i) → (∀ j, 0 < y j) →
      (∀ i j, x i ≠ y j) →
      ∑ i, x i ^ k = ∑ j, y j ^ k →
      k ≤ n + m) := by
  intro h
  have hbad : (1 : ℕ) ≤ 0 + 0 :=
    h 1 0 0
      (fun i => Fin.elim0 i)
      (fun j => Fin.elim0 j)
      (by intro i; exact Fin.elim0 i)
      (by intro j; exact Fin.elim0 j)
      (by intro i; exact Fin.elim0 i)
      (by simp)
  omega

#print axioms lander_parkin_selfridge_false

end LanderParkinSelfridge
