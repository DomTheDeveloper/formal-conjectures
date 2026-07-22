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

public import FormalConjecturesForMathlib.NumberTheory.SquarefreeRadical

@[expose] public section

noncomputable section

namespace Real

/-- Reciprocal square roots of an injective finite family of squarefree naturals are
linearly independent over the rationals. -/
theorem linearIndependent_inv_sqrt_squarefree {ι : Type*} [Fintype ι]
    (s : ι → ℕ) (hs : ∀ i, Squarefree (s i)) (hinj : Function.Injective s) :
    LinearIndependent ℚ (fun i => 1 / Real.sqrt (s i)) := by
  have h := linearIndependent_sqrt_squarefree s hs hinj
  let u : ι → ℚˣ := fun i =>
    Units.mk0 ((s i : ℚ)⁻¹) (inv_ne_zero (by exact_mod_cast (hs i).ne_zero))
  have hu := h.units_smul u
  convert hu using 1
  funext i
  have hpos : (0 : ℝ) < s i := by exact_mod_cast (Nat.pos_of_ne_zero (hs i).ne_zero)
  have hsqrt : Real.sqrt (s i) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  change 1 / Real.sqrt (s i) =
    (((((s i : ℚ)⁻¹ : ℚ) : ℝ)) * Real.sqrt (s i))
  rw [Rat.cast_inv, Rat.cast_natCast]
  field_simp [hsqrt, Real.sq_sqrt hpos.le]

end Real
