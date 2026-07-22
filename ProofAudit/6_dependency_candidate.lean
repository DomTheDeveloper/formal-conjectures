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

import FormalConjectures.Paper.MonochromaticQuantumGraph

/-!
# Color restriction for the N = 6 monochromatic quantum graph system

This file verifies the reduction from the three-color integer case to every
larger number of colors. It deliberately takes the still-missing `D = 3`
nonexistence theorem as a hypothesis rather than importing an unavailable
private module or pretending that the base case has been proved.
-/

namespace MonochromaticQuantumGraph

def restrictColorWeights {N d D : Nat} {α : Type}
    (f : Fin d → Fin D) (W : WeightsN N D α) : WeightsN N d α :=
  fun e => W (mkEdge e.u e.v (f e.i) (f e.j))

def colorEmbedding {d D : Nat} (h : d ≤ D) : Fin d → Fin D :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩

lemma colorEmbedding_injective {d D : Nat} (h : d ≤ D) :
    Function.Injective (colorEmbedding h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg Fin.val hij

private lemma pmSumN_six_restrictColorWeights
    {α : Type} [Semiring α] {d D : Nat}
    (f : Fin d → Fin D) (W : WeightsN 6 D α)
    (ι : V 6 → Fin d) :
    pmSumN 6 d (restrictColorWeights f W) ι =
      pmSumN 6 D W (fun v => f (ι v)) := by
  simp [pmSumN, pmSumList, pmSumListAux, vertices,
    restrictColorWeights, mkEdge]

private lemma allEqual_six_comp_iff
    {d D : Nat} (f : Fin d → Fin D) (hf : Function.Injective f)
    (ι : V 6 → Fin d) :
    allEqual (fun v => f (ι v)) ↔ allEqual ι := by
  simp [allEqual, allEqualList, vertices, hf.eq_iff]

theorem eqSystem6_restrictColors
    {α : Type} [Semiring α] {d D : Nat}
    (f : Fin d → Fin D) (hf : Function.Injective f)
    {W : WeightsN 6 D α} (hW : EqSystemN 6 D W) :
    EqSystemN 6 d (restrictColorWeights f W) := by
  intro ι
  calc
    pmSumN 6 d (restrictColorWeights f W) ι =
        pmSumN 6 D W (fun v => f (ι v)) :=
      pmSumN_six_restrictColorWeights f W ι
    _ = if allEqual (fun v => f (ι v)) then (1 : α) else 0 :=
      hW (fun v => f (ι v))
    _ = if allEqual ι then (1 : α) else 0 := by
      rw [allEqual_six_comp_iff f hf ι]

theorem no_eqSystem6_mono_colors
    {α : Type} [Semiring α] {d : Nat}
    (hd : ¬ ∃ W : WeightsN 6 d α, EqSystemN 6 d W) :
    ∀ D : Nat, d ≤ D →
      ¬ ∃ W : WeightsN 6 D α, EqSystemN 6 D W := by
  intro D hdD
  rintro ⟨W, hW⟩
  apply hd
  refine ⟨restrictColorWeights (colorEmbedding hdD) W, ?_⟩
  exact eqSystem6_restrictColors
    (colorEmbedding hdD) (colorEmbedding_injective hdD) hW

/-- A proof of the integer `D = 3` case implies all integer cases `D ≥ 3`. -/
theorem no_eqSystem6_ge3_int_of_d3
    (h3 : ¬ ∃ W : WeightsN 6 3 ℤ, EqSystemN 6 3 W) :
    ∀ D : Nat, D ≥ 3 →
      ¬ ∃ W : WeightsN 6 D ℤ, EqSystemN 6 D W := by
  exact no_eqSystem6_mono_colors h3

/-- In particular, the integer `D = 3` case implies `D = 5`. -/
theorem no_eqSystem6_d5_int_of_d3
    (h3 : ¬ ∃ W : WeightsN 6 3 ℤ, EqSystemN 6 3 W) :
    ¬ ∃ W : WeightsN 6 5 ℤ, EqSystemN 6 5 W := by
  exact no_eqSystem6_ge3_int_of_d3 h3 5 (by decide)

/-- The unrestricted integer result implies the corresponding trinary result. -/
theorem no_eqSystem6_ge3_trinary_int_of_d3
    (h3 : ¬ ∃ W : WeightsN 6 3 ℤ, EqSystemN 6 3 W) :
    ∀ D : Nat, D ≥ 3 →
      ¬ ∃ W : WeightsN 6 D ℤ,
        (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
          EqSystemN 6 D W := by
  intro D hD
  rintro ⟨W, _, hW⟩
  exact no_eqSystem6_ge3_int_of_d3 h3 D hD ⟨W, hW⟩

/-- In particular, the integer `D = 3` case implies the trinary `D = 5` case. -/
theorem no_eqSystem6_d5_trinary_int_of_d3
    (h3 : ¬ ∃ W : WeightsN 6 3 ℤ, EqSystemN 6 3 W) :
    ¬ ∃ W : WeightsN 6 5 ℤ,
      (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
        EqSystemN 6 5 W := by
  exact no_eqSystem6_ge3_trinary_int_of_d3 h3 5 (by decide)

#print axioms eqSystem6_restrictColors
#print axioms no_eqSystem6_ge3_int_of_d3
#print axioms no_eqSystem6_ge3_trinary_int_of_d3

end MonochromaticQuantumGraph
