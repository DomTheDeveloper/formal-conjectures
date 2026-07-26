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

import FormalConjectures.Wikipedia.MovingSofa

/-!
# Literal counterexample to moving-sofa uniqueness

The catalog's uniqueness declaration quantifies over every set `s : Set ℝ²` and
uses literal set equality. Lebesgue volume is unchanged by inserting or deleting
a singleton, so no set can be uniquely characterized among all sets by its
volume alone.

This only disproves the declaration as written. A corrected uniqueness theorem
must restrict to valid moving sofas and should likely identify sets modulo null
sets or impose suitable regularity.
-/

namespace MovingSofa

open MeasureTheory

/-- Equal volume cannot characterize `gerversSofa` by literal equality among all sets. -/
@[category research solved, AMS 49]
theorem sofaConstant_eq_volume_iff_eq_gerversSofa_false :
    ¬ (∀ s : Set ℝ², sofaConstant = volume s ↔ s = gerversSofa) := by
  intro h
  by_cases hG : gerversSofa = Set.univ
  · let p : ℝ² := 0
    let s : Set ℝ² := ({p}ᶜ)
    have hae : (Set.univ : Set ℝ²) =ᵐ[volume] s := by
      simpa [s] using (insert_ae_eq_self (μ := volume) p ({p}ᶜ))
    have hvol : volume s = volume gerversSofa := by
      rw [hG]
      exact (measure_congr hae).symm
    have hsconst : sofaConstant = volume s :=
      sofaConstant_eq_volume_gerversSofa.trans hvol.symm
    have hseq : s = gerversSofa := (h s).1 hsconst
    have hpG : p ∈ gerversSofa := by
      rw [hG]
      simp
    have hps : p ∈ s := by
      rw [hseq]
      exact hpG
    simpa [s] using hps
  · obtain ⟨p, hp⟩ : ∃ p : ℝ², p ∉ gerversSofa := by
      by_contra hn
      push_neg at hn
      exact hG (Set.eq_univ_of_forall hn)
    let s : Set ℝ² := insert p gerversSofa
    have hae : s =ᵐ[volume] gerversSofa := by
      simpa [s] using (insert_ae_eq_self (μ := volume) p gerversSofa)
    have hvol : volume s = volume gerversSofa := measure_congr hae
    have hsconst : sofaConstant = volume s :=
      sofaConstant_eq_volume_gerversSofa.trans hvol.symm
    have hseq : s = gerversSofa := (h s).1 hsconst
    have hps : p ∈ s := by simp [s]
    have hpG : p ∈ gerversSofa := by
      rw [← hseq]
      exact hps
    exact hp hpG

#print axioms sofaConstant_eq_volume_iff_eq_gerversSofa_false

end MovingSofa
