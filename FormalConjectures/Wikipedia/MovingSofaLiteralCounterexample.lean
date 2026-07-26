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

The catalog's uniqueness declaration quantifies over every set and uses literal
set equality. Lebesgue volume is unchanged by inserting or deleting a singleton,
so no set can be uniquely characterized among all sets by its volume alone.

This only disproves the declaration as written. A corrected uniqueness theorem
must restrict to valid moving sofas and should likely identify sets modulo null
sets or impose suitable regularity.
-/

namespace MovingSofa

open MeasureTheory
open scoped ENNReal Real unitInterval EuclideanGeometry

private abbrev Plane := Fin 2 → ℝ

/-- Under atomless planar volume, no fixed number can characterize one exact set by volume alone. -/
@[category research solved, AMS 28 49]
theorem volume_does_not_characterize_exact_set (c : ℝ≥0∞) (g : Set Plane) :
    ¬ (∀ s : Set Plane, c = volume s ↔ s = g) := by
  intro h
  have hconst : c = volume g := (h g).2 rfl
  by_cases hg : g = Set.univ
  · let p : Plane := 0
    let s : Set Plane := ({p}ᶜ)
    have huniv : (Set.univ : Set Plane) = insert p ({p}ᶜ) := by
      ext x
      simp [eq_comm]
    have hae : (Set.univ : Set Plane) =ᵐ[volume] s := by
      rw [huniv]
      simpa [s] using (insert_ae_eq_self (μ := volume) p ({p}ᶜ))
    have hvol : volume s = volume g := by
      rw [hg]
      exact (measure_congr hae).symm
    have hsconst : c = volume s := hconst.trans hvol.symm
    have hseq : s = g := (h s).1 hsconst
    have hpg : p ∈ g := by
      rw [hg]
      simp
    have hps : p ∈ s := by
      rw [hseq]
      exact hpg
    simpa [s] using hps
  · obtain ⟨p, hp⟩ : ∃ p : Plane, p ∉ g := by
      by_contra hn
      push_neg at hn
      exact hg (Set.eq_univ_of_forall hn)
    let s : Set Plane := insert p g
    have hae : s =ᵐ[volume] g := by
      simpa [s] using (insert_ae_eq_self (μ := volume) p g)
    have hvol : volume s = volume g := measure_congr hae
    have hsconst : c = volume s := hconst.trans hvol.symm
    have hseq : s = g := (h s).1 hsconst
    have hps : p ∈ s := by simp [s]
    have hpg : p ∈ g := by
      rw [← hseq]
      exact hps
    exact hp hpg

/-- The moving-sofa uniqueness declaration is false as literally quantified over all sets. -/
@[category research solved, AMS 49]
theorem sofaConstant_eq_volume_iff_eq_gerversSofa_false :
    ¬ (∀ s : Set ℝ², sofaConstant = volume s ↔ s = gerversSofa) :=
  volume_does_not_characterize_exact_set sofaConstant gerversSofa

#print axioms volume_does_not_characterize_exact_set
#print axioms sofaConstant_eq_volume_iff_eq_gerversSofa_false

end MovingSofa
