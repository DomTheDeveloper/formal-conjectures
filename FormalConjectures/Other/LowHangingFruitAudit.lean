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

import FormalConjectures.Wikipedia.DedekindNumber
import FormalConjectures.Wikipedia.MovingSofa

/-!
# Low-hanging fruit audit

This temporary module checks two candidate formal-conjectures targets before editing their
source declarations.
-/

namespace DedekindNumber

@[category test, AMS 5 6]
theorem M_eq_low_hanging : M = answer(sorry) := by
  exact M_eq_kisielewiczFormula

#print axioms M_eq_low_hanging

end DedekindNumber

namespace MovingSofa

open MeasureTheory
open scoped ENNReal EuclideanGeometry

@[category test, AMS 49]
theorem not_literal_uniqueness :
    ¬ (∀ s : Set ℝ², sofaConstant = volume s ↔ s = gerversSofa) := by
  intro h
  have hvol : sofaConstant = volume gerversSofa := (h gerversSofa).2 rfl
  have hpos : 0 < volume gerversSofa := by
    rw [← hvol]
    exact lt_of_lt_of_le (by norm_num) one_le_sofaConstant
  have hne : gerversSofa.Nonempty := by
    by_contra hne
    have hempty : gerversSofa = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hempty] at hpos
  obtain ⟨p, hp⟩ := hne
  have hmeasure :
      volume (gerversSofa \ ({p} : Set ℝ²)) = volume gerversSofa := by
    exact measure_sdiff_null (by simp)
  have hsvol : sofaConstant = volume (gerversSofa \ ({p} : Set ℝ²)) :=
    hvol.trans hmeasure.symm
  have hset : gerversSofa \ ({p} : Set ℝ²) = gerversSofa :=
    (h (gerversSofa \ ({p} : Set ℝ²))).1 hsvol
  have hp' : p ∈ gerversSofa \ ({p} : Set ℝ²) := by
    rw [hset]
    exact hp
  exact hp'.2 (by simp)

#print axioms not_literal_uniqueness

end MovingSofa
