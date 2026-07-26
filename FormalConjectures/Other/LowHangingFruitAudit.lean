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

/-- A clean formal answer to the underspecified `M_eq` declaration using the already-proved
antichain characterization. -/
@[category test, AMS 5 6]
theorem M_eq_via_antichains : M = answer(M') := by
  exact M_eq_M'

/-- The mathematically intended Kisielewicz answer, audited separately because the source theorem
still contains `sorry`. -/
@[category test, AMS 5 6]
theorem M_eq_via_kisielewicz : M = answer(kisielewiczFormula) := by
  exact M_eq_kisielewiczFormula

end DedekindNumber

namespace MovingSofa

open MeasureTheory
open scoped ENNReal EuclideanGeometry

/-- No set can be the literal unique set with maximal volume: deleting one point preserves volume. -/
@[category test, AMS 49]
theorem no_literal_volume_unique (g : Set ℝ²) :
    ¬ (∀ s : Set ℝ², sofaConstant = volume s ↔ s = g) := by
  intro h
  have hvol : sofaConstant = volume g := (h g).2 rfl
  have hpos : 0 < volume g := by
    rw [← hvol]
    exact lt_of_lt_of_le (by norm_num) one_le_sofaConstant
  have hne : g.Nonempty := by
    by_contra hne
    have hempty : g = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hempty] at hpos
  obtain ⟨p, hp⟩ := hne
  have hmeasure : volume (g \ ({p} : Set ℝ²)) = volume g := by
    exact measure_diff_null (by simp)
  have hsvol : sofaConstant = volume (g \ ({p} : Set ℝ²)) := hvol.trans hmeasure.symm
  have hset : g \ ({p} : Set ℝ²) = g := (h (g \ ({p} : Set ℝ²))).1 hsvol
  have hp' : p ∈ g \ ({p} : Set ℝ²) := by
    rw [hset]
    exact hp
  exact hp'.2 (by simp)

/-- The repository's literal uniqueness conjecture is therefore false as written. This specialization
mentions `gerversSofa`, whose current definition depends on the admitted Gerver-constant existence
statement; the general theorem above is the clean axiom-audited result. -/
@[category test, AMS 49]
theorem not_literal_uniqueness :
    ¬ (∀ s : Set ℝ², sofaConstant = volume s ↔ s = gerversSofa) :=
  no_literal_volume_unique gerversSofa

end MovingSofa
