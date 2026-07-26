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
# Disproofs of misformalized `research open` statements

Each theorem here proves the *negation* of a statement that is tagged
`@[category research open]` in the repository, demonstrating that the
formalization does not capture the intended open problem.

## `MovingSofa.sofaConstant_eq_volume_iff_eq_gerversSofa`

The statement claims: `∀ s : Set ℝ², sofaConstant = volume s ↔ s = gerversSofa`.
This is false for measure-theoretic reasons that have nothing to do with the
sofa problem: `volume` cannot characterize a set up to equality, because
volume-preserving modifications (adding or removing a single point) change the
set but not its volume.

We prove the strong, fully general form: *no* set `g : Set ℝ²` can satisfy
`∀ s, sofaConstant = volume s ↔ s = g`.  In particular the repository statement
(the case `g = gerversSofa`) is false.  The intended uniqueness statement is
presumably uniqueness up to rigid motion and null sets.

`not_volume_characterizes_any_set` is sorry-free (check with `#print axioms`);
the corollary instantiating it at `gerversSofa` unavoidably inherits `sorryAx`
because the *definition* of Gerver's constants in `MovingSofa.lean` relies on
the sorried existence theorem `ABφθSpec.existsUnique`.
-/

namespace MovingSofa

open MeasureTheory
open scoped EuclideanGeometry

/-- No set `g` of the plane is characterized by its volume: the statement
`∀ s, sofaConstant = volume s ↔ s = g` fails for every `g`.  (The same proof
works with any fixed `ℝ≥0∞`-valued constant in place of `sofaConstant`.) -/
theorem not_volume_characterizes_any_set (g : Set ℝ²) :
    ¬ (∀ s : Set ℝ², sofaConstant = volume s ↔ s = g) := by
  intro H
  have h1 : sofaConstant = volume g := (H g).mpr rfl
  by_cases hg : g = Set.univ
  · -- `g` is the whole plane: removing a point keeps the volume but not the set.
    subst hg
    have h2 : volume (Set.univ \ {0} : Set ℝ²) = volume (Set.univ : Set ℝ²) :=
      measure_diff_null (measure_singleton 0)
    have h3 : (Set.univ \ {0} : Set ℝ²) = Set.univ := (H _).mp (h1.trans h2.symm)
    have : (0 : ℝ²) ∈ (Set.univ \ {0} : Set ℝ²) := h3.symm ▸ Set.mem_univ _
    exact this.2 rfl
  · -- otherwise: adding a point outside `g` keeps the volume but not the set.
    obtain ⟨q, hq⟩ := (Set.ne_univ_iff_exists_notMem g).mp hg
    have h2 : volume (insert q g) = volume g := by
      refine le_antisymm ?_ (measure_mono (Set.subset_insert q _))
      calc volume (insert q g)
          = volume ({q} ∪ g) := by rw [Set.insert_eq]
        _ ≤ volume {q} + volume g := measure_union_le _ _
        _ = volume g := by rw [measure_singleton, zero_add]
    have h3 : insert q g = g := (H _).mp (h1.trans h2.symm)
    exact hq (h3 ▸ Set.mem_insert _ g)

/-- The `research open` statement `sofaConstant_eq_volume_iff_eq_gerversSofa`
is false: it is the case `g = gerversSofa` of `not_volume_characterizes_any_set`. -/
theorem not_sofaConstant_eq_volume_iff_eq_gerversSofa :
    ¬ (∀ s : Set ℝ², sofaConstant = volume s ↔ s = gerversSofa) :=
  not_volume_characterizes_any_set gerversSofa

end MovingSofa
