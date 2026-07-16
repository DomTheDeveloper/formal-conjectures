/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Etienne Marion
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-!
# Binomial probability measures

Minimal compatibility layer for the mathlib snapshot pinned by formal-conjectures.  The snapshot
already contains a normalized binomial probability mass function on `Fin (n + 1)`.  We push that
PMF to `ℕ`, and then to any measurable additive monoid via the natural-number cast.
-/

public section

open MeasureTheory Measure
open scoped ProbabilityTheory unitInterval

namespace ProbabilityTheory

variable {R : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {n : ℕ} {p : I}

private noncomputable def unitIntervalNNReal (p : I) : ℝ≥0 := ⟨p, p.2.1⟩

private lemma unitIntervalNNReal_le_one (p : I) : unitIntervalNNReal p ≤ 1 := p.2.2

/-- The binomial probability distribution with parameters `n` and `p`. -/
@[expose]
noncomputable def binomial (n : ℕ) (p : I) : Measure ℕ :=
  ((PMF.binomial (unitIntervalNNReal p) (unitIntervalNNReal_le_one p) n).toMeasure).map Fin.val

/-- The binomial probability distribution on `ℕ`. -/
scoped notation3 "Bin(" n ", " p ")" => binomial n p

/-- The binomial probability distribution valued in the semiring `R`. -/
scoped notation3 "Bin(" R ", " n ", " p ")" => (binomial n p).map (Nat.cast : ℕ → R)

@[simp]
lemma binomial_nat : Bin(ℕ, n, p) = Bin(n, p) := map_id

instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(n, p) :=
  isProbabilityMeasure_map <| by fun_prop

instance isProbabilityMeasure_map_cast_binomial : IsProbabilityMeasure Bin(R, n, p) :=
  isProbabilityMeasure_map .of_discrete

end ProbabilityTheory
