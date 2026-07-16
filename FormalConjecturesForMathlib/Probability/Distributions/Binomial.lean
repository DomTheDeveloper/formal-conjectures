/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Etienne Marion
-/
module

public import Mathlib.Probability.ProbabilityMassFunction.Binomial
public import Mathlib.Topology.UnitInterval

/-!
# Binomial probability measures

Minimal compatibility layer for the mathlib snapshot pinned by formal-conjectures. The snapshot
already contains a normalized binomial probability mass function on `Fin (n + 1)`. We push that
PMF to `ℕ`, and then to any measurable additive monoid via the natural-number cast.
-/

public section

open MeasureTheory Measure
open scoped unitInterval

namespace ProbabilityTheory

variable {R : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {n : ℕ} {p : I}

/-- The binomial probability distribution with parameters `n` and `p`. -/
@[expose]
noncomputable def binomial (n : ℕ) (p : I) : Measure ℕ :=
  ((PMF.binomial (⟨(p : ℝ), p.2.1⟩ : ℝ≥0) (show (⟨(p : ℝ), p.2.1⟩ : ℝ≥0) ≤ 1 from p.2.2) n).toMeasure).map Fin.val

/-- The binomial probability distribution on `ℕ`. -/
scoped notation3 "Bin(" n ", " p ")" => binomial n p

/-- The binomial probability distribution valued in the semiring `R`. -/
scoped notation3 "Bin(" R ", " n ", " p ")" => (binomial n p).map (Nat.cast : ℕ → R)

@[simp]
lemma binomial_nat : Bin(ℕ, n, p) = Bin(n, p) := map_id

instance isProbabilityMeasure_binomial : IsProbabilityMeasure Bin(n, p) :=
  isProbabilityMeasure_map (.of_discrete : Measurable (Fin.val : Fin (n + 1) → ℕ)).aemeasurable

instance isProbabilityMeasure_map_cast_binomial : IsProbabilityMeasure Bin(R, n, p) :=
  isProbabilityMeasure_map .of_discrete

end ProbabilityTheory
