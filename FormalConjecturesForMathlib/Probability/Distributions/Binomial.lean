/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.NCard
public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Binomial probability measures

Minimal compatibility backport for the mathlib snapshot pinned by formal-conjectures.  This file
keeps only the measure-valued binomial law and its probability-measure instances.  The
Voronovskaja development adds the few analytic identities it needs separately instead of
backporting the much larger modern binomial API.
-/

public section

open MeasureTheory Set Measure
open scoped ProbabilityTheory unitInterval

namespace ProbabilityTheory

variable {R : Type*} [MeasurableSpace R] [AddMonoidWithOne R] {n : ℕ} {p : I}

/-- The binomial probability distribution with parameters `n` and `p`. -/
@[expose]
noncomputable def binomial (n : ℕ) (p : I) : Measure ℕ := setBer(Iio n, p).map ncard

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
