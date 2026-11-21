import Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily

/-! # 1. What the prime sum measures
For y ≥ 1, each prime power n = p^k ≤ y contributes log(p)·(y/n − 1).
Subtracting y·(log y − 1 − γ) removes the expected main term. The ramp vanishes
at the cutoff n = y. This file gives a formula with real summands for the exact
function used by the archive's analytic argument. -/

namespace RH17

noncomputable abbrev primeError := Deduction.G

open scoped ArithmeticFunction.vonMangoldt

theorem primeError_eq (y : ℝ) : primeError y =
    (∑ n ∈ Finset.range (⌊y⌋₊ + 1), Λ n * max (y / n - 1) 0) -
      y * (Real.log y - 1 - Real.eulerMascheroniConstant) := by
  simp [Deduction.G, Deduction.ramp, Complex.re_sum, Complex.mul_re]
  ring

end RH17
