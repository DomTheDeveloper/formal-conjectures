import Bridge
import Main
import Solution.Candidate

open Filter ZetaZeros

private theorem score_zeros_eq (a b : ℝ) : zerosIn a b = nontrivialZeros riemannZeta a b := by
  ext z
  simp only [zerosIn, IsNontrivialZero, nontrivialZeros, Set.mem_ofPred_eq]
  tauto

/-- DeepMind's distinct-zero question, using Knausgård's dyadic lower bound.
The numerical witness is exactly 17/20. -/
theorem riemannZeta.distinct_prop_lt : ∃ c > (3 - montgomeryTaylorConst⁻¹) / 2,
    ∃ o : ℝ → ℝ, o =o[atTop] (1 : ℝ → ℝ) ∧ ∀ T > 0,
      (c - o T) * N riemannZeta T (2 * T) ≤ Nd riemannZeta T (2 * T) := by
  apply DistinctZeros.distinct_prop_lt_of_record (k := candidateKappa) (by norm_num [candidateKappa])
  simpa only [Ncount, N0star, score_zeros_eq, zeroMult, N, Complex.zeroCountOn,
    analyticOrderNatAt, DistinctZeros.lineCount] using candidate_critical_line_bound

#print axioms riemannZeta.distinct_prop_lt
