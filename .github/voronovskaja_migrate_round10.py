from pathlib import Path


def replace_once(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    path.write_text(text.replace(old, new, 1))


path = Path("FormalConjectures/Paper/VoronovskajaRemainder.lean")
replace_once(
    path,
    """      exact mul_le_mul_of_nonneg_right hTaylor hw
""",
    """      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hTaylor hw
""",
    "remainder weighted Taylor associativity",
)
replace_once(
    path,
    """  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ norm_nonneg _
  · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hrem := abs_bezierTaylorRemainder_le_sq_moment
      n hn α hα f hf (x : ℝ) x.property M hM0 hM
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg n)]
    calc
      Real.sqrt n *
          |bezierTaylorRemainder n α f (x : ℝ)
            (iteratedDerivWithin 1 f I (x : ℝ))| ≤
        Real.sqrt n *
          (M *
            (∑ k ∈ Finset.range (n + 1),
              ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
                bezierWeight n k α (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hrem (Real.sqrt_nonneg n)
      _ = M *
          (Real.sqrt n *
            (∑ k ∈ Finset.range (n + 1),
              ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
                bezierWeight n k α (x : ℝ))) := by ring
  · exact hupper
""",
    """  apply squeeze_zero_norm'
  · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
    have hrem := abs_bezierTaylorRemainder_le_sq_moment
      n hn α hα f hf (x : ℝ) x.property M hM0 hM
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg n)]
    calc
      Real.sqrt n *
          |bezierTaylorRemainder n α f (x : ℝ)
            (iteratedDerivWithin 1 f I (x : ℝ))| ≤
        Real.sqrt n *
          (M *
            (∑ k ∈ Finset.range (n + 1),
              ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
                bezierWeight n k α (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hrem (Real.sqrt_nonneg n)
      _ = M *
          (Real.sqrt n *
            (∑ k ∈ Finset.range (n + 1),
              ((((k : ℝ) / (n : ℝ)) - (x : ℝ)) ^ 2) *
                bezierWeight n k α (x : ℝ))) := by ring
  · exact hupper
""",
    "remainder direct norm squeeze",
)
