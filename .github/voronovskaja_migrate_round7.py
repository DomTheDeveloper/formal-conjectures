from pathlib import Path


def replace_once(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    path.write_text(text.replace(old, new, 1))


path = Path("FormalConjectures/Paper/VoronovskajaMomentLimit.lean")
replace_once(
    path,
    """  rw [bezierCenteredMoment, Finset.mul_sum, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
""",
    """  rw [bezierCenteredMoment, Finset.mul_sum, Finset.mul_sum]
  have hsum :
      (∑ k : Fin (n + 1),
        bernoulliStdDev x *
          (bezierWeight n (k : ℕ) α (x : ℝ) *
            standardizeBinomial n x ((k : ℕ) : ℝ))) =
        ∑ k ∈ Finset.range (n + 1),
          bernoulliStdDev x *
            (bezierWeight n k α (x : ℝ) *
              standardizeBinomial n x (k : ℝ)) := by
    simpa using (Fin.sum_univ_eq_sum_range
      (f := fun k : ℕ =>
        bernoulliStdDev x *
          (bezierWeight n k α (x : ℝ) *
            standardizeBinomial n x (k : ℝ))) (n + 1))
  rw [hsum]
  apply Finset.sum_congr rfl
""",
    "moment-limit Fin-to-range sum",
)
replace_once(
    path,
    """  field_simp [hnR, hsqrt, hsd]
  rw [Real.sq_sqrt]
  · ring
  · positivity
""",
    """  field_simp [hnR, hsqrt, hsd]
  rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
  ring_nf
""",
    "moment-limit terminal square-root normalization",
)
