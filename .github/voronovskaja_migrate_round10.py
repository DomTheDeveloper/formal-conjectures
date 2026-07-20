from pathlib import Path


def replace_once_or_already(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    old_count = text.count(old)
    new_count = text.count(new)
    if old_count == 1:
        path.write_text(text.replace(old, new, 1))
        return
    if old_count == 0 and new_count == 1:
        return
    raise SystemExit(
        f"{label}: expected one old occurrence or one already-migrated occurrence, "
        f"found old={old_count}, new={new_count}"
    )


path = Path("FormalConjectures/Paper/VoronovskajaRemainder.lean")
replace_once_or_already(
    path,
    """      exact mul_le_mul_of_nonneg_right hTaylor hw
""",
    """      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hTaylor hw
""",
    "remainder weighted Taylor associativity",
)

old_squeeze = """  rw [tendsto_zero_iff_norm_tendsto_zero]
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
"""
legacy_new = """  apply squeeze_zero_norm'
  · refine eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩
"""
explicit_new = """  apply squeeze_zero_norm'
    (a := fun n : ℕ ↦ M *
"""
text = path.read_text()
if text.count(old_squeeze) == 1:
    raise SystemExit(
        "remainder direct norm squeeze: source still uses the obsolete implicit-envelope proof"
    )
if text.count(explicit_new) == 1:
    pass
elif text.count(legacy_new) == 1:
    raise SystemExit(
        "remainder direct norm squeeze: implicit envelope remains; commit the explicit `a :=` form"
    )
else:
    raise SystemExit("remainder direct norm squeeze: expected explicit migrated proof exactly once")
