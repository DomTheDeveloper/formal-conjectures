from pathlib import Path


def replace_once(path: Path, old: str, new: str, label: str) -> None:
    text = path.read_text()
    count = text.count(old)
    if count != 1:
        raise SystemExit(f"{label}: expected one occurrence, found {count}")
    path.write_text(text.replace(old, new, 1))


path = Path("FormalConjectures/Paper/VoronovskajaTaylorBound.lean")
replace_once(
    path,
    """  have h := congrFun (iteratedDerivWithin_succ (n := 1) (f := f) (s := I)) y
  norm_num at h ⊢
  exact h.symm
""",
    """  have h := iteratedDerivWithin_succ (n := 1) (f := f) (s := I) (x := y)
  norm_num at h ⊢
  exact h.symm
""",
    "Taylor-bound pointwise iterated derivative",
)
replace_once(
    path,
    """  obtain ⟨y, hy, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn nonempty_Icc hcont
""",
    """  have hnonempty : Set.Nonempty I := nonempty_Icc.mpr zero_le_one
  obtain ⟨y, hy, hmax⟩ :=
    isCompact_Icc.exists_isMaxOn hnonempty hcont
""",
    "Taylor-bound compact maximum nonemptiness",
)
replace_once(
    path,
    """      rw [d, hzx] at hL
      exact hL.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2.le x) hM0)
""",
    """      change ‖d z - d x‖ ≤ M * ‖z - x‖ at hL
      rw [hzx] at hL
      exact hL.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hz.2.le x) hM0)
""",
    "Taylor-bound forward local derivative bound",
)
replace_once(
    path,
    """      rw [d, hzx] at hL
      exact hL.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hz.1 x) hM0)
""",
    """      change ‖d z - d x‖ ≤ M * ‖z - x‖ at hL
      rw [hzx] at hL
      exact hL.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hz.1 x) hM0)
""",
    "Taylor-bound reverse local derivative bound",
)
replace_once(
    path,
    """    have hsquare : (x - y) * (x - y) = (y - x) ^ 2 := by ring
    simpa [g, d, pow_two, hsquare] using h
""",
    """    have hsquare :
        M * (x - y) * (x - y) = M * ((y - x) * (y - x)) := by ring
    rw [hsquare] at h
    simpa [g, d, pow_two] using h
""",
    "Taylor-bound reverse square normalization",
)
