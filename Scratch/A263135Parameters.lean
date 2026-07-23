import Scratch.A263135Upper

namespace OeisA263135

/-- Balanced side parameters for a perimeter parameter `r`. -/
def balancedA (r : ℕ) : ℕ := r / 3

def balancedB (r : ℕ) : ℕ := (r + 1) / 3

def balancedC (r : ℕ) : ℕ := (r + 2) / 3

/-- The three balanced parameters sum to `r`. -/
theorem balanced_sum (r : ℕ) :
    balancedA r + balancedB r + balancedC r = r := by
  unfold balancedA balancedB balancedC
  omega

/-- The balanced parameters are weakly increasing. -/
theorem balanced_order (r : ℕ) :
    balancedA r ≤ balancedB r ∧ balancedB r ≤ balancedC r := by
  unfold balancedA balancedB balancedC
  omega

/-- Pair-product sum of balanced parameters. -/
theorem balanced_pair_sum (r : ℕ) :
    balancedA r * balancedB r + balancedB r * balancedC r +
      balancedC r * balancedA r = r ^ 2 / 3 := by
  unfold balancedA balancedB balancedC
  let q := r / 3
  have hmod : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hmod with h | h | h
  · have hr : r = 3 * q := by dsimp [q]; omega
    have h0 : r / 3 = q := rfl
    have h1 : (r + 1) / 3 = q := by dsimp [q]; omega
    have h2 : (r + 2) / 3 = q := by dsimp [q]; omega
    have hs : r ^ 2 / 3 = 3 * q ^ 2 := by
      rw [hr]
      ring_nf
      omega
    rw [h0, h1, h2, hs]
    ring
  · have hr : r = 3 * q + 1 := by dsimp [q]; omega
    have h0 : r / 3 = q := rfl
    have h1 : (r + 1) / 3 = q := by dsimp [q]; omega
    have h2 : (r + 2) / 3 = q + 1 := by dsimp [q]; omega
    have hs : r ^ 2 / 3 = 3 * q ^ 2 + 2 * q := by
      rw [hr]
      ring_nf
      omega
    rw [h0, h1, h2, hs]
    ring
  · have hr : r = 3 * q + 2 := by dsimp [q]; omega
    have h0 : r / 3 = q := rfl
    have h1 : (r + 1) / 3 = q + 1 := by dsimp [q]; omega
    have h2 : (r + 2) / 3 = q + 1 := by dsimp [q]; omega
    have hs : r ^ 2 / 3 = 3 * q ^ 2 + 4 * q + 1 := by
      rw [hr]
      ring_nf
      omega
    rw [h0, h1, h2, hs]
    ring

/-- Width of the available clipping corner. -/
theorem balanced_corner_width (r : ℕ) (hr : 3 ≤ r) :
    balancedA r + balancedB r - 1 =
      r ^ 2 / 3 - (r - 1) ^ 2 / 3 - 1 := by
  rw [← balanced_pair_sum r, ← balanced_pair_sum (r - 1)]
  unfold balancedA balancedB balancedC
  let q := r / 3
  have hmod : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases hmod with h | h | h
  · have hre : r = 3 * q := by dsimp [q]; omega
    have hq : 1 ≤ q := by omega
    have h0 : r / 3 = q := rfl
    have h1 : (r + 1) / 3 = q := by dsimp [q]; omega
    have h2 : (r + 2) / 3 = q := by dsimp [q]; omega
    have hp0 : (r - 1) / 3 = q - 1 := by dsimp [q]; omega
    have hp1 : (r - 1 + 1) / 3 = q := by dsimp [q]; omega
    have hp2 : (r - 1 + 2) / 3 = q := by
      have hnum : r - 1 + 2 = 3 * q + 1 := by omega
      rw [hnum]
      omega
    simp only [h0, h1, h2, hp0, hp1, hp2]
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    have hpoly :
        (q - 1) * q + q * q + q * (q - 1) + (q + q) =
          q * q + q * q + q * q := by
      rw [hk]
      simp
      ring
    omega
  · have hre : r = 3 * q + 1 := by dsimp [q]; omega
    have hq : 1 ≤ q := by omega
    have h0 : r / 3 = q := rfl
    have h1 : (r + 1) / 3 = q := by dsimp [q]; omega
    have h2 : (r + 2) / 3 = q + 1 := by dsimp [q]; omega
    have hp0 : (r - 1) / 3 = q := by dsimp [q]; omega
    have hp1 : (r - 1 + 1) / 3 = q := by dsimp [q]; omega
    have hp2 : (r - 1 + 2) / 3 = q := by dsimp [q]; omega
    simp only [h0, h1, h2, hp0, hp1, hp2]
    have hpoly :
        q * q + q * (q + 1) + (q + 1) * q =
          (q * q + q * q + q * q) + (q + q) := by ring
    omega
  · have hre : r = 3 * q + 2 := by dsimp [q]; omega
    have h0 : r / 3 = q := rfl
    have h1 : (r + 1) / 3 = q + 1 := by dsimp [q]; omega
    have h2 : (r + 2) / 3 = q + 1 := by dsimp [q]; omega
    have hp0 : (r - 1) / 3 = q := by dsimp [q]; omega
    have hp1 : (r - 1 + 1) / 3 = q := by dsimp [q]; omega
    have hp2 : (r - 1 + 2) / 3 = q + 1 := by dsimp [q]; omega
    simp only [h0, h1, h2, hp0, hp1, hp2]
    have hpoly :
        q * (q + 1) + (q + 1) * (q + 1) + (q + 1) * q =
          (q * q + q * (q + 1) + (q + 1) * q) + (q + q + 1) := by ring
    omega

/-- Positivity of the balanced side parameters once `r ≥ 3`. -/
theorem balanced_positive (r : ℕ) (hr : 3 ≤ r) :
    0 < balancedA r ∧ 0 < balancedB r ∧ 0 < balancedC r := by
  unfold balancedA balancedB balancedC
  omega

/-- The ceiling-square interval supplies ordered balanced parameters and a valid clipping budget. -/
theorem exists_balanced_clipping_parameters
    (n r : ℕ) (hn : 1 < n) (hr : IsNatCeilSqrt (3 * n) r) :
    ∃ a b c d : ℕ,
      0 < a ∧ 0 < b ∧ 0 < c ∧
      a ≤ b ∧ b ≤ c ∧
      a + b + c = r ∧
      a * b + b * c + c * a = n + d ∧
      d ≤ a + b - 1 := by
  have hr3 : 3 ≤ r := by
    by_contra h
    have hr2 : r ≤ 2 := by omega
    have hsquare : r ^ 2 ≤ 4 := by nlinarith
    have hn6 : 6 ≤ 3 * n := by omega
    have hupper := hr.2
    omega
  let a := balancedA r
  let b := balancedB r
  let c := balancedC r
  let M := r ^ 2 / 3
  have hM : a * b + b * c + c * a = M := by
    simpa [a, b, c, M] using balanced_pair_sum r
  have hnM : n ≤ M := by
    dsimp [M]
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
    simpa [mul_comm] using hr.2
  let d := M - n
  refine ⟨a, b, c, d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (balanced_positive r hr3).1
  · exact (balanced_positive r hr3).2.1
  · exact (balanced_positive r hr3).2.2
  · exact (balanced_order r).1
  · exact (balanced_order r).2
  · simpa [a, b, c] using balanced_sum r
  · dsimp [d]
    rw [hM]
    omega
  · have hlower : (r - 1) ^ 2 / 3 < n := by
      apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 3)).2
      simpa [mul_comm] using hr.1
    have hwidth : a + b - 1 = M - (r - 1) ^ 2 / 3 - 1 := by
      simpa [a, b, M] using balanced_corner_width r hr3
    change M - n ≤ a + b - 1
    rw [hwidth]
    have hsucc : (r - 1) ^ 2 / 3 + 1 ≤ n := by omega
    have hsub := Nat.sub_le_sub_left hsucc M
    omega

end OeisA263135
