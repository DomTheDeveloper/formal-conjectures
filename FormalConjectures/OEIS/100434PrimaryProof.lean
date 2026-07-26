/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.OEIS.«100434»

namespace OeisA100434

@[category API, AMS 11]
private theorem cAbs_four_step (n : ℕ) :
    cAbs (n + 4) = 6 * cAbs (n + 2) - cAbs n := by
  simp only [cAbs]
  ring

@[category API, AMS 11]
private theorem dHalfAbs_four_step (n : ℕ) :
    dHalfAbs (n + 4) = 6 * dHalfAbs (n + 2) - dHalfAbs n := by
  simp only [dHalfAbs]
  ring

@[category API, AMS 11]
private theorem parity_split_primary (n : ℕ) :
    (∃ k, n = 2 * k) ∨ ∃ k, n = 2 * k + 1 := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · exact Or.inl ⟨k, hk⟩
  · exact Or.inr ⟨k, hk⟩

@[category API, AMS 11]
private theorem h_even (k : ℕ) :
    h (2 * k) = (-1 : ℤ) ^ k * cAbs (2 * k + 1) := by
  rw [h, if_pos (by omega), c]
  rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, pow_succ]
  ring

@[category API, AMS 11]
private theorem h_odd (k : ℕ) :
    h (2 * k + 1) = 2 * ((-1 : ℤ) ^ k * dHalfAbs (2 * k + 1)) := by
  rw [h, if_neg (by omega), d]
  rw [show (2 * k + 1) / 2 = k by omega]

@[category API, AMS 11]
private theorem h_four_step (n : ℕ) :
    h (n + 4) = -6 * h (n + 2) - h n := by
  rcases parity_split_primary n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hc := cAbs_four_step (2 * k + 1)
    have hp1 : (-1 : ℤ) ^ (k + 1) = -((-1 : ℤ) ^ k) := by
      rw [pow_succ]
      ring
    have hp2 : (-1 : ℤ) ^ (k + 2) = (-1 : ℤ) ^ k := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, hp1]
      ring
    rw [show 2 * k + 4 = 2 * (k + 2) by omega,
      show 2 * k + 2 = 2 * (k + 1) by omega,
      h_even (k + 2), h_even (k + 1), h_even k]
    rw [show 2 * (k + 2) + 1 = (2 * k + 1) + 4 by omega,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
      hc, hp1, hp2]
    ring
  · have hd := dHalfAbs_four_step (2 * k + 1)
    have hp1 : (-1 : ℤ) ^ (k + 1) = -((-1 : ℤ) ^ k) := by
      rw [pow_succ]
      ring
    have hp2 : (-1 : ℤ) ^ (k + 2) = (-1 : ℤ) ^ k := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, hp1]
      ring
    rw [show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by omega,
      show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by omega,
      h_odd (k + 2), h_odd (k + 1), h_odd k]
    rw [show 2 * (k + 2) + 1 = (2 * k + 1) + 4 by omega,
      show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
      hd, hp1, hp2]
    ring

@[category API, AMS 11]
theorem a_eq_h (n : ℕ) : a n = h n := by
  apply Nat.strong_induction_on n
  intro n ih
  by_cases hn : n < 4
  · interval_cases n <;> norm_num [a, h, c, d, cAbs, dHalfAbs]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := by omega
    rw [a, ih (m + 2) (by omega), ih m (by omega), h_four_step]

@[category research solved, AMS 11]
theorem a100434_auxiliary_identities_primary (n : ℕ) :
    c n + d n = e n + f n ∧
    e n + f n = g n + a n ∧
    c n + d n = (-1 : ℤ) ^ (n + 1) * b n := by
  obtain ⟨h₁, h₂, h₃⟩ := a100434_auxiliary_identities n
  exact ⟨h₁, by simpa [a_eq_h n] using h₂, h₃⟩

end OeisA100434
