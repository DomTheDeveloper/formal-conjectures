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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 486: the formal statement is false even with positive moduli

`FormalConjectures/ErdosProblems/486.lean` states:

```
theorem erdos_486 : answer(sorry) ↔
    ∀ X : (n : ℕ) → Set (ZMod n), ∃ d, {m : ℕ | ∀ n, (m : ZMod n) ∉ X n}.HasLogDensity d
```

The file `workspace/claude/Erdos486.lean` proves that the right-hand side is
false, by exploiting the modulus `n = 0` (`ZMod 0 = ℤ`, so a single set `X 0`
can exclude an arbitrary subset of `ℕ`).  The accompanying report claimed that
restricting the quantification to moduli `n ≥ 1` would repair the
formalization.  **This file proves that claim is insufficient.**  The genuine
Erdős problem (erdosproblems.com/486) sieves an integer `m` only by the
congruence classes of the moduli *smaller than `m`* (`B = {m : m ≢ x (mod n)
for all n < m, x ∈ X_n}`); the formalization lacks that `m > n` guard.
Without it a single huge modulus `n ≫ m` can pin down `m` individually, and
the right-hand side remains false even when `X 0` is forced to be empty:

`theorem erdos_486_rhs_false_pos_moduli :
    ¬ (∀ X : (n : ℕ) → Set (ZMod n), (∀ n, n = 0 → X n = ∅) →
        ∃ d, {m : ℕ | ∀ n, (m : ZMod n) ∉ X n}.HasLogDensity d)`

## The construction

Let `a j = 2 ^ 10 ^ j`, `b j = 2 ^ (2 * 10 ^ j)` and `nMod j = a (j + 1)`.
The family `Xfam` puts, in the single modulus `nMod j`, the residue classes of
the block `[a j, b j)`; every other modulus (including `0`) gets `∅`.  Since
`b j < nMod j`, the surviving set `B` is exactly the complement of the union
over `j` of the block `[a j, b j)` together with all its translates by
positive multiples of `nMod j`.

* At the top of block `j` the whole block `[a j, b j)` (a positive proportion
  of the logarithmic mass) has just been removed, so the log-density partial
  sum is `≤ 0.6`.
* Just below `a (j + 1)`, the removed mass consists of the blocks `i ≤ j`
  (log-mass `≲ (10/9) · 10 ^ j · log 2`, small compared to
  `log (a (j+1)) = 10 · 10 ^ j · log 2`) plus all translates, whose total mass
  is `≤ (∑ i, b i / nMod i) · H X ≤ (1/128) · H X` because
  `b i / nMod i = 2 ^ (-8 · 10 ^ i)`.  Hence the partial sum is `≥ 0.8`.

`0.8 > 0.6`, so the partial sums oscillate and no logarithmic density exists.

## What this does and does not show

This shows the formal statement of Erdős 486 must be answered `False` even
after excluding the degenerate modulus `n = 0`: a faithful formalization must
also incorporate the `m > n` guard from the original problem.  It does **not**
resolve the actual Erdős problem 486 (with the `m > n` guard), which remains
open.
-/

open Filter Finset Real Topology

namespace Erdos486Strong

/-! ## Block parameters

Block `j` is `[a j, b j)`; it is sieved out using the single modulus
`nMod j = a (j + 1)`, which is vastly larger than `b j`. -/

/-- Lower endpoint of the `j`-th block. -/
def a (j : ℕ) : ℕ := 2 ^ (10 ^ j)

/-- Upper endpoint (exclusive) of the `j`-th block. -/
def b (j : ℕ) : ℕ := 2 ^ (2 * 10 ^ j)

/-- The modulus used to kill block `j`. -/
def nMod (j : ℕ) : ℕ := a (j + 1)

lemma two_le_a (j : ℕ) : 2 ≤ a j := by
  have h : 0 < 10 ^ j := by positivity
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (10 ^ j) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma a_lt_b (j : ℕ) : a j < b j := by
  apply Nat.pow_lt_pow_right (by norm_num)
  have : 0 < 10 ^ j := by positivity
  omega

lemma b_lt_nMod (j : ℕ) : b j < nMod j := by
  apply Nat.pow_lt_pow_right (by norm_num)
  have h : 0 < 10 ^ j := by positivity
  have h2 : 10 ^ (j + 1) = 10 * 10 ^ j := by ring
  omega

lemma a_mono : Monotone a := by
  intro i j hij
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hij)

lemma log_a (j : ℕ) : Real.log (a j) = 10 ^ j * Real.log 2 := by
  rw [a]; push_cast; rw [Real.log_pow]; push_cast; ring

lemma log_b (j : ℕ) : Real.log (b j) = 2 * 10 ^ j * Real.log 2 := by
  rw [b]; push_cast; rw [Real.log_pow]; push_cast; ring

lemma log_two_lb : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-! ## Harmonic sum notation and block-sum estimates -/

/-- Real harmonic partial sum `∑_{k=1}^{n} 1/k`, written as a sum over `Ioc 0 n`. -/
noncomputable def H (n : ℕ) : ℝ := ∑ k ∈ Ioc 0 n, (k : ℝ)⁻¹

lemma H_eq_harmonic (n : ℕ) : H n = (harmonic n : ℝ) := by
  rw [harmonic_eq_sum_Icc, H]
  push_cast
  congr 1

lemma H_le (n : ℕ) : H n ≤ 1 + Real.log n := by
  rw [H_eq_harmonic]; exact harmonic_le_one_add_log n

lemma le_H (n : ℕ) : Real.log (n + 1) ≤ H n := by
  rw [H_eq_harmonic]
  have := log_add_one_le_harmonic n
  push_cast at this
  exact this

lemma H_nonneg (n : ℕ) : 0 ≤ H n := by
  rw [H]; exact Finset.sum_nonneg fun k _ => by positivity

/-- Sum of reciprocals over a block `Ico p q` (with `1 ≤ p ≤ q`) as a
difference of harmonic sums. -/
lemma sum_Ico_inv (p q : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∑ k ∈ Finset.Ico p q, (k : ℝ)⁻¹ = H (q - 1) - H (p - 1) := by
  have h1 : Finset.Ico p q = Finset.Ioc (p - 1) (q - 1) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
  have h2 : H (p - 1) + ∑ k ∈ Finset.Ioc (p - 1) (q - 1), (k : ℝ)⁻¹ = H (q - 1) := by
    rw [H, H]
    exact Finset.sum_Ioc_consecutive _ (by omega) (by omega)
  rw [h1]; linarith

/-- The reciprocal sum over `Iic n` equals the harmonic sum (the `k = 0` term
vanishes). -/
lemma sum_Iic_inv (n : ℕ) : ∑ k ∈ Finset.Iic n, (k : ℝ)⁻¹ = H n := by
  have h : Finset.Iic n = insert 0 (Finset.Ioc 0 n) := by
    ext k; simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Ioc]; omega
  rw [h, Finset.sum_insert (by simp)]
  simp [H]

/-- The harmonic sum as a sum over `range`. -/
lemma H_eq_sum_range (n : ℕ) : H n = ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ)⁻¹ := by
  rw [H]
  have h : Finset.Ioc 0 n = Finset.Ico 1 (n + 1) := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
  rw [h, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun k _ => by rw [Nat.add_comm 1 k]

/-- The sum of reciprocals over block `j` is at least `10^j log 2 - 1`. -/
lemma block_sum_lower (j : ℕ) :
    10 ^ j * Real.log 2 - 1 ≤ ∑ k ∈ Finset.Ico (a j) (b j), (k : ℝ)⁻¹ := by
  rw [sum_Ico_inv _ _ (by have := two_le_a j; omega) (a_lt_b j).le]
  have h1 : Real.log (b j) ≤ H (b j - 1) := by
    have := le_H (b j - 1)
    have hb : 1 ≤ b j := (two_le_a j).trans (a_lt_b j).le |>.trans' (by norm_num)
    rwa [show ((b j - 1 : ℕ) : ℝ) + 1 = (b j : ℝ) by
      have : 2 ≤ b j := (two_le_a j).trans (a_lt_b j).le
      push_cast [Nat.cast_sub (by omega : 1 ≤ b j)]; ring] at this
  have h2 : H (a j - 1) ≤ 1 + Real.log (a j) := by
    have := H_le (a j - 1)
    have ha : 2 ≤ a j := two_le_a j
    calc H (a j - 1) ≤ 1 + Real.log (a j - 1 : ℕ) := this
      _ ≤ 1 + Real.log (a j) := by
          have h1 : (1 : ℝ) ≤ ((a j - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ a j - 1)
          have h2 : ((a j - 1 : ℕ) : ℝ) ≤ (a j : ℝ) := by
            exact_mod_cast (by omega : a j - 1 ≤ a j)
          have := Real.log_le_log (by linarith) h2
          linarith
  have := sub_le_sub h1 h2
  rw [log_b, log_a] at this
  linarith

/-- The sum of reciprocals over block `j` is at most `1 + 10^j log 2`. -/
lemma block_sum_upper (j : ℕ) :
    ∑ k ∈ Finset.Ico (a j) (b j), (k : ℝ)⁻¹ ≤ 1 + 10 ^ j * Real.log 2 := by
  rw [sum_Ico_inv _ _ (by have := two_le_a j; omega) (a_lt_b j).le]
  have hb2 : 2 ≤ b j := (two_le_a j).trans (a_lt_b j).le
  have h1 : H (b j - 1) ≤ 1 + Real.log (b j) := by
    calc H (b j - 1) ≤ 1 + Real.log (b j - 1 : ℕ) := H_le _
      _ ≤ 1 + Real.log (b j) := by
          have h1' : (1 : ℝ) ≤ ((b j - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ b j - 1)
          have h2' : ((b j - 1 : ℕ) : ℝ) ≤ (b j : ℝ) := by
            exact_mod_cast (by omega : b j - 1 ≤ b j)
          have := Real.log_le_log (by linarith) h2'
          linarith
  have h2 : Real.log (a j) ≤ H (a j - 1) := by
    have := le_H (a j - 1)
    have ha : 2 ≤ a j := two_le_a j
    rwa [show ((a j - 1 : ℕ) : ℝ) + 1 = (a j : ℝ) by
      push_cast [Nat.cast_sub (by omega : 1 ≤ a j)]; ring] at this
  have := sub_le_sub h1 h2
  rw [log_b, log_a] at this
  linarith

/-! ## The family of excluded residues and the surviving set `B` -/

/-- The family of excluded residue classes: in modulus `nMod j` we exclude the
residues of the block `[a j, b j)`; all other moduli (in particular `0`)
exclude nothing. -/
def Xfam (n : ℕ) : Set (ZMod n) :=
  {z : ZMod n | ∃ j, n = nMod j ∧ ∃ r ∈ Set.Ico (a j) (b j), z = (r : ZMod n)}

/-- The set of naturals avoiding every excluded residue class. -/
def B : Set ℕ := {m : ℕ | ∀ n, (m : ZMod n) ∉ Xfam n}

/-- The modulus `0` excludes nothing: the `n = 0` loophole is plugged. -/
lemma Xfam_zero : Xfam 0 = ∅ := by
  ext z
  simp only [Xfam, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  rintro j ⟨hj, -⟩
  have h2 := two_le_a (j + 1)
  rw [nMod] at hj
  omega

/-- **Key characterization**: `m` survives iff for every `j` the residue of
`m` mod `nMod j` misses the block `[a j, b j)`. -/
lemma mem_B_iff (m : ℕ) :
    m ∈ B ↔ ∀ i, ¬ (a i ≤ m % nMod i ∧ m % nMod i < b i) := by
  constructor
  · intro hm i hi
    exact hm (nMod i)
      ⟨i, rfl, m % nMod i, Set.mem_Ico.mpr hi, (ZMod.natCast_mod m (nMod i)).symm⟩
  · rintro h n ⟨j, rfl, r, hr, heq⟩
    rw [Set.mem_Ico] at hr
    have hmod : m ≡ r [MOD nMod j] := (ZMod.natCast_eq_natCast_iff m r (nMod j)).mp heq
    have hrlt : r < nMod j := lt_trans hr.2 (b_lt_nMod j)
    have hmr : m % nMod j = r := by
      have h2 : m % nMod j = r % nMod j := hmod
      rwa [Nat.mod_eq_of_lt hrlt] at h2
    exact h j ⟨hmr ▸ hr.1, hmr ▸ hr.2⟩

/-- Every element of block `j` itself is killed (its residue mod `nMod j` is
itself, since `b j < nMod j`). -/
lemma block_killed {j m : ℕ} (h1 : a j ≤ m) (h2 : m < b j) : m ∉ B := fun hm => by
  have hmod : m % nMod j = m := Nat.mod_eq_of_lt (h2.trans (b_lt_nMod j))
  exact (mem_B_iff m).mp hm j (by rw [hmod]; exact ⟨h1, h2⟩)

/-! ## The log-density partial sums of `B` -/

open Classical in
/-- The quantity whose convergence `B.HasLogDensity d` asserts. -/
noncomputable def f (n : ℕ) : ℝ := ∑ k ≤ n with k ∈ B, (k : ℝ)⁻¹ / Real.log n

lemma hasLogDensity_iff {d : ℝ} : B.HasLogDensity d ↔ Tendsto f atTop (𝓝 d) := Iff.rfl

/-! ## Upper bound at the top of a block -/

/-- At the top of block `j`, the log-density partial sum has dropped to `≤ 0.6`:
the whole block `[a j, b j)` has just been removed. -/
lemma f_upper_top {j : ℕ} (hj : 2 ≤ j) : f (b j - 1) ≤ 0.6 := by
  classical
  set n := b j - 1 with hn
  have hb4 : 4 ≤ b j := by
    have h : 0 < 10 ^ j := by positivity
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * 10 ^ j) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = b j := rfl
  have hn3 : 3 ≤ n := by omega
  have hden_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hsubset : (Finset.Iic n).filter (fun m => m ∈ B) ⊆
      Finset.Iic n \ Finset.Ico (a j) (b j) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Finset.mem_sdiff]
    refine ⟨hk.1, fun hmem => ?_⟩
    rw [Finset.mem_Ico] at hmem
    exact block_killed hmem.1 hmem.2 hk.2
  have hIco_sub : Finset.Ico (a j) (b j) ⊆ Finset.Iic n := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_Iic]
    omega
  have hnum : ∑ k ∈ (Finset.Iic n).filter (fun m => m ∈ B), (k : ℝ)⁻¹ ≤
      H n - (10 ^ j * Real.log 2 - 1) := by
    have h1 : ∑ k ∈ (Finset.Iic n).filter (fun m => m ∈ B), (k : ℝ)⁻¹ ≤
        ∑ k ∈ Finset.Iic n \ Finset.Ico (a j) (b j), (k : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun k _ _ => by positivity
    have h2 : ∑ k ∈ Finset.Iic n \ Finset.Ico (a j) (b j), (k : ℝ)⁻¹ =
        (∑ k ∈ Finset.Iic n, (k : ℝ)⁻¹) - ∑ k ∈ Finset.Ico (a j) (b j), (k : ℝ)⁻¹ :=
      Finset.sum_sdiff_eq_sub hIco_sub
    rw [sum_Iic_inv] at h2
    have h3 := block_sum_lower j
    linarith
  have hLle : Real.log (n : ℝ) ≤ 2 * 10 ^ j * Real.log 2 := by
    have h1 : Real.log (n : ℝ) ≤ Real.log ((b j : ℕ) : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
      exact_mod_cast (by omega : n ≤ b j)
    rwa [log_b] at h1
  have hHle : H n ≤ 1 + Real.log (n : ℝ) := H_le n
  have hE : (69 : ℝ) ≤ 10 ^ j * Real.log 2 := by
    have h100 : (100 : ℝ) ≤ 10 ^ j := by
      calc (100 : ℝ) = 10 ^ 2 := by norm_num
        _ ≤ 10 ^ j := pow_le_pow_right₀ (by norm_num) hj
    have := mul_le_mul h100 log_two_lb.le (by norm_num) (by positivity)
    linarith
  have hf : f n = (∑ k ∈ (Finset.Iic n).filter (fun m => m ∈ B), (k : ℝ)⁻¹) /
      Real.log (n : ℝ) := by
    rw [f, Finset.sum_div]
  rw [hf, div_le_iff₀ hden_pos]
  linarith [hnum, hLle, hHle, hE]

/-! ## Lower bound just before the next block

Below `a (j + 1)` the removed set is covered by the blocks `i ≤ j` together
with their translates by positive multiples of `nMod i`; the translates carry
a negligible share of the logarithmic mass because `b i / nMod i ≤ 2⁻¹ ^ (8 + i)`. -/

/-- Sum of a nonnegative function over a `biUnion` is at most the double sum. -/
lemma sum_biUnion_le {α β : Type*} [DecidableEq β] {s : Finset α} {t : α → Finset β}
    {g : β → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ∑ x ∈ s.biUnion t, g x ≤ ∑ i ∈ s, ∑ x ∈ t i, g x := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.cons_eq_insert, Finset.biUnion_insert, Finset.sum_insert hi]
    have hui := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := g)
    have hnn : 0 ≤ ∑ x ∈ t i ∩ s.biUnion t, g x := Finset.sum_nonneg fun x _ => hg x
    linarith [ih]

/-- The `k`-th translate of block `i` has reciprocal sum at most
`(b i / nMod i) · k⁻¹` (for `k ≥ 1`): it has fewer than `b i` elements, all of
size at least `k * nMod i`. -/
lemma translate_sum_le (i k : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Finset.Ico (k * nMod i + a i) (k * nMod i + b i), (m : ℝ)⁻¹ ≤
      (b i : ℝ) / (nMod i : ℝ) * ((k : ℕ) : ℝ)⁻¹ := by
  have hpos : 0 < nMod i := lt_of_lt_of_le (by norm_num) (two_le_a (i + 1))
  have hkn : 0 < k * nMod i := Nat.mul_pos hk hpos
  have hbound : ∀ m ∈ Finset.Ico (k * nMod i + a i) (k * nMod i + b i),
      (m : ℝ)⁻¹ ≤ ((k * nMod i : ℕ) : ℝ)⁻¹ := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have h1 : k * nMod i ≤ m := le_trans (Nat.le_add_right _ _) hm.1
    exact inv_anti₀ (by exact_mod_cast hkn) (by exact_mod_cast h1)
  have hcard : (Finset.Ico (k * nMod i + a i) (k * nMod i + b i)).card ≤ b i := by
    rw [Nat.card_Ico, Nat.add_sub_add_left]
    exact Nat.sub_le _ _
  calc ∑ m ∈ Finset.Ico (k * nMod i + a i) (k * nMod i + b i), (m : ℝ)⁻¹
      ≤ (Finset.Ico (k * nMod i + a i) (k * nMod i + b i)).card •
          ((k * nMod i : ℕ) : ℝ)⁻¹ := Finset.sum_le_card_nsmul _ _ _ hbound
    _ ≤ (b i : ℝ) * ((k * nMod i : ℕ) : ℝ)⁻¹ := by
        rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
    _ = (b i : ℝ) / (nMod i : ℝ) * ((k : ℕ) : ℝ)⁻¹ := by
        push_cast
        rw [mul_inv, div_eq_mul_inv]
        ring

/-- All translates of block `i` (including the block itself, `k = 0`) up to
level `N` contribute at most `(1 + 10^i log 2) + (b i / nMod i) · H N`. -/
lemma inner_sum_le (i N : ℕ) :
    ∑ k ∈ Finset.range (N + 1),
        ∑ m ∈ Finset.Ico (k * nMod i + a i) (k * nMod i + b i), (m : ℝ)⁻¹ ≤
      (1 + 10 ^ i * Real.log 2) + (b i : ℝ) / (nMod i : ℝ) * H N := by
  have h0 : ∑ m ∈ Finset.Ico (0 * nMod i + a i) (0 * nMod i + b i), (m : ℝ)⁻¹ ≤
      1 + 10 ^ i * Real.log 2 := by
    simpa using block_sum_upper i
  have h1 : ∑ k ∈ Finset.range N,
      ∑ m ∈ Finset.Ico ((k + 1) * nMod i + a i) ((k + 1) * nMod i + b i), (m : ℝ)⁻¹ ≤
      (b i : ℝ) / (nMod i : ℝ) * H N := by
    rw [H_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => translate_sum_le i (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  calc ∑ k ∈ Finset.range (N + 1),
        ∑ m ∈ Finset.Ico (k * nMod i + a i) (k * nMod i + b i), (m : ℝ)⁻¹
      = (∑ k ∈ Finset.range N,
          ∑ m ∈ Finset.Ico ((k + 1) * nMod i + a i) ((k + 1) * nMod i + b i), (m : ℝ)⁻¹)
        + ∑ m ∈ Finset.Ico (0 * nMod i + a i) (0 * nMod i + b i), (m : ℝ)⁻¹ :=
        Finset.sum_range_succ' _ N
    _ ≤ (b i : ℝ) / (nMod i : ℝ) * H N + (1 + 10 ^ i * Real.log 2) := add_le_add h1 h0
    _ = (1 + 10 ^ i * Real.log 2) + (b i : ℝ) / (nMod i : ℝ) * H N := by ring

/-- The block/modulus ratio decays doubly exponentially; crude bound
`b i / nMod i ≤ 2⁻¹ ^ (8 + i)`. -/
lemma ratio_le (i : ℕ) : (b i : ℝ) / (nMod i : ℝ) ≤ (2 : ℝ)⁻¹ ^ (8 + i) := by
  have hkey : nMod i = b i * 2 ^ (8 * 10 ^ i) := by
    rw [nMod, a, b, ← pow_add]
    congr 1
    rw [pow_succ]
    ring
  have hb_pos : (0 : ℝ) < (b i : ℝ) := by
    have h : 0 < b i := by rw [b]; positivity
    exact_mod_cast h
  have heq : (b i : ℝ) / (nMod i : ℝ) = (2 : ℝ)⁻¹ ^ (8 * 10 ^ i) := by
    rw [hkey]
    push_cast
    rw [div_mul_eq_div_div, div_self hb_pos.ne', one_div, ← inv_pow]
  rw [heq]
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  have h1 : i + 1 ≤ 10 ^ i :=
    Nat.succ_le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left (by norm_num) i))
  omega

/-- The total block/modulus ratio over all blocks is at most `1/128`. -/
lemma ratio_sum_le (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (b i : ℝ) / (nMod i : ℝ) ≤ 1 / 128 := by
  calc ∑ i ∈ Finset.range (j + 1), (b i : ℝ) / (nMod i : ℝ)
      ≤ ∑ i ∈ Finset.range (j + 1), (2 : ℝ)⁻¹ ^ (8 + i) :=
        Finset.sum_le_sum fun i _ => ratio_le i
    _ = (2 : ℝ)⁻¹ ^ 8 * ∑ i ∈ Finset.range (j + 1), (2 : ℝ)⁻¹ ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => pow_add _ 8 i
    _ ≤ (2 : ℝ)⁻¹ ^ 8 * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [geom_sum_eq (by norm_num : (2 : ℝ)⁻¹ ≠ 1)]
        have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (j + 1) := by positivity
        rw [div_le_iff_of_neg (by norm_num : (2 : ℝ)⁻¹ - 1 < 0)]
        linarith
    _ = 1 / 128 := by norm_num

/-- Linear growth is dominated by `10 ^ j` (crude form used below). -/
lemma linear_le_pow (k : ℕ) : 2 * (k + 1) + 6 ≤ 10 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ m ih =>
    have h : 10 ^ (m + 2) = 10 * 10 ^ (m + 1) := by ring
    omega

open Classical in
/-- Below `a (j + 1)`, everything removed lies in a translate of some block
`i ≤ j` by a multiple `k ≤ M` of `nMod i`. -/
lemma removed_cover (j M : ℕ) (hM : M < a (j + 1)) :
    (Finset.Iic M).filter (fun m => ¬ m ∈ B) ⊆
      (Finset.range (j + 1)).biUnion fun i =>
        (Finset.range (M + 1)).biUnion fun k =>
          Finset.Ico (k * nMod i + a i) (k * nMod i + b i) := by
  intro m hm
  rw [Finset.mem_filter, Finset.mem_Iic] at hm
  obtain ⟨hmM, hmB⟩ := hm
  rw [mem_B_iff] at hmB
  push_neg at hmB
  obtain ⟨i, hi⟩ := hmB
  have hij : i < j + 1 := by
    by_contra hij
    push_neg at hij
    have h1 : a (j + 1) ≤ a i := a_mono (by omega)
    have h3 : a i ≤ m := le_trans hi.1 (Nat.mod_le m _)
    omega
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hij, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨m / nMod i, Finset.mem_range.mpr ?_, ?_⟩
  · exact Nat.lt_succ_of_le (le_trans (Nat.div_le_self m _) hmM)
  · rw [Finset.mem_Ico]
    have key : m / nMod i * nMod i + m % nMod i = m := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod m (nMod i)
    constructor
    · calc m / nMod i * nMod i + a i
          ≤ m / nMod i * nMod i + m % nMod i := Nat.add_le_add_left hi.1 _
        _ = m := key
    · calc m = m / nMod i * nMod i + m % nMod i := key.symm
        _ < m / nMod i * nMod i + b i := Nat.add_lt_add_left hi.2 _

/-- Total reciprocal sum of the per-block contributions. -/
lemma outer_sum_le (j N : ℕ) (hH : 0 ≤ H N) :
    ∑ i ∈ Finset.range (j + 1),
        ((1 + 10 ^ i * Real.log 2) + (b i : ℝ) / (nMod i : ℝ) * H N) ≤
      ((j : ℝ) + 1) + 10 / 9 * 10 ^ j * Real.log 2 + 1 / 128 * H N := by
  have hsplit : ∑ i ∈ Finset.range (j + 1),
      ((1 + 10 ^ i * Real.log 2) + (b i : ℝ) / (nMod i : ℝ) * H N)
      = (∑ i ∈ Finset.range (j + 1), ((1 : ℝ) + 10 ^ i * Real.log 2))
        + ∑ i ∈ Finset.range (j + 1), (b i : ℝ) / (nMod i : ℝ) * H N :=
    Finset.sum_add_distrib
  have hconst : ∑ i ∈ Finset.range (j + 1), ((1 : ℝ) + 10 ^ i * Real.log 2)
      = ((j : ℝ) + 1) + (∑ i ∈ Finset.range (j + 1), (10 : ℝ) ^ i) * Real.log 2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      ← Finset.sum_mul]
    push_cast
    ring
  have hgeom : ∑ i ∈ Finset.range (j + 1), (10 : ℝ) ^ i ≤ 10 / 9 * 10 ^ j := by
    rw [geom_sum_eq (by norm_num : (10 : ℝ) ≠ 1)]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 - 1)]
    have hrw : (10 : ℝ) ^ (j + 1) = 10 * 10 ^ j := by ring
    linarith
  have h1 : (∑ i ∈ Finset.range (j + 1), (10 : ℝ) ^ i) * Real.log 2 ≤
      10 / 9 * 10 ^ j * Real.log 2 :=
    mul_le_mul_of_nonneg_right hgeom (Real.log_nonneg (by norm_num))
  have h2 : ∑ i ∈ Finset.range (j + 1), (b i : ℝ) / (nMod i : ℝ) * H N ≤ 1 / 128 * H N := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (ratio_sum_le j) hH
  linarith [hsplit, hconst, h1, h2]

/-- Just before block `j + 1`, the log-density partial sum has recovered to `≥ 0.8`. -/
lemma f_lower_pre {j : ℕ} (hj : 2 ≤ j) : 0.8 ≤ f (a (j + 1) - 1) := by
  classical
  set n := a (j + 1) - 1 with hn
  have ha2 : 2 ≤ a (j + 1) := two_le_a _
  have h10 : 3 ≤ 10 ^ (j + 1) := by
    calc 3 ≤ 10 ^ 1 := by norm_num
      _ ≤ 10 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have ha8 : 8 ≤ a (j + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (10 ^ (j + 1)) := Nat.pow_le_pow_right (by norm_num) h10
      _ = a (j + 1) := rfl
  have hn7 : 7 ≤ n := by omega
  have hden_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hLle : Real.log (n : ℝ) ≤ 10 * 10 ^ j * Real.log 2 := by
    have h1 : Real.log (n : ℝ) ≤ Real.log ((a (j + 1) : ℕ) : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
      exact_mod_cast (by omega : n ≤ a (j + 1))
    rw [log_a] at h1
    calc Real.log (n : ℝ) ≤ (10 : ℝ) ^ (j + 1) * Real.log 2 := h1
      _ = 10 * 10 ^ j * Real.log 2 := by ring
  have hHge : 10 * 10 ^ j * Real.log 2 ≤ H n := by
    have h1 := le_H n
    have hcast : ((n : ℕ) : ℝ) + 1 = ((a (j + 1) : ℕ) : ℝ) := by
      rw [hn]
      push_cast [Nat.cast_sub (by omega : 1 ≤ a (j + 1))]
      ring
    rw [hcast, log_a] at h1
    calc (10 : ℝ) * 10 ^ j * Real.log 2 = 10 ^ (j + 1) * Real.log 2 := by ring
      _ ≤ H n := h1
  have hH_nonneg : 0 ≤ H n := H_nonneg n
  have hrem : ∑ k ∈ (Finset.Iic n).filter (fun m => ¬ m ∈ B), (k : ℝ)⁻¹ ≤
      ((j : ℝ) + 1) + 10 / 9 * 10 ^ j * Real.log 2 + 1 / 128 * H n := by
    calc ∑ k ∈ (Finset.Iic n).filter (fun m => ¬ m ∈ B), (k : ℝ)⁻¹
        ≤ ∑ k ∈ (Finset.range (j + 1)).biUnion (fun i =>
            (Finset.range (n + 1)).biUnion fun k =>
              Finset.Ico (k * nMod i + a i) (k * nMod i + b i)), (k : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg (removed_cover j n (by omega))
            fun k _ _ => by positivity
      _ ≤ ∑ i ∈ Finset.range (j + 1), ∑ x ∈ (Finset.range (n + 1)).biUnion (fun k =>
            Finset.Ico (k * nMod i + a i) (k * nMod i + b i)), (x : ℝ)⁻¹ :=
          sum_biUnion_le fun x => by positivity
      _ ≤ ∑ i ∈ Finset.range (j + 1),
            ((1 + 10 ^ i * Real.log 2) + (b i : ℝ) / (nMod i : ℝ) * H n) := by
          apply Finset.sum_le_sum
          intro i _
          calc ∑ x ∈ (Finset.range (n + 1)).biUnion (fun k =>
                Finset.Ico (k * nMod i + a i) (k * nMod i + b i)), (x : ℝ)⁻¹
              ≤ ∑ k ∈ Finset.range (n + 1),
                  ∑ x ∈ Finset.Ico (k * nMod i + a i) (k * nMod i + b i), (x : ℝ)⁻¹ :=
                sum_biUnion_le fun x => by positivity
            _ ≤ _ := inner_sum_le i n
      _ ≤ ((j : ℝ) + 1) + 10 / 9 * 10 ^ j * Real.log 2 + 1 / 128 * H n :=
          outer_sum_le j n hH_nonneg
  have hsplit : (∑ k ∈ (Finset.Iic n).filter (fun m => m ∈ B), (k : ℝ)⁻¹)
      + ∑ k ∈ (Finset.Iic n).filter (fun m => ¬ m ∈ B), (k : ℝ)⁻¹ = H n := by
    rw [Finset.sum_filter_add_sum_filter_not, sum_Iic_inv]
  have hPL : 0.69 * (10 : ℝ) ^ j ≤ (10 : ℝ) ^ j * Real.log 2 := by
    have := mul_le_mul_of_nonneg_left log_two_lb.le (by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ j)
    linarith
  have hP : 2 * (j : ℝ) + 6 ≤ (10 : ℝ) ^ j := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have := linear_le_pow k
    exact_mod_cast this
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hf : f n = (∑ k ∈ (Finset.Iic n).filter (fun m => m ∈ B), (k : ℝ)⁻¹) /
      Real.log (n : ℝ) := by
    rw [f, Finset.sum_div]
  rw [hf, le_div_iff₀ hden_pos]
  linarith [hsplit, hrem, hHge, hLle, hPL, hP, hjR, hH_nonneg]

/-! ## `B` has no logarithmic density -/

theorem B_not_hasLogDensity (d : ℝ) : ¬ B.HasLogDensity d := by
  intro hd
  rw [hasLogDensity_iff] at hd
  have hidx1 : Tendsto (fun j => b j - 1) atTop atTop := by
    apply tendsto_atTop_mono (fun j => ?_) tendsto_id
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 2 ^ j ≤ b j := Nat.pow_le_pow_right (by norm_num) (by
      have h3 : j ≤ 10 ^ j := (Nat.lt_two_pow_self).le.trans
        (Nat.pow_le_pow_left (by norm_num) j)
      omega)
    simp only [id_eq]
    omega
  have hidx2 : Tendsto (fun j => a (j + 1) - 1) atTop atTop := by
    apply tendsto_atTop_mono (fun j => ?_) tendsto_id
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 2 ^ j ≤ a (j + 1) := Nat.pow_le_pow_right (by norm_num) (by
      have h3 : j ≤ 10 ^ j := (Nat.lt_two_pow_self).le.trans
        (Nat.pow_le_pow_left (by norm_num) j)
      have h4 : 10 ^ j ≤ 10 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
    simp only [id_eq]
    omega
  have hcomp1 : Tendsto (fun j => f (b j - 1)) atTop (𝓝 d) := hd.comp hidx1
  have hcomp2 : Tendsto (fun j => f (a (j + 1) - 1)) atTop (𝓝 d) := hd.comp hidx2
  have hd1 : d ≤ (0.6 : ℝ) :=
    le_of_tendsto hcomp1 (Filter.eventually_atTop.mpr ⟨2, fun j hj => f_upper_top hj⟩)
  have hd2 : (0.8 : ℝ) ≤ d :=
    ge_of_tendsto hcomp2 (Filter.eventually_atTop.mpr ⟨2, fun j hj => f_lower_pre hj⟩)
  norm_num at hd1 hd2
  linarith

/-! ## Main theorem -/

/-- **The right-hand side of the formalized Erdős Problem 486 is false even
with the `n = 0` modulus forced to be vacuous.**  Hence merely restricting the
formalization of erdosproblems.com/486 to positive moduli does *not* make it
faithful: the original problem's guard that a modulus `n` only constrains
integers `m > n` is essential, since without it a modulus far larger than `m`
can pin down `m` individually.  (The genuine Erdős problem, with the `m > n`
guard, remains open.) -/
theorem erdos_486_rhs_false_pos_moduli :
    ¬ (∀ X : (n : ℕ) → Set (ZMod n), (∀ n, n = 0 → X n = ∅) →
        ∃ d, {m : ℕ | ∀ n, (m : ZMod n) ∉ X n}.HasLogDensity d) := by
  intro Hyp
  obtain ⟨d, hd⟩ := Hyp Xfam (fun n hn => by subst hn; exact Xfam_zero)
  exact B_not_hasLogDensity d hd

end Erdos486Strong
