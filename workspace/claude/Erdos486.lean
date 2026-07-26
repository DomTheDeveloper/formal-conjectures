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
# Resolution of the formal statement of Erdős Problem 486

`FormalConjectures/ErdosProblems/486.lean` states:

```
theorem erdos_486 : answer(sorry) ↔
    ∀ X : (n : ℕ) → Set (ZMod n), ∃ d, {m : ℕ | ∀ n, (m : ZMod n) ∉ X n}.HasLogDensity d
```

Because the family `X` ranges over ALL moduli `n : ℕ` *including `n = 0`*, and
`ZMod 0 = ℤ` with the injective coercion `ℕ → ℤ`, the single set `X 0` can
exclude an arbitrary subset of `ℕ`: taking `X 0` to be the complement of the
image of `S` and `X (n+1) = ∅` makes `B = S` for any prescribed `S ⊆ ℕ`.

Hence the right-hand side asserts that EVERY subset of `ℕ` has a logarithmic
density.  This is false: the union of blocks `[2^(4^j), 2^(2·4^j))` has
log-partial-sums oscillating between ≈ 1/2 and ≈ 1/3.  So the correct answer
to the formal statement is `False`, and this file proves the corresponding
theorem: the negation of the right-hand side.

The *intended* problem (erdosproblems.com/486, moduli `n ≥ 1`) remains open;
the formalization should quantify over `n : ℕ+` or add `n ≠ 0`.
-/

open Filter Finset Real Topology

namespace Erdos486Resolution

/-! ## The bad set: blocks `[2^(4^j), 2^(2·4^j))` -/

/-- Lower endpoint of the `j`-th block. -/
def a (j : ℕ) : ℕ := 2 ^ (4 ^ j)

/-- Upper endpoint of the `j`-th block. -/
def b (j : ℕ) : ℕ := 2 ^ (2 * 4 ^ j)

/-- The bad set: union of the blocks `[a j, b j)`. -/
def S : Set ℕ := ⋃ j, Set.Ico (a j) (b j)

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

/-- Sum of reciprocals over a block `Ico a b` (with `1 ≤ a ≤ b`) as a
difference of harmonic sums. -/
lemma sum_Ico_inv (p q : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) :
    ∑ k ∈ Finset.Ico p q, (k : ℝ)⁻¹ = H (q - 1) - H (p - 1) := by
  have h1 : Finset.Ico p q = Finset.Ioc (p - 1) (q - 1) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
  have h2 : H (p - 1) + ∑ k ∈ Finset.Ioc (p - 1) (q - 1), (k : ℝ)⁻¹ = H (q - 1) := by
    rw [H, H]
    exact Finset.sum_Ioc_consecutive _ (by omega) (by omega)
  rw [h1]; linarith

/-! ## Basic block facts -/

lemma two_le_a (j : ℕ) : 2 ≤ a j := by
  have h : 0 < 4 ^ j := by positivity
  calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (4 ^ j) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma a_lt_b (j : ℕ) : a j < b j := by
  apply Nat.pow_lt_pow_right (by norm_num)
  have : 0 < 4 ^ j := by positivity
  omega

lemma b_le_a_succ (j : ℕ) : b j ≤ a (j + 1) := by
  apply Nat.pow_le_pow_right (by norm_num)
  rw [pow_succ]
  omega

lemma a_mono : Monotone a := by
  intro i j hij
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) hij)

/-! ## Logarithms of the endpoints -/

lemma log_a (j : ℕ) : Real.log (a j) = 4 ^ j * Real.log 2 := by
  rw [a]; push_cast; rw [Real.log_pow]; push_cast; ring

lemma log_b (j : ℕ) : Real.log (b j) = 2 * 4 ^ j * Real.log 2 := by
  rw [b]; push_cast; rw [Real.log_pow]; push_cast; ring

/-- The sum of reciprocals over block `j` is at least `4^j log 2 - 1`. -/
lemma block_sum_lower (j : ℕ) :
    4 ^ j * Real.log 2 - 1 ≤ ∑ k ∈ Finset.Ico (a j) (b j), (k : ℝ)⁻¹ := by
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

/-- The sum of reciprocals over block `j` is at most `1 + 4^j log 2`. -/
lemma block_sum_upper (j : ℕ) :
    ∑ k ∈ Finset.Ico (a j) (b j), (k : ℝ)⁻¹ ≤ 1 + 4 ^ j * Real.log 2 := by
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

/-! ## The log-density partial sums of `S` -/

open Classical in
/-- The quantity whose convergence `S.HasLogDensity d` asserts. -/
noncomputable def f (n : ℕ) : ℝ := ∑ k ≤ n with k ∈ S, (k : ℝ)⁻¹ / Real.log n

lemma hasLogDensity_iff {d : ℝ} : S.HasLogDensity d ↔ Tendsto f atTop (𝓝 d) := Iff.rfl

lemma log_two_lb : (0.69 : ℝ) < Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

/-- At the top of block `j`, the log-density partial sum is at least `0.45`. -/
lemma f_lower {j : ℕ} (hj : 3 ≤ j) : 0.45 ≤ f (b j - 1) := by
  classical
  have hb4 : 4 ≤ b j := by
    have : 0 < 4 ^ j := by positivity
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * 4 ^ j) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hden_pos : 0 < Real.log ((b j - 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < b j - 1)
  -- rewrite f as a single quotient
  have hf : f (b j - 1) =
      (∑ k ∈ (Finset.Iic (b j - 1)).filter (· ∈ S), (k : ℝ)⁻¹) / Real.log ((b j - 1 : ℕ) : ℝ) := by
    rw [f, Finset.sum_div]
  -- the whole block `j` contributes
  have hsub : Finset.Ico (a j) (b j) ⊆ (Finset.Iic (b j - 1)).filter (· ∈ S) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_filter, Finset.mem_Iic]
    exact ⟨by omega, Set.mem_iUnion.mpr ⟨j, Set.mem_Ico.mpr hk⟩⟩
  have hnum : 4 ^ j * Real.log 2 - 1 ≤
      ∑ k ∈ (Finset.Iic (b j - 1)).filter (· ∈ S), (k : ℝ)⁻¹ :=
    (block_sum_lower j).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity))
  have hden : Real.log ((b j - 1 : ℕ) : ℝ) ≤ 2 * 4 ^ j * Real.log 2 := by
    rw [← log_b]
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < b j - 1))
    exact_mod_cast (by omega : b j - 1 ≤ b j)
  rw [hf, le_div_iff₀ hden_pos]
  have hF : (64 : ℝ) ≤ 4 ^ j := by
    calc (64 : ℝ) = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ j := by
        apply pow_le_pow_right₀ (by norm_num) hj
  have hL := log_two_lb
  have hFL : (0.69 * 64 : ℝ) ≤ Real.log 2 * 4 ^ j := by
    apply mul_le_mul hL.le hF (by norm_num) (Real.log_nonneg (by norm_num))
  nlinarith [hden_pos, hden, hnum]

/-- The blocks are pairwise disjoint (as finsets). -/
lemma blocks_disjoint : ∀ i ∈ Finset.range (Nat.succ 0 + 0), True := fun _ _ => trivial

lemma block_disjoint {i i' : ℕ} (h : i ≠ i') :
    Disjoint (Finset.Ico (a i) (b i)) (Finset.Ico (a i') (b i')) := by
  wlog hlt : i < i' generalizing i i'
  · exact (this h.symm (by omega)).symm
  rw [Finset.disjoint_left]
  intro k hk hk'
  rw [Finset.mem_Ico] at hk hk'
  have h1 : b i ≤ a (i + 1) := b_le_a_succ i
  have h2 : a (i + 1) ≤ a i' := a_mono hlt
  omega

open Classical in
/-- Below block `j+1`, only blocks `0..j` contribute. -/
lemma cover (j : ℕ) :
    (Finset.Iic (a (j + 1) - 1)).filter (· ∈ S) ⊆
      (Finset.range (j + 1)).biUnion (fun i => Finset.Ico (a i) (b i)) := by
  intro k hk
  rw [Finset.mem_filter, Finset.mem_Iic] at hk
  obtain ⟨hkn, hkS⟩ := hk
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hkS
  rw [Set.mem_Ico] at hi
  rw [Finset.mem_biUnion]
  refine ⟨i, ?_, Finset.mem_Ico.mpr hi⟩
  rw [Finset.mem_range]
  by_contra hij
  have h1 : a (j + 1) ≤ a i := a_mono (by omega)
  have h2 : 2 ≤ a (j + 1) := two_le_a (j + 1)
  omega

/-- Just below block `j+1`, the log-density partial sum is at most `0.40`. -/
lemma f_upper {j : ℕ} (hj : 3 ≤ j) : f (a (j + 1) - 1) ≤ 0.40 := by
  classical
  set n := a (j + 1) - 1 with hn
  have hE : 2 ≤ 4 ^ (j + 1) := by
    calc 2 ≤ 4 ^ 1 := by norm_num
      _ ≤ 4 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have han : 2 ^ (4 ^ (j + 1) - 1) ≤ n := by
    rw [hn, a]
    have h1 : 2 ^ (4 ^ (j + 1) - 1) * 2 = 2 ^ (4 ^ (j + 1)) := by
      rw [← pow_succ]
      congr 1
      omega
    have h2 : 0 < 2 ^ (4 ^ (j + 1) - 1) := by positivity
    omega
  have hn2 : 2 ≤ n := by
    have : 2 ^ 1 ≤ 2 ^ (4 ^ (j + 1) - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hden_pos : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < n)
  -- lower bound for the denominator
  have hden : ((4 ^ (j + 1) : ℕ) - 1 : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
    have h1 : Real.log ((2 ^ (4 ^ (j + 1) - 1) : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast han
    calc ((4 ^ (j + 1) : ℕ) - 1 : ℝ) * Real.log 2
        = Real.log ((2 ^ (4 ^ (j + 1) - 1) : ℕ) : ℝ) := by
          push_cast
          rw [Real.log_pow]
          push_cast [Nat.cast_sub (by omega : 1 ≤ 4 ^ (j + 1))]
          ring
      _ ≤ Real.log (n : ℝ) := h1
  -- upper bound for the numerator via the block cover
  have hnum : ∑ k ∈ (Finset.Iic n).filter (· ∈ S), (k : ℝ)⁻¹ ≤
      (j + 1 : ℝ) + (4 ^ (j + 1) - 1) / 3 * Real.log 2 := by
    have h1 : ∑ k ∈ (Finset.Iic n).filter (· ∈ S), (k : ℝ)⁻¹ ≤
        ∑ k ∈ (Finset.range (j + 1)).biUnion (fun i => Finset.Ico (a i) (b i)), (k : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (cover j) (fun k _ _ => by positivity)
    have h2 : ∑ k ∈ (Finset.range (j + 1)).biUnion (fun i => Finset.Ico (a i) (b i)), (k : ℝ)⁻¹ =
        ∑ i ∈ Finset.range (j + 1), ∑ k ∈ Finset.Ico (a i) (b i), (k : ℝ)⁻¹ := by
      apply Finset.sum_biUnion
      intro x _ y _ hxy
      exact block_disjoint hxy
    have h3 : ∑ i ∈ Finset.range (j + 1), ∑ k ∈ Finset.Ico (a i) (b i), (k : ℝ)⁻¹ ≤
        ∑ i ∈ Finset.range (j + 1), (1 + 4 ^ i * Real.log 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact block_sum_upper i
    have h4 : ∑ i ∈ Finset.range (j + 1), ((1 : ℝ) + 4 ^ i * Real.log 2) =
        (j + 1 : ℝ) + (4 ^ (j + 1) - 1) / 3 * Real.log 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
      rw [← Finset.sum_mul, geom_sum_eq (by norm_num : (4 : ℝ) ≠ 1)]
      push_cast
      ring
    calc ∑ k ∈ (Finset.Iic n).filter (· ∈ S), (k : ℝ)⁻¹
        ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h3
      _ = _ := h4
  -- put it together
  have hf : f n = (∑ k ∈ (Finset.Iic n).filter (· ∈ S), (k : ℝ)⁻¹) / Real.log (n : ℝ) := by
    rw [f, Finset.sum_div]
  rw [hf, div_le_iff₀ hden_pos]
  -- numeric endgame
  have hG : (8 : ℝ) ≤ 2 ^ j := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := by apply pow_le_pow_right₀ (by norm_num) hj
  have hj1 : (j + 1 : ℝ) ≤ 2 ^ j := by
    have := Nat.lt_two_pow_self (n := j)
    exact_mod_cast Nat.succ_le_of_lt this
  have h4j : (4 : ℝ) ^ j = 2 ^ j * 2 ^ j := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have hL := log_two_lb
  have hcast : ((4 ^ (j + 1) : ℕ) - 1 : ℝ) = 4 * 4 ^ j - 1 := by
    push_cast
    ring
  rw [hcast] at hden
  have hcast2 : ((4 : ℝ) ^ (j + 1) - 1) = 4 * 4 ^ j - 1 := by ring
  rw [hcast2] at hnum
  set L := Real.log 2 with hLdef
  set G : ℝ := 2 ^ j with hGdef
  have hGpos : (0 : ℝ) < G := by positivity
  -- key: (j+1) + (4G²-1)/3·L ≤ 0.4·((4G²-1)·L)
  have key : (j + 1 : ℝ) + (4 * 4 ^ j - 1) / 3 * L ≤ 0.40 * ((4 * 4 ^ j - 1) * L) := by
    rw [h4j]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ G - 8) hGpos.le,
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ G - 8) hGpos.le) (by linarith : (0:ℝ) ≤ L),
      mul_nonneg (mul_nonneg hGpos.le hGpos.le) (by linarith : (0:ℝ) ≤ L - 0.69),
      mul_nonneg (by linarith : (0:ℝ) ≤ G - 8) (by linarith : (0:ℝ) ≤ L)]
  have hden' : 0.40 * ((4 * 4 ^ j - 1) * L) ≤ 0.40 * Real.log (n : ℝ) := by
    nlinarith [hden]
  calc ∑ k ∈ (Finset.Iic n).filter (· ∈ S), (k : ℝ)⁻¹
      ≤ (j + 1 : ℝ) + (4 * 4 ^ j - 1) / 3 * L := hnum
    _ ≤ 0.40 * ((4 * 4 ^ j - 1) * L) := key
    _ ≤ 0.40 * Real.log (n : ℝ) := hden'

/-! ## `S` has no logarithmic density -/

theorem S_not_hasLogDensity (d : ℝ) : ¬ S.HasLogDensity d := by
  intro hd
  rw [hasLogDensity_iff] at hd
  -- indices grow at least linearly, so the two subsequences tend to infinity
  have hidx1 : Tendsto (fun j => b j - 1) atTop atTop := by
    apply tendsto_atTop_mono (fun j => ?_) tendsto_id
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 2 ^ j ≤ b j := Nat.pow_le_pow_right (by norm_num) (by
      have : j ≤ 4 ^ j := (Nat.lt_two_pow_self).le.trans
        (Nat.pow_le_pow_left (by norm_num) j)
      omega)
    simp only [id_eq]
    omega
  have hidx2 : Tendsto (fun j => a (j + 1) - 1) atTop atTop := by
    apply tendsto_atTop_mono (fun j => ?_) tendsto_id
    have h1 : j < 2 ^ j := Nat.lt_two_pow_self
    have h2 : 2 ^ j ≤ a (j + 1) := Nat.pow_le_pow_right (by norm_num) (by
      have : j ≤ 4 ^ j := (Nat.lt_two_pow_self).le.trans
        (Nat.pow_le_pow_left (by norm_num) j)
      have : 4 ^ j ≤ 4 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
    simp only [id_eq]
    omega
  have hcomp1 : Tendsto (fun j => f (b j - 1)) atTop (𝓝 d) := hd.comp hidx1
  have hcomp2 : Tendsto (fun j => f (a (j + 1) - 1)) atTop (𝓝 d) := hd.comp hidx2
  have hd1 : (0.45 : ℝ) ≤ d :=
    ge_of_tendsto hcomp1 (Filter.eventually_atTop.mpr ⟨3, fun j hj => f_lower hj⟩)
  have hd2 : d ≤ (0.40 : ℝ) :=
    le_of_tendsto hcomp2 (Filter.eventually_atTop.mpr ⟨3, fun j hj => f_upper hj⟩)
  norm_num at hd1 hd2
  linarith

/-! ## Resolution of the formal statement of Erdős 486 -/

/-- **The right-hand side of the formalized Erdős Problem 486 is false**:
because the moduli range over all of `ℕ` including `0`, and `ZMod 0 = ℤ`,
the sets `B` realizable in the statement include *every* subset of `ℕ` —
in particular one with no logarithmic density.  Hence `erdos_486` is resolved
by `answer(False)`.  (The intended problem, with moduli `n ≥ 1`, remains open.) -/
theorem erdos_486_rhs_false :
    ¬ (∀ X : (n : ℕ) → Set (ZMod n),
        ∃ d, {m : ℕ | ∀ n, (m : ZMod n) ∉ X n}.HasLogDensity d) := by
  intro Hyp
  have hcarve : ∃ X : (n : ℕ) → Set (ZMod n),
      {m : ℕ | ∀ n, (m : ZMod n) ∉ X n} = S := by
    refine ⟨fun n => match n with
      | 0 => {z : ℤ | z ∉ (Nat.cast '' S : Set ℤ)}
      | _ + 1 => ∅, ?_⟩
    ext m
    constructor
    · intro h
      have h0 : ¬ ((m : ℤ) ∉ (Nat.cast '' S : Set ℤ)) := h 0
      rw [not_not] at h0
      obtain ⟨s, hs, hcast⟩ := h0
      rw [Int.natCast_inj] at hcast
      exact hcast ▸ hs
    · intro hm n
      cases n with
      | zero => exact not_not_intro ⟨m, hm, rfl⟩
      | succ k => exact Set.notMem_empty _
  obtain ⟨X, hX⟩ := hcarve
  obtain ⟨d, hd⟩ := Hyp X
  rw [hX] at hd
  exact S_not_hasLogDensity d hd

end Erdos486Resolution
