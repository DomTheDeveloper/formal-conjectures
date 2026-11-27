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
module

public import FormalConjecturesUtil

/-!
# Mills' Theorem

There exists a real $A > 1$ such that
$\lfloor A^{3^n}\rfloor$ is prime for every positive integer $n$, where $\lfloor\cdot\rfloor$
denotes the floor function.

The least such $A$ is known as *Mills' constant*. It is irrational. Caldwell and
Cheng showed that it is $1.3063778838\ldots$ assuming the Riemann hypothesis, which is proved
[Al26].

*References:*
- [Wikipedia, Mills' constant](https://en.wikipedia.org/wiki/Mills%27_constant)
- [A prime-representing function](https://www.ams.org/journals/bull/1947-53-06/S0002-9904-1947-08849-2/)
  by *W. H. Mills*, Bull. Amer. Math. Soc. **53** (1947), 604.
- [Mills' constant](https://mathworld.wolfram.com/MillsConstant.html) on Wolfram MathWorld.
- [Mills' constant is irrational](https://doi.org/10.1112/mtk.70027) by *Kota Saito*,
  Mathematika **71** (2025), no. 3, e70027, [arXiv:2404.19461](https://arxiv.org/abs/2404.19461).
- [Determining Mills' Constant ..](https://cs.uwaterloo.ca/journals/JIS/VOL8/Caldwell/caldwell78.pdf)
  by *Chris K. Caldwell and Yuanyou Cheng*, J. Integer Seq. **8** (2005), Article 05.4.1.
- [OEIS A051021](https://oeis.org/A051021) (decimal expansion of Mills' constant)
- [Al26] Alpöge, L., [Note on the Riemann Hypothesis](https://alpo.ge/remark.pdf) (2026).
-/

@[expose] public section

namespace Mills

/--
Given any real $A$, `IsMills A` encodes the statement that $\lfloor A^{3^n}\rfloor,n > 0$ is prime.
-/
abbrev IsMills (A : ℝ) : Prop := ∀ (n : ℕ+), Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊

/--
**Mills' theorem** (Mills, 1947).
There is a real number $A > 1$ such that $\lfloor A^{3^n}\rfloor$ is prime.
-/
@[category research solved, AMS 11]
theorem exists' : ∃ A > 1, IsMills A := by
  sorry

/--
For a real $A$, `IsMinMills A` is the smallest value satisfying `IsMills A`.
-/
abbrev IsMinMills (A : ℝ) : Prop := IsLeast {x | x > 1 ∧ IsMills x} A

/--
**Mills' constant.**
There is a *least* Mills number.
-/
@[category research solved, AMS 11]
theorem exists_least : ∃ A, IsMinMills A := by
  sorry

/--
**Mills' constant is irrational** (Saito, 2024).
-/
@[category research solved, AMS 11]
theorem irrational {A} (hA : IsMinMills A) :
    Irrational A := by
  sorry

/-- If the integers from `m³` to `p - 1` are all composite, a prime floor of
`x³` with `m ≤ x` must be at least `p`. -/
@[category API, AMS 11]
private theorem prime_cube_floor_lower {x : ℝ} {m p : ℕ} (hm : (m : ℝ) ≤ x)
    (hp : (⌊x ^ 3⌋₊).Prime) (gap : ∀ k : ℕ, m ^ 3 ≤ k → k < p → ¬k.Prime) :
    (p : ℝ) ≤ x ^ 3 := by
  have hfloor : m ^ 3 ≤ ⌊x ^ 3⌋₊ := Nat.le_floor (by
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg m) hm 3)
  have hp' : p ≤ ⌊x ^ 3⌋₊ := le_of_not_gt (fun h => gap _ hfloor h hp)
  exact (Nat.cast_le.mpr hp').trans (Nat.floor_le (pow_nonneg ((Nat.cast_nonneg m).trans hm) 3))

/-- Every Mills number greater than one exceeds the lower endpoint of
Caldwell and Cheng's ten-decimal interval. -/
@[category API, AMS 11]
theorem lower_bound_of_isMills {A : ℝ} (hA : 1 < A) (h : IsMills A) : 1.3063778838 < A := by
  have hp (n : ℕ+) := Nat.prime_iff.mpr (h n)
  have h3 : (2 : ℝ) ≤ A ^ 3 :=
    (Nat.cast_le.mpr (hp 1).two_le).trans (Nat.floor_le (by positivity))
  have h9 : (11 : ℝ) ≤ (A ^ 3) ^ 3 := by
    apply prime_cube_floor_lower (m := 2) (p := 11) h3
    · simpa only [← pow_mul] using hp 2
    · intro k hk hlt
      norm_num at hk
      interval_cases k <;> norm_num1
  have h27 : (1361 : ℝ) ≤ ((A ^ 3) ^ 3) ^ 3 := by
    apply prime_cube_floor_lower (m := 11) (p := 1361) h9
    · simpa only [← pow_mul] using hp 3
    · intro k hk hlt
      norm_num at hk
      interval_cases k <;> norm_num1
  have h81 : (2521008887 : ℝ) ≤ (((A ^ 3) ^ 3) ^ 3) ^ 3 := by
    apply prime_cube_floor_lower (m := 1361) (p := 2521008887) h27
    · simpa only [← pow_mul] using hp 4
    · intro k hk hlt
      norm_num at hk
      interval_cases k <;> norm_num1
  simp only [← pow_mul] at h81
  apply lt_of_pow_lt_pow_left₀ 81 (by linarith)
  exact (by norm_num : (1.3063778838 : ℝ) ^ 81 < 2521008887).trans_le h81

/--
**Mills' constant lower bound** (Caldwell–Cheng, 2005): assuming the Riemann hypothesis,
Mills' constant begins at $1.3063778838\ldots$.
-/
@[category research solved, AMS 11]
theorem lower_bound_of_RH (hRH : RiemannHypothesis) {A} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  sorry

/--
Mills' constant begins at $1.3063778838\ldots$ unconditionally, since the Riemann hypothesis is
proved [Al26].
-/
@[category research solved, AMS 11]
theorem mem_Ioo {A} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  sorry

end Mills
