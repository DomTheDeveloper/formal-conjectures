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

import Mathlib.NumberTheory.PrimeCounting

/-!
# Finite range for Zhi-Wei Sun's Conjecture 2.6

The finite remainder is checked by ordinary `decide`, so every computation is
replayed by Lean's kernel. To avoid the C-stack overflow caused by enumerating
`Fin 214 × Fin 214` as two large nested quantifiers, each index is represented
by a small block number and an offset inside the block.

The two public theorems cover:

* every admissible pair with `n < 214`;
* every admissible pair with `214 ≤ n` and `k * n < 2401`.
-/

namespace SunConjectures

open scoped Nat.Prime

private abbrev sun26Claim (n k : ℕ) : Prop :=
  (π (k * n)) ^ (k + 1) > (π ((k + 1) * n)) ^ k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_n_blocks :
    ∀ b : Fin 27, ∀ i : Fin 8, ∀ k : Fin 214,
      let n := b.val * 8 + i.val
      n < 214 → 4 < n → 1 ≤ k.val → k.val ≤ n → sun26Claim n k.val := by
  decide

/-- All admissible pairs with `5 ≤ n < 214`, checked by kernel reduction. -/
theorem conjecture_2_6_finite_small_n :
    ∀ n : Fin 214, ∀ k : Fin 214,
      4 < n.val → 1 ≤ k.val → k.val ≤ n.val →
        (π (k.val * n.val)) ^ (k.val + 1) >
          (π ((k.val + 1) * n.val)) ^ k.val := by
  intro n k hn hk hkn
  have hb : n.val / 8 < 27 := by omega
  let b : Fin 27 := ⟨n.val / 8, hb⟩
  let i : Fin 8 := ⟨n.val % 8, Nat.mod_lt _ (by norm_num)⟩
  have heq : b.val * 8 + i.val = n.val := by
    simpa [b, i, Nat.mul_comm] using Nat.div_add_mod n.val 8
  have h := small_n_blocks b i k
    (by simpa [heq] using n.isLt)
    (by simpa [heq] using hn)
    hk
    (by simpa [heq] using hkn)
  simpa [sun26Claim, heq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_x_blocks :
    ∀ b : Fin 49, ∀ i : Fin 50, ∀ k : Fin 12,
      let n := b.val * 50 + i.val
      n < 2401 → 214 ≤ n → 1 ≤ k.val → k.val ≤ n →
        k.val * n < 2401 → sun26Claim n k.val := by
  decide

/-- All remaining admissible pairs below the analytic threshold `k * n = 2401`. -/
theorem conjecture_2_6_finite_small_x :
    ∀ n : Fin 2401, ∀ k : Fin 12,
      214 ≤ n.val → 1 ≤ k.val → k.val ≤ n.val → k.val * n.val < 2401 →
        (π (k.val * n.val)) ^ (k.val + 1) >
          (π ((k.val + 1) * n.val)) ^ k.val := by
  intro n k hn hk hkn hx
  have hb : n.val / 50 < 49 := by omega
  let b : Fin 49 := ⟨n.val / 50, hb⟩
  let i : Fin 50 := ⟨n.val % 50, Nat.mod_lt _ (by norm_num)⟩
  have heq : b.val * 50 + i.val = n.val := by
    simpa [b, i, Nat.mul_comm] using Nat.div_add_mod n.val 50
  have h := small_x_blocks b i k
    (by simpa [heq] using n.isLt)
    (by simpa [heq] using hn)
    hk
    (by simpa [heq] using hkn)
    (by simpa [heq] using hx)
  simpa [sun26Claim, heq] using h

#print axioms conjecture_2_6_finite_small_n
#print axioms conjecture_2_6_finite_small_x

end SunConjectures
