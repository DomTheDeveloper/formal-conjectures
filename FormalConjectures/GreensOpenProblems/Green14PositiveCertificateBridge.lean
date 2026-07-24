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

import FormalConjectures.GreensOpenProblems.Green14FunctionCertificateBridge

/-!
# Positive finite-checker bridge for Green14

The lower-bound certificate bridge turns a negative direct checker result into
absence of a catalog arithmetic progression. The upper bound needs the converse
kind of reflection: a positive direct checker result must construct the exact
`Finset (Icc 1 N)` witness used by `mixedMonoAPGuaranteeSet`.
-/

open Set
open scoped Classical

namespace Green14.PositiveCertificateBridge

open Green14.FunctionCertificateBridge

private lemma mem_value_set_iff {N : Nat} {s : Finset (Icc 1 N)} {z : Nat} :
    z ∈ ({(x : Nat) | x ∈ s} : Set Nat) ↔ ∃ x ∈ s, (x : Nat) = z := by
  simp

/-- Testing whether a `Fin 2` color is one and then converting the Boolean result
back to `Fin 2` recovers the original color. -/
lemma boolColor_beq_one (c : Fin 2) : boolColor (c == (1 : Fin 2)) = c := by
  fin_cases c <;> rfl

/-- A positive direct checker result constructs a monochromatic arithmetic
progression in the catalog's exact `Set.IsAPOfLength` representation. -/
theorem exists_monoAP_of_hasAP_eq_true
    {N k : Nat} {coloring : Nat → Bool} {color : Bool}
    (hk : 2 ≤ k) (hcheck : hasAP N k coloring color = true) :
    ∃ s : Finset (Icc 1 N),
      ({(x : Nat) | x ∈ s} : Set Nat).IsAPOfLength k ∧
        ∀ x ∈ s, certificateColoring N coloring x = boolColor color := by
  simp only [hasAP, List.any_eq_true, List.mem_range, List.all_eq_true] at hcheck
  rcases hcheck with ⟨a, ha, d0, hd0, hall⟩
  have haN : a < N := by simpa using ha
  have hd0lt : d0 < (N - 1 - a) / (k - 1) := by simpa using hd0
  let d := d0 + 1
  have hdpos : 0 < d := by simp [d]
  have hkden : 0 < k - 1 := by omega
  have hdle : d ≤ (N - 1 - a) / (k - 1) := by
    dsimp [d]
    omega
  have hmul : d * (k - 1) ≤ N - 1 - a :=
    (Nat.le_div_iff_mul_le hkden).mp hdle
  have hend : a + (k - 1) * d < N := by
    rw [Nat.mul_comm] at hmul
    omega
  let term : Fin k ↪ Icc 1 N :=
    ⟨fun i => ⟨a + 1 + i.1 * d, by
        constructor
        · omega
        · have hi : i.1 ≤ k - 1 := by omega
          have hterm : a + i.1 * d ≤ a + (k - 1) * d := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_right d hi) a
          omega⟩,
      by
        intro i j hij
        apply Fin.ext
        have hval := congrArg Subtype.val hij
        dsimp at hval
        omega⟩
  let s : Finset (Icc 1 N) := Finset.univ.map term
  let valEmb : Icc 1 N ↪ Nat := ⟨Subtype.val, Subtype.val_injective⟩
  let sVal : Finset Nat := s.map valEmb
  let T : Set Nat := {(x : Nat) | x ∈ s}
  have hT_sVal : T = (sVal : Set Nat) := by
    ext z
    simp [T, sVal, valEmb]
  have hT_AP : T = {a + 1 + n • d | (n : Nat) (_ : n < k)} := by
    ext z
    constructor
    · intro hz
      rcases mem_value_set_iff.mp hz with ⟨x, hxs, hx⟩
      rcases Finset.mem_map.mp hxs with ⟨i, -, hi⟩
      refine ⟨i.1, ?_, ?_⟩
      · exact_mod_cast i.2
      · have hval := congrArg Subtype.val hi
        simpa [term, nsmul_eq_mul] using hval.trans hx
    · rintro ⟨n, hn, rfl⟩
      let i : Fin k := ⟨n, by exact_mod_cast hn⟩
      apply mem_value_set_iff.mpr
      refine ⟨term i, ?_, ?_⟩
      · apply Finset.mem_map.mpr
        exact ⟨i, Finset.mem_univ _, rfl⟩
      · simp [term, i, nsmul_eq_mul]
  refine ⟨s, ⟨a + 1, d, ?_⟩, ?_⟩
  · constructor
    · change T.encard = (k : ℕ∞)
      rw [hT_sVal]
      simp [sVal, s]
    · exact hT_AP
  · intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, -, hi⟩
    have hbool : coloring (a + i.1 * d) = color := by
      have hirange : i.1 ∈ List.range k := by simpa using i.2
      have := hall i.1 hirange
      simpa [d] using this
    have hindex : x.1 - 1 = a + i.1 * d := by
      have hval := congrArg Subtype.val hi
      dsimp [term] at hval
      omega
    apply boolColor_injective
    simpa [certificateColoring, hindex] using hbool

/-- If every Boolean coloring is detected by one of the two direct checkers,
then `N` belongs to the repository's mixed progression guarantee set. -/
theorem mem_mixed_of_direct_checks
    {N k r : Nat} (hk : 2 ≤ k) (hr : 2 ≤ r)
    (hcomplete : ∀ coloring : Nat → Bool,
      hasAP N k coloring false = true ∨ hasAP N r coloring true = true) :
    N ∈ Green14.mixedMonoAPGuaranteeSet k r := by
  intro coloring
  let direct : Nat → Bool := fun i =>
    if hi : i < N then coloring ⟨i + 1, by omega⟩ == (1 : Fin 2) else false
  have direct_roundtrip (x : Icc 1 N) :
      certificateColoring N direct x = coloring x := by
    unfold certificateColoring
    dsimp [direct]
    rw [dif_pos (by omega)]
    rw [boolColor_beq_one]
    congr 1
    apply Subtype.ext
    omega
  rcases hcomplete direct with hzero | hone
  · left
    obtain ⟨s, hAP, hmono⟩ :=
      exists_monoAP_of_hasAP_eq_true hk hzero
    refine ⟨s, hAP, ?_⟩
    intro x hx
    rw [← direct_roundtrip x]
    exact hmono x hx
  · right
    obtain ⟨s, hAP, hmono⟩ :=
      exists_monoAP_of_hasAP_eq_true hr hone
    refine ⟨s, hAP, ?_⟩
    intro x hx
    rw [← direct_roundtrip x]
    exact hmono x hx

end Green14.PositiveCertificateBridge
