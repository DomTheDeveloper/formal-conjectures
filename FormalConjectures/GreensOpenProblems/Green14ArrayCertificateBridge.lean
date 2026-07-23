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

import FormalConjectures.GreensOpenProblems.Green14OrderBridge

/-!
# Kernel-clean array certificate bridge for Green14

This file reflects a negative direct-array arithmetic-progression checker into
the repository's `Set.IsAPOfLength` formulation. It is independent of
`native_decide`: concrete certificate files may prove the Boolean equality with
kernel `decide` and then obtain the numerical `W(3,r)` lower bound here.
-/

open Set
open scoped Classical

namespace Green14.ArrayCertificateBridge

def colorAt (colors : Array Bool) (i : Nat) : Bool := colors[i]!

def hasAP (N k : Nat) (colors : Array Bool) (color : Bool) : Bool :=
  (List.range N).any fun a =>
    (List.range ((N - 1 - a) / (k - 1))).any fun d0 =>
      let d := d0 + 1
      (List.range k).all fun i => colorAt colors (a + i * d) == color

def boolColor : Bool → Fin 2
  | false => 0
  | true => 1

lemma boolColor_injective : Function.Injective boolColor := by
  intro x y h
  cases x <;> cases y <;> simp_all [boolColor]

def certificateColoring (N : Nat) (colors : Array Bool) : Icc 1 N → Fin 2 :=
  fun x => boolColor (colorAt colors (x.1 - 1))

lemma exists_mismatch_of_hasAP_eq_false
    {N k : Nat} {colors : Array Bool} {color : Bool}
    (hk : 2 ≤ k) (hcheck : hasAP N k colors color = false)
    {a d : Nat} (ha : a < N) (hdpos : 0 < d)
    (hend : a + (k - 1) * d < N) :
    ∃ i : Nat, i < k ∧ colorAt colors (a + i * d) ≠ color := by
  by_contra hnone
  push_neg at hnone
  have hall : (List.range k).all fun i => colorAt colors (a + i * d) == color := by
    rw [List.all_eq_true]
    intro i hi
    have hik : i < k := by simpa using hi
    simp [hnone i hik]
  let q : Nat := (N - 1 - a) / (k - 1)
  have hkden : 0 < k - 1 := by omega
  have hmul : d * (k - 1) ≤ N - 1 - a := by
    have hmul' : (k - 1) * d ≤ N - 1 - a := by omega
    simpa [Nat.mul_comm] using hmul'
  have hdle : d ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hkden).2 hmul
  have hd0lt : d - 1 < q := by omega
  have hdback : d - 1 + 1 = d := by omega
  have hinner :
      (List.range q).any fun d0 =>
        let d' := d0 + 1
        (List.range k).all fun i => colorAt colors (a + i * d') == color := by
    apply List.any_of_mem (by simpa using hd0lt)
    simpa [hdback] using hall
  have houter :
      (List.range N).any fun a' =>
        (List.range ((N - 1 - a') / (k - 1))).any fun d0 =>
          let d' := d0 + 1
          (List.range k).all fun i => colorAt colors (a' + i * d') == color := by
    apply List.any_of_mem (by simpa using ha)
    simpa [q] using hinner
  have : hasAP N k colors color = true := by
    simpa [hasAP] using houter
  rw [hcheck] at this
  contradiction

private lemma mem_coe_finset_set_iff {N : Nat} {s : Finset (Icc 1 N)} {z : Nat} :
    z ∈ ({(x : Nat) | x ∈ s} : Set Nat) ↔ ∃ x ∈ s, (x : Nat) = z := by
  simp

lemma no_monoAP_of_hasAP_eq_false
    {N k : Nat} {colors : Array Bool} {color : Bool}
    (hk : 2 ≤ k) (hcheck : hasAP N k colors color = false) :
    ¬ ∃ s : Finset (Icc 1 N),
        ({(x : Nat) | x ∈ s}).IsAPOfLength k ∧
          ∀ x ∈ s, certificateColoring N colors x = boolColor color := by
  rintro ⟨s, hAP, hmono⟩
  rcases hAP with ⟨start, step, hWith⟩
  let T : Set Nat := {(x : Nat) | x ∈ s}
  have hT : T.IsAPOfLengthWith k start step := hWith
  have term_mem (i : Nat) (hi : i < k) : start + i * step ∈ T := by
    rw [hT.2]
    refine ⟨i, ?_, ?_⟩
    · exact_mod_cast hi
    · simp [nsmul_eq_mul]
  have start_mem : start ∈ T := by simpa using term_mem 0 (by omega)
  have last_mem : start + (k - 1) * step ∈ T := term_mem (k - 1) (by omega)
  rcases (mem_coe_finset_set_iff.mp start_mem) with ⟨x0, hx0s, hx0⟩
  rcases (mem_coe_finset_set_iff.mp last_mem) with ⟨xlast, hxlasts, hxlast⟩
  have hstart_lo : 1 ≤ start := by simpa [hx0] using x0.2.1
  have hstart_hi : start ≤ N := by simpa [hx0] using x0.2.2
  have hlast_hi : start + (k - 1) * step ≤ N := by simpa [hxlast] using xlast.2.2
  have hstep_pos : 0 < step := by
    by_contra hnot
    have hstep : step = 0 := Nat.eq_zero_of_not_pos hnot
    have hTsingle : T = {start} := by
      rw [hT.2]
      ext z
      constructor
      · rintro ⟨i, hi, rfl⟩
        simp [hstep]
      · intro hz
        have hz' : z = start := by simpa using hz
        subst z
        refine ⟨0, ?_, by simp [hstep]⟩
        exact_mod_cast (show 0 < k by omega)
    have hcard : (k : ℕ∞) = 1 := by
      rw [← hT.1, hTsingle]
      simp
    have : k = 1 := by exact_mod_cast hcard
    omega
  have ha0_ltN : start - 1 < N := by omega
  have hend0 : start - 1 + (k - 1) * step < N := by omega
  obtain ⟨i, hi, hmismatch⟩ :=
    exists_mismatch_of_hasAP_eq_false hk hcheck ha0_ltN hstep_pos hend0
  have hiterm : start + i * step ∈ T := term_mem i hi
  rcases (mem_coe_finset_set_iff.mp hiterm) with ⟨x, hxs, hx⟩
  have hxindex : x.1 - 1 = start - 1 + i * step := by
    have hxval : x.1 = start + i * step := hx
    omega
  have hcolor := hmono x hxs
  have hbool : colorAt colors (start - 1 + i * step) = color := by
    apply boolColor_injective
    simpa [certificateColoring, hxindex] using hcolor
  exact hmismatch hbool

lemma not_mem_mixed_of_checks
    {N r : Nat} {colors : Array Bool}
    (hr : 2 ≤ r)
    (hchecks : hasAP N 3 colors false = false ∧ hasAP N r colors true = false) :
    N ∉ Green14.mixedMonoAPGuaranteeSet 3 r := by
  intro hguarantee
  rcases hguarantee (certificateColoring N colors) with hzero | hone
  · exact no_monoAP_of_hasAP_eq_false (k := 3) (by omega) hchecks.1 hzero
  · exact no_monoAP_of_hasAP_eq_false (k := r) hr hchecks.2 hone

theorem W_ge_succ_of_checks
    {N r : Nat} {colors : Array Bool}
    (hr : 2 ≤ r)
    (hchecks : hasAP N 3 colors false = false ∧ hasAP N r colors true = false) :
    N + 1 ≤ Green14.W 3 r := by
  apply Green14.W_ge_succ_of_not_mem 3 r N (by omega) (by omega)
  exact not_mem_mixed_of_checks hr hchecks

end Green14.ArrayCertificateBridge
