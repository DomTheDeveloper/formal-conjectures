/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.GreensOpenProblems.Green14Certificates
import FormalConjectures.GreensOpenProblems.Green14OrderBridge

/-!
# Reflection bridge for the Green14 finite certificates

The certificate lists in `Green14Certificates` are intentionally private.  The
public checker below is definitionally identical to the private checker, so
Lean can infer the hidden list when a theorem such as `valid_20` is supplied to
the generic bridge.
-/

open Set
open scoped Classical

namespace Green14.CertificateBridge

/-- Boolean color at zero-based position `i`.  `false` is color 0 and `true`
is color 1. -/
def colorAt (zeros : List Nat) (i : Nat) : Bool :=
  !(zeros.contains (i + 1))

/-- Exhaustive bounded checker for a monochromatic arithmetic progression. -/
def hasAP (N k : Nat) (zeros : List Nat) (color : Bool) : Bool :=
  (List.range N).any fun a =>
    (List.range N).any fun d =>
      decide (0 < d ∧ a + (k - 1) * d < N) &&
        (List.range k).all fun i => colorAt zeros (a + i * d) == color

/-- Embed a Boolean color into `Fin 2`. -/
def boolColor : Bool → Fin 2
  | false => 0
  | true => 1

lemma boolColor_injective : Function.Injective boolColor := by
  intro x y h
  cases x <;> cases y <;> simp_all [boolColor]

/-- The coloring of `{1, ..., N}` encoded by a certificate list. -/
def certificateColoring (N : Nat) (zeros : List Nat) : Icc 1 N → Fin 2 :=
  fun x => boolColor (colorAt zeros (x.1 - 1))

/-- A false checker result gives a mismatching term for every admissible
start/difference pair. -/
lemma exists_mismatch_of_hasAP_eq_false {N k : Nat} {zeros : List Nat} {color : Bool}
    (hcheck : hasAP N k zeros color = false)
    {a d : Nat} (ha : a < N) (hd : d < N)
    (hdpos : 0 < d) (hend : a + (k - 1) * d < N) :
    ∃ i : Nat, i < k ∧ colorAt zeros (a + i * d) ≠ color := by
  by_contra hnone
  push_neg at hnone
  have hall : (List.range k).all fun i => colorAt zeros (a + i * d) == color := by
    rw [List.all_iff_forall_prop]
    intro i hi
    have hik : i < k := by simpa using hi
    simp [hnone i hik]
  have hdterm :
      decide (0 < d ∧ a + (k - 1) * d < N) &&
          (List.range k).all fun i => colorAt zeros (a + i * d) == color := by
    simp [hdpos, hend, hall]
  have hinner :
      (List.range N).any fun d' =>
        decide (0 < d' ∧ a + (k - 1) * d' < N) &&
          (List.range k).all fun i => colorAt zeros (a + i * d') == color :=
    List.any_of_mem (by simpa using hd) hdterm
  have houter :
      (List.range N).any fun a' =>
        (List.range N).any fun d' =>
          decide (0 < d' ∧ a' + (k - 1) * d' < N) &&
            (List.range k).all fun i => colorAt zeros (a' + i * d') == color :=
    List.any_of_mem (by simpa using ha) hinner
  have : hasAP N k zeros color = true := by
    exact Bool.eq_true_iff.mpr (by simpa [hasAP] using houter)
  rw [hcheck] at this
  contradiction

/-- The set-builder used by the Green14 statement is the image of the subtype
coercion. -/
private lemma mem_coe_finset_set_iff {N : Nat} {s : Finset (Icc 1 N)} {z : Nat} :
    z ∈ ({(x : Nat) | x ∈ s} : Set Nat) ↔
      ∃ x ∈ s, (x : Nat) = z := by
  rfl

/-- A negative Boolean checker excludes a monochromatic progression in the
repository's `Set.IsAPOfLength` formulation. -/
lemma no_monoAP_of_hasAP_eq_false {N k : Nat} {zeros : List Nat} {color : Bool}
    (hk : 2 ≤ k) (hcheck : hasAP N k zeros color = false) :
    ¬ ∃ s : Finset (Icc 1 N),
        ({(x : Nat) | x ∈ s}).IsAPOfLength k ∧
          ∀ x ∈ s, certificateColoring N zeros x = boolColor color := by
  rintro ⟨s, hAP, hmono⟩
  rcases hAP with ⟨start, step, hWith⟩
  let T : Set Nat := {(x : Nat) | x ∈ s}
  have hT : T.IsAPOfLengthWith k start step := hWith

  have term_mem (i : Nat) (hi : i < k) : start + i * step ∈ T := by
    rw [hT.2]
    refine ⟨i, ?_, ?_⟩
    · exact_mod_cast hi
    · simp [nsmul_eq_mul]

  have start_mem : start ∈ T := by
    simpa using term_mem 0 (by omega)
  have last_mem : start + (k - 1) * step ∈ T :=
    term_mem (k - 1) (by omega)

  rcases (mem_coe_finset_set_iff.mp start_mem) with ⟨x0, hx0s, hx0⟩
  rcases (mem_coe_finset_set_iff.mp last_mem) with ⟨xlast, hxlasts, hxlast⟩
  have hstart_lo : 1 ≤ start := by simpa [hx0] using x0.2.1
  have hstart_hi : start ≤ N := by simpa [hx0] using x0.2.2
  have hlast_hi : start + (k - 1) * step ≤ N := by
    simpa [hxlast] using xlast.2.2

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

  have hstep_le_prod : step ≤ (k - 1) * step := by
    calc
      step = 1 * step := by simp
      _ ≤ (k - 1) * step := Nat.mul_le_mul_right step (by omega)
  have hstep_ltN : step < N := by omega
  have ha0_ltN : start - 1 < N := by omega
  have hend0 : start - 1 + (k - 1) * step < N := by omega

  obtain ⟨i, hi, hmismatch⟩ :=
    exists_mismatch_of_hasAP_eq_false hcheck ha0_ltN hstep_ltN hstep_pos hend0
  have hiterm : start + i * step ∈ T := term_mem i hi
  rcases (mem_coe_finset_set_iff.mp hiterm) with ⟨x, hxs, hx⟩
  have hxindex : x.1 - 1 = start - 1 + i * step := by
    have hxval : x.1 = start + i * step := hx
    omega
  have hcolor := hmono x hxs
  have hbool : colorAt zeros (start - 1 + i * step) = color := by
    apply boolColor_injective
    simpa [certificateColoring, hxindex] using hcolor
  exact hmismatch hbool

/-- A pair of checker results yields the exact countercoloring required by the
mixed Green14 guarantee set. -/
lemma not_mem_mixed_of_checks {N r : Nat} {zeros : List Nat}
    (hr : 2 ≤ r)
    (hchecks : hasAP N 3 zeros false = false ∧ hasAP N r zeros true = false) :
    N ∉ Green14.mixedMonoAPGuaranteeSet 3 r := by
  intro hguarantee
  rcases hguarantee (certificateColoring N zeros) with hzero | hone
  · exact no_monoAP_of_hasAP_eq_false (k := 3) (by omega) hchecks.1 ⟨hzero⟩
  · exact no_monoAP_of_hasAP_eq_false (k := r) hr hchecks.2 ⟨hone⟩

/-- Generic numerical lower bound obtained from one checked coloring. -/
theorem W_ge_succ_of_checks {N r : Nat} {zeros : List Nat}
    (hr : 2 ≤ r)
    (hchecks : hasAP N 3 zeros false = false ∧ hasAP N r zeros true = false) :
    N + 1 ≤ Green14.W 3 r := by
  apply Green14.W_ge_succ_of_not_mem 3 r N (by omega) (by omega)
  exact not_mem_mixed_of_checks hr hchecks

/-- The twenty Appendix-A certificates prove all recorded lower bounds. -/
theorem W_3_20_lower_proved : Green14.W 3 20 ≥ 389 := by
  exact W_ge_succ_of_checks (N := 388) (r := 20) (by omega) Green14.Certificate.valid_20

theorem W_3_21_lower_proved : Green14.W 3 21 ≥ 416 := by
  exact W_ge_succ_of_checks (N := 415) (r := 21) (by omega) Green14.Certificate.valid_21

theorem W_3_22_lower_proved : Green14.W 3 22 ≥ 464 := by
  exact W_ge_succ_of_checks (N := 463) (r := 22) (by omega) Green14.Certificate.valid_22

theorem W_3_23_lower_proved : Green14.W 3 23 ≥ 516 := by
  exact W_ge_succ_of_checks (N := 515) (r := 23) (by omega) Green14.Certificate.valid_23

theorem W_3_24_lower_proved : Green14.W 3 24 ≥ 593 := by
  exact W_ge_succ_of_checks (N := 592) (r := 24) (by omega) Green14.Certificate.valid_24

theorem W_3_25_lower_proved : Green14.W 3 25 ≥ 656 := by
  exact W_ge_succ_of_checks (N := 655) (r := 25) (by omega) Green14.Certificate.valid_25

theorem W_3_26_lower_proved : Green14.W 3 26 ≥ 727 := by
  exact W_ge_succ_of_checks (N := 726) (r := 26) (by omega) Green14.Certificate.valid_26

theorem W_3_27_lower_proved : Green14.W 3 27 ≥ 770 := by
  exact W_ge_succ_of_checks (N := 769) (r := 27) (by omega) Green14.Certificate.valid_27

theorem W_3_28_lower_proved : Green14.W 3 28 ≥ 827 := by
  exact W_ge_succ_of_checks (N := 826) (r := 28) (by omega) Green14.Certificate.valid_28

theorem W_3_29_lower_proved : Green14.W 3 29 ≥ 868 := by
  exact W_ge_succ_of_checks (N := 867) (r := 29) (by omega) Green14.Certificate.valid_29

theorem W_3_30_lower_proved : Green14.W 3 30 ≥ 903 := by
  exact W_ge_succ_of_checks (N := 902) (r := 30) (by omega) Green14.Certificate.valid_30

theorem W_3_31_lower_proved : Green14.W 3 31 ≥ 931 := by
  exact W_ge_succ_of_checks (N := 930) (r := 31) (by omega) Green14.Certificate.valid_31

theorem W_3_32_lower_proved : Green14.W 3 32 ≥ 1007 := by
  exact W_ge_succ_of_checks (N := 1006) (r := 32) (by omega) Green14.Certificate.valid_32

theorem W_3_33_lower_proved : Green14.W 3 33 ≥ 1064 := by
  exact W_ge_succ_of_checks (N := 1063) (r := 33) (by omega) Green14.Certificate.valid_33

theorem W_3_34_lower_proved : Green14.W 3 34 ≥ 1144 := by
  exact W_ge_succ_of_checks (N := 1143) (r := 34) (by omega) Green14.Certificate.valid_34

theorem W_3_35_lower_proved : Green14.W 3 35 ≥ 1205 := by
  exact W_ge_succ_of_checks (N := 1204) (r := 35) (by omega) Green14.Certificate.valid_35

theorem W_3_36_lower_proved : Green14.W 3 36 ≥ 1258 := by
  exact W_ge_succ_of_checks (N := 1257) (r := 36) (by omega) Green14.Certificate.valid_36

theorem W_3_37_lower_proved : Green14.W 3 37 ≥ 1339 := by
  exact W_ge_succ_of_checks (N := 1338) (r := 37) (by omega) Green14.Certificate.valid_37

theorem W_3_38_lower_proved : Green14.W 3 38 ≥ 1379 := by
  exact W_ge_succ_of_checks (N := 1378) (r := 38) (by omega) Green14.Certificate.valid_38

theorem W_3_39_lower_proved : Green14.W 3 39 ≥ 1419 := by
  exact W_ge_succ_of_checks (N := 1418) (r := 39) (by omega) Green14.Certificate.valid_39

end Green14.CertificateBridge
