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

import FormalConjectures.GreensOpenProblems.Green14Core
import Mathlib.Combinatorics.HalesJewett

/-!
# Finite existence for the mixed van der Waerden guarantee set

The definition of `Green14.W` uses `sInf`, so a finite lower-bound certificate
also needs the guarantee set to be nonempty. This file derives that missing
finitary existence statement directly from the finite Hales--Jewett theorem.
-/

open Set
open scoped Classical

namespace Green14

/-- For positive progression lengths, some finite interval forces either a
color-0 progression of length `k` or a color-1 progression of length `r`.

This is deliberately only an existence theorem; its bound is the enormous
Hales--Jewett bound and is not intended for computation. -/
theorem mixedMonoAPGuaranteeSet_nonempty (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    (mixedMonoAPGuaranteeSet k r).Nonempty := by
  classical
  let m := max k r
  obtain ⟨ι, instι, hι⟩ :=
    Combinatorics.Line.exists_mono_in_high_dimension (Fin m) (Fin 2)
  letI : Fintype ι := instι
  let N := Fintype.card ι * (m - 1) + 1

  have word_sum_le (v : ι → Fin m) :
      ∑ i, (v i : ℕ) ≤ Fintype.card ι * (m - 1) := by
    calc
      ∑ i, (v i : ℕ) ≤ ∑ _i : ι, (m - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.le_pred_of_lt (v i).isLt
      _ = Fintype.card ι * (m - 1) := by simp

  refine ⟨N, ?_⟩
  intro coloring

  let wordPoint (v : ι → Fin m) : Icc 1 N :=
    ⟨1 + ∑ i, (v i : ℕ), by
      constructor
      · omega
      · dsimp only [N]
        have h := word_sum_le v
        omega⟩

  obtain ⟨line, color, hmono⟩ := hι (fun v ↦ coloring (wordPoint v))

  set active : Finset ι := {i | line.idxFun i = none} with hactive
  let a : ℕ := active.card
  let b : ℕ :=
    ∑ i ∈ activeᶜ, ((line.idxFun i).map fun x : Fin m ↦ (x : ℕ)).getD 0

  have ha : 0 < a := by
    apply Finset.card_pos.mpr
    refine ⟨line.proper.choose, ?_⟩
    rw [hactive, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, line.proper.choose_spec⟩

  have line_sum (x : Fin m) :
      ∑ i, ((line x i : Fin m) : ℕ) = a * (x : ℕ) + b := by
    rw [← Finset.sum_add_sum_compl active]
    congr 1
    · calc
        ∑ i ∈ active, ((line x i : Fin m) : ℕ) =
            ∑ _i ∈ active, (x : ℕ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hnone : line.idxFun i = none := by
            rw [hactive, Finset.mem_filter] at hi
            exact hi.2
          simp [Combinatorics.Line.coe_apply, hnone]
        _ = active.card * (x : ℕ) := by simp
        _ = a * (x : ℕ) := rfl
    · calc
        ∑ i ∈ activeᶜ, ((line x i : Fin m) : ℕ) =
            ∑ i ∈ activeᶜ,
              ((line.idxFun i).map fun y : Fin m ↦ (y : ℕ)).getD 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          cases hopt : line.idxFun i with
          | none =>
              have himem : i ∈ active := by
                rw [hactive, Finset.mem_filter]
                exact ⟨Finset.mem_univ _, hopt⟩
              exact ((Finset.mem_compl.mp hi) himem).elim
          | some y =>
              simp [Combinatorics.Line.coe_apply, hopt]
        _ = b := rfl

  have build_progression (q : ℕ) (hq : 1 ≤ q) (hqm : q ≤ m) :
      ∃ s : Finset (Icc 1 N),
        ({(z : ℕ) | z ∈ s}).IsAPOfLength q ∧
          ∀ z ∈ s, coloring z = color := by
    let liftFin : Fin q → Fin m := fun x ↦ Fin.castLE hqm x
    let value : Fin q → ℕ := fun x ↦ a * (x : ℕ) + b + 1
    have hvalue_inj : Function.Injective value := by
      intro x y hxy
      apply Fin.ext
      dsimp only [value] at hxy
      have hmul : a * (x : ℕ) = a * (y : ℕ) := by omega
      exact Nat.eq_of_mul_eq_mul_left ha hmul

    let point : Fin q → Icc 1 N := fun x ↦
      ⟨value x, by
        constructor
        · dsimp only [value]
          omega
        · have hp := (wordPoint (line (liftFin x))).property.2
          dsimp only [wordPoint] at hp
          rw [line_sum] at hp
          simpa [liftFin, value, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp⟩

    have hpoint_inj : Function.Injective point := by
      intro x y hxy
      apply hvalue_inj
      exact Subtype.ext_iff.mp hxy

    let emb : Fin q ↪ Icc 1 N := ⟨point, hpoint_inj⟩
    let s : Finset (Icc 1 N) := Finset.univ.map emb
    let T : Set ℕ := Set.range value

    have hT : T.IsAPOfLengthWith q (b + 1) a := by
      constructor
      · rw [_root_.ENat.card_coe_set_eq]
        change T.encard = (q : ℕ∞)
        have hTrange : T = value '' Set.univ := by
          ext z
          simp [T]
        rw [hTrange, hvalue_inj.encard_image]
        simp
      · ext z
        constructor
        · rintro ⟨x, rfl⟩
          refine ⟨x, ?_, ?_⟩
          · exact_mod_cast x.isLt
          · simp [value, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]
        · rintro ⟨n, hn, rfl⟩
          have hnq : n < q := by exact_mod_cast hn
          refine ⟨⟨n, hnq⟩, ?_⟩
          simp [value, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

    have hsT : ({(z : ℕ) | z ∈ s} : Set ℕ) = T := by
      ext z
      simp [s, emb, point, T, value]

    refine ⟨s, ?_, ?_⟩
    · rw [hsT]
      exact ⟨b + 1, a, hT⟩
    · intro z hz
      rcases Finset.mem_map.mp hz with ⟨x, -, rfl⟩
      change coloring (point x) = color
      have hpoint_word : point x = wordPoint (line (liftFin x)) := by
        apply Subtype.ext
        dsimp only [point, value, wordPoint]
        rw [line_sum]
        simp [liftFin, Nat.add_comm]
      rw [hpoint_word]
      exact hmono (liftFin x)

  fin_cases color
  · exact Or.inl (build_progression k hk (le_max_left k r))
  · exact Or.inr (build_progression r hr (le_max_right k r))

end Green14
