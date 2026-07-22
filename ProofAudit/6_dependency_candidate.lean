/-
Copyright 2026

A color-restriction proof for the N = 6 monochromatic quantum graph system.

Audit copy. Requires `QuantumGraphGlobal.no_eqSystem_int`.
-/

import QuantumGraphGlobal

open MonochromaticQuantumGraph

namespace MonochromaticQuantumGraph

def restrictColorWeights {N d D : Nat} {alpha : Type}
    (f : Fin d -> Fin D) (W : WeightsN N D alpha) : WeightsN N d alpha :=
  fun e => W (mkEdge e.u e.v (f e.i) (f e.j))

def colorEmbedding {d D : Nat} (h : d ≤ D) : Fin d -> Fin D :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩

lemma colorEmbedding_injective {d D : Nat} (h : d ≤ D) :
    Function.Injective (colorEmbedding h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg Fin.val hij

private lemma pmSumN_six_restrictColorWeights
    {alpha : Type} [Semiring alpha] {d D : Nat}
    (f : Fin d -> Fin D) (W : WeightsN 6 D alpha)
    (iota : V 6 -> Fin d) :
    pmSumN 6 d (restrictColorWeights f W) iota =
      pmSumN 6 D W (fun v => f (iota v)) := by
  simp [pmSumN, pmSumList, pmSumListAux, vertices,
    restrictColorWeights, mkEdge]

private lemma allEqual_six_comp_iff
    {d D : Nat} (f : Fin d -> Fin D) (hf : Function.Injective f)
    (iota : V 6 -> Fin d) :
    allEqual (fun v => f (iota v)) ↔ allEqual iota := by
  simp [allEqual, allEqualList, vertices, hf.eq_iff]

theorem eqSystem6_restrictColors
    {alpha : Type} [Semiring alpha] {d D : Nat}
    (f : Fin d -> Fin D) (hf : Function.Injective f)
    {W : WeightsN 6 D alpha} (hW : EqSystemN 6 D W) :
    EqSystemN 6 d (restrictColorWeights f W) := by
  intro iota
  calc
    pmSumN 6 d (restrictColorWeights f W) iota =
        pmSumN 6 D W (fun v => f (iota v)) :=
      pmSumN_six_restrictColorWeights f W iota
    _ = if allEqual (fun v => f (iota v)) then (1 : alpha) else 0 :=
      hW (fun v => f (iota v))
    _ = if allEqual iota then (1 : alpha) else 0 := by
      rw [allEqual_six_comp_iff f hf iota]

theorem no_eqSystem6_mono_colors
    {alpha : Type} [Semiring alpha] {d : Nat}
    (hd : ¬ ∃ W : WeightsN 6 d alpha, EqSystemN 6 d W) :
    ∀ D : Nat, d ≤ D →
      ¬ ∃ W : WeightsN 6 D alpha, EqSystemN 6 D W := by
  intro D hdD
  rintro ⟨W, hW⟩
  apply hd
  refine ⟨restrictColorWeights (colorEmbedding hdD) W, ?_⟩
  exact eqSystem6_restrictColors
    (colorEmbedding hdD) (colorEmbedding_injective hdD) hW

theorem no_eqSystem6_ge3_int :
    ∀ D : Nat, D ≥ 3 →
      ¬ ∃ W : WeightsN 6 D Int, EqSystemN 6 D W := by
  exact no_eqSystem6_mono_colors QuantumGraphGlobal.no_eqSystem_int

theorem no_eqSystem6_d5_int :
    ¬ ∃ W : WeightsN 6 5 Int, EqSystemN 6 5 W := by
  exact no_eqSystem6_ge3_int 5 (by decide)

theorem no_eqSystem6_ge3_trinary_int :
    ∀ D : Nat, D ≥ 3 →
      ¬ ∃ W : WeightsN 6 D Int,
        (∀ e, W e = (-1 : Int) ∨ W e = 0 ∨ W e = 1) ∧
          EqSystemN 6 D W := by
  intro D hD
  rintro ⟨W, _, hW⟩
  exact no_eqSystem6_ge3_int D hD ⟨W, hW⟩

theorem no_eqSystem6_d5_trinary_int :
    ¬ ∃ W : WeightsN 6 5 Int,
      (∀ e, W e = (-1 : Int) ∨ W e = 0 ∨ W e = 1) ∧
        EqSystemN 6 5 W := by
  exact no_eqSystem6_ge3_trinary_int 5 (by decide)

theorem eqSystem6_no_solution_d5_int_full :
    answer(True) ↔
      ¬ ∃ W : WeightsN 6 5 Int, EqSystemN 6 5 W := by
  constructor
  · intro _
    exact no_eqSystem6_d5_int
  · intro _
    trivial

theorem eqSystem6_no_solution_ge3_int_full :
    answer(True) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D Int, EqSystemN 6 D W := by
  constructor
  · intro _
    exact no_eqSystem6_ge3_int
  · intro _
    trivial

theorem eqSystem6_no_solution_d5_trinary_int_full :
    answer(True) ↔
      ¬ ∃ W : WeightsN 6 5 Int,
        (∀ e, W e = (-1 : Int) ∨ W e = 0 ∨ W e = 1) ∧
          EqSystemN 6 5 W := by
  constructor
  · intro _
    exact no_eqSystem6_d5_trinary_int
  · intro _
    trivial

theorem eqSystem6_no_solution_ge3_trinary_int_full :
    answer(True) ↔
      ∀ D : Nat, D ≥ 3 →
        ¬ ∃ W : WeightsN 6 D Int,
          (∀ e, W e = (-1 : Int) ∨ W e = 0 ∨ W e = 1) ∧
            EqSystemN 6 D W := by
  constructor
  · intro _
    exact no_eqSystem6_ge3_trinary_int
  · intro _
    trivial

#print axioms eqSystem6_no_solution_ge3_int_full
#print axioms eqSystem6_no_solution_ge3_trinary_int_full

end MonochromaticQuantumGraph
