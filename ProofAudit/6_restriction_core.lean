/-
Copyright 2026

Kernel audit of the color-restriction core from the uploaded N = 6
monochromatic quantum graph candidate. This file deliberately excludes the
missing theorem `QuantumGraphGlobal.no_eqSystem_int`.
-/

import FormalConjectures.Paper.MonochromaticQuantumGraph

open MonochromaticQuantumGraph

namespace MonochromaticQuantumGraph

def restrictColorWeightsCore {N d D : Nat} {alpha : Type}
    (f : Fin d -> Fin D) (W : WeightsN N D alpha) : WeightsN N d alpha :=
  fun e => W (mkEdge e.u e.v (f e.i) (f e.j))

def colorEmbeddingCore {d D : Nat} (h : d ≤ D) : Fin d -> Fin D :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩

lemma colorEmbeddingCore_injective {d D : Nat} (h : d ≤ D) :
    Function.Injective (colorEmbeddingCore h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun z : Fin D => z.val) hij

private lemma pmSumN_six_restrictColorWeightsCore
    {alpha : Type} [Semiring alpha] {d D : Nat}
    (f : Fin d -> Fin D) (W : WeightsN 6 D alpha)
    (iota : V 6 -> Fin d) :
    pmSumN 6 d (restrictColorWeightsCore f W) iota =
      pmSumN 6 D W (fun v => f (iota v)) := by
  simp [pmSumN, pmSumList, pmSumListAux, vertices,
    restrictColorWeightsCore, mkEdge]

private lemma allEqual_six_comp_iff_core
    {d D : Nat} (f : Fin d -> Fin D) (hf : Function.Injective f)
    (iota : V 6 -> Fin d) :
    allEqual (fun v => f (iota v)) ↔ allEqual iota := by
  simp [allEqual, allEqualList, vertices, hf.eq_iff]

theorem eqSystem6_restrictColors_core
    {alpha : Type} [Semiring alpha] {d D : Nat}
    (f : Fin d -> Fin D) (hf : Function.Injective f)
    {W : WeightsN 6 D alpha} (hW : EqSystemN 6 D W) :
    EqSystemN 6 d (restrictColorWeightsCore f W) := by
  intro iota
  calc
    pmSumN 6 d (restrictColorWeightsCore f W) iota =
        pmSumN 6 D W (fun v => f (iota v)) :=
      pmSumN_six_restrictColorWeightsCore f W iota
    _ = if allEqual (fun v => f (iota v)) then (1 : alpha) else 0 :=
      hW (fun v => f (iota v))
    _ = if allEqual iota then (1 : alpha) else 0 := by
      by_cases hi : allEqual iota
      · have hfi : allEqual (fun v => f (iota v)) :=
          (allEqual_six_comp_iff_core f hf iota).2 hi
        simp [hi, hfi]
      · have hfi : ¬ allEqual (fun v => f (iota v)) := by
          intro hcomp
          exact hi ((allEqual_six_comp_iff_core f hf iota).1 hcomp)
        simp [hi, hfi]

theorem no_eqSystem6_mono_colors_core
    {alpha : Type} [Semiring alpha] {d : Nat}
    (hd : ¬ ∃ W : WeightsN 6 d alpha, EqSystemN 6 d W) :
    ∀ D : Nat, d ≤ D →
      ¬ ∃ W : WeightsN 6 D alpha, EqSystemN 6 D W := by
  intro D hdD
  rintro ⟨W, hW⟩
  apply hd
  refine ⟨restrictColorWeightsCore (colorEmbeddingCore hdD) W, ?_⟩
  exact eqSystem6_restrictColors_core
    (colorEmbeddingCore hdD) (colorEmbeddingCore_injective hdD) hW

#print axioms eqSystem6_restrictColors_core
#print axioms no_eqSystem6_mono_colors_core

end MonochromaticQuantumGraph
