import QuantumGraphGlobal

/-!
# Color restriction for monochromatic quantum graphs

For a fixed number of vertices `N` and coefficient semiring `α`, a solution with `D` colors
restricts along every embedding `Fin d ↪ Fin D` to a solution with `d` colors. Consequently,
nonexistence at `d` colors implies nonexistence at every `D ≥ d`.

The final four theorems combine this structural reduction with the independently checked
`N = 6`, `D = 3` integer obstruction in `QuantumGraphGlobal`.
-/

namespace MonochromaticQuantumGraph
namespace ColorRestriction

section General

variable {α : Type*} [Semiring α]

/-- Pull a weighting back along an embedding of color sets. -/
def restrictWeights {N d D : Nat} (f : Fin d ↪ Fin D)
    (W : WeightsN N D α) : WeightsN N d α :=
  fun e => W (mkEdge e.u e.v (f e.i) (f e.j))

@[simp]
lemma restrictWeights_mkEdge {N d D : Nat} (f : Fin d ↪ Fin D)
    (W : WeightsN N D α) (u v : V N) (i j : Fin d) :
    restrictWeights f W (mkEdge u v i j) =
      W (mkEdge u v (f i) (f j)) := by
  rfl

/-- Injective relabeling preserves and reflects the monochromaticity predicate. -/
lemma allEqual_comp_embedding_iff {N d D : Nat} (f : Fin d ↪ Fin D)
    (ι : V N → Fin d) :
    allEqual (fun v => f (ι v)) ↔ allEqual ι := by
  unfold allEqual allEqualList
  apply List.IsChain.iff
  intro u v
  constructor
  · exact f.injective
  · exact congrArg f

/-- Pullback leaves the recursive perfect-matching sum unchanged. -/
lemma pmSumListAux_restrict {N d D : Nat} (f : Fin d ↪ Fin D)
    (W : WeightsN N D α) (ι : V N → Fin d) :
    ∀ n L,
      pmSumListAux (restrictWeights f W) ι n L =
        pmSumListAux W (fun v => f (ι v)) n L := by
  intro n
  refine Nat.twoStepInduction ?_ ?_ ?_ n
  · intro L
    rfl
  · intro L
    rfl
  · intro n ih _ihSucc L
    cases L with
    | nil => rfl
    | cons v vs =>
        cases vs with
        | nil => rfl
        | cons u us =>
            simp only [pmSumListAux, restrictWeights_mkEdge, ih]

/-- Pullback leaves the perfect-matching sum on the canonical vertex list unchanged. -/
lemma pmSumN_restrict {N d D : Nat} (f : Fin d ↪ Fin D)
    (W : WeightsN N D α) (ι : V N → Fin d) :
    pmSumN N d (restrictWeights f W) ι =
      pmSumN N D W (fun v => f (ι v)) := by
  unfold pmSumN pmSumList
  exact pmSumListAux_restrict f W ι _ _

/-- Every `D`-color solution restricts along an embedding `Fin d ↪ Fin D`. -/
lemma eqSystem_restrict {N d D : Nat} (f : Fin d ↪ Fin D)
    (W : WeightsN N D α) (hW : EqSystemN N D W) :
    EqSystemN N d (restrictWeights f W) := by
  intro ι
  calc
    pmSumN N d (restrictWeights f W) ι =
        pmSumN N D W (fun v => f (ι v)) :=
      pmSumN_restrict f W ι
    _ = (if allEqual (fun v => f (ι v)) then (1 : α) else 0) :=
      hW (fun v => f (ι v))
    _ = (if allEqual ι then (1 : α) else 0) := by
      rw [allEqual_comp_embedding_iff f ι]

/-- Solution existence is downward-closed in the number of colors. -/
theorem exists_eqSystem_of_embedding {N d D : Nat} (f : Fin d ↪ Fin D) :
    (∃ W : WeightsN N D α, EqSystemN N D W) →
      ∃ W : WeightsN N d α, EqSystemN N d W := by
  rintro ⟨W, hW⟩
  exact ⟨restrictWeights f W, eqSystem_restrict f W hW⟩

/-- Nonexistence is upward-closed in the number of colors. -/
theorem no_solution_of_color_le {N d D : Nat} (h : d ≤ D)
    (hsmall : ¬ ∃ W : WeightsN N d α, EqSystemN N d W) :
    ¬ ∃ W : WeightsN N D α, EqSystemN N D W := by
  intro hbig
  apply hsmall
  exact exists_eqSystem_of_embedding (Fin.castLEEmb h) hbig

/-- The whole nonexistence family for `D ≥ d` is equivalent to its base case `D = d`. -/
theorem no_solution_ge_iff_base {N d : Nat} :
    (∀ D : Nat, d ≤ D → ¬ ∃ W : WeightsN N D α, EqSystemN N D W) ↔
      ¬ ∃ W : WeightsN N d α, EqSystemN N d W := by
  constructor
  · intro h
    exact h d le_rfl
  · intro hsmall D hD
    exact no_solution_of_color_le hD hsmall

/-- A pointwise restriction on allowed edge weights is preserved by color restriction. -/
theorem no_pointwise_solution_of_color_le {N d D : Nat} {P : α → Prop}
    (h : d ≤ D)
    (hsmall : ¬ ∃ W : WeightsN N d α,
      (∀ e, P (W e)) ∧ EqSystemN N d W) :
    ¬ ∃ W : WeightsN N D α,
      (∀ e, P (W e)) ∧ EqSystemN N D W := by
  rintro ⟨W, hP, hW⟩
  apply hsmall
  let f : Fin d ↪ Fin D := Fin.castLEEmb h
  refine ⟨restrictWeights f W, ?_, eqSystem_restrict f W hW⟩
  intro e
  simpa only [restrictWeights] using
    hP (mkEdge e.u e.v (f e.i) (f e.j))

/-- For any coefficient semiring, the all-even-`N`, all-`D ≥ 3` statement is equivalent to
proving only the `D = 3` case for each relevant `N`. -/
theorem no_solution_even_ge6_ge3_iff_d3 :
    (∀ N : Nat, N ≥ 6 → Even N →
      ¬ ∃ W : WeightsN N 3 α, EqSystemN N 3 W) ↔
    (∀ N D : Nat, N ≥ 6 → Even N → D ≥ 3 →
      ¬ ∃ W : WeightsN N D α, EqSystemN N D W) := by
  constructor
  · intro h3 N D hN hEven hD
    exact no_solution_of_color_le hD (h3 N hN hEven)
  · intro hall N hN hEven
    exact hall N 3 hN hEven le_rfl

end General

section N6IntegerConsequences

/-- The `N = 6`, `D = 5` unrestricted integer obstruction. -/
theorem no_eqSystem6_d5_int :
    ¬ ∃ W : WeightsN 6 5 ℤ, EqSystemN 6 5 W := by
  exact no_solution_of_color_le (α := ℤ) (N := 6) (d := 3) (D := 5)
    (by omega) QuantumGraphGlobal.no_eqSystem_int

/-- The unrestricted integer obstruction for every `D ≥ 3`. -/
theorem no_eqSystem6_ge3_int :
    ∀ D : Nat, D ≥ 3 →
      ¬ ∃ W : WeightsN 6 D ℤ, EqSystemN 6 D W := by
  intro D hD
  exact no_solution_of_color_le (α := ℤ) (N := 6) (d := 3) (D := D)
    hD QuantumGraphGlobal.no_eqSystem_int

/-- The `D = 5` trinary obstruction. -/
theorem no_eqSystem6_d5_trinary_int :
    ¬ ∃ W : WeightsN 6 5 ℤ,
      (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
        EqSystemN 6 5 W := by
  rintro ⟨W, _, hW⟩
  exact no_eqSystem6_d5_int ⟨W, hW⟩

/-- The trinary obstruction for every `D ≥ 3`. -/
theorem no_eqSystem6_ge3_trinary_int :
    ∀ D : Nat, D ≥ 3 →
      ¬ ∃ W : WeightsN 6 D ℤ,
        (∀ e, W e = (-1 : ℤ) ∨ W e = 0 ∨ W e = 1) ∧
          EqSystemN 6 D W := by
  intro D hD
  rintro ⟨W, _, hW⟩
  exact no_eqSystem6_ge3_int D hD ⟨W, hW⟩

end N6IntegerConsequences

end ColorRestriction
end MonochromaticQuantumGraph

#print axioms MonochromaticQuantumGraph.ColorRestriction.exists_eqSystem_of_embedding
#print axioms MonochromaticQuantumGraph.ColorRestriction.no_solution_of_color_le
#print axioms MonochromaticQuantumGraph.ColorRestriction.no_pointwise_solution_of_color_le
#print axioms MonochromaticQuantumGraph.ColorRestriction.no_solution_even_ge6_ge3_iff_d3
#print axioms MonochromaticQuantumGraph.ColorRestriction.no_eqSystem6_d5_int
#print axioms MonochromaticQuantumGraph.ColorRestriction.no_eqSystem6_ge3_int
#print axioms MonochromaticQuantumGraph.ColorRestriction.no_eqSystem6_d5_trinary_int
#print axioms MonochromaticQuantumGraph.ColorRestriction.no_eqSystem6_ge3_trinary_int
