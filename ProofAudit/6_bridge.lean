import FormalConjectures.Paper.MonochromaticQuantumGraph
import Mathlib.Data.BitVec

namespace MonochromaticQuantumGraph

/-- Apply a ring homomorphism to every edge weight. -/
def mapWeights {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) {N D : Nat} (W : WeightsN N D α) : WeightsN N D β :=
  fun e => f (W e)

lemma pmSumListAux_map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) {N D : Nat} (W : WeightsN N D α)
    (ι : V N → Fin D) :
    ∀ n L,
      f (pmSumListAux W ι n L) =
        pmSumListAux (mapWeights f W) ι n L := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro L
      cases n with
      | zero => simp [pmSumListAux]
      | succ n =>
          cases n with
          | zero => simp [pmSumListAux]
          | succ n =>
              cases L with
              | nil => simp [pmSumListAux]
              | cons v vs =>
                  cases vs with
                  | nil => simp [pmSumListAux]
                  | cons u us =>
                      simp [pmSumListAux, mapWeights, ih n (by omega)]

lemma pmSumN_map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) {N D : Nat} (W : WeightsN N D α)
    (ι : V N → Fin D) :
    f (pmSumN N D W ι) = pmSumN N D (mapWeights f W) ι := by
  unfold pmSumN pmSumList
  exact pmSumListAux_map f W ι _ _

lemma EqSystemN.map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) {N D : Nat} {W : WeightsN N D α}
    (hW : EqSystemN N D W) : EqSystemN N D (mapWeights f W) := by
  intro ι
  rw [← pmSumN_map f W ι, hW ι]
  by_cases h : allEqual ι <;> simp [h]

abbrev F2 := BitVec 1

/-- An integer solution would reduce to a characteristic-two solution. -/
theorem no_eqSystem6_d3_int_of_no_f2
    (hF2 : ¬ ∃ W : WeightsN 6 3 F2, EqSystemN 6 3 W) :
    ¬ ∃ W : WeightsN 6 3 Int, EqSystemN 6 3 W := by
  rintro ⟨W, hW⟩
  apply hF2
  exact ⟨mapWeights (Int.castRingHom F2) W,
    hW.map (Int.castRingHom F2)⟩

#print axioms pmSumN_map
#print axioms EqSystemN.map
#print axioms no_eqSystem6_d3_int_of_no_f2

end MonochromaticQuantumGraph
