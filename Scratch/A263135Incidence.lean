import Scratch.A263135Symmetry

namespace OeisA263135

/-- Directed honeycomb incidences whose two endpoints lie in `S`. -/
def internalDarts (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (S ×ˢ Finset.univ).filter fun vd => neighbor vd.1 vd.2 ∈ S

/-- Internal darts based at the `A` side. -/
def aInternalDarts (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (internalDarts S).filter fun vd => vd.1.side = false

/-- Internal darts based at the `B` side. -/
def bInternalDarts (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (internalDarts S).filter fun vd => vd.1.side = true

private theorem internal_boundary_disjoint (S : Finset Vertex) :
    Disjoint (internalDarts S) (boundaryDarts S) := by
  rw [Finset.disjoint_left]
  intro vd hi hb
  exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hi).2

private theorem internal_union_boundary (S : Finset Vertex) :
    internalDarts S ∪ boundaryDarts S = S ×ˢ Finset.univ := by
  ext vd
  by_cases h : neighbor vd.1 vd.2 ∈ S <;>
    simp [internalDarts, boundaryDarts, h]

/-- Every vertex has three directed incidences, split into internal and boundary darts. -/
theorem card_internalDarts_add_edgeBoundary (S : Finset Vertex) :
    (internalDarts S).card + edgeBoundary S = 3 * S.card := by
  rw [edgeBoundary, ← Finset.card_union_of_disjoint (internal_boundary_disjoint S),
    internal_union_boundary]
  have hdir : Fintype.card Direction = 3 := by decide
  simp [hdir, mul_comm]

private theorem a_b_internal_disjoint (S : Finset Vertex) :
    Disjoint (aInternalDarts S) (bInternalDarts S) := by
  rw [Finset.disjoint_left]
  intro vd ha hb
  have hfalse := (Finset.mem_filter.mp ha).2
  have htrue := (Finset.mem_filter.mp hb).2
  simp [hfalse] at htrue

private theorem a_union_b_internal (S : Finset Vertex) :
    aInternalDarts S ∪ bInternalDarts S = internalDarts S := by
  ext vd
  simp [aInternalDarts, bInternalDarts]
  cases h : vd.1.side <;> simp [h]

/-- Reversal of a directed honeycomb incidence. -/
def reverseDart (vd : Vertex × Direction) : Vertex × Direction :=
  (neighbor vd.1 vd.2, vd.2)

@[simp]
theorem reverseDart_involutive (vd : Vertex × Direction) :
    reverseDart (reverseDart vd) = vd := by
  rcases vd with ⟨v, d⟩
  simp [reverseDart]

private theorem reverseDart_injective : Function.Injective reverseDart :=
  Function.LeftInverse.injective reverseDart_involutive

private theorem reverse_a_mem_b (S : Finset Vertex) {vd : Vertex × Direction}
    (h : vd ∈ aInternalDarts S) : reverseDart vd ∈ bInternalDarts S := by
  rcases vd with ⟨v, d⟩
  rcases Finset.mem_filter.mp h with ⟨hint, hvside⟩
  rcases Finset.mem_filter.mp hint with ⟨hprod, hnmem⟩
  rcases Finset.mem_product.mp hprod with ⟨hvS, hd⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hnmem, hd⟩, by
      simpa [reverseDart] using hvS⟩
  · rcases v with ⟨i, j, side⟩
    cases side <;> cases d <;> simp [reverseDart, neighbor] at hvside ⊢

private theorem reverse_b_mem_a (S : Finset Vertex) {vd : Vertex × Direction}
    (h : vd ∈ bInternalDarts S) : reverseDart vd ∈ aInternalDarts S := by
  rcases vd with ⟨v, d⟩
  rcases Finset.mem_filter.mp h with ⟨hint, hvside⟩
  rcases Finset.mem_filter.mp hint with ⟨hprod, hnmem⟩
  rcases Finset.mem_product.mp hprod with ⟨hvS, hd⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hnmem, hd⟩, by
      simpa [reverseDart] using hvS⟩
  · rcases v with ⟨i, j, side⟩
    cases side <;> cases d <;> simp [reverseDart, neighbor] at hvside ⊢

/-- Internal darts based at the two bipartite sides are equinumerous. -/
theorem card_aInternalDarts_eq_card_bInternalDarts (S : Finset Vertex) :
    (aInternalDarts S).card = (bInternalDarts S).card := by
  apply Nat.le_antisymm
  · exact Finset.card_le_card_of_injOn reverseDart
      (fun _ h => reverse_a_mem_b S h)
      (fun _ _ _ _ h => reverseDart_injective h)
  · exact Finset.card_le_card_of_injOn reverseDart
      (fun _ h => reverse_b_mem_a S h)
      (fun _ _ _ _ h => reverseDart_injective h)

/-- The original `contacts` sum is the cardinality of the `A`-based internal darts. -/
theorem contacts_eq_card_aInternalDarts (S : Finset Vertex) :
    contacts S = (aInternalDarts S).card := by
  classical
  unfold contacts aInternalDarts internalDarts
  let D : Finset (Vertex × Direction) :=
    ((S ×ˢ Finset.univ).filter fun vd => neighbor vd.1 vd.2 ∈ S).filter
      fun vd => vd.1.side = false
  change (∑ v ∈ S, if v.side = true then 0 else
      ∑ d ∈ Finset.univ, if neighbor v d ∈ S then 1 else 0) = D.card
  have hmap : (D : Set (Vertex × Direction)).MapsTo Prod.fst S := by
    intro vd hv
    have hv' : vd ∈ D := hv
    exact (Finset.mem_product.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hv').1).1).1
  have hcard : D.card =
      ∑ v ∈ S, (D.filter fun vd => Prod.fst vd = v).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  rw [hcard]
  apply Finset.sum_congr rfl
  intro v hv
  cases hside : v.side
  · let E : Finset Direction := Finset.univ.filter fun d => neighbor v d ∈ S
    let F : Finset (Vertex × Direction) := D.filter fun vd => Prod.fst vd = v
    have hsum :
        (∑ d ∈ Finset.univ, if neighbor v d ∈ S then 1 else 0) = E.card := by
      rw [Finset.card_eq_sum_ones]
      simp [E]
    rw [hsum]
    change E.card = F.card
    refine Finset.card_bij (fun d _hd => (v, d)) ?_ ?_ ?_
    · intro d hd
      have hdn : neighbor v d ∈ S := (Finset.mem_filter.mp hd).2
      simp [F, D, hv, hside, hdn]
    · intro d₁ hd₁ d₂ hd₂ hpair
      exact congrArg Prod.snd hpair
    · intro vd hvd
      rcases vd with ⟨w, d⟩
      have hwv : w = v := (Finset.mem_filter.mp hvd).2
      subst w
      have hvdD : (v, d) ∈ D := (Finset.mem_filter.mp hvd).1
      have hn : neighbor v d ∈ S :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hvdD).1).2
      refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hn⟩, rfl⟩
  · simp [D, hside]

/-- The number of directed internal darts is twice the contact count. -/
theorem card_internalDarts_eq_two_mul_contacts (S : Finset Vertex) :
    (internalDarts S).card = 2 * contacts S := by
  calc
    (internalDarts S).card = (aInternalDarts S ∪ bInternalDarts S).card := by
      rw [a_union_b_internal]
    _ = (aInternalDarts S).card + (bInternalDarts S).card :=
      Finset.card_union_of_disjoint (a_b_internal_disjoint S)
    _ = (aInternalDarts S).card + (aInternalDarts S).card := by
      rw [← card_aInternalDarts_eq_card_bInternalDarts S]
    _ = 2 * contacts S := by
      rw [← contacts_eq_card_aInternalDarts S]
      omega

/-- Incidence bookkeeping for every finite honeycomb set. -/
theorem three_mul_card_eq_two_mul_contacts_add_boundary (S : Finset Vertex) :
    3 * S.card = 2 * contacts S + edgeBoundary S := by
  have h := card_internalDarts_add_edgeBoundary S
  rw [card_internalDarts_eq_two_mul_contacts] at h
  exact h.symm

end OeisA263135
