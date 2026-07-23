import Scratch.A263135Staircase

namespace OeisA263135

/-- An occupied-row label attached to a vertex of `S`. -/
def rowLabel (r : RowKind) (S : Finset Vertex) (v : ↥S) : ↥(occupiedRows r S) :=
  ⟨rowCoord r v, Finset.mem_image.mpr ⟨v, v.property, rfl⟩⟩

/-- Rank of a vertex's row among all occupied rows in the chosen direction. -/
noncomputable def rowRank (r : RowKind) (S : Finset Vertex) (v : ↥S) :
    Fin (occupiedRows r S).card :=
  ((occupiedRows r S).orderIsoOfFin rfl).symm (rowLabel r S v)

private theorem orderIso_rowRank (r : RowKind) (S : Finset Vertex) (v : ↥S) :
    (occupiedRows r S).orderIsoOfFin rfl (rowRank r S v) = rowLabel r S v := by
  exact ((occupiedRows r S).orderIsoOfFin rfl).apply_symm_apply _

/-- Increasing row ranks imply increasing integer row coordinates. -/
theorem rowCoord_le_of_rowRank_le (r : RowKind) (S : Finset Vertex) (v w : ↥S)
    (h : rowRank r S v ≤ rowRank r S w) :
    rowCoord r v ≤ rowCoord r w := by
  have hmono := ((occupiedRows r S).orderIsoOfFin rfl).monotone h
  simpa [orderIso_rowRank] using hmono

/-- Equal row ranks are equivalent to equal row coordinates. -/
theorem rowRank_eq_iff_rowCoord_eq (r : RowKind) (S : Finset Vertex) (v w : ↥S) :
    rowRank r S v = rowRank r S w ↔ rowCoord r v = rowCoord r w := by
  constructor
  · intro h
    have hlabels : rowLabel r S v = rowLabel r S w := by
      rw [← orderIso_rowRank r S v, ← orderIso_rowRank r S w, h]
    exact congrArg Subtype.val hlabels
  · intro h
    apply ((occupiedRows r S).orderIsoOfFin rfl).injective
    rw [orderIso_rowRank, orderIso_rowRank]
    apply Subtype.ext
    exact h

/-- The symmetric-chain index of a cell in an `a × b` rectangle. -/
def rectangleChainIndex {a b : ℕ} (p : Fin a × Fin b) : ℕ :=
  min p.1.val (b - 1 - p.2.val)

private theorem le_of_complement_le_complement {b x y : ℕ}
    (hx : x < b) (hy : y < b)
    (h : b - 1 - y ≤ b - 1 - x) : x ≤ y := by
  omega

private theorem eq_of_complement_eq_complement {b x y : ℕ}
    (hx : x < b) (hy : y < b)
    (h : b - 1 - x = b - 1 - y) : x = y := by
  apply Nat.le_antisymm
  · exact le_of_complement_le_complement hx hy h.ge
  · exact le_of_complement_le_complement hy hx h.le

/-- Points with the same rectangle-chain index are comparable coordinatewise. -/
theorem rectangleChain_comparable {a b : ℕ} (p q : Fin a × Fin b)
    (h : rectangleChainIndex p = rectangleChainIndex q) :
    (p.1.val ≤ q.1.val ∧ p.2.val ≤ q.2.val) ∨
      (q.1.val ≤ p.1.val ∧ q.2.val ≤ p.2.val) := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  have hjlt : j.val < b := j.isLt
  have hllt : l.val < b := l.isLt
  unfold rectangleChainIndex at h
  by_cases hi : i.val ≤ b - 1 - j.val
  · rw [Nat.min_eq_left hi] at h
    by_cases hk : k.val ≤ b - 1 - l.val
    · rw [Nat.min_eq_left hk] at h
      have hik : i.val = k.val := h
      rcases le_total j.val l.val with hjl | hlj
      · exact Or.inl ⟨hik.le, hjl⟩
      · exact Or.inr ⟨hik.ge, hlj⟩
    · rw [Nat.min_eq_right (Nat.le_of_not_ge hk)] at h
      have hik : i.val ≤ k.val := by omega
      have hcomp : b - 1 - l.val ≤ b - 1 - j.val := by omega
      have hjl : j.val ≤ l.val :=
        le_of_complement_le_complement hjlt hllt hcomp
      exact Or.inl ⟨hik, hjl⟩
  · rw [Nat.min_eq_right (Nat.le_of_not_ge hi)] at h
    by_cases hk : k.val ≤ b - 1 - l.val
    · rw [Nat.min_eq_left hk] at h
      have hki : k.val ≤ i.val := by omega
      have hcomp : b - 1 - j.val ≤ b - 1 - l.val := by omega
      have hlj : l.val ≤ j.val :=
        le_of_complement_le_complement hllt hjlt hcomp
      exact Or.inr ⟨hki, hlj⟩
    · rw [Nat.min_eq_right (Nat.le_of_not_ge hk)] at h
      have hjl : j.val = l.val :=
        eq_of_complement_eq_complement hjlt hllt h
      rcases le_total i.val k.val with hik | hki
      · exact Or.inl ⟨hik, hjl.le⟩
      · exact Or.inr ⟨hki, hjl.ge⟩

/-- The last grid point of its symmetric chain. -/
def isRectangleChainLast {a b : ℕ} (p : Fin a × Fin b) : Prop :=
  p.1.val = a - 1 ∧
    p.2.val = b - 1 - rectangleChainIndex p

instance {a b : ℕ} (p : Fin a × Fin b) : Decidable (isRectangleChainLast p) := by
  unfold isRectangleChainLast
  infer_instance

/-- The two chains obtained after multiplying a rectangle chain by the two honeycomb sides.
`false` denotes the long chain (all `A` points plus the last `B` point); `true` denotes the short
chain (all remaining `B` points). -/
def boxSubchain {a b : ℕ} (p : Fin a × Fin b) (side : Bool) : Bool :=
  side && decide (¬ isRectangleChainLast p)

end OeisA263135
