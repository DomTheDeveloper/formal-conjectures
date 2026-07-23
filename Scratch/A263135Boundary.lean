import Scratch.A263135Rows

namespace OeisA263135

/-- Row directions preserved by a directed honeycomb edge. -/
def preservedRows (vd : Vertex × Direction) : Finset RowKind :=
  Finset.univ.filter fun r => rowCoord r (neighbor vd.1 vd.2) = rowCoord r vd.1

private theorem preservedRows_eq (v : Vertex) (d : Direction) :
    preservedRows (v, d) =
      match d with
      | .same => {RowKind.first, RowKind.second}
      | .horizontal => {RowKind.second, RowKind.diagonal}
      | .diagonal => {RowKind.first, RowKind.diagonal} := by
  rcases v with ⟨i, j, side⟩
  cases side <;> cases d <;>
    ext r <;> cases r <;>
      simp [preservedRows, rowCoord, neighbor] <;> omega

@[simp]
theorem card_preservedRows (v : Vertex) (d : Direction) :
    (preservedRows (v, d)).card = 2 := by
  rw [preservedRows_eq]
  cases d <;> simp

/-- Boundary darts lying along the rows of kind `r`. -/
def rowBoundaryDarts (r : RowKind) (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (boundaryDarts S).filter fun vd => r ∈ preservedRows vd

/-- Every boundary dart is counted in exactly two of the three row families. -/
theorem sum_rowBoundaryDarts_card (S : Finset Vertex) :
    (∑ r : RowKind, (rowBoundaryDarts r S).card) = 2 * edgeBoundary S := by
  classical
  have hrow (r : RowKind) :
      (rowBoundaryDarts r S).card =
        ∑ vd ∈ boundaryDarts S, if r ∈ preservedRows vd then 1 else 0 := by
    symm
    simpa [rowBoundaryDarts] using
      (Finset.sum_boole (R := ℕ)
        (fun vd : Vertex × Direction => r ∈ preservedRows vd) (boundaryDarts S))
  calc
    (∑ r : RowKind, (rowBoundaryDarts r S).card) =
        ∑ r : RowKind, ∑ vd ∈ boundaryDarts S,
          if r ∈ preservedRows vd then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hrow r
    _ = ∑ vd ∈ boundaryDarts S, ∑ r : RowKind,
          if r ∈ preservedRows vd then 1 else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ vd ∈ boundaryDarts S, (preservedRows vd).card := by
            apply Finset.sum_congr rfl
            intro vd hv
            simpa using
              (Finset.sum_boole (R := ℕ)
                (fun r : RowKind => r ∈ preservedRows vd) Finset.univ)
    _ = ∑ vd ∈ boundaryDarts S, 2 := by
            apply Finset.sum_congr rfl
            intro vd hv
            rcases vd with ⟨v, d⟩
            simp
    _ = 2 * edgeBoundary S := by
            simp [edgeBoundary, mul_comm]

end OeisA263135
