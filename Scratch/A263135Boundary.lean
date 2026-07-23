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

import Scratch.A263135Rows

namespace OeisA263135

/-- Row directions preserved by a directed honeycomb edge. -/
def preservedRows (vd : Vertex × Direction) : Finset RowKind :=
  Finset.univ.filter fun r => rowCoord r (neighbor vd.1 vd.2) = rowCoord r vd.1

@[simp]
theorem card_preservedRows (v : Vertex) (d : Direction) :
    (preservedRows (v, d)).card = 2 := by
  rcases v with ⟨i, j, side⟩
  cases side <;> cases d
  · have h : preservedRows (⟨i, j, false⟩, .same) =
        ({.first, .second} : Finset RowKind) := by
      ext r
      cases r <;> simp [preservedRows, rowCoord, neighbor] <;> omega
    rw [h]
    simp
  · have h : preservedRows (⟨i, j, false⟩, .horizontal) =
        ({.second, .diagonal} : Finset RowKind) := by
      ext r
      cases r <;> simp [preservedRows, rowCoord, neighbor] <;> omega
    rw [h]
    simp
  · have h : preservedRows (⟨i, j, false⟩, .diagonal) =
        ({.first, .diagonal} : Finset RowKind) := by
      ext r
      cases r <;> simp [preservedRows, rowCoord, neighbor] <;> omega
    rw [h]
    simp
  · have h : preservedRows (⟨i, j, true⟩, .same) =
        ({.first, .second} : Finset RowKind) := by
      ext r
      cases r <;> simp [preservedRows, rowCoord, neighbor] <;> omega
    rw [h]
    simp
  · have h : preservedRows (⟨i, j, true⟩, .horizontal) =
        ({.second, .diagonal} : Finset RowKind) := by
      ext r
      cases r <;> simp [preservedRows, rowCoord, neighbor] <;> omega
    rw [h]
    simp
  · have h : preservedRows (⟨i, j, true⟩, .diagonal) =
        ({.first, .diagonal} : Finset RowKind) := by
      ext r
      cases r <;> simp [preservedRows, rowCoord, neighbor] <;> omega
    rw [h]
    simp

/-- Boundary darts lying along the rows of kind `r`. -/
def rowBoundaryDarts (r : RowKind) (S : Finset Vertex) : Finset (Vertex × Direction) :=
  (boundaryDarts S).filter fun vd => r ∈ preservedRows vd

/-- Every boundary dart is counted in exactly two of the three row families. -/
theorem sum_rowBoundaryDarts_card (S : Finset Vertex) :
    (∑ r : RowKind, (rowBoundaryDarts r S).card) = 2 * edgeBoundary S := by
  classical
  simp_rw [rowBoundaryDarts, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [edgeBoundary]
  calc
    (∑ vd ∈ boundaryDarts S, ∑ r : RowKind, if r ∈ preservedRows vd then 1 else 0) =
        ∑ vd ∈ boundaryDarts S, (preservedRows vd).card := by
          apply Finset.sum_congr rfl
          intro vd _hvd
          have hfilter :
              Finset.univ.filter (fun r : RowKind => r ∈ preservedRows vd) =
                preservedRows vd := by
            ext r
            simp
          change (∑ r : RowKind, if r ∈ preservedRows vd then 1 else 0) =
            (preservedRows vd).card
          rw [← Finset.sum_filter, hfilter]
          simp
    _ = ∑ _vd ∈ boundaryDarts S, 2 := by
          apply Finset.sum_congr rfl
          intro vd _hvd
          rcases vd with ⟨v, d⟩
          simp
    _ = 2 * (boundaryDarts S).card := by simp [mul_comm]

end OeisA263135
