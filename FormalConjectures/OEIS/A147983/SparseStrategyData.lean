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

import FormalConjectures.OEIS.A147983.StrategyCertificate

/-!
# Sparse packed response tables for the 10 × 42 Chomp witness

A concrete certificate stores every ten-row position in one 60-bit natural number and one packed
30-bit response for each legal opponent move.  `offsets[i]` points to the first response for
carrier position `i`; legal moves are ordered lexicographically by bite row and target.  The reply
storage is a total lookup function, allowing generated data to be split into independent chunks.
Missing or malformed data evaluates to an invalid default, so the data producer is not trusted.
A proof of `SparseStrategyData.Valid` is converted into the exact `StrategyCertificate` used by the
final theorem.
-/

namespace OeisA147983

/-- One decoded response-table cell. -/
structure SparseReply where
  next : ℕ
  row : ℕ
  target : ℕ
  deriving DecidableEq, Repr

/-- Packed carrier positions, per-position offsets, and a total packed-reply lookup. -/
structure SparseStrategyData where
  positions : Array ℕ
  offsets : Array ℕ
  replyCode : ℕ → ℕ

namespace SparseStrategyData

/-- Unpack ten six-bit row lengths from a natural number. -/
def unpackPosition (code : ℕ) : List ℕ :=
  (List.range 10).map fun row => (code / (64 ^ row)) % 64

/-- Decode `next` in bits 0–19, `row` in bits 20–23, and `target` in bits 24–29. -/
def unpackReply (code : ℕ) : SparseReply :=
  { next := code % 1048576
    row := (code / 1048576) % 16
    target := (code / 16777216) % 64 }

/-- Decode one carrier position. -/
def positionAt (D : SparseStrategyData) (i : Fin D.positions.size) : List ℕ :=
  unpackPosition D.positions[i]

/-- Number of legal bite targets in one row. -/
def rowMoveCount (p : List ℕ) (row : ℕ) : ℕ :=
  if row = 0 then p.getD row 0 - 1 else p.getD row 0

/-- Number of legal moves in rows strictly before `row`. -/
def movesBefore (p : List ℕ) (row : ℕ) : ℕ :=
  ((List.range row).map fun r => rowMoveCount p r).sum

/-- Zero-based response index within one position's sparse block. -/
def localMoveIndex (p : List ℕ) (row target : ℕ) : ℕ :=
  movesBefore p row + if row = 0 then target - 1 else target

/-- Read and decode one response without trusting any generated dimension. -/
def replyAt (D : SparseStrategyData) (i : Fin D.positions.size)
    (row : Fin 10) (target : Fin 43) : SparseReply :=
  let p := D.positionAt i
  let base := D.offsets.getD i.1 0
  unpackReply (D.replyCode (base + localMoveIndex p row.1 target.1))

/-- The finite carrier represented by the packed position array. -/
def carrier (D : SparseStrategyData) : Set (List ℕ) :=
  Set.range D.positionAt

/-- One sparse response cell is sound for the corresponding legal opponent move. -/
def ReplyValid (D : SparseStrategyData) (i : Fin D.positions.size)
    (row : Fin 10) (target : Fin 43) : Prop :=
  let p := D.positionAt i
  let q := bite row.1 target.1 p
  let response := D.replyAt i row target
  response.next < D.positions.size ∧
    response.row < q.length ∧
    response.target < q.getD response.row 0 ∧
    (response.row = 0 → 0 < response.target) ∧
    unpackPosition (D.positions.getD response.next 0) =
      bite response.row response.target q

/-- Finite validity conditions for a packed sparse response table.

The offset and reply functions are deliberately not trusted separately: every legal move must
retrieve a sound response through `replyAt`.  Incorrect dimensions or offsets therefore make this
proposition false. -/
def Valid (D : SparseStrategyData) : Prop :=
  (∀ i : Fin D.positions.size,
      (D.positionAt i).length = 10 ∧
        ∀ row : Fin 10, (D.positionAt i).getD row.1 0 ≤ 42) ∧
    (∀ (i : Fin D.positions.size) (row : Fin 10) (target : Fin 43),
      target.1 < (D.positionAt i).getD row.1 0 →
      (row.1 = 0 → 0 < target.1) →
      D.ReplyValid i row target) ∧
    (∃ i : Fin D.positions.size, D.positionAt i = child₁) ∧
    (∃ i : Fin D.positions.size, D.positionAt i = child₂) ∧
    (∃ i : Fin D.positions.size, D.positionAt i = child₃)

/-- A valid sparse packed table is a genuine closed second-player strategy. -/
def strategyCertificate (D : SparseStrategyData) (hD : D.Valid) : StrategyCertificate where
  carrier := D.carrier
  reply := by
    rcases hD with ⟨hshape, hresponse, _, _, _⟩
    intro p hp q hpq
    rcases hp with ⟨i, rfl⟩
    rcases hpq with ⟨row, target, hrow, htarget, hpoison, rfl⟩
    have hlength : (D.positionAt i).length = 10 := (hshape i).1
    have hrow10 : row < 10 := by
      rw [hlength] at hrow
      exact hrow
    have hwidth : (D.positionAt i).getD row 0 ≤ 42 :=
      (hshape i).2 ⟨row, hrow10⟩
    have htarget43 : target < 43 := by omega
    let rowFin : Fin 10 := ⟨row, hrow10⟩
    let targetFin : Fin 43 := ⟨target, htarget43⟩
    have hvalid := hresponse i rowFin targetFin (by simpa [rowFin, targetFin] using htarget) (by
      simpa [rowFin, targetFin] using hpoison)
    let response := D.replyAt i rowFin targetFin
    rcases hvalid with ⟨hnext, hreplyRow, hreplyTarget, hreplyPoison, hreplyEq⟩
    let next : Fin D.positions.size := ⟨response.next, hnext⟩
    refine ⟨D.positionAt next, ⟨next, rfl⟩, ?_⟩
    refine ⟨response.row, response.target, hreplyRow, hreplyTarget, hreplyPoison, ?_⟩
    simpa [positionAt, next, response, Array.getD, hnext] using hreplyEq
  child₁_mem := by
    rcases hD.2.2.1 with ⟨i, hi⟩
    exact ⟨i, hi⟩
  child₂_mem := by
    rcases hD.2.2.2.1 with ⟨i, hi⟩
    exact ⟨i, hi⟩
  child₃_mem := by
    rcases hD.2.2.2.2 with ⟨i, hi⟩
    exact ⟨i, hi⟩

/-- A valid sparse packed response table proves the exact three-opening challenge. -/
@[category API, AMS 5]
theorem three_openings (D : SparseStrategyData) (hD : D.Valid) :
    IsWinningOpening rectangle child₁ ∧
      IsWinningOpening rectangle child₂ ∧
      IsWinningOpening rectangle child₃ ∧
      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ :=
  (D.strategyCertificate hD).three_openings

#print axioms strategyCertificate
#print axioms three_openings

end SparseStrategyData
end OeisA147983
