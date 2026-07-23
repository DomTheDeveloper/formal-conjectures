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
# Kernel checker for explicit finite Chomp strategy tables

The untrusted certificate generator supplies a finite array of carrier positions and a bounded
response table. For each carrier index, opponent row, and opponent target, one table entry records
an index of the next carrier position and the row/target of the legal response.

`ExplicitStrategyData.Valid` is a finite proposition. A concrete generated certificate may prove it
with ordinary kernel reduction (`by decide`) or with sharded lemmas. No external executable is part
of the proof chain.
-/

namespace OeisA147983

/-- One response-table cell. `next` indexes the next carrier position; `row` and `target` describe
the second player's bite. -/
structure ExplicitReply where
  next : ℕ
  row : ℕ
  target : ℕ
  deriving DecidableEq, Repr

/-- Explicit carrier positions and a three-dimensional response table. -/
structure ExplicitStrategyData where
  positions : Array (List ℕ)
  replies : Array (Array (Array ExplicitReply))

namespace ExplicitStrategyData

/-- The deliberately invalid default used for missing response cells. -/
def defaultReply : ExplicitReply :=
  { next := 0, row := 0, target := 0 }

/-- Read one response cell without trusting array dimensions. -/
def replyAt (D : ExplicitStrategyData) (i : Fin D.positions.size)
    (row : Fin 10) (target : Fin 43) : ExplicitReply :=
  (((D.replies.getD i.1 #[]).getD row.1 #[]).getD target.1 defaultReply)

/-- The carrier represented by the position array. -/
def carrier (D : ExplicitStrategyData) : Set (List ℕ) :=
  Set.range fun i : Fin D.positions.size => D.positions[i]

/-- One response cell is sound for a concrete legal opponent bite. -/
def ReplyValid (D : ExplicitStrategyData) (i : Fin D.positions.size)
    (row : Fin 10) (target : Fin 43) : Prop :=
  let p := D.positions[i]
  let q := bite row.1 target.1 p
  let response := D.replyAt i row target
  ∃ next : Fin D.positions.size,
    response.next = next.1 ∧
      response.row < q.length ∧
      response.target < q.getD response.row 0 ∧
      (response.row = 0 → 0 < response.target) ∧
      D.positions[next] = bite response.row response.target q

/-- Finite validity conditions for an explicit strategy table.

Every carrier position has exactly ten rows and width at most `42`. Every legal bounded opponent
move has a sound table response. Finally, the three claimed children occur in the carrier. -/
def Valid (D : ExplicitStrategyData) : Prop :=
  (∀ i : Fin D.positions.size,
      D.positions[i].length = 10 ∧
        ∀ row : Fin 10, D.positions[i].getD row.1 0 ≤ 42) ∧
    (∀ (i : Fin D.positions.size) (row : Fin 10) (target : Fin 43),
      target.1 < D.positions[i].getD row.1 0 →
      (row.1 = 0 → 0 < target.1) →
      D.ReplyValid i row target) ∧
    (∃ i : Fin D.positions.size, D.positions[i] = child₁) ∧
    (∃ i : Fin D.positions.size, D.positions[i] = child₂) ∧
    (∃ i : Fin D.positions.size, D.positions[i] = child₃)

/-- A valid explicit finite table is a genuine closed second-player strategy. -/
def strategyCertificate (D : ExplicitStrategyData) (hD : D.Valid) : StrategyCertificate where
  carrier := D.carrier
  reply := by
    rcases hD with ⟨hshape, hresponse, _, _, _⟩
    intro p hp q hpq
    rcases hp with ⟨i, rfl⟩
    rcases hpq with ⟨row, target, hrow, htarget, hpoison, rfl⟩
    have hlength : D.positions[i].length = 10 := (hshape i).1
    have hrow10 : row < 10 := by omega
    let rowFin : Fin 10 := ⟨row, hrow10⟩
    have hwidth : D.positions[i].getD row 0 ≤ 42 := by
      simpa [rowFin] using (hshape i).2 rowFin
    have htarget43 : target < 43 := by omega
    let targetFin : Fin 43 := ⟨target, htarget43⟩
    have hvalid := hresponse i rowFin targetFin (by simpa [rowFin] using htarget) (by
      simpa [rowFin, targetFin] using hpoison)
    let response := D.replyAt i rowFin targetFin
    rcases hvalid with ⟨next, _, hreplyRow, hreplyTarget, hreplyPoison, hreplyEq⟩
    refine ⟨D.positions[next], ⟨next, rfl⟩, ?_⟩
    exact ⟨response.row, response.target, hreplyRow, hreplyTarget, hreplyPoison, hreplyEq⟩
  child₁_mem := by
    rcases hD.2.2.1 with ⟨i, hi⟩
    exact ⟨i, hi⟩
  child₂_mem := by
    rcases hD.2.2.2.1 with ⟨i, hi⟩
    exact ⟨i, hi⟩
  child₃_mem := by
    rcases hD.2.2.2.2 with ⟨i, hi⟩
    exact ⟨i, hi⟩

/-- A valid explicit response table proves the exact three-opening challenge. -/
@[category API, AMS 5]
theorem three_openings (D : ExplicitStrategyData) (hD : D.Valid) :
    IsWinningOpening rectangle child₁ ∧
      IsWinningOpening rectangle child₂ ∧
      IsWinningOpening rectangle child₃ ∧
      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ :=
  (D.strategyCertificate hD).three_openings

#print axioms strategyCertificate
#print axioms three_openings

end ExplicitStrategyData
end OeisA147983
