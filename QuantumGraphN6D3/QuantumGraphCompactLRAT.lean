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

import Std.Tactic.BVDecide.Reflect

/-!
# A compact, reflected LRAT certificate container

This is only a space-efficient parser.  Soundness still comes entirely from
Lean's proved LRAT checker: malformed packed data either fails to parse or is
rejected by that checker.
-/

open Std Sat
open Std.Tactic.BVDecide

namespace QuantumGraphCompactLRAT

private partial def readNatAux (data : ByteArray) (position shift acc : Nat) :
    Option (Nat × Nat) :=
  if h : position < data.size then
    let byte := data[position]
    let acc := acc + (byte.toNat % 64) * 2 ^ shift
    if byte.toNat < 64 then
      some (acc, position + 1)
    else
      readNatAux data (position + 1) (shift + 6) acc
  else
    none

private def readNat (data : ByteArray) (position : Nat) : Option (Nat × Nat) :=
  readNatAux data position 0 0

private def decodeInt (code : Nat) : Int :=
  if code % 2 = 0 then
    Int.ofNat (code / 2)
  else
    -Int.ofNat (code / 2)

private def applyDelta (base code : Nat) : Option Nat :=
  if code % 2 = 0 then
    some (base + code / 2)
  else
    let amount := code / 2
    if amount ≤ base then some (base - amount) else none

private partial def readClauseAux (data : ByteArray) (remaining position : Nat)
    (acc : Array Int) : Option (Array Int × Nat) :=
  if remaining = 0 then
    some (acc, position)
  else do
    let (code, position) ← readNat data position
    readClauseAux data (remaining - 1) position (acc.push (decodeInt code))

private def readClause (data : ByteArray) (count position : Nat) :
    Option (Array Int × Nat) :=
  readClauseAux data count position #[]

private partial def readHintsAux (data : ByteArray) (remaining position previous : Nat)
    (acc : Array Nat) : Option (Array Nat × Nat) :=
  if remaining = 0 then
    some (acc, position)
  else do
    let (code, position) ← readNat data position
    let hint ← applyDelta previous code
    if hint = 0 then none
    else readHintsAux data (remaining - 1) position hint (acc.push hint)

private def readHints (data : ByteArray) (count position previous : Nat) :
    Option (Array Nat × Nat) :=
  readHintsAux data count position previous #[]

private partial def readDeletionsAux (data : ByteArray) (remaining position ident : Nat)
    (acc : Array Nat) : Option (Array Nat × Nat) :=
  if remaining = 0 then
    some (acc, position)
  else do
    let (gap, position) ← readNat data position
    if ident < gap then none
    else
      let deleted := ident - gap
      if deleted = 0 then none
      else readDeletionsAux data (remaining - 1) position ident (acc.push deleted)

private def readDeletions (data : ByteArray) (count position ident : Nat) :
    Option (Array Nat × Nat) :=
  readDeletionsAux data count position ident #[]

private partial def parseAux (data : ByteArray) (position previousId : Nat)
    (actions : Array LRAT.IntAction) : Option (Array LRAT.IntAction) :=
  if h : position < data.size then do
    let (header, position) ← readNat data position
    let ident := previousId + header / 2
    if header % 2 = 1 then
      let (count, position) ← readNat data position
      let (deleted, position) ← readDeletions data count position ident
      parseAux data position ident (actions.push (.del deleted))
    else
      let (clauseCount, position) ← readNat data position
      let (clause, position) ← readClause data clauseCount position
      let (hintCount, position) ← readNat data position
      let (hints, position) ← readHints data hintCount position ident
      let action : LRAT.IntAction :=
        if clause.isEmpty then .addEmpty ident hints else .addRup ident clause hints
      parseAux data position ident (actions.push action)
  else if position = data.size then
    some actions
  else
    none

def parseCompactProof (packed : String) : Option (Array LRAT.IntAction) :=
  parseAux packed.toUTF8 0 0 #[]

def verifyCompactCert (cnf : CNF Nat) (packed : String) : Bool :=
  match parseCompactProof packed with
  | some proof => LRAT.check proof cnf
  | none => false

theorem verifyCompactCert_correct (cnf : CNF Nat) (packed : String)
    (h : verifyCompactCert cnf packed = true) : cnf.Unsat := by
  unfold verifyCompactCert at h
  split at h
  · exact LRAT.check_sound _ _ h
  · contradiction

end QuantumGraphCompactLRAT