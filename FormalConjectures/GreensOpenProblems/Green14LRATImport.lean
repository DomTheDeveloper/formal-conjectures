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

import FormalConjectures.GreensOpenProblems.Green14LRATKernelChecker
import Lean

/-!
# Kernel-mode LRAT certificate importer

The LRAT text parser runs only at elaboration time. Its parsed `IntAction` list
is quoted into the generated theorem, and the proof obligation is discharged by
`Green14.LRATKernelV2.checkKernel_sound` with `decide +kernel`. Therefore an
incorrect parser result or malformed certificate can only make elaboration
fail; it cannot establish an unsound theorem.
-/

open Lean Elab Command
open Std.Tactic.BVDecide.LRAT

namespace Green14.LRATImport

private instance : Quote Int where
  quote
    | .ofNat n => Syntax.mkCApp ``Int.ofNat #[quote n]
    | .negSucc n => Syntax.mkCApp ``Int.negSucc #[quote n]

private instance : Quote IntAction where
  quote
    | .addEmpty id rup =>
        Syntax.mkCApp ``Action.addEmpty #[quote id, quote rup]
    | .addRup id clause rup =>
        Syntax.mkCApp ``Action.addRup #[quote id, quote clause, quote rup]
    | .addRat id clause pivot rup rat =>
        Syntax.mkCApp ``Action.addRat
          #[quote id, quote clause, quote pivot, quote rup, quote rat]
    | .del ids => Syntax.mkCApp ``Action.del #[quote ids]

/-- Read a certificate file during command elaboration. -/
def readFile' (path : String) : CommandElabM String := do
  try
    IO.FS.readFile (System.FilePath.mk path)
  catch error =>
    throwError "cannot read '{path}': {error.toMessageData}"

/-- Parse an LRAT file during elaboration and reject parse errors explicitly. -/
def loadLRAT (pathSyntax : TSyntax `str) : CommandElabM (Array IntAction) := do
  let path := pathSyntax.getString
  let text ← readFile' path
  match parseLRATProof text.toUTF8 with
  | .ok actions => return actions
  | .error error => throwError "LRAT parse error in '{path}': {error}"

/-- Emit a theorem proving a Lean-defined CNF unsatisfiable from pre-parsed
LRAT actions. Only the Boolean checker is evaluated by kernel reduction. -/
def emitKernelTheorem (name : Ident) (cnfTerm : Term)
    (actions : Array IntAction) : CommandElabM Unit := do
  let actionTerm := quote actions.toList
  elabCommand (← `(command|
    set_option maxRecDepth 1000000 in
    set_option maxHeartbeats 0 in
    theorem $name : Std.Sat.CNF.Unsat ($cnfTerm : Std.Sat.CNF Nat) :=
      Green14.LRATKernelV2.checkKernel_sound $cnfTerm $actionTerm
        (by decide +kernel)))

/--
`green14_lrat_cnf +kernel theoremName (cnfTerm) "proof.lrat"` reads and parses
the LRAT certificate during elaboration, embeds the resulting action list, and
creates `theoremName : cnfTerm.Unsat` using kernel-only checking.
-/
elab "green14_lrat_cnf " "+" noWs &"kernel" ppSpace name:ident ppSpace
    "(" cnfTerm:term ")" ppSpace lratFile:str : command => do
  let actions ← loadLRAT lratFile
  emitKernelTheorem name cnfTerm actions

end Green14.LRATImport
