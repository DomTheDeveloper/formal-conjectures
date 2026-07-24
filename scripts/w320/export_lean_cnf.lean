/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import FormalConjectures.GreensOpenProblems.Green14CNFEncoding

open Green14.CNFEncoding

/-- Emit the exact Lean-defined `W(3,20)` CNF in DIMACS format. -/
def main : IO Unit :=
  IO.print w320CNF.dimacs
