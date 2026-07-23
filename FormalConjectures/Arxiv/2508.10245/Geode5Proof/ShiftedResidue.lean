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

import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.CenteredCRT
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.ModularExtraction
import Mathlib.Algebra.CharP.Basic

/-!
# From one modular computation to one centered CRT congruence

This theorem is the interface between the verified modular recurrence and the
centered CRT uniqueness theorem.  Concrete residue modules only need to check
primality, denominator nonvanishing, and the computed modular value.
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- A verified modular value yields the shifted natural-number congruence. -/
theorem shifted_modEq_of_modular_value
    (p r : ℕ) [Fact p.Prime]
    (hden : modularDenominator p 1000 ≠ 0)
    (hcalc : modularGeode p 1000 = (r : ZMod p))
    (hanswer : answerValue ≡ r [MOD p]) :
    shiftedGeode ≡ shiftedAnswer [MOD p] := by
  have htrue : (geode5Diagonal 1000 : ZMod p) = (r : ZMod p) := by
    rw [← modularGeode_eq_cast p 1000 hden]
    exact hcalc
  have hans : (answerValue : ZMod p) = (r : ZMod p) :=
    (CharP.natCast_eq_natCast (ZMod p) p).2 hanswer
  have hcenter :
      (geode5Diagonal 1000 : ZMod p) + (crtShift : ZMod p) =
        (answerValue : ZMod p) + (crtShift : ZMod p) := by
    rw [htrue, hans]
  have hshiftedGeode :
      (shiftedGeode : ZMod p) =
        (geode5Diagonal 1000 : ZMod p) + (crtShift : ZMod p) := by
    have h := congrArg (fun z : ℤ => (z : ZMod p)) shiftedGeode_cast
    simpa using h
  apply (CharP.natCast_eq_natCast (ZMod p) p).1
  rw [hshiftedGeode]
  simpa [shiftedAnswer] using hcenter

#print axioms shifted_modEq_of_modular_value

end Arxiv.«2508.10245».Geode5Proof
