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

import FormalConjectures.Arxiv.«2508.10245».Geode5
import FormalConjectures.Arxiv.«2508.10245».Geode5Proof.CRT

/-!
# Final arithmetic bridge for the Geode5 benchmark

The moment/coefficient layer must supply nonnegativity, the rigorous upper bound,
and all 480 modular residues. The CRT module then forces the exact value.
-/

namespace Arxiv.«2508.10245».Geode5Proof

/-- Apply the audited CRT certificate to the Formal Conjectures definition. -/
theorem geode5_1000_of_certificate
    (hnonneg : 0 ≤ geode5Diagonal 1000)
    (hbound : Int.toNat (geode5Diagonal 1000) < upperBound)
    (hres : ∀ pr ∈ residuePairs,
      Int.toNat (geode5Diagonal 1000) ≡ pr.2 [MOD pr.1]) :
    geode5Diagonal 1000 = (answerValue : ℤ) := by
  have hnat : Int.toNat (geode5Diagonal 1000) = answerValue :=
    eq_answerValue_of_residues_of_lt_upperBound _ hres hbound
  calc
    geode5Diagonal 1000 = Int.toNat (geode5Diagonal 1000) := by
      symm
      exact Int.toNat_of_nonneg hnonneg
    _ = answerValue := by exact_mod_cast hnat

#print axioms geode5_1000_of_certificate

end Arxiv.«2508.10245».Geode5Proof
