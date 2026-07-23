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

import FormalConjectures.OEIS.A147983.MoveClosureCertificate

/-!
# Symbolic certificate interface for the 10 × 42 Chomp witness

The strongest useful interface is a closed second-player strategy, not a classification of every
position outside the losing set. This alias keeps the final proof entry point explicit while the
concrete decision-diagram certificate is developed.
-/

namespace OeisA147983

/-- A complete symbolic certificate for the three target roots. -/
abbrev SymbolicCertificate := MoveClosureCertificate

/-- A complete symbolic certificate proves the exact three-opening statement. -/
@[category API, AMS 5]
theorem three_openings_of_symbolic_certificate (C : SymbolicCertificate) :
    IsWinningOpening rectangle child₁ ∧
      IsWinningOpening rectangle child₂ ∧
      IsWinningOpening rectangle child₃ ∧
      child₁ ≠ child₂ ∧ child₁ ≠ child₃ ∧ child₂ ≠ child₃ :=
  C.three_openings

end OeisA147983