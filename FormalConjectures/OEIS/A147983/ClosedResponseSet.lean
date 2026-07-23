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

import FormalConjectures.OEIS.A147983.KernelCertificate

/-!
# Closed two-ply response sets

A certificate may be represented extensionally as a set of purported losing positions.  Soundness
requires only that every opponent move has a legal reply back into the set and that the reply
strictly decreases a natural-number measure.  The certificate producer is untrusted; Lean checks
this closure condition and reconstructs the complete normal-play proof by strong induction.
-/

namespace OeisA147983.KernelCertificate

variable {P : Type} {Move : P → P → Prop} {measure : P → ℕ}

/-- A set closed under a strictly decreasing two-ply response strategy. -/
structure ClosedResponseSet (Move : P → P → Prop) (measure : P → ℕ) where
  carrier : Set P
  reply : ∀ ⦃p⦄, p ∈ carrier → ∀ ⦃q⦄, Move p q →
    ∃ r ∈ carrier, Move q r ∧ measure r < measure p

namespace ClosedResponseSet

/-- Every member of a closed response set is genuinely losing. -/
theorem outcome (C : ClosedResponseSet Move measure) {p : P} (hp : p ∈ C.carrier) :
    Outcome Move p false := by
  have all : ∀ k : ℕ, ∀ p : P, measure p = k → p ∈ C.carrier → Outcome Move p false := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro p hmeasure hp
        exact Outcome.losing (fun q hpq ↦ by
          obtain ⟨r, hr, hqr, hrlt⟩ := C.reply hp hpq
          have hrltk : measure r < k := by simpa [← hmeasure] using hrlt
          exact Outcome.winning hqr (ih _ hrltk r rfl hr))
  exact all _ p rfl hp

/-- Every member of a closed response set has a kernel-checked losing proof. -/
theorem isLosing (C : ClosedResponseSet Move measure) {p : P} (hp : p ∈ C.carrier) :
    IsLosing Move p :=
  ⟨C.outcome hp⟩

end ClosedResponseSet
end OeisA147983.KernelCertificate
