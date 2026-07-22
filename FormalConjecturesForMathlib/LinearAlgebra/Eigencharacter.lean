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
module

import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

open Function

noncomputable section

namespace Eigencharacter

variable {K E G ι : Type*}
  [Field K] [Field E] [Algebra K E]
  [Group G] [MulSemiringAction G E] [SMulCommClass G K E]

/-- Send an element to its orbit function under a group action. -/
def orbit : E →ₗ[K] (G → E) where
  toFun x g := g • x
  map_add' x y := by ext g; exact smul_add _ _ _
  map_smul' c x := by ext g; exact smul_comm _ _ _

/-- Lift a base-field-valued multiplicative character to the extension field. -/
def liftHom (χ : G →* K) : G →* E :=
  (algebraMap K E).comp χ

lemma liftHom_injective : Injective (liftHom : (G →* K) → (G →* E)) := by
  intro χ ψ h
  ext g
  apply (algebraMap K E).injective
  exact DFunLike.congr_fun h g

/-- Eigenvectors belonging to distinct base-field-valued characters are linearly independent. -/
theorem linearIndependent_of_eigencharacters
    (v : ι → E) (hv : ∀ i, v i ≠ 0)
    (χ : ι → G →* K) (hχ : Injective χ)
    (heig : ∀ i g, g • v i = algebraMap K E (χ i g) * v i) :
    LinearIndependent K v := by
  have hchar : LinearIndependent E (fun i => (liftHom (χ i) : G → E)) :=
    (linearIndependent_monoidHom G E).comp (fun i => liftHom (χ i))
      (liftHom_injective.comp hχ)
  have hscaled : LinearIndependent E
      ((fun i => Units.mk0 (v i) (hv i)) •
        (fun i => (liftHom (χ i) : G → E))) :=
    hchar.units_smul (fun i => Units.mk0 (v i) (hv i))
  have horbitE : LinearIndependent E (fun i => orbit (K := K) (E := E) (G := G) (v i)) := by
    convert hscaled using 1
    funext i g
    simp only [Pi.smul_apply', Units.smul_def, liftHom, MonoidHom.comp_apply, orbit]
    rw [heig i g]
    ring
  have horbitK : LinearIndependent K (fun i => orbit (K := K) (E := E) (G := G) (v i)) :=
    horbitE.restrict_scalars' K
  exact LinearIndependent.of_comp (orbit (K := K) (E := E) (G := G)) horbitK

variable [CharZero K] [CharZero E]

/-- The ±1 character carried by a nonzero vector whose orbit is contained in `{v,-v}`. -/
def signHom (v : E) (hv : v ≠ 0) (horbit : ∀ g : G, g • v = v ∨ g • v = -v) :
    G →* K where
  toFun g := if g • v = v then 1 else -1
  map_one' := by simp
  map_mul' g h := by
    have hneg : -v ≠ v := by
      simpa only [CharZero.neg_eq_self_iff] using hv
    rcases horbit g with hg | hg <;>
      rcases horbit h with hh | hh <;>
      simp [mul_smul, hg, hh, hneg]

@[simp] lemma signHom_apply_eq_one {v : E} {hv horbit} (g : G)
    (hg : g • v = v) : signHom (K := K) v hv horbit g = 1 := by
  simp [signHom, hg]

@[simp] lemma signHom_apply_eq_neg_one {v : E} {hv horbit} (g : G)
    (hg : g • v = -v) : signHom (K := K) v hv horbit g = -1 := by
  have hneg : -v ≠ v := by simpa only [CharZero.neg_eq_self_iff] using hv
  simp [signHom, hg, hneg]

lemma signHom_eigen {v : E} {hv horbit} (g : G) :
    g • v = algebraMap K E (signHom (K := K) v hv horbit g) * v := by
  rcases horbit g with hg | hg
  · simp [hg]
  · rw [signHom_apply_eq_neg_one (K := K) g hg]
    simp [hg]

lemma fixed_mul_of_signHom_eq {v w : E} {hv : v ≠ 0} {hw : w ≠ 0}
    {hv_orbit : ∀ g : G, g • v = v ∨ g • v = -v}
    {hw_orbit : ∀ g : G, g • w = w ∨ g • w = -w}
    (hχ : signHom (K := K) v hv hv_orbit = signHom (K := K) w hw hw_orbit)
    (g : G) : g • (v * w) = v * w := by
  have hχg := DFunLike.congr_fun hχ g
  rcases hv_orbit g with hvg | hvg <;> rcases hw_orbit g with hwg | hwg
  · simp [smul_mul', hvg, hwg]
  · have : (1 : K) = -1 := by
      simpa [signHom, hvg, hwg, CharZero.neg_eq_self_iff, hv, hw] using hχg
    exact (one_ne_neg_one (R := K) this).elim
  · have : (-1 : K) = 1 := by
      simpa [signHom, hvg, hwg, CharZero.neg_eq_self_iff, hv, hw] using hχg
    exact (neg_one_ne_one (R := K) this).elim
  · simp [smul_mul', hvg, hwg]

end Eigencharacter
