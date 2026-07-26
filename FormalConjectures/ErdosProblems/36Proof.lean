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

import FormalConjectures.ErdosProblems.«36»

/-!
# Exact proof of the first nontrivial minimum-overlap value
-/

open scoped Topology
open Filter

namespace Erdos36

private lemma one_le_overlap_kernel {A B : Finset ℤ} {a b : ℤ}
    (ha : a ∈ A) (hb : b ∈ B) : 1 ≤ Overlap A B (a - b) :=
  Finset.card_pos.mpr ⟨(a, b), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩⟩

private lemma overlap_le_card_mul_kernel {A B : Finset ℤ} (k : ℤ) :
    Overlap A B k ≤ A.card * B.card := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.product_eq_sprod, Finset.card_product]

private lemma maxOverlap_one_four_two_three_kernel :
    MaxOverlap ({1, 4} : Finset ℤ) ({2, 3} : Finset ℤ) = 1 := by
  apply le_antisymm
  · refine ciSup_le ?_
    intro k
    apply Finset.card_le_one.mpr
    rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq
    obtain ⟨hp_prod, hp_eq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hq_prod, hq_eq⟩ := Finset.mem_filter.mp hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp_prod
    obtain ⟨h4, h5⟩ := Finset.mem_product.mp hq_prod
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h4 h5
    simp only at hp_eq hq_eq
    have hdiff : p1 - p2 = q1 - q2 := by rw [hp_eq, hq_eq]
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
      rcases h4 with rfl | rfl <;> rcases h5 with rfl | rfl <;>
      first | rfl | (exfalso; omega)
  · refine le_ciSup_of_le ⟨4, ?_⟩ (-1) ?_
    · rintro x ⟨k, rfl⟩
      exact (overlap_le_card_mul_kernel k).trans (by decide)
    · exact one_le_overlap_kernel (by decide : (1 : ℤ) ∈ ({1, 4} : Finset ℤ))
        (by decide : (2 : ℤ) ∈ ({2, 3} : Finset ℤ))

/-- The balanced partition `{1,4} ⊔ {2,3}` proves `M(2) = 1`. -/
@[category test, AMS 5 11]
theorem M_two_kernel : M 2 = 1 := by
  apply le_antisymm
  · exact Nat.sInf_le
      ⟨{1, 4}, {2, 3}, by decide, by decide, by decide,
        maxOverlap_one_four_two_three_kernel⟩
  · apply le_csInf
    · exact ⟨_, {1, 4}, {2, 3}, by decide, by decide, by decide,
        maxOverlap_one_four_two_three_kernel⟩
    rintro x ⟨A, B, hd, hu, hsc, rfl⟩
    have hcardsum : A.card + B.card = 4 := by
      rw [← Finset.card_union_of_disjoint hd, hu]
      decide
    have hca : A.card = 2 := by omega
    have hcb : B.card = 2 := by omega
    obtain ⟨a, ha⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, hb⟩ : B.Nonempty := Finset.card_pos.mp (by omega)
    refine le_ciSup_of_le ⟨A.card * B.card, ?_⟩ (a - b)
      (one_le_overlap_kernel ha hb)
    rintro x ⟨k, rfl⟩
    exact overlap_le_card_mul_kernel k

#print axioms M_two_kernel

end Erdos36
