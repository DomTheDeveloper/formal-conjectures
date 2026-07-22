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

public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

@[expose] public section

open Set Topology MeasureTheory
open scoped Topology BigOperators

noncomputable section

namespace Set

variable {ι : Type*} [Fintype ι]
variable {α : Type*} [TopologicalSpace α]

private theorem mem_interior_of_mem_notMem_frontier {A : Set α} {x : α}
    (hx : x ∈ A) (hfront : x ∉ frontier A) : x ∈ interior A := by
  by_contra hxint
  apply hfront
  rw [frontier]
  exact ⟨subset_closure hx, hxint⟩

/-- The frontier of a finite product rectangle is contained in the union of the coordinate
frontiers. -/
theorem frontier_pi_subset_iUnion (A : ι → Set α) :
    frontier (Set.pi univ A) ⊆
      ⋃ i, (fun x : ι → α => x i) ⁻¹' frontier (A i) := by
  classical
  intro x hx
  by_contra hnot
  have hcoord : ∀ i, x i ∉ frontier (A i) := by
    simpa only [Set.mem_iUnion, Set.mem_preimage, not_exists] using hnot
  by_cases hxA : x ∈ Set.pi univ A
  · have hxint : x ∈ interior (Set.pi univ A) := by
      let U : Set (ι → α) := Set.pi univ (fun i => interior (A i))
      have hUopen : IsOpen U := isOpen_set_pi finite_univ (fun i _ => isOpen_interior)
      have hxU : x ∈ U := by
        intro i _
        exact mem_interior_of_mem_notMem_frontier (hxA i trivial) (hcoord i)
      have hUsub : U ⊆ Set.pi univ A := by
        intro y hy i _
        exact interior_subset (hy i trivial)
      exact interior_maximal hUsub hUopen hxU
    rw [frontier] at hx
    exact hx.2 hxint
  · have hex : ∃ i, x i ∉ A i := by
      simpa only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] using hxA
    obtain ⟨i, hi⟩ := hex
    let V : Set (ι → α) := (fun y => y i) ⁻¹' interior (A i)ᶜ
    have hVopen : IsOpen V := isOpen_interior.preimage (continuous_apply i)
    have hxV : x ∈ V := by
      exact mem_interior_of_mem_notMem_frontier
        (show x i ∈ (A i)ᶜ by simpa) (by simpa using hcoord i)
    have hVsub : V ⊆ (Set.pi univ A)ᶜ := by
      intro y hy hyA
      exact (interior_subset hy) (hyA i trivial)
    have hxcompint : x ∈ interior (Set.pi univ A)ᶜ :=
      interior_maximal hVsub hVopen hxV
    have hnotfront : x ∉ frontier (Set.pi univ A)ᶜ := by
      intro hfront
      rw [frontier] at hfront
      exact hfront.2 hxcompint
    exact hnotfront (by simpa using hx)

end Set

namespace MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α]

/-- A finite product of coordinate continuity sets is a continuity set for the product measure. -/
theorem measure_frontier_pi_eq_zero
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (A : ι → Set α) (hnull : ∀ i, μ i (frontier (A i)) = 0) :
    Measure.pi μ (frontier (Set.pi univ A)) = 0 := by
  classical
  apply measure_mono_null (Set.frontier_pi_subset_iUnion A)
  apply measure_iUnion_null
  intro i
  have heq :
      (fun x : ι → α => x i) ⁻¹' frontier (A i) =
        Set.pi univ (fun j => if j = i then frontier (A j) else univ) := by
    ext x
    simp [Set.mem_pi]
  rw [heq, Measure.pi_pi, Finset.prod_eq_zero_iff]
  exact ⟨i, Finset.mem_univ i, by simp [hnull i]⟩

end MeasureTheory
