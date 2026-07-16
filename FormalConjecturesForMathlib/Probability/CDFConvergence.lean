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

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.CDF

/-!
# Weak convergence from cumulative distribution functions

For real probability measures, pointwise convergence of the CDF at every real threshold implies
weak convergence.  This is a convenient specialization of the Portmanteau π-system criterion.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory

private def iocSystem : Set (Set ℝ) :=
  Set.range fun ab : ℝ × ℝ ↦ Ioc ab.1 ab.2

private lemma isPiSystem_iocSystem : IsPiSystem iocSystem := by
  rintro s ⟨⟨a, b⟩, rfl⟩ t ⟨⟨c, d⟩, rfl⟩ _
  refine ⟨(max a c, min b d), ?_⟩
  ext x
  simp only [mem_inter_iff, mem_Ioc, Prod.fst, Prod.snd, max_lt_iff, le_min_iff]
  aesop

private lemma iocSystem_basis
    (u : Set ℝ) (hu : IsOpen u) (x : ℝ) (hx : x ∈ u) :
    ∃ s ∈ iocSystem, s ∈ 𝓝 x ∧ s ⊆ u := by
  rcases Metric.isOpen_iff.1 hu x hx with ⟨ε, hε, hball⟩
  let a := x - ε / 2
  let b := x + ε / 2
  refine ⟨Ioc a b, ⟨(a, b), rfl⟩, ?_, ?_⟩
  · exact Ioc_mem_nhds (by dsimp [a]; linarith) (by dsimp [b]; linarith)
  · intro y hy
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    rcases hy with ⟨hay, hyb⟩
    dsimp [a, b] at hay hyb
    constructor <;> linarith

private lemma measureReal_Ioc_eq_cdf_sub
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ} (hab : a ≤ b) :
    μ.real (Ioc a b) = cdf μ b - cdf μ a := by
  have hdisj : Disjoint (Iic a) (Ioc a b) := by
    refine Set.disjoint_left.2 ?_
    intro z hza hzb
    exact (not_lt_of_ge hza hzb.1)
  have hunion : Iic a ∪ Ioc a b = Iic b := by
    ext z
    simp only [mem_union, mem_Iic, mem_Ioc]
    constructor
    · rintro (hz | hz)
      · exact hz.trans hab
      · exact hz.2
    · intro hzb
      by_cases hza : z ≤ a
      · exact Or.inl hza
      · exact Or.inr ⟨lt_of_not_ge hza, hzb⟩
  have hsum := measureReal_union hdisj measurableSet_Ioc
    (μ := μ) (s₁ := Iic a) (s₂ := Ioc a b)
  rw [hunion, ← cdf_eq_real μ b, ← cdf_eq_real μ a] at hsum
  linarith

/-- Pointwise convergence of CDFs at every real point implies weak convergence of real probability
measures. -/
lemma ProbabilityMeasure.tendsto_of_tendsto_cdf
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : ∀ x : ℝ, Tendsto (fun i ↦ cdf (μs i : Measure ℝ) x) l
      (𝓝 (cdf (μ : Measure ℝ) x))) :
    Tendsto μs l (𝓝 μ) := by
  refine isPiSystem_iocSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    (fun s hs ↦ ?_) iocSystem_basis ?_
  · rcases hs with ⟨⟨a, b⟩, rfl⟩
    exact measurableSet_Ioc
  · rintro s ⟨⟨a, b⟩, rfl⟩
    by_cases hab : a ≤ b
    · have hreal : Tendsto
          (fun i ↦ (μs i : Measure ℝ).real (Ioc a b)) l
          (𝓝 ((μ : Measure ℝ).real (Ioc a b))) := by
        simp_rw [measureReal_Ioc_eq_cdf_sub _ hab]
        exact (h b).sub (h a)
      simpa using hreal
    · have hempty : Ioc a b = ∅ := Ioc_eq_empty (le_of_not_ge hab)
      simp [hempty]

end ProbabilityTheory
