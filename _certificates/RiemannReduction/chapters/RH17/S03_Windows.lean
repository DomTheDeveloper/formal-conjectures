import RH17.S01_PrimeSum

/-! # 3. Specify the quantifiers
A window can begin beyond any requested starting point. Once it is chosen,
the same bound must hold at every real point up to Y^(1+δ). The constant and
the windows may vary with the chosen exponent θ. -/

namespace RH17

def OnWindows (δ : ℝ) (P : ℝ → Prop) : Prop :=
  ∀ start : ℝ, ∃ Y ≥ start, ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), P y

def PowerWindows (g : ℝ → ℝ) (δ θ : ℝ) : Prop :=
  ∃ C : ℝ, OnWindows δ (fun y => g y ≤ C * y ^ θ)

def NearHalf (g : ℝ → ℝ) (δ : ℝ) : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → PowerWindows g δ θ

theorem OnWindows.weaken {δ : ℝ} {P Q : ℝ → Prop} (h : OnWindows δ P)
    (cut : ℝ) (hPQ : ∀ y ≥ cut, P y → Q y) : OnWindows δ Q := by
  intro start
  obtain ⟨Y, hY, hP⟩ := h (max start cut)
  exact ⟨Y, (le_max_left _ _).trans hY, fun y hy =>
    hPQ y ((le_max_right _ _).trans (hY.trans hy.1)) (hP y hy)⟩

end RH17
