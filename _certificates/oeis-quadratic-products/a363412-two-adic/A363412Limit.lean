import A363412TwoAdic
import A363412Growth

/-! The two-adic growth conjecture for the product defining OEIS A363412. -/
namespace A363412Two
open Filter Topology

theorem two_adic_slope :
    Tendsto (fun n : ℕ => (2:ℚ)*(padicValInt 2 (term n):ℚ)/(n:ℚ)) atTop (𝓝 1) :=
  slope_from_classes _ small_residues middle_residues paired_eights

/-- Bala's A363412 limit, stated directly on the quadratic integer product. -/
theorem product_two_adic_slope :
    Tendsto (fun n : ℕ => (2:ℚ)*
      (padicValInt 2 ((∏ j ∈ Finset.range n, (⟨1, 1+(j:ℤ)⟩ : Zsqrtd (-3))).im):ℚ) /
      (n:ℚ)) atTop (𝓝 1) := by
  simpa only [term_eq_product] using two_adic_slope

end A363412Two
#print axioms A363412Two.product_two_adic_slope
