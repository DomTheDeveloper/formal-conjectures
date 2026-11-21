import Mathlib

set_option linter.unusedVariables false in
theorem UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot :
    ∀ {R S M : Type} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : AddCommGroup M]
        [inst_3 : Module R M] (s : S →+* R) (I K : Ideal S), I ≤ K →
      ∀ (c : ℕ) (e : M ≃+ (Fin c → S ⧸ I)),
        (∀ (z : S) (x : M), e (s z • x) = z • e x) →
        ∃ e' : (M ⧸ (Ideal.map s K • ⊤ : Submodule R M)) ≃+ (Fin c → S ⧸ K),
          ∀ (a : S) (x : M ⧸ (Ideal.map s K • ⊤ : Submodule R M)), e' (s a • x) = a • e' x := by
  intro R S M _ _ _ _ s I K hIK c e he
  let _ : Algebra S R := s.toAlgebra
  let _ : Module S M := Module.compHom M s
  let _ : IsScalarTower S R M := IsScalarTower.of_compHom S R M
  let coords : M ≃ₗ[S] (Fin c → S ⧸ I) := { e with map_smul' := he }
  have relations := Ideal.smul_restrictScalars K (⊤ : Submodule R M)
  simp only [RingHom.algebraMap_toAlgebra, Submodule.restrictScalars_top] at relations
  have vanishes : I • (⊤ : Submodule S (S ⧸ K)) = ⊥ := by
    rwa [← Submodule.le_annihilator_iff, Submodule.annihilator_top, Ideal.annihilator_quotient]
  let coord := TensorProduct.tensorQuotEquivQuotSMul (S ⧸ K) I ≪≫ₗ Submodule.quotEquivOfEqBot _ vanishes
  let result := (Submodule.Quotient.restrictScalarsEquiv S (Ideal.map s K • ⊤ : Submodule R M)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ relations ≪≫ₗ (TensorProduct.quotTensorEquivQuotSMul M K).symm ≪≫ₗ
    coords.lTensor (S ⧸ K) ≪≫ₗ TensorProduct.piRight S S (S ⧸ K) (fun _ : Fin c => S ⧸ I) ≪≫ₗ
    LinearEquiv.piCongrRight fun _ => coord
  exact ⟨result.toAddEquiv, fun a x => result.map_smul a x⟩
