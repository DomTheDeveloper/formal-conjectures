import Mathlib

theorem UpperTheory.Reformulated.B.FreeModuleQuotient.freeN_quot :
    ∀ {R S M : Type} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : AddCommGroup M]
        [inst_3 : Module R M] (s : S →+* R) (I K : Ideal S), I ≤ K →
      ∀ (c : ℕ) (e : M ≃+ (Fin c → S ⧸ I)),
        (∀ (z : S) (x : M), e (s z • x) = z • e x) →
        ∃ e' : (M ⧸ (Ideal.map s K • ⊤ : Submodule R M)) ≃+ (Fin c → S ⧸ K),
          ∀ (a : S) (x : M ⧸ (Ideal.map s K • ⊤ : Submodule R M)), e' (s a • x) = a • e' x := by
  intro R S M _ _ _ _ s I K hIK c e he
  classical
  let φ : M →+ (Fin c → S ⧸ K) :=
    { toFun := fun x i => Ideal.Quotient.factor hIK (e x i)
      map_zero' := by funext i; simp
      map_add' := by intro x y; funext i; simp }
  have hφ : ∀ x i, φ x i = Ideal.Quotient.factor hIK (e x i) := fun _ _ => rfl
  have hsm : ∀ (a : S) (x : M), φ (s a • x) = a • φ x := by
    intro a x
    funext i
    rw [Pi.smul_apply, hφ, hφ, he, Pi.smul_apply]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e x i)
    rw [← hy]
    rfl
  have hsurj : Function.Surjective φ := by
    intro y
    choose t ht using fun i => Ideal.Quotient.mk_surjective (y i)
    refine ⟨e.symm (fun i => Ideal.Quotient.mk I (t i)), ?_⟩
    funext i
    rw [hφ, e.apply_symm_apply, Ideal.Quotient.factor_mk, ht]
  have h1 : ∀ r ∈ Ideal.map s K, ∀ x : M, φ (r • x) = 0 := by
    intro r hr
    refine Submodule.span_induction (p := fun r _ => ∀ x : M, φ (r • x) = 0) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨k, hk, rfl⟩ x
      rw [hsm]
      funext i
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (φ x i)
      rw [Pi.smul_apply, ← hy]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (K.mul_mem_right y hk)
    · intro x; simp
    · intro a b _ _ ha hb x
      rw [add_smul, map_add, ha, hb, add_zero]
    · intro a b _ hb x
      rw [smul_eq_mul, mul_comm, mul_smul, hb]
  have hker : ∀ x : M, x ∈ (Ideal.map s K • ⊤ : Submodule R M) ↔ φ x = 0 := by
    intro x
    constructor
    · intro hx
      refine Submodule.smul_induction_on (p := fun x => φ x = 0) hx ?_ ?_
      · intro r hr n _; exact h1 r hr n
      · intro a b ha hb; rw [map_add, ha, hb, add_zero]
    · intro hx
      choose t ht using fun i => Ideal.Quotient.mk_surjective (e x i)
      have htK : ∀ i, t i ∈ K := by
        intro i
        have := congrFun hx i
        rw [hφ, ← ht, Ideal.Quotient.factor_mk] at this
        exact Ideal.Quotient.eq_zero_iff_mem.1 this
      have hxe : x = ∑ i, s (t i) • e.symm (Pi.single i 1) := by
        apply e.injective
        rw [map_sum]
        simp only [he, e.apply_symm_apply]
        rw [← Finset.univ_sum_single (e x)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Pi.single_smul, ← ht, ← Algebra.algebraMap_eq_smul_one]
        rfl
      rw [hxe]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem_smul (Ideal.mem_map_of_mem s (htK i)) Submodule.mem_top
  let ψ : (M ⧸ (Ideal.map s K • ⊤ : Submodule R M)) →+ (Fin c → S ⧸ K) :=
    QuotientAddGroup.lift (Ideal.map s K • ⊤ : Submodule R M).toAddSubgroup φ
      (fun x hx => (hker x).1 hx)
  have hψ : ∀ x : M, ψ (Submodule.Quotient.mk x) = φ x := fun _ => rfl
  have hbij : Function.Bijective ψ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [hψ] at hx
      exact (Submodule.Quotient.mk_eq_zero _).2 ((hker y).2 hx)
    · intro y
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨Submodule.Quotient.mk x, hψ x⟩
  refine ⟨AddEquiv.ofBijective ψ hbij, fun a x => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul]
  exact hsm a y
