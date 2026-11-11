import NS25Lean.PrincipalTensorColonGraded
import NS25Lean.PrincipalTensorColonLayers

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace NS25Lean.PrincipalTensorColon
open L5A2BFinalRepair L3A MvPolynomial ToricPresentation
variable {k : Type*} [Field k] {H : NumericalSemigroup}
  {I : RelativeIdeal H} {f : H.toAddSubmonoid} {g : Fin 3 → H.toAddSubmonoid}

variable (T : GradedPresentation (k:=k) I f g)

def tensorBivariateBasis : Module.Basis (standardExponents T.J) k
    (MvPolynomial (Fin 3) k ⧸ T.J) := standardBasis T.J T.monomialJ

def colonGenerator (T : GradedPresentation (k:=k) I f g) (i : Fin 3) : Colon (k:=k) I f :=
  Ideal.Quotient.mkₐ k _ (AddMonoidAlgebra.single (g i) 1)

abbrev tensorBivariateQuotient := MvPolynomial (Fin 3) k ⧸ T.J

def tensorBivariateGenerator (i : Fin 2) : MvPolynomial (Fin 3) k ⧸ T.J :=
  Ideal.Quotient.mkₐ k T.J (X i.succ)

theorem tensor_bivariate_standard_iff (a : L3A.Exponent) :
    a∈standardExponents T.J ↔ a 0=0 ∧ a∈standardExponents T.K := by
  constructor
  · intro ha
    have hz := T.plane a ha
    refine ⟨hz,(T.standard_split a).mpr ⟨by rw [hz]; exact T.positive,?_⟩⟩
    have he : a.erase 0=a := by ext i; by_cases hi:i=0 <;> simp [hi,hz]
    rwa [he]
  · rintro ⟨hz,ha⟩
    have he : a.erase 0=a := by ext i; by_cases hi:i=0 <;> simp [hi,hz]
    simpa only [he] using ((T.standard_split a).mp ha).2

private theorem erase_add_X (a : Fin 3 →₀ ℕ) (ha : a 0=0) (n : ℕ) :
    (Finsupp.single 0 n+a).erase 0=a := by
  classical
  ext i
  fin_cases i <;> simp [Finsupp.erase_apply,ha]

/-- Exact standard monomial product indexing, constructed from the actual
kernel presentation rather than posited as a tensor decomposition. -/
def tensorStandardXEquiv
    (T : GradedPresentation (k:=k) I f g) :
    L3A.standardExponents (T.K) ≃
      Fin (T.D) ×
        L3A.standardExponents (T.J) where
  toFun a :=
    let hs := (T.standard_split a.val).mp a.property
    (⟨a.val 0,hs.1⟩,⟨a.val.erase 0,hs.2⟩)
  invFun p := ⟨Finsupp.single 0 p.1.val+p.2.val,by
    apply (T.standard_split _).mpr
    have hz := (tensor_bivariate_standard_iff T p.2.val).mp p.2.property
    constructor
    · simpa [hz.1] using p.1.property
    · rw [erase_add_X _ hz.1]; exact p.2.property⟩
  left_inv a := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [Finsupp.erase_apply]
  right_inv p := by
    have hz := (tensor_bivariate_standard_iff T p.2.val).mp p.2.property
    apply Prod.ext
    · apply Fin.ext
      simp [hz.1]
    · apply Subtype.ext
      exact erase_add_X _ hz.1 _

def tensorPolynomialColonBasis
    (T : GradedPresentation (k:=k) I f g) :
    Module.Basis (L3A.standardExponents (T.K)) k
      (MvPolynomial (Fin 3) k ⧸ T.K) :=
  L3A.standardBasis _ (T.monomialK)

/-- Coefficient-level product dictionary. No algebra or cochain compatibility
is hidden in this linear equivalence. -/
def tensorColonXCoefficients
    (T : GradedPresentation (k:=k) I f g) :
    Colon (k:=k) I f ≃ₗ[k]
      Fin (T.D) →
        (L3A.standardExponents (T.J) →₀ k) :=
  (T.equiv).symm.toLinearEquiv |>.trans
    ((tensorPolynomialColonBasis T).reindex
      (tensorStandardXEquiv T)).repr |>.trans
    (Finsupp.curryLinearEquiv k) |>.trans
    (Finsupp.linearEquivFunOnFinite k _ _)

def tensorColonXLayerEquiv
    (T : GradedPresentation (k:=k) I f g) :
    Colon (k:=k) I f ≃ₗ[k]
      Fin (T.D) → tensorBivariateQuotient T :=
  (tensorColonXCoefficients T).trans
    (LinearEquiv.piCongrRight fun _ => (tensorBivariateBasis T).repr.symm)

def tensorColonLayerBasis
    (T : GradedPresentation (k:=k) I f g) :
    Module.Basis (Fin (T.D) ×
      L3A.standardExponents (T.J)) k
      (Colon (k:=k) I f) :=
  ((tensorPolynomialColonBasis T).reindex
    (tensorStandardXEquiv T)).map
      (T.equiv).toLinearEquiv

theorem tensor_layer_basis_image
    (T : GradedPresentation (k:=k) I f g)
    (p : Fin (T.D) ×
      L3A.standardExponents (T.J)) :
    tensorColonXLayerEquiv T (tensorColonLayerBasis T p)=
      Pi.single p.1 (tensorBivariateBasis T p.2) := by
  classical
  simp only [tensorColonXLayerEquiv,tensorColonXCoefficients,
    tensorColonLayerBasis,LinearEquiv.trans_apply,Module.Basis.map_apply]
  simp only [AlgEquiv.toLinearEquiv_apply,AlgEquiv.symm_apply_apply,Module.Basis.repr_self]
  ext i
  by_cases hi : i=p.1
  · subst i
    simp [LinearEquiv.piCongrRight,Finsupp.curryLinearEquiv,Finsupp.curry_single]
  · simp [LinearEquiv.piCongrRight,Finsupp.curryLinearEquiv,Finsupp.curry_single,
      Finsupp.single_apply,Pi.single_apply,hi,Ne.symm hi]

theorem tensor_layer_basis_monomial
    (T : GradedPresentation (k:=k) I f g)
    (p : Fin (T.D) ×
      L3A.standardExponents (T.J)) :
    tensorColonLayerBasis T p = T.equiv
      (L3A.monomialClass (T.K)
        (Finsupp.single 0 p.1.val+p.2.val)) := by
  simp [tensorColonLayerBasis,tensorPolynomialColonBasis,
    Module.Basis.reindex_apply,tensorStandardXEquiv,L3A.standardBasis]

theorem tensorColonAlgEquiv_X
    (T : GradedPresentation (k:=k) I f g) (i : Fin 3) :
    T.equiv
      (Ideal.Quotient.mkₐ k (T.K) (X i))=
        colonGenerator T i := by
  exact T.generator_images i

theorem tensorColonAlgEquiv_X_mul
    (T : GradedPresentation (k:=k) I f g) (i : Fin 3) (a : Fin 3 →₀ ℕ) :
    colonGenerator T i *
      T.equiv
        (L3A.monomialClass (T.K) a) =
      T.equiv
        (L3A.monomialClass (T.K) (a+Finsupp.single i 1)) := by
  rw [← tensorColonAlgEquiv_X,← map_mul]
  congr 1
  exact L3A.X_mul_monomialClass _ a i

/-- Every bounded X layer is the actual bivariate monomial class, including
the vanishing monomials; this is stronger than an index cardinality statement. -/
theorem tensor_layer_monomial_image
    (T : GradedPresentation (k:=k) I f g) (n : Fin (T.D))
    (b : Fin 3 →₀ ℕ) (hb : b 0=0) :
    tensorColonXLayerEquiv T
      (T.equiv
        (L3A.monomialClass (T.K) (Finsupp.single 0 n.val+b))) =
      Pi.single n (L3A.monomialClass (T.J) b) := by
  classical
  by_cases hs : b ∈ L3A.standardExponents (T.J)
  · have h := tensor_layer_basis_image T (n,⟨b,hs⟩)
    rw [tensor_layer_basis_monomial] at h
    simpa [tensorBivariateBasis,L3A.standardBasis] using h
  · have hbm : monomial b (1 : k) ∈ T.J := not_not.mp hs
    have hi : monomial (Finsupp.single 0 n.val+b) (1:k)∈T.K := by
      by_contra hout
      have hs := ((T.standard_split _).mp hout).2
      rw [erase_add_X b hb n.val] at hs
      exact hs hbm
    have h0 : L3A.monomialClass (T.K) (Finsupp.single 0 n.val+b)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hi
    have hb0 : L3A.monomialClass (T.J) b=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hbm
    rw [h0,map_zero,map_zero,hb0]
    simp

theorem tensor_layer_basis_YZ_image
    (T : GradedPresentation (k:=k) I f g)
    (p : Fin (T.D) ×
      L3A.standardExponents (T.J)) (i : Fin 2) :
    tensorColonXLayerEquiv T
      (colonGenerator T i.succ * tensorColonLayerBasis T p) =
      Pi.single p.1 (tensorBivariateGenerator T i * tensorBivariateBasis T p.2) := by
  classical
  rw [tensor_layer_basis_monomial,tensorColonAlgEquiv_X_mul]
  have hb := (tensor_bivariate_standard_iff T p.2.val).mp p.2.property
  have hz : (p.2.val+Finsupp.single i.succ 1 : Fin 3 →₀ ℕ) 0=0 := by
    simp [hb.1,Fin.succ_ne_zero]
  rw [add_assoc,tensor_layer_monomial_image T p.1 _ hz]
  congr 1
  simp only [tensorBivariateBasis,L3A.standardBasis,Module.Basis.mk_apply]
  exact (L3A.X_mul_monomialClass _ p.2.val i.succ).symm

theorem tensor_layer_basis_X_image_lt
    (T : GradedPresentation (k:=k) I f g)
    (p : Fin (T.D) ×
      L3A.standardExponents (T.J))
    (hp : p.1.val+1 < T.D) :
    tensorColonXLayerEquiv T
      (colonGenerator T 0 * tensorColonLayerBasis T p) =
      Pi.single (⟨p.1.val+1,hp⟩ : Fin (T.D))
        (tensorBivariateBasis T p.2) := by
  rw [tensor_layer_basis_monomial,tensorColonAlgEquiv_X_mul]
  have he : Finsupp.single 0 p.1.val+p.2.val+Finsupp.single 0 1 =
      Finsupp.single 0 (p.1.val+1)+p.2.val := by ext i; fin_cases i <;> simp <;> omega
  rw [he]
  have hb := (tensor_bivariate_standard_iff T p.2.val).mp p.2.property
  rw [tensor_layer_monomial_image T ⟨p.1.val+1,hp⟩ _ hb.1]
  simp [tensorBivariateBasis,L3A.standardBasis]

theorem tensor_layer_basis_X_image_ge
    (T : GradedPresentation (k:=k) I f g)
    (p : Fin (T.D) ×
      L3A.standardExponents (T.J))
    (hp : T.D ≤ p.1.val+1) :
    tensorColonXLayerEquiv T
      (colonGenerator T 0 * tensorColonLayerBasis T p)=0 := by
  rw [tensor_layer_basis_monomial,tensorColonAlgEquiv_X_mul]
  have hb := (tensor_bivariate_standard_iff T p.2.val).mp p.2.property
  have hm : L3A.monomialClass (T.K)
      (Finsupp.single 0 p.1.val+p.2.val+Finsupp.single 0 1)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    by_contra hout
    have hs := ((T.standard_split _).mp hout).1
    have he : (Finsupp.single 0 p.1.val+p.2.val+Finsupp.single 0 1 : L3A.Exponent) 0=p.1.val+1 := by simp [hb.1]
    rw [he] at hs
    omega
  rw [hm,map_zero,map_zero]

theorem tensor_layer_YZ_intertwines
    (T : GradedPresentation (k:=k) I f g) (i : Fin 2) :
    (tensorColonXLayerEquiv T).toLinearMap.comp
      (LinearMap.mulLeft k (colonGenerator T i.succ)) =
    (layerMultiply (k:=k) (T.D) (tensorBivariateGenerator T i)).comp
      (tensorColonXLayerEquiv T).toLinearMap := by
  classical
  apply (tensorColonLayerBasis T).ext
  intro p
  simp only [LinearMap.comp_apply,LinearMap.mulLeft_apply,LinearEquiv.coe_coe]
  rw [tensor_layer_basis_YZ_image,tensor_layer_basis_image]
  ext j
  by_cases hj : j=p.1 <;> simp [layerMultiply,Pi.single_apply,hj]

theorem tensor_layer_X_intertwines
    (T : GradedPresentation (k:=k) I f g) :
    (tensorColonXLayerEquiv T).toLinearMap.comp
      (LinearMap.mulLeft k (colonGenerator T 0)) =
    (truncatedLayerShift (k:=k) (T.D)).comp
      (tensorColonXLayerEquiv T).toLinearMap := by
  classical
  apply (tensorColonLayerBasis T).ext
  intro p
  simp only [LinearMap.comp_apply,LinearMap.mulLeft_apply,LinearEquiv.coe_coe]
  rw [tensor_layer_basis_image,truncatedLayerShift_single]
  split_ifs with hp
  · exact tensor_layer_basis_X_image_lt T p hp
  · exact tensor_layer_basis_X_image_ge T p (by omega)

theorem tensor_layer_operator_packet
    (T : GradedPresentation (k:=k) I f g) :
    ∃ e : Colon (k:=k) I f ≃ₗ[k]
      (Fin (T.D) → tensorBivariateQuotient T),
      ∀ t,
        e (colonGenerator T 0*t)=truncatedLayerShift (k:=k) (T.D) (e t) ∧
        e (colonGenerator T 1*t)=layerMultiply (k:=k) (T.D)
          (tensorBivariateGenerator T 0) (e t) ∧
        e (colonGenerator T 2*t)=layerMultiply (k:=k) (T.D)
          (tensorBivariateGenerator T 1) (e t) := by
  refine ⟨tensorColonXLayerEquiv T,fun t => ⟨?_,?_,?_⟩⟩
  · exact LinearMap.congr_fun (tensor_layer_X_intertwines T) t
  · exact LinearMap.congr_fun (tensor_layer_YZ_intertwines T 0) t
  · exact LinearMap.congr_fun (tensor_layer_YZ_intertwines T 1) t

/-- The tensor multiplication operators are built from the monomial basis,
not supplied as dimension or homology hypotheses. -/
theorem tensor_poly_operator_packet :
    ∃ e : Poly T ≃ₗ[k] (Fin T.D → tensorBivariateQuotient T), ∀ t,
      e (generators T 0*t)=truncatedLayerShift (k:=k) T.D (e t) ∧
      e (generators T 1*t)=layerMultiply (k:=k) T.D (tensorBivariateGenerator T 0) (e t) ∧
      e (generators T 2*t)=layerMultiply (k:=k) T.D (tensorBivariateGenerator T 1) (e t) := by
  obtain ⟨e,he⟩ := tensor_layer_operator_packet T
  refine ⟨T.equiv.toLinearEquiv.trans e,fun t => ⟨?_,?_,?_⟩⟩
  · simpa only [LinearEquiv.trans_apply,AlgEquiv.toLinearEquiv_apply,map_mul,
      generators,T.generator_images,colonGenerator] using (he (T.equiv t)).1
  · simpa only [LinearEquiv.trans_apply,AlgEquiv.toLinearEquiv_apply,map_mul,
      generators,T.generator_images,colonGenerator] using (he (T.equiv t)).2.1
  · simpa only [LinearEquiv.trans_apply,AlgEquiv.toLinearEquiv_apply,map_mul,
      generators,T.generator_images,colonGenerator] using (he (T.equiv t)).2.2

theorem tensor_poly_finite : Module.Finite k (Poly T) := by
  letI := carrierMonomialQuotient_finite (k:=k) I
  exact Module.Finite.of_injective (inject T) (inject_injective T)

theorem tensor_bivariate_finite : Module.Finite k (tensorBivariateQuotient T) := by
  letI := tensor_poly_finite T
  have hstd : Finite (standardExponents T.K) := (standard_linearIndependent T.K T.monomialK).finite
  letI := hstd
  let fn : standardExponents T.J → standardExponents T.K := fun a =>
    ⟨a.val,((tensor_bivariate_standard_iff T a.val).mp a.property).2⟩
  have hf : Function.Injective fn := by intro a b he; exact Subtype.ext (congrArg (fun x : standardExponents T.K => x.val) he)
  letI := Finite.of_injective fn hf
  letI := Fintype.ofFinite (standardExponents T.J)
  exact Module.Finite.of_basis (tensorBivariateBasis T)

theorem tensor_bivariate_proper (hf : (f.val:ℤ)∉I) :
    (1:MvPolynomial (Fin 3) k)∉T.J := by
  have hk : (0:L3A.Exponent)∈standardExponents T.K := by
    intro hm
    have hz : monomialClass T.K 0=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    have he := congrArg (inject T) hz
    rw [inject_monomial,map_zero] at he
    have hd : degree g 0=0 := by simp [degree]
    rw [hd,add_zero,carrierMonomialClass_eq_zero_iff] at he
    exact hf he
  have hj := ((T.standard_split 0).mp hk).2
  simpa [standardExponents] using hj

#print axioms tensor_poly_operator_packet
#print axioms tensor_bivariate_proper
end NS25Lean.PrincipalTensorColon
