import NS25Lean.P2BranchBNonsymmetricFinalRepair

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1 MvPolynomial

section TwoCochain
variable {k T : Type*} [Field k] [CommRing T] [Algebra k T]

/-- The two-variable Koszul COCHAIN maps, ordered Y,Z. -/
def twoKoszulD0 (y z : T) : T →ₗ[k] (Fin 2 → T) where
  toFun := fun t => ![y*t,z*t]
  map_add' := by intro a b; ext i; fin_cases i <;> simp [mul_add]
  map_smul' := by intro a b; ext i; fin_cases i <;> simp

def twoKoszulD1 (y z : T) : (Fin 2 → T) →ₗ[k] T where
  toFun := fun t => z*t 0-y*t 1
  map_add' := by intro a b; simp; ring
  map_smul' := by intro a b; simp [mul_smul_comm,smul_sub]

theorem twoKoszul_range_D0_le_cycles (y z : T) :
    LinearMap.range (twoKoszulD0 (k:=k) y z) ≤ LinearMap.ker (twoKoszulD1 y z) := by
  rintro _ ⟨t,rfl⟩
  change z*(y*t)-y*(z*t)=0
  ring

abbrev TwoKoszulH0 (y z : T) := LinearMap.ker (twoKoszulD0 (k:=k) y z)
abbrev TwoKoszulH1 (y z : T) :=
  LinearMap.ker (twoKoszulD1 (k:=k) y z) ⧸
    (LinearMap.range (twoKoszulD0 (k:=k) y z)).comap (LinearMap.ker (twoKoszulD1 y z)).subtype
abbrev TwoKoszulH2 (y z : T) := T ⧸ LinearMap.range (twoKoszulD1 (k:=k) y z)

/-- Rank-nullity, without truncated dimension subtraction. This generic Euler
identity is later instantiated on the actual staircase quotient. -/
theorem twoKoszul_finrank_euler [Module.Finite k T] (y z : T) :
    Module.finrank k (TwoKoszulH1 (k:=k) y z) =
      Module.finrank k (TwoKoszulH0 (k:=k) y z) +
      Module.finrank k (TwoKoszulH2 (k:=k) y z) := by
  have h0 := LinearMap.finrank_range_add_finrank_ker (twoKoszulD0 (k:=k) y z)
  have h1 := LinearMap.finrank_range_add_finrank_ker (twoKoszulD1 (k:=k) y z)
  have h2 := (LinearMap.range (twoKoszulD1 (k:=k) y z)).finrank_quotient_add_finrank
  have hh := ((LinearMap.range (twoKoszulD0 (k:=k) y z)).comap
    (LinearMap.ker (twoKoszulD1 (k:=k) y z)).subtype).finrank_quotient_add_finrank
  have hb := (Submodule.comapSubtypeEquivOfLe
    (twoKoszul_range_D0_le_cycles (k:=k) y z)).finrank_eq
  have hp : Module.finrank k (Fin 2 → T) = 2*Module.finrank k T := by
    simp [Module.finrank_pi_fintype]
  change Module.finrank k (TwoKoszulH1 (k:=k) y z) + _ = _ at hh
  change Module.finrank k (TwoKoszulH2 (k:=k) y z) + _ = _ at h2
  change _ + Module.finrank k (TwoKoszulH0 (k:=k) y z) = _ at h0
  omega
end TwoCochain

variable {k : Type*} [Field k] {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Actual Y/Z staircase: quotient of B88's proved polynomial presentation
by X=0. This is not a hypothesized tensor factor. -/
def nonsymmetricBivariateIdeal (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Ideal (MvPolynomial (Fin 3) k) :=
  nonsymmetricPolynomialColonIdeal k R hB hQ ⊔ Ideal.span {X 0}

abbrev nonsymmetricBivariateQuotient (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  MvPolynomial (Fin 3) k ⧸ nonsymmetricBivariateIdeal (k:=k) R hB hQ

def nonsymmetricBivariateGenerator (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 2) :
    nonsymmetricBivariateQuotient (k:=k) R hB hQ :=
  Ideal.Quotient.mkₐ k _ (X i.succ)

theorem nonsymmetric_polynomial_colon_le_augmentation_kernel
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPolynomialColonIdeal k R hB hQ ≤
      RingHom.ker (aeval (0 : Fin 3 → k)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f (hf | hf)
  · rcases hf with rfl
    change aeval (0 : Fin 3 → k) (X 0 ^ nonsymmetricDa R hB hQ)=0
    simp [nonsymmetricDa_positive R hB hQ |>.ne']
  · obtain ⟨⟨ell,i⟩,rfl⟩ := hf
    have ht := nonsymmetricReturnTuple_spec R hB ell
    have hi : 0 < nsC2 R-(nonsymmetricReturnTuple R hB ell).1 := by
      have := ht.1.1; omega
    have hj : 0 < nsC3 R-(nonsymmetricReturnTuple R hB ell).2.1 := by
      have := ht.1.2.1; omega
    have hm : 0 < nsP R-(nonsymmetricReturnTuple R hB ell).1 ∨
        0 < nsQ R-(nonsymmetricReturnTuple R hB ell).2.1 := by
      have := ht.1.2.2; omega
    change aeval (0 : Fin 3 → k) _=0
    fin_cases i
    · simp [hi.ne']
    · simp [hj.ne']
    · rcases hm with hm | hm <;> simp [hm.ne']

theorem nonsymmetric_bivariate_le_augmentation_kernel
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricBivariateIdeal (k:=k) R hB hQ ≤
      RingHom.ker (aeval (0 : Fin 3 → k)).toRingHom := by
  apply sup_le (nonsymmetric_polynomial_colon_le_augmentation_kernel R hB hQ)
  apply Ideal.span_le.mpr
  rintro p (rfl : p=X 0)
  change aeval (0 : Fin 3 → k) (X 0)=0
  simp

def nonsymmetricBivariateAugmentation (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricBivariateQuotient (k:=k) R hB hQ →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (aeval (0 : Fin 3 → k))
    (fun p hp => nonsymmetric_bivariate_le_augmentation_kernel R hB hQ hp)

theorem nonsymmetric_bivariate_augmentation_surjective
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Surjective (nonsymmetricBivariateAugmentation (k:=k) R hB hQ) := by
  intro a
  exact ⟨Ideal.Quotient.mkₐ k _ (C a),by simp [nonsymmetricBivariateAugmentation]⟩

theorem nonsymmetric_bivariate_X_zero (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Ideal.Quotient.mkₐ k (nonsymmetricBivariateIdeal (k:=k) R hB hQ) (X 0)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_sup_right
  exact Ideal.subset_span (Set.mem_singleton _)

def nonsymmetricBivariateFactor (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    (MvPolynomial (Fin 3) k ⧸ nonsymmetricPolynomialColonIdeal k R hB hQ) →ₐ[k]
      nonsymmetricBivariateQuotient (k:=k) R hB hQ :=
  Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ k _)
    (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hp))

theorem nonsymmetric_bivariate_finite (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Finite k (nonsymmetricBivariateQuotient (k:=k) R hB hQ) := by
  letI := nonsymmetric_colon_finite (k:=k) R hQ
  letI := Module.Finite.of_injective (nonsymmetricPrincipalColonAlgEquiv (k:=k) R hB hQ).toLinearMap
    (nonsymmetricPrincipalColonAlgEquiv (k:=k) R hB hQ).injective
  apply Module.Finite.of_surjective (nonsymmetricBivariateFactor (k:=k) R hB hQ).toLinearMap
  intro b
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ b
  exact ⟨Ideal.Quotient.mkₐ k _ p,rfl⟩

abbrev nonsymmetricBivariateH0 (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  TwoKoszulH0 (k:=k) (nonsymmetricBivariateGenerator (k:=k) R hB hQ 0)
    (nonsymmetricBivariateGenerator (k:=k) R hB hQ 1)
abbrev nonsymmetricBivariateH1 (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  TwoKoszulH1 (k:=k) (nonsymmetricBivariateGenerator (k:=k) R hB hQ 0)
    (nonsymmetricBivariateGenerator (k:=k) R hB hQ 1)

/-- Actual augmentation kernel, not an assumed residue-field dimension. -/
theorem nonsymmetric_bivariate_D1_range (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.range (twoKoszulD1 (k:=k) (nonsymmetricBivariateGenerator R hB hQ 0)
      (nonsymmetricBivariateGenerator R hB hQ 1)) =
      LinearMap.ker (nonsymmetricBivariateAugmentation (k:=k) R hB hQ).toLinearMap := by
  let q := Ideal.Quotient.mkₐ k (nonsymmetricBivariateIdeal (k:=k) R hB hQ)
  let eps := nonsymmetricBivariateAugmentation (k:=k) R hB hQ
  let y := nonsymmetricBivariateGenerator (k:=k) R hB hQ 0
  let z := nonsymmetricBivariateGenerator (k:=k) R hB hQ 1
  have hy : eps y=0 := by change aeval (0 : Fin 3 → k) (X 1)=0; simp
  have hz : eps z=0 := by change aeval (0 : Fin 3 → k) (X 2)=0; simp
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    change eps (z*a 0-y*a 1)=0
    simp [hy,hz]
  · intro b hb
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ b
    have hd : ∀ p, q p-q (C (aeval (0 : Fin 3 → k) p)) ∈ LinearMap.range (twoKoszulD1 (k:=k) y z) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a => simp [q]
      | add p r hp hr =>
        simpa only [map_add,add_sub_add_comm] using Submodule.add_mem _ hp hr
      | mul_X p i hp =>
        simp only [map_mul,aeval_X,Pi.zero_apply,mul_zero,map_zero,sub_zero]
        fin_cases i
        · have hx : q (X 0)=0 := nonsymmetric_bivariate_X_zero R hB hQ
          change q p*q (X 0) ∈ _
          rw [hx,mul_zero]
          exact Submodule.zero_mem _
        · exact ⟨![0,-q p],by change z*0-y*(-q p)=q p*y; ring⟩
        · exact ⟨![q p,0],by change z*q p-y*0=q p*z; ring⟩
    have he : aeval (0 : Fin 3 → k) p=0 := hb
    simpa only [he,map_zero,sub_zero] using hd p

theorem nonsymmetric_bivariate_koszulH2_finrank
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (TwoKoszulH2 (k:=k) (nonsymmetricBivariateGenerator (k:=k) R hB hQ 0)
      (nonsymmetricBivariateGenerator (k:=k) R hB hQ 1))=1 := by
  unfold TwoKoszulH2
  rw [nonsymmetric_bivariate_D1_range]
  exact ((nonsymmetricBivariateAugmentation (k:=k) R hB hQ).toLinearMap.quotKerEquivOfSurjective
    (nonsymmetric_bivariate_augmentation_surjective R hB hQ)).finrank_eq.trans (Module.finrank_self k)

theorem nonsymmetric_bivariate_koszulH1_finrank
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (nonsymmetricBivariateH1 (k:=k) R hB hQ) =
      Module.finrank k (nonsymmetricBivariateH0 (k:=k) R hB hQ)+1 := by
  letI := nonsymmetric_bivariate_finite (k:=k) R hB hQ
  exact (twoKoszul_finrank_euler (k:=k) _ _).trans
    (congrArg (fun n => Module.finrank k (nonsymmetricBivariateH0 (k:=k) R hB hQ)+n)
      (nonsymmetric_bivariate_koszulH2_finrank R hB hQ))

theorem nonsymmetric_bivariate_monomial_presentation
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricBivariateIdeal (k:=k) R hB hQ = Ideal.span
      ((fun a => monomial a (1 : k)) ''
        (nonsymmetricColonExponentSet R hB hQ ∪ {Finsupp.single 0 1})) := by
  rw [Set.image_union,Set.image_singleton,Ideal.span_union]
  rw [← nonsymmetric_polynomial_colon_monomial_presentation]
  simp only [← X_pow_eq_monomial,pow_one]
  rfl

theorem nonsymmetric_bivariate_isMonomial
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    L2B.IsMonomialIdeal k (nonsymmetricBivariateIdeal (k:=k) R hB hQ) :=
  ⟨_,nonsymmetric_bivariate_monomial_presentation R hB hQ⟩

theorem nonsymmetric_bivariate_monomial_mem
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (a : Fin 3 →₀ ℕ) :
    monomial a (1 : k) ∈ nonsymmetricBivariateIdeal (k:=k) R hB hQ ↔
      monomial a (1 : k) ∈ nonsymmetricPolynomialColonIdeal k R hB hQ ∨ 0 < a 0 := by
  rw [nonsymmetric_bivariate_monomial_presentation,L3A.monomial_mem_span_iff]
  constructor
  · rintro ⟨g,hg,hga⟩
    rcases hg with hg | hg
    · left
      rw [nonsymmetric_polynomial_colon_monomial_presentation,L3A.monomial_mem_span_iff]
      exact ⟨g,hg,hga⟩
    · rcases hg with rfl
      right
      have := hga 0
      simp only [Finsupp.single_eq_same] at this
      omega
  · rintro (ha | ha)
    · rw [nonsymmetric_polynomial_colon_monomial_presentation,L3A.monomial_mem_span_iff] at ha
      obtain ⟨g,hg,hga⟩ := ha
      exact ⟨g,Or.inl hg,hga⟩
    · refine ⟨Finsupp.single 0 1,Or.inr (Set.mem_singleton _),?_⟩
      intro i
      fin_cases i <;> simp_all <;> omega

theorem nonsymmetric_bivariate_standard_iff
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (a : Fin 3 →₀ ℕ) :
    a ∈ L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ) ↔
      a 0=0 ∧ a ∈ L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ) := by
  change (monomial a (1 : k) ∉ _) ↔ _
  rw [nonsymmetric_bivariate_monomial_mem]
  simp only [not_or,Nat.not_lt,Nat.le_zero]
  exact and_comm

def nonsymmetricBivariateBasis
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Basis (L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ)) k
      (nonsymmetricBivariateQuotient (k:=k) R hB hQ) :=
  L3A.standardBasis _ (nonsymmetric_bivariate_isMonomial R hB hQ)

theorem nonsymmetric_bivariate_standard_finite
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Finite (L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ)) := by
  letI := nonsymmetric_bivariate_finite (k:=k) R hB hQ
  exact (L3A.standard_linearIndependent _ (nonsymmetric_bivariate_isMonomial R hB hQ)).finite

theorem nonsymmetric_standard_X_split
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (a : Fin 3 →₀ ℕ) :
    a ∈ L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ) ↔
      a 0 < nonsymmetricDa R hB hQ ∧
      a.erase 0 ∈ L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ) := by
  classical
  rw [nonsymmetric_bivariate_standard_iff]
  change (monomial a (1 : k) ∉ _) ↔
    a 0 < nonsymmetricDa R hB hQ ∧ (a.erase 0) 0=0 ∧ monomial (a.erase 0) (1 : k) ∉ _
  rw [nonsymmetric_polynomial_colon_monomial_mem,nonsymmetric_polynomial_colon_monomial_mem]
  have hn : ¬ nonsymmetricDa R hB hQ ≤ 0 := by have := nonsymmetricDa_positive R hB hQ; omega
  simp [Finsupp.erase_apply,hn,not_or,Nat.not_le]

private theorem erase_add_X (a : Fin 3 →₀ ℕ) (ha : a 0=0) (n : ℕ) :
    (Finsupp.single 0 n+a).erase 0=a := by
  classical
  ext i
  fin_cases i <;> simp [Finsupp.erase_apply,ha]

/-- Exact standard monomial product indexing, constructed from the actual
kernel presentation rather than posited as a tensor decomposition. -/
def nonsymmetricStandardXEquiv
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ) ≃
      Fin (nonsymmetricDa R hB hQ) ×
        L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ) where
  toFun a :=
    let hs := (nonsymmetric_standard_X_split R hB hQ a.val).mp a.property
    (⟨a.val 0,hs.1⟩,⟨a.val.erase 0,hs.2⟩)
  invFun p := ⟨Finsupp.single 0 p.1.val+p.2.val,by
    apply (nonsymmetric_standard_X_split R hB hQ _).mpr
    have hz := (nonsymmetric_bivariate_standard_iff R hB hQ p.2.val).mp p.2.property
    constructor
    · simpa [hz.1] using p.1.property
    · rw [erase_add_X _ hz.1]; exact p.2.property⟩
  left_inv a := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [Finsupp.erase_apply]
  right_inv p := by
    have hz := (nonsymmetric_bivariate_standard_iff R hB hQ p.2.val).mp p.2.property
    apply Prod.ext
    · apply Fin.ext
      simp [hz.1]
    · apply Subtype.ext
      exact erase_add_X _ hz.1 _

def nonsymmetricPolynomialColonBasis
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Basis (L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ)) k
      (MvPolynomial (Fin 3) k ⧸ nonsymmetricPolynomialColonIdeal k R hB hQ) :=
  L3A.standardBasis _ (nonsymmetric_polynomial_colon_isMonomial R hB hQ)

/-- Coefficient-level product dictionary. No algebra or cochain compatibility
is hidden in this linear equivalence. -/
def nonsymmetricColonXCoefficients
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrincipalColonQuotient k R hQ ≃ₗ[k]
      Fin (nonsymmetricDa R hB hQ) →
        (L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ) →₀ k) :=
  (nonsymmetricPrincipalColonAlgEquiv (k:=k) R hB hQ).symm.toLinearEquiv |>.trans
    ((nonsymmetricPolynomialColonBasis (k:=k) R hB hQ).reindex
      (nonsymmetricStandardXEquiv R hB hQ)).repr |>.trans
    (Finsupp.curryLinearEquiv k) |>.trans
    (Finsupp.linearEquivFunOnFinite k _ _)

def nonsymmetricColonXLayerEquiv
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrincipalColonQuotient k R hQ ≃ₗ[k]
      Fin (nonsymmetricDa R hB hQ) → nonsymmetricBivariateQuotient (k:=k) R hB hQ :=
  (nonsymmetricColonXCoefficients R hB hQ).trans
    (LinearEquiv.piCongrRight fun _ => (nonsymmetricBivariateBasis R hB hQ).repr.symm)

def nonsymmetricColonLayerBasis
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Basis (Fin (nonsymmetricDa R hB hQ) ×
      L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ)) k
      (nonsymmetricPrincipalColonQuotient k R hQ) :=
  ((nonsymmetricPolynomialColonBasis (k:=k) R hB hQ).reindex
    (nonsymmetricStandardXEquiv R hB hQ)).map
      (nonsymmetricPrincipalColonAlgEquiv R hB hQ).toLinearEquiv

theorem nonsymmetric_layer_basis_image
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : Fin (nonsymmetricDa R hB hQ) ×
      L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ)) :
    nonsymmetricColonXLayerEquiv R hB hQ (nonsymmetricColonLayerBasis R hB hQ p)=
      Pi.single p.1 (nonsymmetricBivariateBasis R hB hQ p.2) := by
  classical
  simp only [nonsymmetricColonXLayerEquiv,nonsymmetricColonXCoefficients,
    nonsymmetricColonLayerBasis,LinearEquiv.trans_apply,Module.Basis.map_apply]
  simp only [AlgEquiv.toLinearEquiv_apply,AlgEquiv.symm_apply_apply,Module.Basis.repr_self]
  ext i
  by_cases hi : i=p.1
  · subst i
    simp [LinearEquiv.piCongrRight,Finsupp.curryLinearEquiv,Finsupp.curry_single]
  · simp [LinearEquiv.piCongrRight,Finsupp.curryLinearEquiv,Finsupp.curry_single,
      Finsupp.single_apply,Pi.single_apply,hi,Ne.symm hi]

theorem nonsymmetric_layer_basis_monomial
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : Fin (nonsymmetricDa R hB hQ) ×
      L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ)) :
    nonsymmetricColonLayerBasis R hB hQ p = nonsymmetricPrincipalColonAlgEquiv R hB hQ
      (L3A.monomialClass (nonsymmetricPolynomialColonIdeal k R hB hQ)
        (Finsupp.single 0 p.1.val+p.2.val)) := by
  simp [nonsymmetricColonLayerBasis,nonsymmetricPolynomialColonBasis,
    Module.Basis.reindex_apply,nonsymmetricStandardXEquiv,L3A.standardBasis]

theorem nonsymmetricColonAlgEquiv_X
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) :
    nonsymmetricPrincipalColonAlgEquiv R hB hQ
      (Ideal.Quotient.mkₐ k (nonsymmetricPolynomialColonIdeal k R hB hQ) (X i))=
        nonsymmetricColonGenerators (k:=k) R hQ i := by
  change nonsymmetricColonPolynomialMap (k:=k) R hQ (X i)=_
  exact (nonsymmetricColonGenerators_eq_eval_X R hQ i).symm

theorem nonsymmetricColonAlgEquiv_X_mul
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) (a : Fin 3 →₀ ℕ) :
    nonsymmetricColonGenerators (k:=k) R hQ i *
      nonsymmetricPrincipalColonAlgEquiv R hB hQ
        (L3A.monomialClass (nonsymmetricPolynomialColonIdeal k R hB hQ) a) =
      nonsymmetricPrincipalColonAlgEquiv R hB hQ
        (L3A.monomialClass (nonsymmetricPolynomialColonIdeal k R hB hQ) (a+Finsupp.single i 1)) := by
  rw [← nonsymmetricColonAlgEquiv_X,← map_mul]
  congr 1
  exact L3A.X_mul_monomialClass _ a i

/-- Every bounded X layer is the actual bivariate monomial class, including
the vanishing monomials; this is stronger than an index cardinality statement. -/
theorem nonsymmetric_layer_monomial_image
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (n : Fin (nonsymmetricDa R hB hQ))
    (b : Fin 3 →₀ ℕ) (hb : b 0=0) :
    nonsymmetricColonXLayerEquiv R hB hQ
      (nonsymmetricPrincipalColonAlgEquiv R hB hQ
        (L3A.monomialClass (nonsymmetricPolynomialColonIdeal k R hB hQ) (Finsupp.single 0 n.val+b))) =
      Pi.single n (L3A.monomialClass (nonsymmetricBivariateIdeal (k:=k) R hB hQ) b) := by
  classical
  by_cases hs : b ∈ L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ)
  · have h := nonsymmetric_layer_basis_image R hB hQ (n,⟨b,hs⟩)
    rw [nonsymmetric_layer_basis_monomial] at h
    simpa [nonsymmetricBivariateBasis,L3A.standardBasis] using h
  · have hbm : monomial b (1 : k) ∈ nonsymmetricBivariateIdeal (k:=k) R hB hQ := not_not.mp hs
    have hoi : monomial b (1 : k) ∈ nonsymmetricPolynomialColonIdeal k R hB hQ := by
      have hh := (nonsymmetric_bivariate_monomial_mem R hB hQ b).mp hbm
      rcases hh with hh | hh
      · exact hh
      · omega
    have hi : monomial (Finsupp.single 0 n.val+b) (1 : k) ∈ nonsymmetricPolynomialColonIdeal k R hB hQ := by
      have hm := (nonsymmetric_polynomial_colon_monomial_mem R hB hQ b).mp hoi
      apply (nonsymmetric_polynomial_colon_monomial_mem R hB hQ _).mpr
      rcases hm with hm | hm
      · have := nonsymmetricDa_positive R hB hQ; omega
      · right
        simpa using hm
    have h0 : L3A.monomialClass (nonsymmetricPolynomialColonIdeal k R hB hQ) (Finsupp.single 0 n.val+b)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hi
    have hb0 : L3A.monomialClass (nonsymmetricBivariateIdeal (k:=k) R hB hQ) b=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hbm
    rw [h0,map_zero,map_zero,hb0]
    simp

theorem nonsymmetric_layer_basis_YZ_image
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : Fin (nonsymmetricDa R hB hQ) ×
      L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ)) (i : Fin 2) :
    nonsymmetricColonXLayerEquiv R hB hQ
      (nonsymmetricColonGenerators (k:=k) R hQ i.succ * nonsymmetricColonLayerBasis R hB hQ p) =
      Pi.single p.1 (nonsymmetricBivariateGenerator R hB hQ i * nonsymmetricBivariateBasis R hB hQ p.2) := by
  classical
  rw [nonsymmetric_layer_basis_monomial,nonsymmetricColonAlgEquiv_X_mul]
  have hb := (nonsymmetric_bivariate_standard_iff R hB hQ p.2.val).mp p.2.property
  have hz : (p.2.val+Finsupp.single i.succ 1 : Fin 3 →₀ ℕ) 0=0 := by
    simp [hb.1,Fin.succ_ne_zero]
  rw [add_assoc,nonsymmetric_layer_monomial_image R hB hQ p.1 _ hz]
  congr 1
  simp only [nonsymmetricBivariateBasis,L3A.standardBasis,Module.Basis.mk_apply]
  exact (L3A.X_mul_monomialClass _ p.2.val i.succ).symm

theorem nonsymmetric_layer_basis_X_image_lt
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : Fin (nonsymmetricDa R hB hQ) ×
      L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ))
    (hp : p.1.val+1 < nonsymmetricDa R hB hQ) :
    nonsymmetricColonXLayerEquiv R hB hQ
      (nonsymmetricColonGenerators (k:=k) R hQ 0 * nonsymmetricColonLayerBasis R hB hQ p) =
      Pi.single (⟨p.1.val+1,hp⟩ : Fin (nonsymmetricDa R hB hQ))
        (nonsymmetricBivariateBasis R hB hQ p.2) := by
  rw [nonsymmetric_layer_basis_monomial,nonsymmetricColonAlgEquiv_X_mul]
  have he : Finsupp.single 0 p.1.val+p.2.val+Finsupp.single 0 1 =
      Finsupp.single 0 (p.1.val+1)+p.2.val := by ext i; fin_cases i <;> simp <;> omega
  rw [he]
  have hb := (nonsymmetric_bivariate_standard_iff R hB hQ p.2.val).mp p.2.property
  rw [nonsymmetric_layer_monomial_image R hB hQ ⟨p.1.val+1,hp⟩ _ hb.1]
  simp [nonsymmetricBivariateBasis,L3A.standardBasis]

theorem nonsymmetric_layer_basis_X_image_ge
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : Fin (nonsymmetricDa R hB hQ) ×
      L3A.standardExponents (nonsymmetricBivariateIdeal (k:=k) R hB hQ))
    (hp : nonsymmetricDa R hB hQ ≤ p.1.val+1) :
    nonsymmetricColonXLayerEquiv R hB hQ
      (nonsymmetricColonGenerators (k:=k) R hQ 0 * nonsymmetricColonLayerBasis R hB hQ p)=0 := by
  rw [nonsymmetric_layer_basis_monomial,nonsymmetricColonAlgEquiv_X_mul]
  have hb := (nonsymmetric_bivariate_standard_iff R hB hQ p.2.val).mp p.2.property
  have hm : L3A.monomialClass (nonsymmetricPolynomialColonIdeal k R hB hQ)
      (Finsupp.single 0 p.1.val+p.2.val+Finsupp.single 0 1)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (nonsymmetric_polynomial_colon_monomial_mem R hB hQ _).mpr
    left
    simpa [hb.1] using hp
  rw [hm,map_zero,map_zero]

def truncatedLayerShift {V : Type*} [AddCommGroup V] [Module k V] (D : ℕ) :
    (Fin D → V) →ₗ[k] (Fin D → V) where
  toFun f i := if hi : i.val=0 then 0 else f ⟨i.val-1,by have := i.isLt; omega⟩
  map_add' := by intro f g; ext i; by_cases hi : i.val=0 <;> simp [hi]
  map_smul' := by intro a f; ext i; by_cases hi : i.val=0 <;> simp [hi]

theorem truncatedLayerShift_single {V : Type*} [AddCommGroup V] [Module k V]
    (D : ℕ) (i : Fin D) (v : V) :
    truncatedLayerShift (k:=k) D (Pi.single i v)=
      if hi : i.val+1<D then Pi.single (⟨i.val+1,hi⟩ : Fin D) v else 0 := by
  classical
  by_cases hi : i.val+1<D
  · simp only [dif_pos hi]
    ext j
    by_cases hj : j.val=0
    · have hji : j≠(⟨i.val+1,hi⟩ : Fin D) := by
        intro he
        have he' : j.val=i.val+1 := congrArg Fin.val he
        omega
      simp [truncatedLayerShift,hj,Pi.single_apply,hji]
    · have he : (⟨j.val-1,by have := j.isLt; omega⟩ : Fin D)=i ↔ j=(⟨i.val+1,hi⟩ : Fin D) := by
        constructor
        · intro h
          apply Fin.ext
          change j.val=i.val+1
          have hv : j.val-1=i.val := congrArg Fin.val h
          omega
        · intro h
          apply Fin.ext
          change j.val-1=i.val
          have hv : j.val=i.val+1 := congrArg Fin.val h
          omega
      simp [truncatedLayerShift,hj,Pi.single_apply,he]
  · simp only [dif_neg hi]
    ext j
    by_cases hj : j.val=0
    · simp [truncatedLayerShift,hj]
    · have he : (⟨j.val-1,by have := j.isLt; omega⟩ : Fin D)≠i := by
        intro h
        have hv : j.val-1=i.val := congrArg Fin.val h
        have := j.isLt
        omega
      simp [truncatedLayerShift,hj,Pi.single_apply,he]

def layerMultiply {V : Type*} [CommRing V] [Algebra k V] (D : ℕ) (b : V) :
    (Fin D → V) →ₗ[k] (Fin D → V) where
  toFun f i := b*f i
  map_add' := by intro f g; ext i; simp [mul_add]
  map_smul' := by intro a f; ext i; simp

theorem nonsymmetric_layer_YZ_intertwines
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 2) :
    (nonsymmetricColonXLayerEquiv (k:=k) R hB hQ).toLinearMap.comp
      (LinearMap.mulLeft k (nonsymmetricColonGenerators R hQ i.succ)) =
    (layerMultiply (k:=k) (nonsymmetricDa R hB hQ) (nonsymmetricBivariateGenerator R hB hQ i)).comp
      (nonsymmetricColonXLayerEquiv R hB hQ).toLinearMap := by
  classical
  apply (nonsymmetricColonLayerBasis (k:=k) R hB hQ).ext
  intro p
  simp only [LinearMap.comp_apply,LinearMap.mulLeft_apply,LinearEquiv.coe_coe]
  rw [nonsymmetric_layer_basis_YZ_image,nonsymmetric_layer_basis_image]
  ext j
  by_cases hj : j=p.1 <;> simp [layerMultiply,Pi.single_apply,hj]

theorem nonsymmetric_layer_X_intertwines
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    (nonsymmetricColonXLayerEquiv (k:=k) R hB hQ).toLinearMap.comp
      (LinearMap.mulLeft k (nonsymmetricColonGenerators R hQ 0)) =
    (truncatedLayerShift (k:=k) (nonsymmetricDa R hB hQ)).comp
      (nonsymmetricColonXLayerEquiv R hB hQ).toLinearMap := by
  classical
  apply (nonsymmetricColonLayerBasis (k:=k) R hB hQ).ext
  intro p
  simp only [LinearMap.comp_apply,LinearMap.mulLeft_apply,LinearEquiv.coe_coe]
  rw [nonsymmetric_layer_basis_image,truncatedLayerShift_single]
  split_ifs with hp
  · exact nonsymmetric_layer_basis_X_image_lt R hB hQ p hp
  · exact nonsymmetric_layer_basis_X_image_ge R hB hQ p (by omega)

theorem nonsymmetric_layer_operator_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    ∃ e : nonsymmetricPrincipalColonQuotient k R hQ ≃ₗ[k]
      (Fin (nonsymmetricDa R hB hQ) → nonsymmetricBivariateQuotient (k:=k) R hB hQ),
      ∀ t,
        e (nonsymmetricColonGenerators R hQ 0*t)=truncatedLayerShift (k:=k) (nonsymmetricDa R hB hQ) (e t) ∧
        e (nonsymmetricColonGenerators R hQ 1*t)=layerMultiply (k:=k) (nonsymmetricDa R hB hQ)
          (nonsymmetricBivariateGenerator R hB hQ 0) (e t) ∧
        e (nonsymmetricColonGenerators R hQ 2*t)=layerMultiply (k:=k) (nonsymmetricDa R hB hQ)
          (nonsymmetricBivariateGenerator R hB hQ 1) (e t) := by
  refine ⟨nonsymmetricColonXLayerEquiv R hB hQ,fun t => ⟨?_,?_,?_⟩⟩
  · exact LinearMap.congr_fun (nonsymmetric_layer_X_intertwines R hB hQ) t
  · exact LinearMap.congr_fun (nonsymmetric_layer_YZ_intertwines R hB hQ 0) t
  · exact LinearMap.congr_fun (nonsymmetric_layer_YZ_intertwines R hB hQ 1) t

end NS25Lean.L5A2BFinalRepair
