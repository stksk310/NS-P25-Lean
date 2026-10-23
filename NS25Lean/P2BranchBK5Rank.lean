import NS25Lean.P2MixedCornerCount
import NS25Lean.P2MixedKoszulLayers

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1 MvPolynomial
variable {k : Type*} [Field k] {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Intrinsically finite actual mixed minimal generators, not a rank packet. -/
abbrev NonsymmetricK5Corners (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  L3A.MixedCorners (nonsymmetricBivariateIdeal (k:=k) R hB hQ)

theorem nonsymmetric_bivariate_H0_eq_socle (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricBivariateH0 (k:=k) R hB hQ =
      L3A.socle (nonsymmetricBivariateIdeal (k:=k) R hB hQ) := by
  ext z
  constructor
  · intro hz i
    have hc : ![nonsymmetricBivariateGenerator (k:=k) R hB hQ 0*z,
        nonsymmetricBivariateGenerator (k:=k) R hB hQ 1*z] = 0 := hz
    fin_cases i
    · change Ideal.Quotient.mkₐ k _ (X 0)*z=0
      rw [nonsymmetric_bivariate_X_zero,zero_mul]
    · exact congrFun hc 0
    · exact congrFun hc 1
  · intro hz
    change ![nonsymmetricBivariateGenerator (k:=k) R hB hQ 0*z,
        nonsymmetricBivariateGenerator (k:=k) R hB hQ 1*z] = 0
    ext i
    fin_cases i
    · exact hz 1
    · exact hz 2

theorem nonsymmetric_K5_corner_count (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (nonsymmetricPrincipalColonH0 (k:=k) R hQ) ≤
      Nat.card (NonsymmetricK5Corners (k:=k) R hB hQ)+1 := by
  rw [nonsymmetric_principal_colon_koszulH0_bivariate_finrank R hB hQ,
    nonsymmetric_bivariate_H0_eq_socle R hB hQ,
    Module.finrank_eq_nat_card_basis (L3A.socleBasis _ (nonsymmetric_bivariate_isMonomial R hB hQ))]
  exact L3A.socle_card_le_mixed_corners_add_one _ (nonsymmetric_bivariate_isMonomial R hB hQ)
    (fun a ha => ((nonsymmetric_bivariate_standard_iff R hB hQ a).mp ha).1)

/-- The three neighboring exponents in the source's K5 corner stencil. -/
def nonsymmetricK5BaseExponent (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) : Fin 3 →₀ ℕ :=
  symmetricBoxExponent (nonsymmetricDa R hB hQ-1) (g.val.val 1-1) (g.val.val 2-1)

theorem nonsymmetric_K5_neighbors_standard (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) :
    ∀ i : Fin 3, i ≠ 0 →
      nonsymmetricK5BaseExponent R hB hQ g + Finsupp.single i 1 ∈
        L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ) := by
  intro i hi
  apply (nonsymmetric_standard_X_split R hB hQ _).mpr
  have hd := nonsymmetricDa_positive R hB hQ
  have hg0 := g.property.1
  have hgr := g.property.2.1
  have hgs := g.property.2.2
  constructor
  · fin_cases i <;> simp_all [nonsymmetricK5BaseExponent,symmetricBoxExponent]
  · apply L3A.standard_below_minimal _ g.val
    · intro j
      fin_cases i <;> fin_cases j <;>
        simp_all [nonsymmetricK5BaseExponent,symmetricBoxExponent]
    · intro he
      have h1 := congrArg (fun a : Fin 3 →₀ ℕ => a 1) he
      have h2 := congrArg (fun a : Fin 3 →₀ ℕ => a 2) he
      fin_cases i
      · exact hi rfl
      · have hz : g.val.val 2-1=g.val.val 2 := by
          simpa [nonsymmetricK5BaseExponent,symmetricBoxExponent] using h2
        omega
      · have hy : g.val.val 1-1=g.val.val 1 := by
          simpa [nonsymmetricK5BaseExponent,symmetricBoxExponent] using h1
        omega

theorem nonsymmetric_K5_base_standard (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) :
    nonsymmetricK5BaseExponent R hB hQ g ∈
      L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ) :=
  L3A.standard_of_le _ (nonsymmetric_polynomial_colon_isMonomial R hB hQ)
    (nonsymmetric_K5_neighbors_standard R hB hQ g 1 (by decide))
    (by intro i; simp only [Finsupp.add_apply]; omega)

theorem nonsymmetric_K5_cycle_exponent_killed (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) :
    ∀ i : Fin 3, i ≠ 2 →
      monomial (nonsymmetricK5BaseExponent R hB hQ g + Finsupp.single 2 1 +
        Finsupp.single i 1) (1 : k) ∈ nonsymmetricPolynomialColonIdeal k R hB hQ := by
  intro i hi
  by_contra hn
  have hs := (nonsymmetric_standard_X_split R hB hQ _).mp hn
  have hd := nonsymmetricDa_positive R hB hQ
  have hg0 := g.property.1
  have hgr := g.property.2.1
  have hgs := g.property.2.2
  fin_cases i
  · have hx := hs.1
    simp [nonsymmetricK5BaseExponent,symmetricBoxExponent] at hx
    omega
  · have he : (nonsymmetricK5BaseExponent R hB hQ g + Finsupp.single 2 1 +
        Finsupp.single 1 1).erase 0 = g.val.val := by
      ext j
      fin_cases j <;> simp_all [nonsymmetricK5BaseExponent,symmetricBoxExponent] <;> omega
    have hs' : (nonsymmetricK5BaseExponent R hB hQ g + Finsupp.single 2 1 +
        Finsupp.single 1 1).erase 0 ∈ L3A.standardExponents
          (nonsymmetricBivariateIdeal (k:=k) R hB hQ) := hs.2
    rw [he] at hs'
    exact hs' g.val.property.1
  · exact hi rfl

def nonsymmetricK5Cycle (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) :
    LinearMap.ker (threeKoszulD1 (k:=k) (nonsymmetricColonGenerators (k:=k) R hQ)) := by
  let a := nonsymmetricK5BaseExponent R hB hQ g + Finsupp.single 2 1
  let z := nonsymmetricPrincipalColonAlgEquiv (k:=k) R hB hQ
    (L3A.monomialClass (nonsymmetricPolynomialColonIdeal k R hB hQ) a)
  have hz : ∀ i : Fin 3, i ≠ 2 → nonsymmetricColonGenerators (k:=k) R hQ i*z=0 := by
    intro i hi
    rw [nonsymmetricColonAlgEquiv_X_mul]
    have he : L3A.monomialClass (nonsymmetricPolynomialColonIdeal k R hB hQ)
        (a+Finsupp.single i 1)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (nonsymmetric_K5_cycle_exponent_killed R hB hQ g i hi)
    rw [he,map_zero]
  refine ⟨![0,0,z],?_⟩
  ext i
  fin_cases i <;> simp [threeKoszulD1,hz 0 (by decide),hz 1 (by decide)]

def nonsymmetricK5Class (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) : nonsymmetricPrincipalColonH1 (k:=k) R hQ :=
  Submodule.Quotient.mk (nonsymmetricK5Cycle R hB hQ g)

def nonsymmetricK5Degree (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) : (nsH R).toAddSubmonoid :=
  nonsymmetricPrincipalDegree R + nonsymmetricGridDegree R
    (nonsymmetricDa R hB hQ-1) (g.val.val 1-1) (g.val.val 2-1)

theorem nonsymmetric_standard_prefix_survival (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (a : L3A.standardExponents (nonsymmetricPolynomialColonIdeal k R hB hQ)) :
    (((nonsymmetricPrincipalDegree R + nonsymmetricGridDegree R
      (a.val 0) (a.val 1) (a.val 2)).val : ℕ) : ℤ) ∉ nonsymmetricPrefixIdeal R hQ := by
  intro hc
  apply nonsymmetric_standard_actual_survives R hB hQ a
  apply (nonsymmetric_principal_colon_single_mem_iff R hQ _).mpr
  refine ⟨⟨_,(nonsymmetricGridDegree R (a.val 0) (a.val 1) (a.val 2)).property,rfl⟩,?_⟩
  exact hc

theorem nonsymmetric_K5_prefix_survival (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) :
    ((nonsymmetricK5Degree R hB hQ g).val : ℤ) ∉ nonsymmetricPrefixIdeal R hQ ∧
    (((nonsymmetricK5Degree R hB hQ g + nonsymmetricTailMonomialDegree R 1).val : ℕ) : ℤ)
      ∉ nonsymmetricPrefixIdeal R hQ ∧
    (((nonsymmetricK5Degree R hB hQ g + nonsymmetricTailMonomialDegree R 2).val : ℕ) : ℤ)
      ∉ nonsymmetricPrefixIdeal R hQ := by
  have hb := nonsymmetric_standard_prefix_survival R hB hQ
    ⟨_,nonsymmetric_K5_base_standard R hB hQ g⟩
  have hy := nonsymmetric_standard_prefix_survival R hB hQ
    ⟨_,nonsymmetric_K5_neighbors_standard R hB hQ g 1 (by decide)⟩
  have hz := nonsymmetric_standard_prefix_survival R hB hQ
    ⟨_,nonsymmetric_K5_neighbors_standard R hB hQ g 2 (by decide)⟩
  constructor
  · simpa [nonsymmetricK5Degree,nonsymmetricK5BaseExponent,symmetricBoxExponent] using hb
  constructor
  · convert hy using 1 <;>
      simp [nonsymmetricK5Degree,nonsymmetricK5BaseExponent,symmetricBoxExponent,
        nonsymmetricGridDegree,nonsymmetricTailMonomialDegree,add_mul] <;> ring
  · convert hz using 1 <;>
      simp [nonsymmetricK5Degree,nonsymmetricK5BaseExponent,symmetricBoxExponent,
        nonsymmetricGridDegree,nonsymmetricTailMonomialDegree,add_mul] <;> ring

theorem nonsymmetric_K5_comparison_components (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) :
    (nonsymmetricPrincipalComparisonCycles (k:=k) R hQ (nonsymmetricK5Cycle R hB hQ g)).val 1=0 ∧
    (nonsymmetricPrincipalComparisonCycles (k:=k) R hQ (nonsymmetricK5Cycle R hB hQ g)).val 2=
      carrierMonomialClass (k:=k) (nonsymmetricPrefixIdeal R hQ)
        (nonsymmetricK5Degree R hB hQ g+nonsymmetricTailMonomialDegree R 2) := by
  constructor
  · exact (nonsymmetricPrincipalInjection (k:=k) R hQ).map_zero
  · let a := nonsymmetricK5BaseExponent R hB hQ g + Finsupp.single 2 1
    change nonsymmetricPrincipalInjection (k:=k) R hQ
      (nonsymmetricColonPolynomialMap (k:=k) R hQ (monomial a 1))=_
    rw [nonsymmetricColonPolynomialMap_monomial]
    change Ideal.Quotient.mkₐ k _
      (AddMonoidAlgebra.single (nonsymmetricPrincipalDegree R) (1 : k) *
        AddMonoidAlgebra.single (nonsymmetricGridDegree R (a 0) (a 1) (a 2)) 1)=_
    rw [AddMonoidAlgebra.single_mul_single,one_mul]
    congr 2
    apply Subtype.ext
    simp [a,nonsymmetricK5Degree,nonsymmetricK5BaseExponent,symmetricBoxExponent,
      nonsymmetricGridDegree,nonsymmetricTailMonomialDegree,add_mul]
    ring

theorem nonsymmetric_K5_degree_injective (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricK5Degree (k:=k) R hB hQ) := by
  intro g g' he
  have hs := nonsymmetric_K5_base_standard R hB hQ g
  have hs' := nonsymmetric_K5_base_standard R hB hQ g'
  have hd := (nonsymmetric_standard_domain R hB hQ ⟨_,hs⟩).2
  have hd' := (nonsymmetric_standard_domain R hB hQ ⟨_,hs'⟩).2
  simp only [nonsymmetricK5BaseExponent,symmetricBoxExponent,Finsupp.add_apply,
    Finsupp.single_apply,Fin.reduceEq,ite_true,ite_false,add_zero,zero_add] at hd hd'
  have hn := congrArg (fun t : (nsH R).toAddSubmonoid => t.val) he
  change _+((nonsymmetricDa R hB hQ-1)*nsA R+(g.val.val 1-1)*nsB R+(g.val.val 2-1)*nsC R)=
    _+((nonsymmetricDa R hB hQ-1)*nsA R+(g'.val.val 1-1)*nsB R+(g'.val.val 2-1)*nsC R) at hn
  have hc := Nat.add_left_cancel hn
  obtain ⟨_,hy,hz⟩ := nonsymmetric_lShape_degree_injective R hd hd' hc
  have hgr := g.property.2.1
  have hgs := g.property.2.2
  have hgr' := g'.property.2.1
  have hgs' := g'.property.2.2
  have h1 : g.val.val 1=g'.val.val 1 := by omega
  have h2 : g.val.val 2=g'.val.val 2 := by omega
  apply Subtype.ext
  apply Subtype.ext
  ext i
  fin_cases i
  · exact g.property.1.trans g'.property.1.symm
  · exact h1
  · exact h2

def nonsymmetricK5Detector (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g : NonsymmetricK5Corners (k:=k) R hB hQ) :
    nonsymmetricPrincipalPrefixH1 (k:=k) R hQ →ₗ[k] k :=
  carrierCornerDetection (nonsymmetricPrefixIdeal R hQ) (nonsymmetricTailMonomialDegree R)
    (nonsymmetricK5Degree R hB hQ g)
    (nonsymmetric_K5_prefix_survival R hB hQ g).1
    (nonsymmetric_K5_prefix_survival R hB hQ g).2.1
    (nonsymmetric_K5_prefix_survival R hB hQ g).2.2

theorem nonsymmetric_K5_detector_delta (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (g g' : NonsymmetricK5Corners (k:=k) R hB hQ) :
    nonsymmetricK5Detector R hB hQ g
      (nonsymmetricPrincipalComparisonH1 (k:=k) R hQ (nonsymmetricK5Class R hB hQ g'))=
      if g'=g then 1 else 0 := by
  classical
  let z := nonsymmetricPrincipalComparisonCycles (k:=k) R hQ (nonsymmetricK5Cycle R hB hQ g')
  change carrierCoefficient (k:=k) (nonsymmetricPrefixIdeal R hQ)
      (nonsymmetricK5Degree R hB hQ g+nonsymmetricTailMonomialDegree R 2)
      (nonsymmetric_K5_prefix_survival R hB hQ g).2.2 (z.val 2)-
    carrierCoefficient (k:=k) (nonsymmetricPrefixIdeal R hQ)
      (nonsymmetricK5Degree R hB hQ g+nonsymmetricTailMonomialDegree R 1)
      (nonsymmetric_K5_prefix_survival R hB hQ g).2.1 (z.val 1)=_
  rw [(nonsymmetric_K5_comparison_components R hB hQ g').1,
    (nonsymmetric_K5_comparison_components R hB hQ g').2, map_zero,sub_zero,carrierCoefficient_class]
  have he : nonsymmetricK5Degree R hB hQ g'+nonsymmetricTailMonomialDegree R 2=
      nonsymmetricK5Degree R hB hQ g+nonsymmetricTailMonomialDegree R 2 ↔ g'=g := by
    constructor
    · intro h
      exact nonsymmetric_K5_degree_injective R hB hQ (add_right_cancel h)
    · rintro rfl; rfl
  simp only [he]

theorem nonsymmetric_K5_comparison_images_independent (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearIndependent k (fun g : NonsymmetricK5Corners (k:=k) R hB hQ =>
      nonsymmetricPrincipalComparisonH1 (k:=k) R hQ (nonsymmetricK5Class R hB hQ g)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc g hg
  have he := congrArg (nonsymmetricK5Detector (k:=k) R hB hQ g) hc
  simpa [map_sum,map_smul,nonsymmetric_K5_detector_delta,hg] using he

/-- Actual K5 detector separation supplies the comparison rank; no desired
cardinality, survival, or rank assumptions are added to Branch B. -/
theorem nonsymmetric_principal_comparison_rank_lower_bound
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (nonsymmetricPrincipalColonH0 (k:=k) R hQ) ≤
      Module.finrank k (LinearMap.range (nonsymmetricPrincipalComparisonH1 (k:=k) R hQ))+1 := by
  classical
  letI := nonsymmetric_colon_H1_finite (k:=k) R hQ
  letI := Fintype.ofFinite (NonsymmetricK5Corners (k:=k) R hB hQ)
  let f := nonsymmetricPrincipalComparisonH1 (k:=k) R hQ
  let v : NonsymmetricK5Corners (k:=k) R hB hQ → LinearMap.range f :=
    fun g => ⟨f (nonsymmetricK5Class R hB hQ g),⟨_,rfl⟩⟩
  have hv : LinearIndependent k v := by
    apply LinearIndependent.of_comp (LinearMap.range f).subtype
    exact nonsymmetric_K5_comparison_images_independent R hB hQ
  have hn := hv.fintype_card_le_finrank
  have hc := nonsymmetric_K5_corner_count (k:=k) R hB hQ
  rw [Nat.card_eq_fintype_card] at hc
  exact hc.trans (Nat.add_le_add_right hn 1)

end NS25Lean.L5A2BFinalRepair
