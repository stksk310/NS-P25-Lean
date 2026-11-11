import NS25Lean.P2BranchBK5Rank

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace NS25Lean.PrincipalTensorColon
open L5A2BFinalRepair L3A MvPolynomial ToricPresentation
variable {k : Type*} [Field k] {H : NumericalSemigroup}

abbrev Carrier (I : RelativeIdeal H) :=
  SemigroupAlgebra k H.toAddSubmonoid ⧸ carrierMonomialIdeal k I
abbrev Colon (I : RelativeIdeal H) (f : H.toAddSubmonoid) :=
  SemigroupAlgebra k H.toAddSubmonoid ⧸
    (carrierMonomialIdeal k I).colon {AddMonoidAlgebra.single f (1:k)}

def degree (g : Fin 3 → H.toAddSubmonoid) (a : L3A.Exponent) : H.toAddSubmonoid :=
  a 0 • g 0 + a 1 • g 1 + a 2 • g 2

/-- A coordinate presentation of the numerically graded tensor colon.
`J` is written in three variables with X killed. `standard_split` expresses
`k[X]/(X^D) ⊗ k[Y,Z]/J`; `monomial_images` is its numerical grading.
No socle, rank, cycle, exceptional witness, or desired bound is stored. -/
structure GradedPresentation (I : RelativeIdeal H) (f : H.toAddSubmonoid)
    (g : Fin 3 → H.toAddSubmonoid) where
  K : Ideal (MvPolynomial (Fin 3) k)
  J : Ideal (MvPolynomial (Fin 3) k)
  monomialK : L2B.IsMonomialIdeal k K
  monomialJ : L2B.IsMonomialIdeal k J
  D : ℕ
  positive : 0<D
  plane : ∀ a∈standardExponents J, a 0=0
  standard_split : ∀ a, a∈standardExponents K ↔
    a 0<D ∧ a.erase 0∈standardExponents J
  equiv : (MvPolynomial (Fin 3) k ⧸ K) ≃ₐ[k] Colon (k:=k) I f
  generator_images : ∀ i, equiv (Ideal.Quotient.mkₐ k K (X i))=
    Ideal.Quotient.mkₐ k _ (AddMonoidAlgebra.single (g i) 1)
  monomial_images : ∀ a, equiv (monomialClass K a)=
    Ideal.Quotient.mkₐ k _ (AddMonoidAlgebra.single (degree g a) 1)

variable {I : RelativeIdeal H} {f : H.toAddSubmonoid} {g : Fin 3 → H.toAddSubmonoid}
variable (T : GradedPresentation (k:=k) I f g)
abbrev Poly := MvPolynomial (Fin 3) k ⧸ T.K

def inject : Poly T →ₗ[k] Carrier (k:=k) I :=
  (principalColonInjection (k:=k) (carrierMonomialIdeal k I)
    (AddMonoidAlgebra.single f 1)).comp T.equiv.toLinearMap

theorem inject_injective : Function.Injective (inject T) :=
  (principalColonInjection_injective (k:=k) (carrierMonomialIdeal k I)
    (AddMonoidAlgebra.single f (1:k))).comp T.equiv.injective

theorem inject_monomial (a : L3A.Exponent) :
    inject T (monomialClass T.K a)=carrierMonomialClass (k:=k) I (f+degree g a) := by
  change principalColonInjection _ _ (T.equiv (monomialClass T.K a))=_
  rw [T.monomial_images]
  change Ideal.Quotient.mkₐ k _
    (AddMonoidAlgebra.single f (1:k)*AddMonoidAlgebra.single (degree g a) 1)=_
  rw [AddMonoidAlgebra.single_mul_single,one_mul]
  rfl

def generators (i : Fin 3) : Poly T := Ideal.Quotient.mkₐ k T.K (X i)

theorem inject_generator (i : Fin 3) (z : Poly T) :
    inject T (generators T i*z)=carrierGenerators (k:=k) I g i*inject T z := by
  change principalColonInjection _ _ (T.equiv (generators T i*z))=_
  rw [map_mul]
  unfold generators
  rw [T.generator_images]
  change principalColonInjection (k:=k) (carrierMonomialIdeal k I) (AddMonoidAlgebra.single f 1)
      (_ * T.equiv z)=carrierGenerators (k:=k) I g i *
      principalColonInjection (k:=k) (carrierMonomialIdeal k I) (AddMonoidAlgebra.single f 1) (T.equiv z)
  generalize he : T.equiv z=w
  refine Quotient.inductionOn' w ?_
  intro p
  change Ideal.Quotient.mkₐ k (carrierMonomialIdeal k I)
    (AddMonoidAlgebra.single f (1:k)*(AddMonoidAlgebra.single (g i) 1*p))=
    Ideal.Quotient.mkₐ k (carrierMonomialIdeal k I) (AddMonoidAlgebra.single (g i) 1)*
      Ideal.Quotient.mkₐ k (carrierMonomialIdeal k I) (AddMonoidAlgebra.single f (1:k)*p)
  rw [← map_mul]
  congr 1
  ring

theorem standard_survives (a : standardExponents T.K) :
    ((f+degree g a.val).val : ℤ)∉I := by
  intro hm
  have hz : inject T (monomialClass T.K a.val)=0 := by
    rw [inject_monomial,carrierMonomialClass_eq_zero_iff]
    exact hm
  have hp : monomialClass T.K a.val=0 := (inject_injective T) (by simpa using hz)
  exact a.property (Ideal.Quotient.eq_zero_iff_mem.mp hp)

/-- Thin numerical grading is proved from the actual graded equivalence,
rather than imposed as independence of the mixed cycle degrees. -/
theorem standard_degree_injective :
    Function.Injective (fun a : standardExponents T.K => degree g a.val) := by
  intro a b he
  change degree g a.val=degree g b.val at he
  have hm : monomialClass T.K a.val=monomialClass T.K b.val := by
    apply T.equiv.injective
    rw [T.monomial_images,T.monomial_images,he]
  exact (standard_linearIndependent T.K T.monomialK).injective hm

abbrev Corners := MixedCorners T.J

def cornerBase (c : Corners T) : L3A.Exponent :=
  symmetricBoxExponent (T.D-1) (c.val.val 1-1) (c.val.val 2-1)

theorem corner_neighbors (c : Corners T) : ∀ i : Fin 3, i≠0 →
    cornerBase T c+Finsupp.single i 1∈standardExponents T.K := by
  intro i hi
  apply (T.standard_split _).mpr
  have hd := T.positive
  have h0 := c.property.1
  have hr := c.property.2.1
  have hs := c.property.2.2
  constructor
  · fin_cases i <;> simp_all [cornerBase,symmetricBoxExponent]
  · apply standard_below_minimal _ c.val
    · intro j
      fin_cases i <;> fin_cases j <;> simp_all [cornerBase,symmetricBoxExponent]
    · intro he
      have h1 := congrArg (fun a : L3A.Exponent => a 1) he
      have h2 := congrArg (fun a : L3A.Exponent => a 2) he
      fin_cases i
      · exact hi rfl
      · have he : c.val.val 2-1=c.val.val 2 := by simpa [cornerBase,symmetricBoxExponent] using h2
        omega
      · have he : c.val.val 1-1=c.val.val 1 := by simpa [cornerBase,symmetricBoxExponent] using h1
        omega

theorem corner_base_standard (c : Corners T) : cornerBase T c∈standardExponents T.K :=
  standard_of_le _ T.monomialK (corner_neighbors T c 1 (by decide))
    (by intro i; simp only [Finsupp.add_apply]; omega)

theorem corner_killed (c : Corners T) : ∀ i : Fin 3, i≠2 →
    monomial (cornerBase T c+Finsupp.single 2 1+Finsupp.single i 1) (1:k)∈T.K := by
  intro i hi
  by_contra hn
  have he := (T.standard_split _).mp hn
  have hd := T.positive
  have h0 := c.property.1
  have hr := c.property.2.1
  have hs := c.property.2.2
  fin_cases i
  · have hx := he.1
    simp [cornerBase,symmetricBoxExponent] at hx
    omega
  · have ha : (cornerBase T c+Finsupp.single 2 1+Finsupp.single 1 1).erase 0=c.val.val := by
      ext j
      fin_cases j <;> simp_all [cornerBase,symmetricBoxExponent] <;> omega
    have hs := he.2
    change (cornerBase T c+Finsupp.single 2 1+Finsupp.single 1 1).erase 0∈standardExponents T.J at hs
    rw [ha] at hs
    exact hs c.val.property.1
  · exact hi rfl

def cornerCycle (c : Corners T) : LinearMap.ker (threeKoszulD1 (k:=k) (generators T)) := by
  let z := monomialClass T.K (cornerBase T c+Finsupp.single 2 1)
  have hz : ∀ i : Fin 3, i≠2 → generators T i*z=0 := by
    intro i hi
    rw [show generators T i*z=monomialClass T.K
      (cornerBase T c+Finsupp.single 2 1+Finsupp.single i 1) from X_mul_monomialClass _ _ _]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (corner_killed T c i hi)
  exact ⟨![0,0,z],by ext i; fin_cases i <;> simp [threeKoszulD1,hz 0 (by decide),hz 1 (by decide)]⟩

def comparisonCycles : LinearMap.ker (threeKoszulD1 (k:=k) (generators T)) →ₗ[k]
    LinearMap.ker (threeKoszulD1 (k:=k) (carrierGenerators (k:=k) I g)) where
  toFun z := ⟨fun i => inject T (z.val i),by
    have hc := z.property
    ext i
    fin_cases i
    · simpa [threeKoszulD1,map_sub,inject_generator] using
        congrArg (inject T) (congrFun hc (0:Fin 3))
    · simpa [threeKoszulD1,map_sub,inject_generator] using
        congrArg (inject T) (congrFun hc (1:Fin 3))
    · simpa [threeKoszulD1,map_sub,inject_generator] using
        congrArg (inject T) (congrFun hc (2:Fin 3))⟩
  map_add' := by
    intro z w; apply Subtype.ext; ext i
    exact (inject T).map_add _ _
  map_smul' := by
    intro a z; apply Subtype.ext; ext i
    exact (inject T).map_smul _ _

def cornerDegree (c : Corners T) : H.toAddSubmonoid := f+degree g (cornerBase T c)

theorem degree_add_generator (a : L3A.Exponent) (i : Fin 3) :
    degree g (a+Finsupp.single i 1)=degree g a+g i := by
  ext
  fin_cases i <;> simp [degree,add_nsmul] <;> omega

theorem corner_survival (c : Corners T) :
    ((cornerDegree T c).val : ℤ)∉I ∧
    (((cornerDegree T c+g 1).val : ℕ):ℤ)∉I ∧
    (((cornerDegree T c+g 2).val : ℕ):ℤ)∉I := by
  refine ⟨standard_survives T ⟨_,corner_base_standard T c⟩,?_,?_⟩
  · simpa [cornerDegree,degree_add_generator,add_assoc] using
      standard_survives T ⟨_,corner_neighbors T c 1 (by decide)⟩
  · simpa [cornerDegree,degree_add_generator,add_assoc] using
      standard_survives T ⟨_,corner_neighbors T c 2 (by decide)⟩

theorem cornerDegree_injective : Function.Injective (cornerDegree T) := by
  intro c c' he
  have hw : degree g (cornerBase T c)=degree g (cornerBase T c') := add_left_cancel he
  have hb : (⟨_,corner_base_standard T c⟩:standardExponents T.K)=
      ⟨_,corner_base_standard T c'⟩ := standard_degree_injective T hw
  have he := congrArg (fun a : standardExponents T.K => a.val) hb
  have hr := c.property.2.1
  have hs := c.property.2.2
  have hr' := c'.property.2.1
  have hs' := c'.property.2.2
  change cornerBase T c=cornerBase T c' at he
  have h1 : c.val.val 1-1=c'.val.val 1-1 := by simpa [cornerBase,symmetricBoxExponent] using congrArg (fun a : L3A.Exponent => a 1) he
  have h2 : c.val.val 2-1=c'.val.val 2-1 := by simpa [cornerBase,symmetricBoxExponent] using congrArg (fun a : L3A.Exponent => a 2) he
  apply Subtype.ext
  apply Subtype.ext
  ext i
  fin_cases i
  · exact c.property.1.trans c'.property.1.symm
  · change c.val.val 1=c'.val.val 1; omega
  · change c.val.val 2=c'.val.val 2; omega

theorem comparison_components (c : Corners T) :
    (comparisonCycles T (cornerCycle T c)).val 1=0 ∧
    (comparisonCycles T (cornerCycle T c)).val 2=
      carrierMonomialClass (k:=k) I (cornerDegree T c+g 2) := by
  constructor
  · exact (inject T).map_zero
  · change inject T (monomialClass T.K (cornerBase T c+Finsupp.single 2 1))=_
    rw [inject_monomial,degree_add_generator,← add_assoc]
    rfl

/-- Actual coefficient detectors separate every staircase mixed-cycle image.
The only inputs are the colon presentation and its numerical grading. -/
theorem mixed_comparison_images_independent :
    LinearIndependent k (fun c : Corners T =>
      (Submodule.Quotient.mk (comparisonCycles T (cornerCycle T c)) :
        ThreeKoszulH1 (k:=k) (carrierGenerators (k:=k) I g))) := by
  classical
  let det := fun c : Corners T => carrierCornerDetection (k:=k) I g (cornerDegree T c)
    (corner_survival T c).1 (corner_survival T c).2.1 (corner_survival T c).2.2
  have delta : ∀ c c' : Corners T,
      det c (Submodule.Quotient.mk (comparisonCycles T (cornerCycle T c')))=
        if c'=c then 1 else 0 := by
    intro c c'
    change carrierCoefficient (k:=k) I (cornerDegree T c+g 2) (corner_survival T c).2.2
      ((comparisonCycles T (cornerCycle T c')).val 2)-
      carrierCoefficient (k:=k) I (cornerDegree T c+g 1) (corner_survival T c).2.1
      ((comparisonCycles T (cornerCycle T c')).val 1)=_
    rw [(comparison_components T c').1,(comparison_components T c').2,map_zero,
      sub_zero,carrierCoefficient_class]
    have he : cornerDegree T c'+g 2=cornerDegree T c+g 2 ↔ c'=c := by
      constructor
      · intro h; exact cornerDegree_injective T (add_right_cancel h)
      · rintro rfl; rfl
    simp only [he]
  apply linearIndependent_iff'.mpr
  intro s v hv c hc
  have hd := congrArg (det c) hv
  simpa [map_sum,map_smul,delta,hc] using hd

def comparisonPre : LinearMap.ker (threeKoszulD1 (k:=k) (generators T)) →ₗ[k]
    ThreeKoszulH1 (k:=k) (carrierGenerators (k:=k) I g) :=
  (((LinearMap.range (threeKoszulD0 (k:=k) (carrierGenerators (k:=k) I g))).comap
    (LinearMap.ker (threeKoszulD1 (k:=k) (carrierGenerators (k:=k) I g))).subtype).mkQ).comp
      (comparisonCycles T)

theorem comparisonPre_boundary_zero
    (z : LinearMap.ker (threeKoszulD1 (k:=k) (generators T)))
    (hz : z∈(LinearMap.range (threeKoszulD0 (k:=k) (generators T))).comap
      (LinearMap.ker (threeKoszulD1 (k:=k) (generators T))).subtype) : comparisonPre T z=0 := by
  obtain ⟨w,hw⟩ := hz
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (fun i => inject T (z.val i))∈LinearMap.range
    (threeKoszulD0 (k:=k) (carrierGenerators (k:=k) I g))
  refine ⟨inject T w,?_⟩
  have he : threeKoszulD0 (k:=k) (generators T) w=z.val := hw
  rw [← he]
  ext i
  exact (inject_generator T i w).symm

def comparisonH1 : ThreeKoszulH1 (k:=k) (generators T) →ₗ[k]
    ThreeKoszulH1 (k:=k) (carrierGenerators (k:=k) I g) :=
  ((LinearMap.range (threeKoszulD0 (k:=k) (generators T))).comap
    (LinearMap.ker (threeKoszulD1 (k:=k) (generators T))).subtype).liftQ
      (comparisonPre T) (comparisonPre_boundary_zero T)

/-- The rank lower bound is derived from all actual mixed generators. -/
theorem mixed_corner_count_le_comparison_rank :
    Nat.card (Corners T) ≤ Module.finrank k (LinearMap.range (comparisonH1 T)) := by
  classical
  letI := carrierMonomialQuotient_finite (k:=k) I
  letI := Module.Finite.of_injective (inject T) (inject_injective T)
  letI := Fintype.ofFinite (Corners T)
  let v : Corners T → LinearMap.range (comparisonH1 T) := fun c =>
    ⟨comparisonH1 T (Submodule.Quotient.mk (cornerCycle T c)),⟨_,rfl⟩⟩
  have hv : LinearIndependent k v := by
    apply LinearIndependent.of_comp (LinearMap.range (comparisonH1 T)).subtype
    exact mixed_comparison_images_independent T
  simpa only [Nat.card_eq_fintype_card] using hv.fintype_card_le_finrank

#print axioms mixed_comparison_images_independent
#print axioms mixed_corner_count_le_comparison_rank
end NS25Lean.PrincipalTensorColon

namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1 MvPolynomial
open PrincipalTensorColon
variable {k : Type*} [Field k] {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Actual old nonsymmetric colon satisfies the common graded presentation;
all fields are taken from its proved kernel and canonical numerical map. -/
def nonsymmetricSharedGradedPresentation (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1<actualPrincipalIndex P.M.base) :
    GradedPresentation (k:=k) (nonsymmetricPrefixIdeal R hQ)
      (nonsymmetricPrincipalDegree R) (nonsymmetricTailMonomialDegree R) where
  K := nonsymmetricPolynomialColonIdeal k R hB hQ
  J := nonsymmetricBivariateIdeal (k:=k) R hB hQ
  monomialK := nonsymmetric_polynomial_colon_isMonomial R hB hQ
  monomialJ := nonsymmetric_bivariate_isMonomial R hB hQ
  D := nonsymmetricDa R hB hQ
  positive := nonsymmetricDa_positive R hB hQ
  plane := fun a ha => ((nonsymmetric_bivariate_standard_iff R hB hQ a).mp ha).1
  standard_split := nonsymmetric_standard_X_split R hB hQ
  equiv := nonsymmetricPrincipalColonAlgEquiv R hB hQ
  generator_images := nonsymmetricColonAlgEquiv_X R hB hQ
  monomial_images := by
    intro a
    change nonsymmetricColonPolynomialMap (k:=k) R hQ (monomial a 1)=_
    rw [nonsymmetricColonPolynomialMap_monomial]
    congr 2

/-- Shared detector theorem instantiated on the actual old Branch B cycles. -/
theorem nonsymmetric_shared_comparison_images_independent
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1<actualPrincipalIndex P.M.base) :
    LinearIndependent k (fun c : NonsymmetricK5Corners (k:=k) R hB hQ =>
      nonsymmetricPrincipalComparisonH1 (k:=k) R hQ (nonsymmetricK5Class R hB hQ c)) := by
  have h := mixed_comparison_images_independent (nonsymmetricSharedGradedPresentation (k:=k) R hB hQ)
  convert h using 1 <;> first | rfl | skip
  apply heq_of_eq
  funext c
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  ext i
  fin_cases i
  · change nonsymmetricPrincipalInjection (k:=k) R hQ 0=
      inject (nonsymmetricSharedGradedPresentation (k:=k) R hB hQ) 0
    simp
  · change nonsymmetricPrincipalInjection (k:=k) R hQ 0=
      inject (nonsymmetricSharedGradedPresentation (k:=k) R hB hQ) 0
    simp
  · rfl

/-- Actual comparison rank now follows from the reusable graded construction. -/
theorem nonsymmetric_shared_principal_comparison_rank_lower_bound
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1<actualPrincipalIndex P.M.base) :
    Module.finrank k (nonsymmetricPrincipalColonH0 (k:=k) R hQ) ≤
      Module.finrank k (LinearMap.range (nonsymmetricPrincipalComparisonH1 (k:=k) R hQ))+1 := by
  classical
  letI := nonsymmetric_colon_H1_finite (k:=k) R hQ
  letI := Fintype.ofFinite (NonsymmetricK5Corners (k:=k) R hB hQ)
  let c := nonsymmetricPrincipalComparisonH1 (k:=k) R hQ
  let v : NonsymmetricK5Corners (k:=k) R hB hQ → LinearMap.range c := fun g =>
    ⟨c (nonsymmetricK5Class R hB hQ g),⟨_,rfl⟩⟩
  have hv : LinearIndependent k v := by
    apply LinearIndependent.of_comp (LinearMap.range c).subtype
    exact nonsymmetric_shared_comparison_images_independent R hB hQ
  have hn := hv.fintype_card_le_finrank
  have hh := nonsymmetric_K5_corner_count (k:=k) R hB hQ
  rw [Nat.card_eq_fintype_card] at hh
  exact hh.trans (Nat.add_le_add_right hn 1)

#print axioms nonsymmetric_shared_comparison_images_independent
#print axioms nonsymmetric_shared_principal_comparison_rank_lower_bound
end NS25Lean.L5A2BFinalRepair
