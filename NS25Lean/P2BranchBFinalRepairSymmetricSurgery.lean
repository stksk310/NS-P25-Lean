import NS25Lean.P2BranchBFinalRepairSymmetricS3
import NS25Lean.TailMonomialIdeal
import NS25Lean.MonomialStaircase

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open ToricPresentation ChosenBase L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR4R2A L5A2B4AR5A L5A2C4H L5A2C4C
open FourGeneratedBridge
variable {k : Type*} [Field k] {H Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The actual relative carrier's monomial ideal in its semigroup algebra. -/
def carrierMonomialIdeal (k : Type*) [Field k] {H : NumericalSemigroup}
    (I : RelativeIdeal H) : Ideal (SemigroupAlgebra k H.toAddSubmonoid) :=
  Ideal.span (AddMonoidAlgebra.of' k H.toAddSubmonoid ''
    {h : H.toAddSubmonoid | (h.val : ℤ) ∈ I})

theorem carrierMonomialIdeal_mem_iff (I : RelativeIdeal H)
    (p : SemigroupAlgebra k H.toAddSubmonoid) :
    p ∈ carrierMonomialIdeal k I ↔ ∀ h ∈ p.coeff.support, (h.val : ℤ) ∈ I := by
  rw [carrierMonomialIdeal, AddMonoidAlgebra.mem_ideal_span_of'_image]
  constructor
  · intro hp h hh
    obtain ⟨j,hj,d,rfl⟩ := hp h hh
    have hm := I.add_mem hj d.property
    simpa only [RelativeIdeal.mem_carrier,AddSubmonoid.coe_add,Nat.cast_add,add_comm] using hm
  · intro hp h hh
    exact ⟨h,hp h hh,0,(zero_add h).symm⟩

theorem carrierMonomialIdeal_colon_mem_iff (I : RelativeIdeal H)
    (f : H.toAddSubmonoid) (p : SemigroupAlgebra k H.toAddSubmonoid) :
    p ∈ (carrierMonomialIdeal k I).colon {AddMonoidAlgebra.single f (1 : k)} ↔
      ∀ h ∈ p.coeff.support, ((f+h).val : ℤ) ∈ I := by
  classical
  rw [Submodule.mem_colon_singleton,smul_eq_mul,carrierMonomialIdeal_mem_iff]
  constructor
  · intro hp h hh
    have hn : (p * AddMonoidAlgebra.single f (1 : k)).coeff (h+f) ≠ 0 := by
      simpa only [AddMonoidAlgebra.coeff_mul_single_add,mul_one] using
        (Finsupp.mem_support_iff.mp hh)
    simpa only [add_comm] using hp (h+f) (Finsupp.mem_support_iff.mpr hn)
  · intro hp h hh
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp
      (AddMonoidAlgebra.support_coeff_mul_single_subset p (1 : k) f hh)
    simpa only [add_comm] using hp j hj

def symmetricPrincipalDegree (A : SectorBCriticalRoleBranchA P) :
    (routingH P.M.base A.reindex).toAddSubmonoid :=
  ⟨actualPrincipalIndex P.M.base * normalizedM P.M.base, by
    rw [symmetric_routingH_eq_normalizedH A]
    exact (actualPrincipalIndex_spec P.M.base).2⟩

def symmetricPrincipalColonIdeal (k : Type*) [Field k]
    (A : SectorBCriticalRoleBranchA P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Ideal (SemigroupAlgebra k (routingH P.M.base A.reindex).toAddSubmonoid) :=
  (carrierMonomialIdeal k (symmetricPrefixIdeal A hQ)).colon
    {AddMonoidAlgebra.single (symmetricPrincipalDegree A) (1 : k)}

/-- T is the actual colon quotient, not a declared box algebra. -/
abbrev symmetricPrincipalColonQuotient (k : Type*) [Field k]
    (A : SectorBCriticalRoleBranchA P) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  SemigroupAlgebra k (routingH P.M.base A.reindex).toAddSubmonoid ⧸
    symmetricPrincipalColonIdeal k A hQ

theorem symmetric_principal_colon_single_mem_iff (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (h : (routingH P.M.base A.reindex).toAddSubmonoid) :
    AddMonoidAlgebra.single h (1 : k) ∈ symmetricPrincipalColonIdeal k A hQ ↔
      (h.val : ℤ) ∈ principalColonCarrier (routingH P.M.base A.reindex)
        (normalizedM P.M.base) (actualPrincipalIndex P.M.base) := by
  rw [symmetricPrincipalColonIdeal,carrierMonomialIdeal_colon_mem_iff]
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.support_single _ one_ne_zero,
    Finset.mem_singleton,forall_eq]
  change ((actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) : ℤ) + h.val ∈
    prefixCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) ↔ _
  exact (and_iff_right (show (h.val : ℤ) ∈
    (routingH P.M.base A.reindex).asRelativeIdeal from ⟨h.val,h.property,rfl⟩)).symm

theorem symmetric_principal_colon_grid_mem_iff (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (h : (routingH P.M.base A.reindex).toAddSubmonoid)
    {height x y : ℕ} (hx : x < ciH A) (hy : y < ciG A)
    (he : h.val = height*n0 A+x*n1 A+y*n2 A) :
    AddMonoidAlgebra.single h (1 : k) ∈ symmetricPrincipalColonIdeal k A hQ ↔
      symmetricDa A hB hQ ≤ height ∨ symmetricDb A hB hQ ≤ x ∨
        symmetricDc A hB hQ ≤ y := by
  rw [symmetric_principal_colon_single_mem_iff,he]
  exact symmetric_colon_box_coordinates A hB hQ hx hy

theorem symmetric_principal_colon_eq_translated_carrier
    (A : SectorBCriticalRoleBranchA P) (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricPrincipalColonIdeal k A hQ = carrierMonomialIdeal k
      ((symmetricPrefixIdeal A hQ).translate
        (-((actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) : ℤ))) := by
  ext p
  rw [symmetricPrincipalColonIdeal,carrierMonomialIdeal_colon_mem_iff,
    carrierMonomialIdeal_mem_iff]
  simp only [RelativeIdeal.mem_translate_iff,sub_neg_eq_add,AddSubmonoid.coe_add,
    Nat.cast_add,symmetricPrincipalDegree,add_comm]

abbrev CarrierSurvivingDegrees (I : RelativeIdeal H) :=
  {h : H.toAddSubmonoid // (h.val : ℤ) ∉ I}

def carrierMonomialClass (I : RelativeIdeal H) (h : H.toAddSubmonoid) :
    SemigroupAlgebra k H.toAddSubmonoid ⧸ carrierMonomialIdeal k I :=
  Ideal.Quotient.mkₐ k (carrierMonomialIdeal k I) (AddMonoidAlgebra.single h 1)

theorem carrierMonomialClass_eq_zero_iff (I : RelativeIdeal H) (h : H.toAddSubmonoid) :
    carrierMonomialClass (k:=k) I h = 0 ↔ (h.val : ℤ) ∈ I := by
  rw [carrierMonomialClass,Ideal.Quotient.mkₐ_eq_mk,Ideal.Quotient.eq_zero_iff_mem,
    carrierMonomialIdeal_mem_iff]
  simp

theorem carrierMonomial_linearIndependent (I : RelativeIdeal H) :
    LinearIndependent k (fun h : CarrierSurvivingDegrees I =>
      carrierMonomialClass (k:=k) I h.val) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  let p : SemigroupAlgebra k H.toAddSubmonoid :=
    ∑ j ∈ s, a j • AddMonoidAlgebra.single j.val 1
  have hp : p ∈ carrierMonomialIdeal k I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ k (carrierMonomialIdeal k I) p = 0
    simpa only [p,map_sum,map_smul,carrierMonomialClass] using ha
  have hz : p.coeff i.val = 0 := by
    by_contra hn
    exact i.property ((carrierMonomialIdeal_mem_iff I p).mp hp
      i.val (Finsupp.mem_support_iff.mpr hn))
  have he : p.coeff i.val = a i := by
    simp [p,Finsupp.single_apply,Subtype.val_injective.eq_iff,hi]
  exact he.symm.trans hz

theorem carrierMonomial_span (I : RelativeIdeal H) :
    Submodule.span k (Set.range (fun h : CarrierSurvivingDegrees I =>
      carrierMonomialClass (k:=k) I h.val)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mkₐ k (carrierMonomialIdeal k I) p ∈ _
  induction p using AddMonoidAlgebra.induction_on with
  | of h =>
    by_cases hh : (h.val : ℤ) ∈ I
    · change carrierMonomialClass (k:=k) I h ∈ _
      rw [(carrierMonomialClass_eq_zero_iff I h).mpr hh]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨h,hh⟩,rfl⟩
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
  | smul a p hp => rw [map_smul]; exact Submodule.smul_mem _ a hp

def carrierMonomialBasis (I : RelativeIdeal H) :
    Module.Basis (CarrierSurvivingDegrees I) k
      (SemigroupAlgebra k H.toAddSubmonoid ⧸ carrierMonomialIdeal k I) :=
  Module.Basis.mk (carrierMonomial_linearIndependent I) (by rw [carrierMonomial_span I])

def symmetricPrincipalColonBasis (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Basis (CarrierSurvivingDegrees ((symmetricPrefixIdeal A hQ).translate
      (-((actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) : ℤ)))) k
      (symmetricPrincipalColonQuotient k A hQ) := by
  unfold symmetricPrincipalColonQuotient
  rw [symmetric_principal_colon_eq_translated_carrier (k:=k) A hQ]
  exact carrierMonomialBasis _

abbrev SymmetricColonBox (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :=
  Fin (symmetricDa A hB hQ) × Fin (symmetricDb A hB hQ) × Fin (symmetricDc A hB hQ)

abbrev SymmetricColonSurvivors (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  CarrierSurvivingDegrees ((symmetricPrefixIdeal A hQ).translate
    (-((actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) : ℤ)))

private theorem symmetric_colon_survivor_iff (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (h : (routingH P.M.base A.reindex).toAddSubmonoid)
    {height x y : ℕ} (hx : x < ciH A) (hy : y < ciG A)
    (he : h.val = height*n0 A+x*n1 A+y*n2 A) :
    (h.val : ℤ) ∉ (symmetricPrefixIdeal A hQ).translate
      (-((actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) : ℤ)) ↔
    height < symmetricDa A hB hQ ∧ x < symmetricDb A hB hQ ∧
      y < symmetricDc A hB hQ := by
  have hg := symmetric_principal_colon_grid_mem_iff (k:=ℚ) A hB hQ h hx hy he
  rw [symmetric_principal_colon_eq_translated_carrier,
    carrierMonomialIdeal_mem_iff] at hg
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.support_single _ one_ne_zero,
    Finset.mem_singleton,forall_eq] at hg
  simpa only [not_or,not_le] using not_congr hg

def symmetricColonBoxDegree (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (z : SymmetricColonBox A hB hQ) : SymmetricColonSurvivors A hQ := by
  let h : (routingH P.M.base A.reindex).toAddSubmonoid :=
    ⟨z.1.val*n0 A+z.2.1.val*n1 A+z.2.2.val*n2 A, by
      change _ ∈ generatedThree (routingA P.M.base A.reindex)
        (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
      rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A]
      exact (mem_generatedThree_iff _ _ _ _).mpr ⟨z.1.val,z.2.1.val,z.2.2.val,rfl⟩⟩
  have hb := symmetric_colon_box_ci_relations_vanish A hB hQ
  exact ⟨h,(symmetric_colon_survivor_iff A hB hQ h
    (lt_of_lt_of_le z.2.1.isLt hb.2.2.2.2.1)
    (lt_of_lt_of_le z.2.2.isLt hb.2.2.2.2.2.1) rfl).mpr
      ⟨z.1.isLt,z.2.1.isLt,z.2.2.isLt⟩⟩

theorem symmetricColonBoxDegree_injective (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (symmetricColonBoxDegree A hB hQ) := by
  intro z w he
  have he' := congrArg (fun h => h.val.val) he
  change z.1.val*n0 A+z.2.1.val*n1 A+z.2.2.val*n2 A =
    w.1.val*n0 A+w.2.1.val*n1 A+w.2.2.val*n2 A at he'
  have hb := symmetric_colon_box_ci_relations_vanish A hB hQ
  have hx : z.2.1.val < alpha A := lt_of_lt_of_le z.2.1.isLt hb.2.2.2.2.1
  have hy : z.2.2.val < d A := lt_of_lt_of_le z.2.2.isLt hb.2.2.2.2.2.1
  have hx' : w.2.1.val < alpha A := lt_of_lt_of_le w.2.1.isLt hb.2.2.2.2.1
  have hy' : w.2.2.val < d A := lt_of_lt_of_le w.2.2.isLt hb.2.2.2.2.2.1
  have hm : z.2.1.val*routingB P.M.base A.reindex+z.2.2.val*routingC P.M.base A.reindex
      ≡ w.2.1.val*routingB P.M.base A.reindex+w.2.2.val*routingC P.M.base A.reindex
      [MOD routingA P.M.base A.reindex] := by
    rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A]
    change _ % n0 A = _ % n0 A
    have hm := congrArg (fun n => n % n0 A) he'
    simpa [Nat.add_mod,Nat.mul_mod] using hm
  obtain ⟨hxx,hyy⟩ := branchA_rectangle_modEq_unique A hx hy hx' hy' hm
  have hn : 0 < n0 A := by simpa only [routingA_eq_n0 A] using routingA_pos P.M.base A.reindex
  have hhh : z.1.val = w.1.val := by rw [hxx,hyy] at he'; nlinarith
  apply Prod.ext (Fin.ext hhh)
  exact Prod.ext (Fin.ext hxx) (Fin.ext hyy)

theorem symmetricColonBoxDegree_surjective (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Surjective (symmetricColonBoxDegree A hB hQ) := by
  intro h
  obtain ⟨p,x,y,hx,hy,he⟩ := branchA_routingH_rectangle_factorization A h.val.property
  rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A] at he
  have hr := (symmetric_colon_survivor_iff A hB hQ h.val hx hy he).mp h.property
  refine ⟨(⟨p,hr.1⟩,⟨x,hr.2.1⟩,⟨y,hr.2.2⟩),?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he.symm

/-- Exact finite box of the actual colon quotient's surviving monomial degrees. -/
def symmetric_colon_box_degree_equiv (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    SymmetricColonBox A hB hQ ≃ SymmetricColonSurvivors A hQ :=
  Equiv.ofBijective (symmetricColonBoxDegree A hB hQ)
    ⟨symmetricColonBoxDegree_injective A hB hQ,symmetricColonBoxDegree_surjective A hB hQ⟩

def symmetricPrincipalColonBoxBasis (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Basis (SymmetricColonBox A hB hQ) k (symmetricPrincipalColonQuotient k A hQ) :=
  (symmetricPrincipalColonBasis A hQ).reindex (symmetric_colon_box_degree_equiv A hB hQ).symm

theorem symmetric_principal_colon_finrank (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (symmetricPrincipalColonQuotient k A hQ) =
      symmetricDa A hB hQ * (symmetricDb A hB hQ * symmetricDc A hB hQ) := by
  rw [Module.finrank_eq_card_basis (symmetricPrincipalColonBoxBasis (k:=k) A hB hQ)]
  simp [SymmetricColonBox]

/-- Actual normalized tail generator, with membership proved in routingH. -/
def symmetricTailMonomialDegree (A : SectorBCriticalRoleBranchA P) (i : Fin 3) :
    (routingH P.M.base A.reindex).toAddSubmonoid :=
  ⟨![n0 A,n1 A,n2 A] i, by
    change _ ∈ generatedThree (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
    rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A]
    fin_cases i
    · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨1,0,0,by simp⟩
    · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨0,1,0,by simp⟩
    · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨0,0,1,by simp⟩⟩

/-- The polynomial action on the actual principal colon quotient. -/
def symmetricColonPolynomialMap (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    MvPolynomial (Fin 3) k →ₐ[k] symmetricPrincipalColonQuotient k A hQ :=
  MvPolynomial.aeval (fun i => Ideal.Quotient.mkₐ k (symmetricPrincipalColonIdeal k A hQ)
    (AddMonoidAlgebra.single (symmetricTailMonomialDegree A i) 1))

/-- The source's three pure power relations; no identification is assumed. -/
def symmetricPolynomialBoxIdeal (k : Type*) [Field k]
    (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span (Set.range (fun i : Fin 3 =>
    MvPolynomial.X i ^ (![symmetricDa A hB hQ,symmetricDb A hB hQ,symmetricDc A hB hQ] i)))

end NS25Lean.L5A2BFinalRepair
