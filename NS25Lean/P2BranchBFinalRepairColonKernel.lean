import NS25Lean.P2BranchBFinalRepairSymmetricSurgery
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open ToricPresentation ChosenBase FourGeneratedBridge L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A L5A2C4H L5A2C4C MvPolynomial
variable {k : Type*} [Field k] {Gamma : NumericalSemigroup} {P : P2Data Gamma}

abbrev symmetricBoxBound (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) :=
  ![symmetricDa A hB hQ,symmetricDb A hB hQ,symmetricDc A hB hQ] i

def symmetricColonGridDegree (A : SectorBCriticalRoleBranchA P) (p x y : ℕ) :
    (routingH P.M.base A.reindex).toAddSubmonoid :=
  ⟨p*n0 A+x*n1 A+y*n2 A, by
    change _ ∈ generatedThree (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
    rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A]
    exact (mem_generatedThree_iff _ _ _ _).mpr ⟨p,x,y,rfl⟩⟩

theorem symmetricColonPolynomialMap_Xpow (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) (d : ℕ) :
    symmetricColonPolynomialMap (k:=k) A hQ (X i ^ d) =
      Ideal.Quotient.mkₐ k (symmetricPrincipalColonIdeal k A hQ)
        (AddMonoidAlgebra.single (d • symmetricTailMonomialDegree A i) 1) := by
  rw [map_pow]
  simp only [symmetricColonPolynomialMap,aeval_X]
  rw [← map_pow,AddMonoidAlgebra.single_pow,one_pow]

theorem symmetric_colon_pure_power_mem (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) :
    AddMonoidAlgebra.single (symmetricBoxBound A hB hQ i • symmetricTailMonomialDegree A i)
      (1 : k) ∈ symmetricPrincipalColonIdeal k A hQ := by
  have S := symmetric_ci_normalized_equations A
  have D := symmetric_colon_box_ci_relations_vanish A hB hQ
  fin_cases i
  · apply (symmetric_principal_colon_grid_mem_iff A hB hQ _ S.2.1 S.1
      (height:=symmetricDa A hB hQ) (x:=0) (y:=0) (by
        simp [symmetricBoxBound,symmetricTailMonomialDegree])).mpr
    exact Or.inl le_rfl
  · by_cases hx : symmetricDb A hB hQ < ciH A
    · apply (symmetric_principal_colon_grid_mem_iff A hB hQ _ hx S.1
        (height:=0) (y:=0) (by
          simp [symmetricBoxBound,symmetricTailMonomialDegree])).mpr
      exact Or.inr (Or.inl le_rfl)
    · have he : symmetricDb A hB hQ = ciH A := by omega
      apply (symmetric_principal_colon_grid_mem_iff A hB hQ _ S.2.1 S.1
        (height:=ciK A) (x:=0) (y:=0) (by
          simp [symmetricBoxBound,symmetricTailMonomialDegree,he,symmetric_ci_b_carry A])).mpr
      exact Or.inl D.2.2.2.1
  · by_cases hy : symmetricDc A hB hQ < ciG A
    · apply (symmetric_principal_colon_grid_mem_iff A hB hQ _ S.2.1 hy
        (height:=0) (x:=0) (by
          simp [symmetricBoxBound,symmetricTailMonomialDegree])).mpr
      exact Or.inr (Or.inr le_rfl)
    · have he : symmetricDc A hB hQ = ciG A := by omega
      have hr := symmetric_ci_c_carry A 0
      simp only [zero_mul,zero_add,Nat.mod_eq_of_lt S.2.2.2.1,
        Nat.div_eq_of_lt S.2.2.2.1,add_zero] at hr
      apply (symmetric_principal_colon_grid_mem_iff A hB hQ _ S.2.2.2.1 S.1
        (height:=ciU A) (x:=ciV A) (y:=0) (by
          have hr' : ciG A * n2 A = ciU A * n0 A + ciV A * n1 A := by omega
          simpa [symmetricBoxBound,symmetricTailMonomialDegree,he] using hr')).mpr
      rcases D.2.2.2.2.2.2 with hu | hv
      · exact Or.inl hu
      · exact Or.inr (Or.inl hv)

theorem symmetric_polynomial_box_le_eval_kernel (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricPolynomialBoxIdeal k A hB hQ ≤
      RingHom.ker (symmetricColonPolynomialMap (k:=k) A hQ).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change symmetricColonPolynomialMap (k:=k) A hQ (X i ^ symmetricBoxBound A hB hQ i) = 0
  rw [symmetricColonPolynomialMap_Xpow,Ideal.Quotient.mkₐ_eq_mk,Ideal.Quotient.eq_zero_iff_mem]
  exact symmetric_colon_pure_power_mem A hB hQ i

theorem symmetricColonPolynomialMap_xyz (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (p x y : ℕ) :
    symmetricColonPolynomialMap (k:=k) A hQ (X 0 ^ p * X 1 ^ x * X 2 ^ y) =
      Ideal.Quotient.mkₐ k (symmetricPrincipalColonIdeal k A hQ)
        (AddMonoidAlgebra.single (symmetricColonGridDegree A p x y) 1) := by
  rw [map_mul,map_mul,symmetricColonPolynomialMap_Xpow,symmetricColonPolynomialMap_Xpow,
    symmetricColonPolynomialMap_Xpow,← map_mul,← map_mul,
    AddMonoidAlgebra.single_mul_single,AddMonoidAlgebra.single_mul_single]
  have he : p • symmetricTailMonomialDegree A 0 + x • symmetricTailMonomialDegree A 1 +
      y • symmetricTailMonomialDegree A 2 = symmetricColonGridDegree A p x y := by
    apply Subtype.ext
    simp [symmetricColonGridDegree,symmetricTailMonomialDegree]
  rw [he]
  simp

theorem symmetricColonPolynomialMap_surjective (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Surjective (symmetricColonPolynomialMap (k:=k) A hQ) := by
  intro z
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective z
  change ∃ p, symmetricColonPolynomialMap (k:=k) A hQ p =
    Ideal.Quotient.mkₐ k (symmetricPrincipalColonIdeal k A hQ) f
  induction f using AddMonoidAlgebra.induction_on with
  | of h =>
    obtain ⟨p,x,y,hx,hy,he⟩ := branchA_routingH_rectangle_factorization A h.property
    rw [routingA_eq_n0 A,routingB_eq_n1 A,routingC_eq_n2 A] at he
    refine ⟨X 0 ^ p * X 1 ^ x * X 2 ^ y,?_⟩
    rw [symmetricColonPolynomialMap_xyz]
    congr 2
    exact Subtype.ext he.symm
  | add f g hf hg =>
    obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
    exact ⟨p+q,by rw [map_add,hp,hq,map_add]⟩
  | smul a f hf =>
    obtain ⟨p,hp⟩ := hf
    exact ⟨a • p,by rw [map_smul,hp,map_smul]⟩

theorem symmetric_polynomial_box_isMonomial (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    L2B.IsMonomialIdeal k (symmetricPolynomialBoxIdeal k A hB hQ) := by
  refine ⟨Set.range (fun i => Finsupp.single i (symmetricBoxBound A hB hQ i)),?_⟩
  simp [symmetricPolynomialBoxIdeal,symmetricBoxBound,← Set.range_comp,X_pow_eq_monomial,Function.comp_def]

theorem symmetric_polynomial_box_monomial_mem (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (a : Fin 3 →₀ ℕ) :
    monomial a (1 : k) ∈ symmetricPolynomialBoxIdeal k A hB hQ ↔
      ∃ i, symmetricBoxBound A hB hQ i ≤ a i := by
  have hi := symmetric_polynomial_box_isMonomial (k:=k) A hB hQ
  have he : symmetricPolynomialBoxIdeal k A hB hQ = Ideal.span
      ((fun b => monomial b (1 : k)) ''
        Set.range (fun i => Finsupp.single i (symmetricBoxBound A hB hQ i))) := by
    simp [symmetricPolynomialBoxIdeal,symmetricBoxBound,← Set.range_comp,X_pow_eq_monomial,Function.comp_def]
  rw [he,L3A.monomial_mem_span_iff]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,ha⟩
    exact ⟨i,by simpa using ha i⟩
  · rintro ⟨i,hi⟩
    refine ⟨_,⟨i,rfl⟩,?_⟩
    intro j
    by_cases hj : j=i
    · subst j; simpa using hi
    · simp [hj]

def symmetricBoxExponent (p x y : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 p + Finsupp.single 1 x + Finsupp.single 2 y

def symmetricPolynomialBoxIndex (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (z : SymmetricColonBox A hB hQ) : L3A.standardExponents (symmetricPolynomialBoxIdeal k A hB hQ) :=
  ⟨symmetricBoxExponent z.1.val z.2.1.val z.2.2.val,by
    rw [L3A.standardExponents,Set.mem_ofPred_eq,symmetric_polynomial_box_monomial_mem]
    rintro ⟨i,hi⟩
    fin_cases i <;> simp [symmetricBoxBound,symmetricBoxExponent] at hi
    · exact (not_le_of_gt z.1.isLt) hi
    · exact (not_le_of_gt z.2.1.isLt) hi
    · exact (not_le_of_gt z.2.2.isLt) hi⟩

theorem symmetricPolynomialBoxIndex_bijective (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Bijective (symmetricPolynomialBoxIndex (k:=k) A hB hQ) := by
  constructor
  · intro z w he
    have hp := congrArg (fun a => a.val 0) he
    have hx := congrArg (fun a => a.val 1) he
    have hy := congrArg (fun a => a.val 2) he
    simp [symmetricPolynomialBoxIndex,symmetricBoxExponent] at hp hx hy
    exact Prod.ext (Fin.ext hp) (Prod.ext (Fin.ext hx) (Fin.ext hy))
  · intro a
    have hn : ∀ i, a.val i < symmetricBoxBound A hB hQ i := by
      intro i
      by_contra hi
      exact a.property ((symmetric_polynomial_box_monomial_mem A hB hQ a.val).mpr ⟨i,by omega⟩)
    refine ⟨(⟨a.val 0,hn 0⟩,⟨a.val 1,hn 1⟩,⟨a.val 2,hn 2⟩),?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [symmetricPolynomialBoxIndex,symmetricBoxExponent]

def symmetricPolynomialBoxBasis (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Basis (SymmetricColonBox A hB hQ) k
      (MvPolynomial (Fin 3) k ⧸ symmetricPolynomialBoxIdeal k A hB hQ) :=
  (L3A.standardBasis _ (symmetric_polynomial_box_isMonomial A hB hQ)).reindex
    (Equiv.ofBijective (symmetricPolynomialBoxIndex (k:=k) A hB hQ)
      (symmetricPolynomialBoxIndex_bijective A hB hQ)).symm

theorem symmetric_polynomial_box_finrank (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (MvPolynomial (Fin 3) k ⧸ symmetricPolynomialBoxIdeal k A hB hQ) =
      symmetricDa A hB hQ * (symmetricDb A hB hQ * symmetricDc A hB hQ) := by
  rw [Module.finrank_eq_card_basis (symmetricPolynomialBoxBasis (k:=k) A hB hQ)]
  simp [SymmetricColonBox]

def symmetricColonBoxFactor (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    (MvPolynomial (Fin 3) k ⧸ symmetricPolynomialBoxIdeal k A hB hQ) →ₐ[k]
      symmetricPrincipalColonQuotient k A hQ :=
  Ideal.Quotient.liftₐ _ (symmetricColonPolynomialMap A hQ)
    (fun _ hp => symmetric_polynomial_box_le_eval_kernel A hB hQ hp)

theorem symmetricColonBoxFactor_surjective (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Surjective (symmetricColonBoxFactor (k:=k) A hB hQ) := by
  intro y
  obtain ⟨p,hp⟩ := symmetricColonPolynomialMap_surjective (k:=k) A hQ y
  exact ⟨Ideal.Quotient.mk _ p,hp⟩

theorem symmetricColonBoxFactor_injective (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (symmetricColonBoxFactor (k:=k) A hB hQ) := by
  let := Module.Finite.of_basis (symmetricPolynomialBoxBasis (k:=k) A hB hQ)
  let := Module.Finite.of_basis (symmetricPrincipalColonBoxBasis (k:=k) A hB hQ)
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f:=(symmetricColonBoxFactor (k:=k) A hB hQ).toLinearMap)
    ((symmetric_polynomial_box_finrank (k:=k) A hB hQ).trans
      (symmetric_principal_colon_finrank (k:=k) A hB hQ).symm)).mpr
        (symmetricColonBoxFactor_surjective A hB hQ)

theorem symmetric_principal_colon_eval_kernel (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    RingHom.ker (symmetricColonPolynomialMap (k:=k) A hQ).toRingHom =
      symmetricPolynomialBoxIdeal k A hB hQ := by
  apply le_antisymm
  · intro p hp
    change symmetricColonPolynomialMap (k:=k) A hQ p = 0 at hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply symmetricColonBoxFactor_injective A hB hQ
    change symmetricColonPolynomialMap (k:=k) A hQ p =
      symmetricColonBoxFactor (k:=k) A hB hQ 0
    simpa only [map_zero] using hp
  · exact symmetric_polynomial_box_le_eval_kernel A hB hQ

def symmetricPrincipalColonAlgEquiv (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    (MvPolynomial (Fin 3) k ⧸ symmetricPolynomialBoxIdeal k A hB hQ) ≃ₐ[k]
      symmetricPrincipalColonQuotient k A hQ :=
  AlgEquiv.ofBijective (symmetricColonBoxFactor A hB hQ)
    ⟨symmetricColonBoxFactor_injective A hB hQ,symmetricColonBoxFactor_surjective A hB hQ⟩

theorem symmetricPrincipalColonAlgEquiv_mk (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (p : MvPolynomial (Fin 3) k) :
    symmetricPrincipalColonAlgEquiv A hB hQ (Ideal.Quotient.mk _ p) =
      symmetricColonPolynomialMap A hQ p := rfl

theorem symmetricPrincipalColonAlgEquiv_X_mul (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3)
    (z : MvPolynomial (Fin 3) k ⧸ symmetricPolynomialBoxIdeal k A hB hQ) :
    symmetricPrincipalColonAlgEquiv A hB hQ (Ideal.Quotient.mk _ (X i) * z) =
      Ideal.Quotient.mkₐ k (symmetricPrincipalColonIdeal k A hQ)
        (AddMonoidAlgebra.single (symmetricTailMonomialDegree A i) 1) *
          symmetricPrincipalColonAlgEquiv A hB hQ z := by
  rw [map_mul,symmetricPrincipalColonAlgEquiv_mk]
  simp [symmetricColonPolynomialMap]

theorem symmetric_polynomial_box_standard_iff (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (a : Fin 3 →₀ ℕ) :
    a ∈ L3A.standardExponents (symmetricPolynomialBoxIdeal k A hB hQ) ↔
      ∀ i, a i < symmetricBoxBound A hB hQ i := by
  simp only [L3A.standardExponents,Set.mem_ofPred_eq,symmetric_polynomial_box_monomial_mem,
    not_exists,not_le]

theorem symmetric_polynomial_box_socle_exponents (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    L3A.socleExponents (symmetricPolynomialBoxIdeal k A hB hQ) =
      {symmetricBoxExponent (symmetricDa A hB hQ-1) (symmetricDb A hB hQ-1)
        (symmetricDc A hB hQ-1)} := by
  have D := symmetric_colon_box_ci_relations_vanish A hB hQ
  have hd : ∀ i, 0 < symmetricBoxBound A hB hQ i := by
    intro i; fin_cases i
    · exact D.1
    · exact D.2.1
    · exact D.2.2.1
  ext a
  constructor
  · intro ha
    have hb := (symmetric_polynomial_box_standard_iff A hB hQ a).mp ha.1
    have ht : ∀ i, a i = symmetricBoxBound A hB hQ i-1 := by
      intro i
      obtain ⟨j,hj⟩ := (symmetric_polynomial_box_monomial_mem A hB hQ _).mp (ha.2 i)
      by_cases he : j=i
      · subst j
        simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hj
        have hi := hb i
        omega
      · have hj' : symmetricBoxBound A hB hQ j ≤ a j := by
          simpa [Finsupp.single_apply,he] using hj
        exact False.elim ((not_le_of_gt (hb j)) hj')
    apply Set.mem_singleton_iff.mpr
    ext i
    fin_cases i
    · simpa [symmetricBoxExponent,symmetricBoxBound] using ht (0 : Fin 3)
    · simpa [symmetricBoxExponent,symmetricBoxBound] using ht (1 : Fin 3)
    · simpa [symmetricBoxExponent,symmetricBoxBound] using ht (2 : Fin 3)
  · intro ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    have ht : ∀ i, symmetricBoxExponent (symmetricDa A hB hQ-1)
        (symmetricDb A hB hQ-1) (symmetricDc A hB hQ-1) i =
          symmetricBoxBound A hB hQ i-1 := by
      intro i; fin_cases i <;> simp [symmetricBoxExponent,symmetricBoxBound]
    refine ⟨(symmetric_polynomial_box_standard_iff A hB hQ _).mpr ?_,?_⟩
    · intro i; rw [ht]; exact Nat.sub_lt (hd i) (by omega)
    · intro i
      apply (symmetric_polynomial_box_monomial_mem A hB hQ _).mpr
      refine ⟨i,?_⟩
      simp only [Finsupp.add_apply,Finsupp.single_eq_same,ht]
      have hi := hd i
      omega

theorem symmetric_polynomial_box_socle_finrank (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (L3A.socle (symmetricPolynomialBoxIdeal k A hB hQ)) = 1 := by
  change L3A.quotientType _ = 1
  rw [L3A.quotientType_eq_socle_count _ (symmetric_polynomial_box_isMonomial A hB hQ),
    symmetric_polynomial_box_socle_exponents,Set.ncard_singleton]

/-- The actual P-socle: annihilation by all three actual normalized tail classes. -/
def symmetricPrincipalColonSocle (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) : Submodule k (symmetricPrincipalColonQuotient k A hQ) where
  carrier := {z | ∀ i, Ideal.Quotient.mkₐ k (symmetricPrincipalColonIdeal k A hQ)
    (AddMonoidAlgebra.single (symmetricTailMonomialDegree A i) 1) * z = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; rw [mul_add,hx i,hy i,add_zero]
  smul_mem' := by intro a x hx i; rw [mul_smul_comm,hx i,smul_zero]

theorem symmetricPrincipalColonAlgEquiv_mem_socle (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (z : MvPolynomial (Fin 3) k ⧸ symmetricPolynomialBoxIdeal k A hB hQ) :
    symmetricPrincipalColonAlgEquiv A hB hQ z ∈ symmetricPrincipalColonSocle (k:=k) A hQ ↔
      z ∈ L3A.socle (symmetricPolynomialBoxIdeal k A hB hQ) := by
  constructor
  · intro hz i
    apply (symmetricPrincipalColonAlgEquiv (k:=k) A hB hQ).injective
    rw [symmetricPrincipalColonAlgEquiv_X_mul,map_zero]
    exact hz i
  · intro hz i
    have he := congrArg (symmetricPrincipalColonAlgEquiv (k:=k) A hB hQ) (hz i)
    rwa [symmetricPrincipalColonAlgEquiv_X_mul,map_zero] at he

def symmetricPrincipalColonSocleEquiv (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    L3A.socle (symmetricPolynomialBoxIdeal k A hB hQ) ≃ₗ[k]
      symmetricPrincipalColonSocle (k:=k) A hQ :=
  LinearEquiv.ofSubmodules (symmetricPrincipalColonAlgEquiv A hB hQ).toLinearEquiv
    _ _ (by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact (symmetricPrincipalColonAlgEquiv_mem_socle A hB hQ z).mpr hz
      · intro hy
        refine ⟨(symmetricPrincipalColonAlgEquiv A hB hQ).symm y,?_,by simp⟩
        apply (symmetricPrincipalColonAlgEquiv_mem_socle A hB hQ _).mp
        simpa using hy)

theorem symmetric_principal_colon_socle_finrank (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (symmetricPrincipalColonSocle (k:=k) A hQ) = 1 :=
  (symmetricPrincipalColonSocleEquiv (k:=k) A hB hQ).finrank_eq.symm.trans
    (symmetric_polynomial_box_socle_finrank A hB hQ)

section Cochain
variable {T : Type*} [CommRing T] [Algebra k T]

/-- Degree-zero differential of the three-variable Koszul COCHAIN complex. -/
def threeKoszulD0 (g : Fin 3 → T) : T →ₗ[k] (Fin 3 → T) where
  toFun := fun z i => g i * z
  map_add' := by intro x y; ext i; exact mul_add _ _ _
  map_smul' := by intro a x; ext i; exact mul_smul_comm _ _ _

/-- Degree-one differential, with components indexed by 01,02,12. -/
def threeKoszulD1 (g : Fin 3 → T) : (Fin 3 → T) →ₗ[k] (Fin 3 → T) where
  toFun := fun z => ![g 1*z 0-g 0*z 1,g 2*z 0-g 0*z 2,g 2*z 1-g 1*z 2]
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by
    intro a x; ext i; fin_cases i <;> simp [smul_sub]

theorem threeKoszulD1_comp_D0 (g : Fin 3 → T) :
    (threeKoszulD1 (k:=k) g).comp (threeKoszulD0 g) = 0 := by
  ext z i
  fin_cases i <;> simp [threeKoszulD0,threeKoszulD1] <;> ring

theorem threeKoszul_range_D0_le_cycles (g : Fin 3 → T) :
    LinearMap.range (threeKoszulD0 (k:=k) g) ≤ LinearMap.ker (threeKoszulD1 g) := by
  rintro _ ⟨z,rfl⟩
  have he := LinearMap.congr_fun (threeKoszulD1_comp_D0 (k:=k) g) z
  exact he

/-- Cycles modulo actual coboundaries, in COHOMOLOGICAL degree one. -/
abbrev ThreeKoszulH1 (g : Fin 3 → T) :=
  LinearMap.ker (threeKoszulD1 (k:=k) g) ⧸
    (LinearMap.range (threeKoszulD0 (k:=k) g)).comap (LinearMap.ker (threeKoszulD1 g)).subtype
end Cochain

def symmetricColonGenerators (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) : symmetricPrincipalColonQuotient k A hQ :=
  Ideal.Quotient.mkₐ k (symmetricPrincipalColonIdeal k A hQ)
    (AddMonoidAlgebra.single (symmetricTailMonomialDegree A i) 1)

theorem symmetric_colon_cochain_H0 (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.ker (threeKoszulD0 (k:=k) (symmetricColonGenerators A hQ)) =
      symmetricPrincipalColonSocle (k:=k) A hQ := by
  ext z
  change (fun i => symmetricColonGenerators (k:=k) A hQ i * z) = 0 ↔ _
  simp only [funext_iff,Pi.zero_apply]
  rfl

abbrev symmetricPrincipalColonH1 (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  ThreeKoszulH1 (k:=k) (symmetricColonGenerators (k:=k) A hQ)

theorem symmetric_colon_H1_finite (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.Finite k (symmetricPrincipalColonH1 (k:=k) A hQ) := by
  let := Module.Finite.of_basis (symmetricPrincipalColonBoxBasis (k:=k) A hB hQ)
  infer_instance

section Principal
variable {R0 : Type*} [CommRing R0] [Algebra k R0]

def principalMulToQuotient (I : Ideal R0) (f : R0) : R0 →ₗ[k] (R0 ⧸ I) where
  toFun := fun p => Ideal.Quotient.mkₐ k I (f*p)
  map_add' := by intro x y; rw [mul_add,map_add]
  map_smul' := by intro a x; rw [mul_smul_comm,map_smul]; rfl

theorem principalMulToQuotient_ker (I : Ideal R0) (f : R0) :
    LinearMap.ker (principalMulToQuotient (k:=k) I f) = (I.colon {f}).restrictScalars k := by
  ext p
  change Ideal.Quotient.mkₐ k I (f*p) = 0 ↔ p ∈ I.colon {f}
  rw [Ideal.Quotient.mkₐ_eq_mk,Ideal.Quotient.eq_zero_iff_mem,Submodule.mem_colon_singleton]
  simp only [smul_eq_mul,mul_comm]

def principalColonInjection (I : Ideal R0) (f : R0) :
    (R0 ⧸ I.colon {f}) →ₗ[k] (R0 ⧸ I) :=
  ((I.colon {f}).restrictScalars k).liftQ (principalMulToQuotient I f)
    (principalMulToQuotient_ker I f).symm.le

theorem principalColonInjection_injective (I : Ideal R0) (f : R0) :
    Function.Injective (principalColonInjection (k:=k) I f) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' _ _ (principalMulToQuotient_ker I f).symm
end Principal

abbrev symmetricPrincipalPrefixQuotient (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  SemigroupAlgebra k (routingH P.M.base A.reindex).toAddSubmonoid ⧸
    carrierMonomialIdeal k (symmetricPrefixIdeal A hQ)

def symmetricPrincipalInjection (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricPrincipalColonQuotient k A hQ →ₗ[k] symmetricPrincipalPrefixQuotient (k:=k) A hQ :=
  principalColonInjection (carrierMonomialIdeal k (symmetricPrefixIdeal A hQ))
    (AddMonoidAlgebra.single (symmetricPrincipalDegree A) 1)

theorem symmetricPrincipalInjection_injective (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (symmetricPrincipalInjection (k:=k) A hQ) :=
  principalColonInjection_injective _ _

theorem symmetricPrincipalInjection_mk (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : SemigroupAlgebra k (routingH P.M.base A.reindex).toAddSubmonoid) :
    symmetricPrincipalInjection (k:=k) A hQ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mkₐ k (carrierMonomialIdeal k (symmetricPrefixIdeal A hQ))
        (AddMonoidAlgebra.single (symmetricPrincipalDegree A) 1 * p) := rfl

end NS25Lean.L5A2BFinalRepair
