import NS25Lean.P2BranchBFinalRepairColonKernel

set_option linter.style.header false
set_option maxHeartbeats 300000
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open ToricPresentation ChosenBase FourGeneratedBridge L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A L5A2C4H L5A2C4C MvPolynomial
variable {k : Type*} [Field k] {Gamma : NumericalSemigroup} {P : P2Data Gamma}

namespace BoxCohomology
attribute [local instance] Classical.propDecidable
variable (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
  (hQ : 1 < actualPrincipalIndex P.M.base)

abbrev Index := L3A.standardExponents (symmetricPolynomialBoxIdeal k A hB hQ)
abbrev Algebra := symmetricPrincipalColonQuotient k A hQ

def basis : Module.Basis (Index (k:=k) A hB hQ) k (Algebra (k:=k) A hQ) :=
  (L3A.standardBasis _ (symmetric_polynomial_box_isMonomial A hB hQ)).map
    (symmetricPrincipalColonAlgEquiv A hB hQ).toLinearEquiv

theorem basis_apply (a : Index (k:=k) A hB hQ) :
    basis A hB hQ a =
      symmetricPrincipalColonAlgEquiv A hB hQ
        (L3A.monomialClass (symmetricPolynomialBoxIdeal k A hB hQ) a.val) := by
  simp [basis,L3A.standardBasis]

theorem bound_pos (i : Fin 3) : 0 < symmetricBoxBound A hB hQ i := by
  have h := symmetric_colon_box_ci_relations_vanish A hB hQ
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

theorem index_bound (a : Index (k:=k) A hB hQ) (i : Fin 3) :
    a.val i < symmetricBoxBound A hB hQ i :=
  (symmetric_polynomial_box_standard_iff A hB hQ a.val).mp a.property i

def pred (a : Index (k:=k) A hB hQ) (i : Fin 3) : Index (k:=k) A hB hQ :=
  ⟨a.val - Finsupp.single i 1, by
    apply (symmetric_polynomial_box_standard_iff A hB hQ _).mpr
    intro j
    simpa only [Finsupp.tsub_apply] using
      lt_of_le_of_lt (Nat.sub_le (a.val j) ((Finsupp.single i 1) j)) (index_bound A hB hQ a j)⟩

def succ (a : Index (k:=k) A hB hQ) (i : Fin 3)
    (hi : a.val i + 1 < symmetricBoxBound A hB hQ i) : Index (k:=k) A hB hQ :=
  ⟨a.val + Finsupp.single i 1, by
    apply (symmetric_polynomial_box_standard_iff A hB hQ _).mpr
    intro j
    by_cases hj : j=i
    · subst j; simpa using hi
    · simpa [Finsupp.single_apply,hj,Ne.symm hj] using index_bound A hB hQ a j⟩

def mul (i : Fin 3) : Algebra (k:=k) A hQ →ₗ[k] Algebra (k:=k) A hQ :=
  LinearMap.mulLeft k (symmetricColonGenerators A hQ i)

theorem mul_basis_lt (i : Fin 3) (a : Index (k:=k) A hB hQ)
    (hi : a.val i + 1 < symmetricBoxBound A hB hQ i) :
    mul (k:=k) A hQ i (basis A hB hQ a) = basis A hB hQ (succ A hB hQ a i hi) := by
  simp only [mul,LinearMap.mulLeft_apply,basis_apply]
  change Ideal.Quotient.mkₐ k (symmetricPrincipalColonIdeal k A hQ)
    (AddMonoidAlgebra.single (symmetricTailMonomialDegree A i) 1) * _ = _
  rw [← symmetricPrincipalColonAlgEquiv_X_mul,L3A.X_mul_monomialClass]
  rfl

theorem mul_basis_ge (i : Fin 3) (a : Index (k:=k) A hB hQ)
    (hi : symmetricBoxBound A hB hQ i ≤ a.val i + 1) :
    mul (k:=k) A hQ i (basis A hB hQ a) = 0 := by
  simp only [mul,LinearMap.mulLeft_apply,basis_apply]
  change Ideal.Quotient.mkₐ k (symmetricPrincipalColonIdeal k A hQ)
    (AddMonoidAlgebra.single (symmetricTailMonomialDegree A i) 1) * _ = _
  rw [← symmetricPrincipalColonAlgEquiv_X_mul,L3A.X_mul_monomialClass]
  have hz : L3A.monomialClass (symmetricPolynomialBoxIdeal k A hB hQ)
      (a.val + Finsupp.single i 1) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (symmetric_polynomial_box_monomial_mem A hB hQ _).mpr
    exact ⟨i,by simpa using hi⟩
  rw [hz,map_zero]

def faceExponent (i : Fin 3) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun j => if j=i then 0 else symmetricBoxBound A hB hQ j - 1)

@[simp] theorem faceExponent_apply (i j : Fin 3) :
    faceExponent A hB hQ i j =
      if j=i then 0 else symmetricBoxBound A hB hQ j - 1 := rfl

def faceIndex (i : Fin 3) : Index (k:=k) A hB hQ :=
  ⟨faceExponent A hB hQ i,by
    apply (symmetric_polynomial_box_standard_iff A hB hQ _).mpr
    intro j
    by_cases hj : j=i
    · simp [hj,bound_pos A hB hQ]
    · simp only [faceExponent_apply,if_neg hj]
      have hp := bound_pos A hB hQ j
      omega⟩

theorem mul_face (i j : Fin 3) (hj : j ≠ i) :
    mul (k:=k) A hQ j (basis A hB hQ (faceIndex A hB hQ i)) = 0 := by
  apply mul_basis_ge
  change symmetricBoxBound A hB hQ j ≤ faceExponent A hB hQ i j + 1
  simp only [faceExponent_apply,if_neg hj]
  omega

def faceVector (i : Fin 3) : Fin 3 → Algebra (k:=k) A hQ :=
  fun j => if j=i then basis A hB hQ (faceIndex A hB hQ i) else 0

theorem faceVector_cycle (i : Fin 3) :
    threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ)
      (faceVector (k:=k) A hB hQ i) = 0 := by
  ext j
  fin_cases i <;> fin_cases j <;> simp [threeKoszulD1,faceVector]
  all_goals exact mul_face A hB hQ _ _ (by decide)

def faceCycle (i : Fin 3) :
    LinearMap.ker (threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ)) :=
  ⟨faceVector A hB hQ i,faceVector_cycle A hB hQ i⟩

def faceClass (i : Fin 3) : symmetricPrincipalColonH1 (k:=k) A hQ :=
  Submodule.Quotient.mk (faceCycle A hB hQ i)

def coefficient (a : Index (k:=k) A hB hQ) : Algebra (k:=k) A hQ →ₗ[k] k :=
  (Finsupp.lapply a).comp (basis A hB hQ).repr.toLinearMap

@[simp] theorem coefficient_basis (a b : Index (k:=k) A hB hQ) :
    coefficient A hB hQ a (basis A hB hQ b) = if b=a then 1 else 0 := by
  classical
  simp [coefficient,Finsupp.single_apply]

theorem coefficient_mul_face (i : Fin 3) :
    (coefficient A hB hQ (faceIndex A hB hQ i)).comp (mul (k:=k) A hQ i) = 0 := by
  classical
  apply (basis A hB hQ).ext
  intro a
  simp only [LinearMap.comp_apply,LinearMap.zero_apply]
  by_cases hi : a.val i + 1 < symmetricBoxBound A hB hQ i
  · rw [mul_basis_lt A hB hQ i a hi,coefficient_basis]
    have hn : succ A hB hQ a i hi ≠ faceIndex A hB hQ i := by
      intro he
      have hh := congrArg (fun z : Index (k:=k) A hB hQ => z.val i) he
      simp [succ,faceIndex] at hh
    simp [hn]
  · rw [mul_basis_ge A hB hQ i a (by omega),map_zero]

def faceCoefficients :
    LinearMap.ker (threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ)) →ₗ[k]
      (Fin 3 → k) where
  toFun := fun z i => coefficient A hB hQ (faceIndex A hB hQ i) (z.val i)
  map_add' := by intro x y; ext i; exact (coefficient A hB hQ _).map_add _ _
  map_smul' := by intro a x; ext i; exact (coefficient A hB hQ _).map_smul a _

theorem faceCoefficients_coboundary
    (z : LinearMap.ker (threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ)))
    (hz : z ∈ (LinearMap.range (threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ))).comap
      (LinearMap.ker (threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ))).subtype) :
    faceCoefficients A hB hQ z = 0 := by
  obtain ⟨w,hw⟩ := hz
  have hw' : threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ) w = z.val := hw
  ext i
  change coefficient A hB hQ (faceIndex A hB hQ i) (z.val i) = 0
  rw [← hw']
  exact LinearMap.congr_fun (coefficient_mul_face (k:=k) A hB hQ i) w

def cohomologyFaces : symmetricPrincipalColonH1 (k:=k) A hQ →ₗ[k] (Fin 3 → k) :=
  ((LinearMap.range (threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ))).comap
    (LinearMap.ker (threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ))).subtype).liftQ
      (faceCoefficients A hB hQ) (fun z hz => faceCoefficients_coboundary A hB hQ z hz)

theorem cohomologyFaces_mk
    (z : LinearMap.ker (threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ))) :
    cohomologyFaces A hB hQ (Submodule.Quotient.mk z) = faceCoefficients A hB hQ z := rfl

theorem cohomologyFaces_faceClass (i : Fin 3) :
    cohomologyFaces A hB hQ (faceClass (k:=k) A hB hQ i) = Pi.single i (1:k) := by
  classical
  rw [faceClass,cohomologyFaces_mk]
  ext j
  change coefficient (k:=k) A hB hQ (faceIndex (k:=k) A hB hQ j)
    (faceVector (k:=k) A hB hQ i j) = (Pi.single i (1:k) : Fin 3 → k) j
  by_cases hj : j=i
  · subst j; simp [faceVector]
  · simp [faceVector,hj,Pi.single_apply,Ne.symm hj]

theorem faceClasses_linearIndependent :
    LinearIndependent k (faceClass (k:=k) A hB hQ) := by
  classical
  apply LinearIndependent.of_comp (cohomologyFaces A hB hQ)
  have he : (cohomologyFaces A hB hQ) ∘ faceClass (k:=k) A hB hQ =
      fun i => Pi.basisFun k (Fin 3) i := by
    funext i
    exact (cohomologyFaces_faceClass A hB hQ i).trans (Pi.basisFun_apply k (Fin 3) i).symm
  rw [he]
  exact (Pi.basisFun k (Fin 3)).linearIndependent

def divide (i : Fin 3) : Algebra (k:=k) A hQ →ₗ[k] Algebra (k:=k) A hQ :=
  (basis A hB hQ).constr k
    (fun a => if 0 < a.val i then basis A hB hQ (pred A hB hQ a i) else 0)

def projection (p : Index (k:=k) A hB hQ → Prop) :
    Algebra (k:=k) A hQ →ₗ[k] Algebra (k:=k) A hQ := by
  classical
  exact (basis A hB hQ).constr k (fun a => if p a then basis A hB hQ a else 0)

def bottom (i : Fin 3) : Algebra (k:=k) A hQ →ₗ[k] Algebra (k:=k) A hQ :=
  projection A hB hQ (fun a => a.val i = 0)

def top (i : Fin 3) : Algebra (k:=k) A hQ →ₗ[k] Algebra (k:=k) A hQ :=
  projection A hB hQ (fun a => a.val i + 1 = symmetricBoxBound A hB hQ i)

@[simp] theorem divide_basis (i : Fin 3) (a : Index (k:=k) A hB hQ) :
    divide A hB hQ i (basis A hB hQ a) =
      if 0 < a.val i then basis A hB hQ (pred A hB hQ a i) else 0 := by
  simp [divide]

@[simp] theorem projection_basis (p : Index (k:=k) A hB hQ → Prop)
    (a : Index (k:=k) A hB hQ) :
    projection A hB hQ p (basis A hB hQ a) = if p a then basis A hB hQ a else 0 := by
  classical
  simp [projection]

theorem pred_succ (i : Fin 3) (a : Index (k:=k) A hB hQ)
    (hi : a.val i + 1 < symmetricBoxBound A hB hQ i) :
    pred A hB hQ (succ A hB hQ a i hi) i = a := by
  apply Subtype.ext
  ext j
  by_cases hj : j=i
  · subst j; simp [pred,succ,Finsupp.tsub_apply]
  · simp [pred,succ,Finsupp.tsub_apply,Finsupp.single_apply,hj,Ne.symm hj]

theorem succ_pred (i : Fin 3) (a : Index (k:=k) A hB hQ) (ha : 0 < a.val i)
    (hi : (pred A hB hQ a i).val i + 1 < symmetricBoxBound A hB hQ i) :
    succ A hB hQ (pred A hB hQ a i) i hi = a := by
  apply Subtype.ext
  ext j
  by_cases hj : j=i
  · subst j
    simp only [pred,succ,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_eq_same]
    omega
  · simp [pred,succ,Finsupp.tsub_apply,Finsupp.single_apply,hj,Ne.symm hj]

theorem mul_divide (i : Fin 3) :
    (mul (k:=k) A hQ i).comp (divide A hB hQ i) =
      LinearMap.id - bottom A hB hQ i := by
  classical
  apply (basis A hB hQ).ext
  intro a
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,divide_basis]
  by_cases ha : 0 < a.val i
  · rw [if_pos ha]
    have hi : (pred A hB hQ a i).val i + 1 < symmetricBoxBound A hB hQ i := by
      have hb := index_bound A hB hQ a i
      simp only [pred,Finsupp.tsub_apply,Finsupp.single_eq_same]
      omega
    rw [mul_basis_lt A hB hQ i _ hi,succ_pred A hB hQ i a ha hi]
    simp [bottom,ha.ne']
  · rw [if_neg ha,map_zero]
    have hz : a.val i = 0 := by omega
    simp [bottom,hz]

theorem divide_mul (i : Fin 3) :
    (divide A hB hQ i).comp (mul (k:=k) A hQ i) =
      LinearMap.id - top A hB hQ i := by
  classical
  apply (basis A hB hQ).ext
  intro a
  simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply]
  by_cases hi : a.val i + 1 < symmetricBoxBound A hB hQ i
  · rw [mul_basis_lt A hB hQ i a hi,divide_basis]
    have hp : 0 < (succ A hB hQ a i hi).val i := by
      simp [succ]
    rw [if_pos hp,pred_succ A hB hQ i a hi]
    simp [top,hi.ne]
  · rw [mul_basis_ge A hB hQ i a (by omega),map_zero]
    have he : a.val i + 1 = symmetricBoxBound A hB hQ i := by
      have hb := index_bound A hB hQ a i
      omega
    simp [top,he]

theorem projection_coefficient (p : Index (k:=k) A hB hQ → Prop)
    (a : Index (k:=k) A hB hQ) (z : Algebra (k:=k) A hQ) :
    coefficient A hB hQ a (projection A hB hQ p z) =
      if p a then coefficient A hB hQ a z else 0 := by
  classical
  suffices he : (coefficient A hB hQ a).comp (projection A hB hQ p) =
      if p a then coefficient A hB hQ a else 0 by
    by_cases hp : p a <;> simpa [hp] using LinearMap.congr_fun he z
  apply (basis A hB hQ).ext
  intro b
  by_cases hb : p b <;> by_cases ha : p a <;> by_cases he : b=a <;>
    simp_all [LinearMap.comp_apply]

theorem projection_idempotent (p : Index (k:=k) A hB hQ → Prop) :
    (projection A hB hQ p).comp (projection A hB hQ p) = projection A hB hQ p := by
  classical
  apply (basis A hB hQ).ext
  intro a
  by_cases hp : p a <;> simp [LinearMap.comp_apply,hp]

theorem bottom_mul (i : Fin 3) :
    (bottom A hB hQ i).comp (mul (k:=k) A hQ i) = 0 := by
  classical
  apply (basis A hB hQ).ext
  intro a
  simp only [LinearMap.comp_apply,LinearMap.zero_apply]
  by_cases hi : a.val i + 1 < symmetricBoxBound A hB hQ i
  · rw [mul_basis_lt A hB hQ i a hi]
    simp [bottom,succ]
  · rw [mul_basis_ge A hB hQ i a (by omega),map_zero]

theorem bottom_comm_mul (i j : Fin 3) (hij : i ≠ j) :
    (bottom A hB hQ i).comp (mul (k:=k) A hQ j) =
      (mul (k:=k) A hQ j).comp (bottom A hB hQ i) := by
  classical
  apply (basis A hB hQ).ext
  intro a
  simp only [LinearMap.comp_apply]
  by_cases hj : a.val j + 1 < symmetricBoxBound A hB hQ j
  · rw [mul_basis_lt A hB hQ j a hj]
    by_cases hi : a.val i = 0
    · simp [bottom,succ,Finsupp.single_apply,hij,Ne.symm hij,hi,
        mul_basis_lt A hB hQ j a hj]
    · simp [bottom,succ,Finsupp.single_apply,hij,Ne.symm hij,hi]
  · rw [mul_basis_ge A hB hQ j a (by omega),map_zero]
    by_cases hi : a.val i = 0
    · simp [bottom,hi,mul_basis_ge A hB hQ j a (by omega)]
    · simp [bottom,hi]

theorem pred_succ_ne (i j : Fin 3) (hij : i ≠ j)
    (a : Index (k:=k) A hB hQ) (hj : a.val j + 1 < symmetricBoxBound A hB hQ j)
    (hj' : (pred A hB hQ a i).val j + 1 < symmetricBoxBound A hB hQ j) :
    pred A hB hQ (succ A hB hQ a j hj) i =
      succ A hB hQ (pred A hB hQ a i) j hj' := by
  apply Subtype.ext
  ext l
  by_cases hli : l=i
  · subst l; simp [pred,succ,hij,Ne.symm hij]
  · by_cases hlj : l=j
    · subst l; simp [pred,succ,hij,Ne.symm hij]
    · simp [pred,succ,Finsupp.single_apply,hli,Ne.symm hli,hlj,Ne.symm hlj]

theorem divide_comm_mul (i j : Fin 3) (hij : i ≠ j) :
    (divide A hB hQ i).comp (mul (k:=k) A hQ j) =
      (mul (k:=k) A hQ j).comp (divide A hB hQ i) := by
  classical
  apply (basis A hB hQ).ext
  intro a
  simp only [LinearMap.comp_apply]
  have hpj : (pred A hB hQ a i).val j = a.val j := by
    simp [pred,Finsupp.single_apply,hij,Ne.symm hij]
  by_cases hj : a.val j + 1 < symmetricBoxBound A hB hQ j
  · rw [mul_basis_lt A hB hQ j a hj,divide_basis,divide_basis]
    have hsi : (succ A hB hQ a j hj).val i = a.val i := by
      simp [succ,Finsupp.single_apply,hij,Ne.symm hij]
    rw [hsi]
    by_cases hi : 0 < a.val i
    · rw [if_pos hi,if_pos hi,mul_basis_lt A hB hQ j _ (by rwa [hpj])]
      congr 1
      exact pred_succ_ne A hB hQ i j hij a hj _
    · rw [if_neg hi,if_neg hi,map_zero]
  · rw [mul_basis_ge A hB hQ j a (by omega),map_zero,divide_basis]
    by_cases hi : 0 < a.val i
    · rw [if_pos hi,mul_basis_ge A hB hQ j _ (by rw [hpj]; omega)]
    · rw [if_neg hi,map_zero]

theorem face_rigidity (i : Fin 3) (z : Algebra (k:=k) A hQ)
    (hz : bottom A hB hQ i z = z)
    (hm : ∀ j, j ≠ i → mul (k:=k) A hQ j z = 0) :
    z = coefficient A hB hQ (faceIndex A hB hQ i) z •
      basis A hB hQ (faceIndex A hB hQ i) := by
  classical
  apply (basis A hB hQ).repr.injective
  ext a
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul]
  change coefficient A hB hQ a z =
    coefficient A hB hQ (faceIndex A hB hQ i) z *
      coefficient A hB hQ a (basis A hB hQ (faceIndex A hB hQ i))
  rw [coefficient_basis]
  by_cases ha : a=faceIndex A hB hQ i
  · subst a; simp
  · rw [if_neg (Ne.symm ha),mul_zero]
    by_contra hc
    have hzi : a.val i = 0 := by
      have he := congrArg (coefficient A hB hQ a) hz
      change coefficient A hB hQ a (projection A hB hQ (fun b => b.val i=0) z) = _ at he
      rw [projection_coefficient] at he
      by_contra hi
      simp [hi] at he
      exact hc he.symm
    have ht : ∀ j, j ≠ i → a.val j + 1 = symmetricBoxBound A hB hQ j := by
      intro j hj
      have he := LinearMap.congr_fun (divide_mul (k:=k) A hB hQ j) z
      simp only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,hm j hj,map_zero] at he
      have htz : top A hB hQ j z = z := (sub_eq_zero.mp he.symm).symm
      have hh := congrArg (coefficient A hB hQ a) htz
      change coefficient A hB hQ a
        (projection A hB hQ (fun b => b.val j+1=symmetricBoxBound A hB hQ j) z) = _ at hh
      rw [projection_coefficient] at hh
      by_contra hn
      simp [hn] at hh
      exact hc hh.symm
    apply ha
    apply Subtype.ext
    ext j
    change a.val j = faceExponent A hB hQ i j
    rw [faceExponent_apply]
    by_cases hj : j=i
    · subst j; simp [hzi]
    · rw [if_neg hj]
      have hh := ht j hj
      omega

theorem cycle_cross (z : Fin 3 → Algebra (k:=k) A hQ)
    (hz : threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ) z = 0)
    (i j : Fin 3) :
    mul (k:=k) A hQ i (z j) = mul (k:=k) A hQ j (z i) := by
  have h01 := congrFun hz 0
  have h02 := congrFun hz 1
  have h12 := congrFun hz 2
  change mul (k:=k) A hQ 1 (z 0) - mul (k:=k) A hQ 0 (z 1) = 0 at h01
  change mul (k:=k) A hQ 2 (z 0) - mul (k:=k) A hQ 0 (z 2) = 0 at h02
  change mul (k:=k) A hQ 2 (z 1) - mul (k:=k) A hQ 1 (z 2) = 0 at h12
  have he01 := sub_eq_zero.mp h01
  have he02 := sub_eq_zero.mp h02
  have he12 := sub_eq_zero.mp h12
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact he01 | exact he01.symm | exact he02 |
      exact he02.symm | exact he12 | exact he12.symm

def reduce (i : Fin 3) (z : Fin 3 → Algebra (k:=k) A hQ) :
    Fin 3 → Algebra (k:=k) A hQ :=
  z - threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ)
    (divide A hB hQ i (z i))

theorem reduce_cycle (i : Fin 3) (z : Fin 3 → Algebra (k:=k) A hQ)
    (hz : threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ) z = 0) :
    threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ) (reduce A hB hQ i z) = 0 := by
  rw [reduce,map_sub,hz]
  have he := LinearMap.congr_fun
    (threeKoszulD1_comp_D0 (k:=k) (symmetricColonGenerators (k:=k) A hQ))
      (divide A hB hQ i (z i))
  change (threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ))
    (threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ)
      (divide A hB hQ i (z i))) = 0 at he
  rw [he,sub_self]

theorem reduce_self (i : Fin 3) (z : Fin 3 → Algebra (k:=k) A hQ) :
    reduce A hB hQ i z i = bottom A hB hQ i (z i) := by
  have he := LinearMap.congr_fun (mul_divide (k:=k) A hB hQ i) (z i)
  change mul (k:=k) A hQ i (divide A hB hQ i (z i)) =
    z i - bottom A hB hQ i (z i) at he
  change z i - mul (k:=k) A hQ i (divide A hB hQ i (z i)) = _
  rw [he]
  abel

theorem bottom_cycle_kills (i : Fin 3) (z : Fin 3 → Algebra (k:=k) A hQ)
    (hz : threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ) z = 0)
    (hb : bottom A hB hQ i (z i) = z i) (j : Fin 3) (hj : j ≠ i) :
    mul (k:=k) A hQ j (z i) = 0 ∧ mul (k:=k) A hQ i (z j) = 0 := by
  have hc := cycle_cross (k:=k) A hQ z hz i j
  have he := LinearMap.congr_fun (bottom_comm_mul (k:=k) A hB hQ i j (Ne.symm hj)) (z i)
  change bottom A hB hQ i (mul (k:=k) A hQ j (z i)) =
    mul (k:=k) A hQ j (bottom A hB hQ i (z i)) at he
  rw [hb] at he
  have hm : mul (k:=k) A hQ j (z i) = 0 := by
    rw [← he,← hc]
    exact LinearMap.congr_fun (bottom_mul (k:=k) A hB hQ i) (z j)
  exact ⟨hm,hc.trans hm⟩

theorem reduce_bottom (i : Fin 3) (z : Fin 3 → Algebra (k:=k) A hQ) :
    bottom A hB hQ i (reduce A hB hQ i z i) = reduce A hB hQ i z i := by
  rw [reduce_self]
  exact LinearMap.congr_fun
    (projection_idempotent (k:=k) A hB hQ (fun a => a.val i=0)) (z i)

theorem reduce_kills (i : Fin 3) (z : Fin 3 → Algebra (k:=k) A hQ)
    (hz : threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ) z = 0)
    (j : Fin 3) (hj : j ≠ i) :
    mul (k:=k) A hQ j (reduce A hB hQ i z i) = 0 ∧
      mul (k:=k) A hQ i (reduce A hB hQ i z j) = 0 :=
  bottom_cycle_kills A hB hQ i _ (reduce_cycle A hB hQ i z hz)
    (reduce_bottom A hB hQ i z) j hj

theorem reduce_fixed (i j : Fin 3) (hij : i ≠ j) (z : Fin 3 → Algebra (k:=k) A hQ)
    (hz : threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ) z = 0)
    (hm : mul (k:=k) A hQ i (z j) = 0) :
    reduce A hB hQ i z j = z j := by
  have hc := cycle_cross (k:=k) A hQ z hz i j
  have he := LinearMap.congr_fun (divide_comm_mul (k:=k) A hB hQ i j hij) (z i)
  change divide A hB hQ i (mul (k:=k) A hQ j (z i)) =
    mul (k:=k) A hQ j (divide A hB hQ i (z i)) at he
  rw [← hc,hm,map_zero] at he
  change z j - mul (k:=k) A hQ j (divide A hB hQ i (z i)) = z j
  rw [← he,sub_zero]

def faceSum (c : Fin 3 → k) : Fin 3 → Algebra (k:=k) A hQ :=
  ∑ i, c i • faceVector A hB hQ i

theorem faceSum_apply (c : Fin 3 → k) (i : Fin 3) :
    faceSum A hB hQ c i = c i • basis A hB hQ (faceIndex A hB hQ i) := by
  classical
  simp [faceSum,faceVector,Finset.sum_apply,Pi.smul_apply]

theorem cycle_decomposition (z : Fin 3 → Algebra (k:=k) A hQ)
    (hz : threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ) z = 0) :
    ∃ (w : Algebra (k:=k) A hQ) (c : Fin 3 → k),
      z = threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ) w + faceSum A hB hQ c := by
  let z0 := reduce A hB hQ 0 z
  have hz0 := reduce_cycle A hB hQ 0 z hz
  let z1 := reduce A hB hQ 1 z0
  have hz1 := reduce_cycle A hB hQ 1 z0 hz0
  let z2 := reduce A hB hQ 2 z1
  have h10 : z1 0 = z0 0 :=
    reduce_fixed A hB hQ 1 0 (by decide) z0 hz0 (reduce_kills A hB hQ 0 z hz 1 (by decide)).1
  have h21 : z2 1 = z1 1 :=
    reduce_fixed A hB hQ 2 1 (by decide) z1 hz1 (reduce_kills A hB hQ 1 z0 hz0 2 (by decide)).1
  have h20 : z2 0 = z1 0 := by
    apply reduce_fixed A hB hQ 2 0 (by decide) z1 hz1
    rw [h10]
    exact (reduce_kills A hB hQ 0 z hz 2 (by decide)).1
  have h200 : z2 0 = z0 0 := h20.trans h10
  have hface : ∀ i, z2 i =
      coefficient A hB hQ (faceIndex A hB hQ i) (z2 i) • basis A hB hQ (faceIndex A hB hQ i) := by
    intro i
    fin_cases i
    · apply face_rigidity A hB hQ 0
      · change bottom A hB hQ 0 (z2 0) = z2 0
        rw [h200]
        exact reduce_bottom A hB hQ 0 z
      · intro j hj
        change mul (k:=k) A hQ j (z2 0) = 0
        rw [h200]
        exact (reduce_kills A hB hQ 0 z hz j hj).1
    · apply face_rigidity A hB hQ 1
      · change bottom A hB hQ 1 (z2 1) = z2 1
        rw [h21]
        exact reduce_bottom A hB hQ 1 z0
      · intro j hj
        change mul (k:=k) A hQ j (z2 1) = 0
        rw [h21]
        exact (reduce_kills A hB hQ 1 z0 hz0 j hj).1
    · apply face_rigidity A hB hQ 2
      · exact reduce_bottom A hB hQ 2 z1
      · intro j hj
        exact (reduce_kills A hB hQ 2 z1 hz1 j hj).1
  let w := divide A hB hQ 0 (z 0) + divide A hB hQ 1 (z0 1) + divide A hB hQ 2 (z1 2)
  have hred : z2 = z - threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ) w := by
    ext i
    change z i - mul (k:=k) A hQ i (divide A hB hQ 0 (z 0)) -
      mul (k:=k) A hQ i (divide A hB hQ 1 (z0 1)) -
      mul (k:=k) A hQ i (divide A hB hQ 2 (z1 2)) = z i -
      mul (k:=k) A hQ i (divide A hB hQ 0 (z 0) +
        divide A hB hQ 1 (z0 1) + divide A hB hQ 2 (z1 2))
    rw [map_add,map_add]
    abel
  refine ⟨w,fun i => coefficient A hB hQ (faceIndex A hB hQ i) (z2 i),?_⟩
  ext i
  rw [Pi.add_apply,faceSum_apply]
  rw [← hface i]
  have hh := congrFun hred i
  change z2 i = z i - mul (k:=k) A hQ i w at hh
  change z i = mul (k:=k) A hQ i w + z2 i
  rw [hh]
  abel

theorem faceClasses_span :
    Submodule.span k (Set.range (faceClass (k:=k) A hB hQ)) = ⊤ := by
  classical
  let p := (LinearMap.range (threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ))).comap
    (LinearMap.ker (threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ))).subtype
  apply top_unique
  intro x _
  obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective p x
  obtain ⟨w,c,he⟩ := cycle_decomposition A hB hQ z.val z.property
  let bdy : LinearMap.ker (threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ)) :=
    ⟨threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ) w,
      threeKoszul_range_D0_le_cycles (k:=k) (symmetricColonGenerators (k:=k) A hQ) ⟨w,rfl⟩⟩
  have hcyc : z = bdy + ∑ i, c i • faceCycle (k:=k) A hB hQ i := by
    apply Subtype.ext
    simpa [bdy,faceCycle,faceSum] using he
  have hbdy : p.mkQ bdy = 0 := by
    apply (Submodule.Quotient.mk_eq_zero p).mpr
    exact ⟨w,rfl⟩
  change p.mkQ z ∈ _
  rw [hcyc,map_add,hbdy,zero_add,map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i,rfl⟩

def cohomologyBasis : Module.Basis (Fin 3) k (symmetricPrincipalColonH1 (k:=k) A hQ) :=
  Module.Basis.mk (faceClasses_linearIndependent A hB hQ) (by rw [faceClasses_span A hB hQ])

end BoxCohomology

theorem symmetric_colon_face_cycles (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) :
    threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ)
      (BoxCohomology.faceVector (k:=k) A hB hQ i) = 0 :=
  BoxCohomology.faceVector_cycle A hB hQ i

theorem symmetric_colon_face_classes_linearIndependent (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearIndependent k (BoxCohomology.faceClass (k:=k) A hB hQ) :=
  BoxCohomology.faceClasses_linearIndependent A hB hQ

theorem symmetric_principal_colon_koszulH1_finrank_ge_three (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    3 ≤ Module.finrank k (symmetricPrincipalColonH1 (k:=k) A hQ) := by
  letI := symmetric_colon_H1_finite (k:=k) A hB hQ
  simpa using (symmetric_colon_face_classes_linearIndependent (k:=k) A hB hQ).fintype_card_le_finrank

theorem symmetric_colon_face_classes_span (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Submodule.span k (Set.range (BoxCohomology.faceClass (k:=k) A hB hQ)) = ⊤ :=
  BoxCohomology.faceClasses_span A hB hQ

theorem symmetric_principal_colon_koszulH1_finrank (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (symmetricPrincipalColonH1 (k:=k) A hQ) = 3 := by
  rw [Module.finrank_eq_card_basis (BoxCohomology.cohomologyBasis (k:=k) A hB hQ)]
  simp

section PrincipalProjection
variable {R0 : Type*} [CommRing R0] [Algebra k R0]

def principalFinalProjection (I : Ideal R0) (f : R0) :
    (R0 ⧸ I) →ₗ[k] (R0 ⧸ (I ⊔ Ideal.span {f})) :=
  (Ideal.Quotient.factorₐ k (show I ≤ I ⊔ Ideal.span {f} from le_sup_left)).toLinearMap

theorem principalFinalProjection_mk (I : Ideal R0) (f p : R0) :
    principalFinalProjection (k:=k) I f (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (I ⊔ Ideal.span {f}) p := rfl

theorem principalFinalProjection_surjective (I : Ideal R0) (f : R0) :
    Function.Surjective (principalFinalProjection (k:=k) I f) :=
  Ideal.Quotient.factor_surjective le_sup_left

theorem principalFinalProjection_exact (I : Ideal R0) (f : R0) :
    LinearMap.range (principalColonInjection (k:=k) I f) =
      LinearMap.ker (principalFinalProjection (k:=k) I f) := by
  ext x
  refine Quotient.inductionOn' x ?_
  intro p
  constructor
  · rintro ⟨z,hz⟩
    refine Quotient.inductionOn' z ?_ hz
    intro q hq
    rw [← hq]
    change Ideal.Quotient.mk (I ⊔ Ideal.span {f}) (f*q) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show Ideal.span {f} ≤ I ⊔ Ideal.span {f} from le_sup_right)
      (Ideal.mem_span_singleton.mpr ⟨q,rfl⟩)
  · intro hp
    have hp' : p ∈ I ⊔ Ideal.span {f} := Ideal.Quotient.eq_zero_iff_mem.mp hp
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hp'
    obtain ⟨q,hq⟩ := Ideal.mem_span_singleton.mp hb
    refine ⟨Ideal.Quotient.mk (I.colon {f}) q,?_⟩
    change Ideal.Quotient.mk I (f*q) = Ideal.Quotient.mk I p
    rw [← hq,← he,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr ha,zero_add]
end PrincipalProjection

def symmetricFinalIdeal (A : SectorBCriticalRoleBranchA P) :
    RelativeIdeal (routingH P.M.base A.reindex) where
  carrier := actualFinalCarrier P.M.base
  nonempty := by rw [← normalizedTailIdeal_eq_actualFinalCarrier]; exact (normalizedI _).nonempty
  bddBelow := by rw [← normalizedTailIdeal_eq_actualFinalCarrier]; exact (normalizedI _).bddBelow
  add_mem := by
    intro z h hz hh
    rw [← normalizedTailIdeal_eq_actualFinalCarrier] at hz ⊢
    rw [symmetric_routingH_eq_normalizedH A] at hh
    exact (normalizedI P.M.base).add_mem hz hh

theorem symmetricFinalIdeal_mem (A : SectorBCriticalRoleBranchA P) (z : ℤ) :
    z ∈ symmetricFinalIdeal A ↔ z ∈ normalizedI P.M.base := by
  change z ∈ actualFinalCarrier P.M.base ↔ _
  rw [← normalizedTailIdeal_eq_actualFinalCarrier]
  rfl

theorem symmetricFinalIdeal_mem_split (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : ℤ) :
    z ∈ symmetricFinalIdeal A ↔ z ∈ symmetricPrefixIdeal A hQ ∨
      z - (symmetricPrincipalDegree A).val ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
  change z ∈ finalCarrier _ _ _ ↔ _
  rw [mem_finalCarrier_iff]
  change z ∈ prefixCarrier _ _ _ ∨ z - _ ∈ _ ↔
    z ∈ prefixCarrier (routingH P.M.base A.reindex) _ _ ∨
      z - (actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) ∈
        (routingH P.M.base A.reindex).asRelativeIdeal
  rw [symmetric_routingH_eq_normalizedH A,Nat.cast_mul]

theorem symmetricFinalIdeal_monomial_eq (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    carrierMonomialIdeal k (symmetricFinalIdeal A) =
      carrierMonomialIdeal k (symmetricPrefixIdeal A hQ) ⊔
        Ideal.span {AddMonoidAlgebra.single (symmetricPrincipalDegree A) (1 : k)} := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨h,hh,rfl⟩
    rcases (symmetricFinalIdeal_mem_split A hQ _).mp hh with hp | ht
    · exact (show carrierMonomialIdeal k (symmetricPrefixIdeal A hQ) ≤ _ from le_sup_left)
        (Ideal.subset_span ⟨h,hp,rfl⟩)
    · obtain ⟨d,hd,he⟩ := ht
      let dH : (routingH P.M.base A.reindex).toAddSubmonoid := ⟨d,hd⟩
      have eh : h = symmetricPrincipalDegree A + dH := by
        apply Subtype.ext
        change h.val = _ + d
        omega
      apply (show Ideal.span {AddMonoidAlgebra.single (symmetricPrincipalDegree A) (1 : k)} ≤ _ from le_sup_right)
      apply Ideal.mem_span_singleton.mpr
      refine ⟨AddMonoidAlgebra.single dH 1,?_⟩
      rw [AddMonoidAlgebra.of'_apply,AddMonoidAlgebra.single_mul_single,one_mul,← eh]
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨h,hh,rfl⟩
      exact Ideal.subset_span ⟨h,(symmetricFinalIdeal_mem_split A hQ _).mpr (Or.inl hh),rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      apply Ideal.subset_span
      refine ⟨symmetricPrincipalDegree A,?_,?_⟩
      · apply (symmetricFinalIdeal_mem_split A hQ _).mpr
        right
        exact ⟨0,(routingH _ _).zero_mem,by simp⟩
      · exact AddMonoidAlgebra.of'_apply _

abbrev symmetricPrincipalFinalQuotient (A : SectorBCriticalRoleBranchA P) :=
  SemigroupAlgebra k (routingH P.M.base A.reindex).toAddSubmonoid ⧸
    carrierMonomialIdeal k (symmetricFinalIdeal A)

def symmetricPrincipalSurgeryEquiv (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  Ideal.quotientEquivAlgOfEq k (symmetricFinalIdeal_monomial_eq (k:=k) A hQ).symm

def symmetricPrincipalFinalProjection (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricPrincipalPrefixQuotient (k:=k) A hQ →ₗ[k] symmetricPrincipalFinalQuotient (k:=k) A :=
  (symmetricPrincipalSurgeryEquiv (k:=k) A hQ).toLinearEquiv.toLinearMap.comp
    (principalFinalProjection _ (AddMonoidAlgebra.single (symmetricPrincipalDegree A) 1))

theorem symmetricPrincipalFinalProjection_surjective (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Surjective (symmetricPrincipalFinalProjection (k:=k) A hQ) :=
  (symmetricPrincipalSurgeryEquiv A hQ).surjective.comp
    (principalFinalProjection_surjective _ _)

theorem symmetricPrincipalFinalProjection_exact (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.range (symmetricPrincipalInjection (k:=k) A hQ) =
      LinearMap.ker (symmetricPrincipalFinalProjection (k:=k) A hQ) := by
  change LinearMap.range (principalColonInjection (k:=k)
    (carrierMonomialIdeal k (symmetricPrefixIdeal A hQ))
    (AddMonoidAlgebra.single (symmetricPrincipalDegree A) 1)) = _
  rw [principalFinalProjection_exact]
  ext z
  change _ = 0 ↔ (symmetricPrincipalSurgeryEquiv (k:=k) A hQ) _ = 0
  exact (map_eq_zero_iff (symmetricPrincipalSurgeryEquiv (k:=k) A hQ)
    (symmetricPrincipalSurgeryEquiv (k:=k) A hQ).injective).symm

def symmetricPrefixGenerators (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3) :
    symmetricPrincipalPrefixQuotient (k:=k) A hQ :=
  Ideal.Quotient.mkₐ k (carrierMonomialIdeal k (symmetricPrefixIdeal A hQ))
    (AddMonoidAlgebra.single (symmetricTailMonomialDegree A i) 1)

def symmetricFinalGenerators (A : SectorBCriticalRoleBranchA P) (i : Fin 3) :
    symmetricPrincipalFinalQuotient (k:=k) A :=
  Ideal.Quotient.mkₐ k (carrierMonomialIdeal k (symmetricFinalIdeal A))
    (AddMonoidAlgebra.single (symmetricTailMonomialDegree A i) 1)

theorem symmetricPrincipalInjection_generator (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3)
    (z : symmetricPrincipalColonQuotient k A hQ) :
    symmetricPrincipalInjection (k:=k) A hQ (symmetricColonGenerators (k:=k) A hQ i*z) =
      symmetricPrefixGenerators (k:=k) A hQ i * symmetricPrincipalInjection (k:=k) A hQ z := by
  refine Quotient.inductionOn' z ?_
  intro p
  change Ideal.Quotient.mk _ (_*(_*p)) = Ideal.Quotient.mk _ (_*(_*p))
  congr 1
  ring

theorem symmetricPrincipalFinalProjection_mk (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : SemigroupAlgebra k (routingH P.M.base A.reindex).toAddSubmonoid) :
    symmetricPrincipalFinalProjection (k:=k) A hQ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ p := by
  simp [symmetricPrincipalFinalProjection,symmetricPrincipalSurgeryEquiv,
    principalFinalProjection,Ideal.quotientEquivAlgOfEq]

theorem symmetricPrincipalFinalProjection_generator (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3)
    (z : symmetricPrincipalPrefixQuotient (k:=k) A hQ) :
    symmetricPrincipalFinalProjection (k:=k) A hQ (symmetricPrefixGenerators (k:=k) A hQ i*z) =
      symmetricFinalGenerators (k:=k) A i * symmetricPrincipalFinalProjection (k:=k) A hQ z := by
  refine Quotient.inductionOn' z ?_
  intro p
  change symmetricPrincipalFinalProjection (k:=k) A hQ (Ideal.Quotient.mk _ (_*p)) =
    Ideal.Quotient.mk _ _ * symmetricPrincipalFinalProjection (k:=k) A hQ (Ideal.Quotient.mk _ p)
  rw [symmetricPrincipalFinalProjection_mk,symmetricPrincipalFinalProjection_mk,map_mul]

abbrev symmetricPrefixH0 (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  LinearMap.ker (threeKoszulD0 (k:=k) (symmetricPrefixGenerators (k:=k) A hQ))

abbrev symmetricFinalH0 (A : SectorBCriticalRoleBranchA P) :=
  LinearMap.ker (threeKoszulD0 (k:=k) (symmetricFinalGenerators (k:=k) A))

def symmetricPrincipalLinearLift (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricPrincipalFinalQuotient (k:=k) A →ₗ[k] symmetricPrincipalPrefixQuotient (k:=k) A hQ :=
  ((symmetricPrincipalFinalProjection (k:=k) A hQ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (symmetricPrincipalFinalProjection_surjective A hQ))).choose

theorem symmetricPrincipalLinearLift_spec (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : symmetricPrincipalFinalQuotient (k:=k) A) :
    symmetricPrincipalFinalProjection (k:=k) A hQ (symmetricPrincipalLinearLift (k:=k) A hQ z) = z :=
  LinearMap.congr_fun
    ((symmetricPrincipalFinalProjection (k:=k) A hQ).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (symmetricPrincipalFinalProjection_surjective A hQ))).choose_spec z

theorem symmetricPrincipal_retract_on_kernel (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (z : symmetricPrincipalPrefixQuotient (k:=k) A hQ)
    (hz : symmetricPrincipalFinalProjection (k:=k) A hQ z = 0) :
    symmetricPrincipalInjection (k:=k) A hQ
      ((symmetricPrincipalInjection (k:=k) A hQ).leftInverse z) = z := by
  have hr : z ∈ LinearMap.range (symmetricPrincipalInjection (k:=k) A hQ) := by
    rw [symmetricPrincipalFinalProjection_exact]
    exact hz
  obtain ⟨w,rfl⟩ := hr
  rw [LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (symmetricPrincipalInjection_injective A hQ))]

def symmetricPrincipalConnectingPre (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricFinalH0 (k:=k) A →ₗ[k] (Fin 3 → symmetricPrincipalColonQuotient k A hQ) where
  toFun := fun z i => (symmetricPrincipalInjection (k:=k) A hQ).leftInverse
    (symmetricPrefixGenerators (k:=k) A hQ i * symmetricPrincipalLinearLift (k:=k) A hQ z.val)
  map_add' := by intro z w; ext i; simp [map_add,mul_add]
  map_smul' := by intro a z; ext i; simp [map_smul,mul_smul_comm]

theorem symmetricPrincipalConnectingPre_image (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : symmetricFinalH0 (k:=k) A) (i : Fin 3) :
    symmetricPrincipalInjection (k:=k) A hQ (symmetricPrincipalConnectingPre (k:=k) A hQ z i) =
      symmetricPrefixGenerators (k:=k) A hQ i * symmetricPrincipalLinearLift (k:=k) A hQ z.val := by
  apply symmetricPrincipal_retract_on_kernel
  rw [symmetricPrincipalFinalProjection_generator,symmetricPrincipalLinearLift_spec]
  exact congrFun z.property i

theorem symmetricPrincipalConnectingPre_cycle (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : symmetricFinalH0 (k:=k) A) :
    threeKoszulD1 (k:=k) (symmetricColonGenerators (k:=k) A hQ)
      (symmetricPrincipalConnectingPre (k:=k) A hQ z) = 0 := by
  have hc : ∀ i j : Fin 3,
      symmetricColonGenerators (k:=k) A hQ j * symmetricPrincipalConnectingPre (k:=k) A hQ z i -
      symmetricColonGenerators (k:=k) A hQ i * symmetricPrincipalConnectingPre (k:=k) A hQ z j = 0 := by
    intro i j
    apply symmetricPrincipalInjection_injective (k:=k) A hQ
    rw [map_sub,map_zero,symmetricPrincipalInjection_generator,symmetricPrincipalInjection_generator,
      symmetricPrincipalConnectingPre_image,symmetricPrincipalConnectingPre_image]
    ring
  ext i
  fin_cases i <;> simpa [threeKoszulD1] using hc _ _

def symmetricPrincipalConnecting (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricFinalH0 (k:=k) A →ₗ[k] symmetricPrincipalColonH1 (k:=k) A hQ :=
  Submodule.mkQ _ ∘ₗ (symmetricPrincipalConnectingPre (k:=k) A hQ).codRestrict _
    (symmetricPrincipalConnectingPre_cycle (k:=k) A hQ)

def symmetricPrincipalH0Projection (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricPrefixH0 (k:=k) A hQ →ₗ[k] symmetricFinalH0 (k:=k) A :=
  ((symmetricPrincipalFinalProjection (k:=k) A hQ).comp
    (symmetricPrefixH0 (k:=k) A hQ).subtype).codRestrict _ (by
      intro z
      ext i
      change symmetricFinalGenerators (k:=k) A i * symmetricPrincipalFinalProjection (k:=k) A hQ z.val = 0
      rw [← symmetricPrincipalFinalProjection_generator]
      have hz := congrFun z.property i
      change symmetricPrefixGenerators (k:=k) A hQ i*z.val=0 at hz
      rw [hz,map_zero])

theorem symmetricPrincipalConnecting_eq_zero (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : symmetricFinalH0 (k:=k) A) :
    symmetricPrincipalConnecting (k:=k) A hQ z = 0 ↔
      ∃ w : symmetricPrincipalColonQuotient k A hQ,
        threeKoszulD0 (k:=k) (symmetricColonGenerators (k:=k) A hQ) w =
          symmetricPrincipalConnectingPre (k:=k) A hQ z := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem symmetricPrincipalConnecting_exact (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.range (symmetricPrincipalH0Projection (k:=k) A hQ) =
      LinearMap.ker (symmetricPrincipalConnecting (k:=k) A hQ) := by
  ext z
  constructor
  · rintro ⟨b,rfl⟩
    rw [LinearMap.mem_ker,symmetricPrincipalConnecting_eq_zero]
    let l := symmetricPrincipalLinearLift (k:=k) A hQ
      (symmetricPrincipalH0Projection (k:=k) A hQ b).val
    let w := (symmetricPrincipalInjection (k:=k) A hQ).leftInverse (l-b.val)
    have hw : symmetricPrincipalInjection (k:=k) A hQ w = l-b.val := by
      apply symmetricPrincipal_retract_on_kernel
      rw [map_sub,symmetricPrincipalLinearLift_spec]
      exact sub_self _
    refine ⟨w,?_⟩
    ext i
    apply symmetricPrincipalInjection_injective (k:=k) A hQ
    change symmetricPrincipalInjection (k:=k) A hQ (symmetricColonGenerators (k:=k) A hQ i*w) = _
    rw [symmetricPrincipalInjection_generator,hw,symmetricPrincipalConnectingPre_image,mul_sub]
    have hb := congrFun b.property i
    change symmetricPrefixGenerators (k:=k) A hQ i*b.val=0 at hb
    rw [hb,sub_zero]
  · intro hz
    obtain ⟨w,hw⟩ := (symmetricPrincipalConnecting_eq_zero A hQ z).mp hz
    let b := symmetricPrincipalLinearLift (k:=k) A hQ z.val - symmetricPrincipalInjection (k:=k) A hQ w
    have hb : b ∈ symmetricPrefixH0 (k:=k) A hQ := by
      ext i
      change symmetricPrefixGenerators (k:=k) A hQ i*b=0
      dsimp [b]
      rw [mul_sub,← symmetricPrincipalInjection_generator]
      have hwi := congrFun hw i
      change symmetricColonGenerators (k:=k) A hQ i*w = _ at hwi
      rw [hwi,symmetricPrincipalConnectingPre_image,sub_self]
    refine ⟨⟨b,hb⟩,?_⟩
    apply Subtype.ext
    change symmetricPrincipalFinalProjection (k:=k) A hQ b = z.val
    dsimp [b]
    rw [map_sub,symmetricPrincipalLinearLift_spec]
    have hi : symmetricPrincipalFinalProjection (k:=k) A hQ (symmetricPrincipalInjection (k:=k) A hQ w)=0 := by
      have hr : symmetricPrincipalInjection (k:=k) A hQ w ∈ LinearMap.range (symmetricPrincipalInjection (k:=k) A hQ) := ⟨w,rfl⟩
      rw [symmetricPrincipalFinalProjection_exact] at hr
      exact hr
    rw [hi,sub_zero]

def symmetricPrincipalH0Injection (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    symmetricPrincipalColonSocle (k:=k) A hQ →ₗ[k] symmetricPrefixH0 (k:=k) A hQ :=
  ((symmetricPrincipalInjection (k:=k) A hQ).comp
    (symmetricPrincipalColonSocle (k:=k) A hQ).subtype).codRestrict _ (by
      intro z
      ext i
      change symmetricPrefixGenerators (k:=k) A hQ i * symmetricPrincipalInjection (k:=k) A hQ z.val=0
      rw [← symmetricPrincipalInjection_generator]
      have hz := z.property i
      change symmetricColonGenerators (k:=k) A hQ i*z.val=0 at hz
      rw [hz,map_zero])

theorem symmetricPrincipalH0Injection_injective (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (symmetricPrincipalH0Injection (k:=k) A hQ) := by
  intro z w he
  apply Subtype.ext
  exact symmetricPrincipalInjection_injective (k:=k) A hQ (congrArg Subtype.val he)

theorem symmetricPrincipalH0Projection_exact (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.range (symmetricPrincipalH0Injection (k:=k) A hQ) =
      LinearMap.ker (symmetricPrincipalH0Projection (k:=k) A hQ) := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    have hr : symmetricPrincipalInjection (k:=k) A hQ w.val ∈
        LinearMap.range (symmetricPrincipalInjection (k:=k) A hQ) := ⟨w.val,rfl⟩
    rw [symmetricPrincipalFinalProjection_exact] at hr
    exact hr
  · intro hz
    have hz' : z.val ∈ LinearMap.range (symmetricPrincipalInjection (k:=k) A hQ) := by
      rw [symmetricPrincipalFinalProjection_exact]
      exact congrArg Subtype.val hz
    obtain ⟨w,hw⟩ := hz'
    have hs : w ∈ symmetricPrincipalColonSocle (k:=k) A hQ := by
      intro i
      change symmetricColonGenerators (k:=k) A hQ i*w=0
      apply symmetricPrincipalInjection_injective (k:=k) A hQ
      rw [symmetricPrincipalInjection_generator,hw,map_zero]
      exact congrFun z.property i
    exact ⟨⟨w,hs⟩,Subtype.ext hw⟩

theorem carrierSurvivingDegrees_finite {H : NumericalSemigroup} (I : RelativeIdeal H) :
    Finite (CarrierSurvivingDegrees I) := by
  obtain ⟨N,hN⟩ := I.exists_tail
  let f : CarrierSurvivingDegrees I → Fin (N.toNat+1) := fun h => ⟨h.val.val,by
    have hn : (h.val.val : ℤ) < N := lt_of_not_ge (fun hg => h.property (hN _ hg))
    omega⟩
  apply Finite.of_injective f
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Fin.val he

theorem carrierMonomialQuotient_finite {H : NumericalSemigroup} (I : RelativeIdeal H) :
    Module.Finite k (SemigroupAlgebra k H.toAddSubmonoid ⧸ carrierMonomialIdeal k I) := by
  letI := carrierSurvivingDegrees_finite I
  letI := Fintype.ofFinite (CarrierSurvivingDegrees I)
  exact Module.Finite.of_basis (carrierMonomialBasis (k:=k) I)

theorem symmetric_principal_algebraic_socle_gain_le_two
    (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (symmetricFinalH0 (k:=k) A) ≤
      Module.finrank k (symmetricPrefixH0 (k:=k) A hQ)+2 := by
  letI := carrierMonomialQuotient_finite (k:=k) (symmetricFinalIdeal A)
  letI := carrierMonomialQuotient_finite (k:=k) (symmetricPrefixIdeal A hQ)
  letI := symmetric_colon_H1_finite (k:=k) A hB hQ
  have hker : Module.finrank k (LinearMap.ker (symmetricPrincipalH0Projection (k:=k) A hQ))=1 := by
    rw [← symmetricPrincipalH0Projection_exact,
      LinearMap.finrank_range_of_inj (symmetricPrincipalH0Injection_injective A hQ)]
    exact symmetric_principal_colon_socle_finrank (k:=k) A hB hQ
  have h1 := LinearMap.finrank_range_add_finrank_ker (symmetricPrincipalH0Projection (k:=k) A hQ)
  have h2 := LinearMap.finrank_range_add_finrank_ker (symmetricPrincipalConnecting (k:=k) A hQ)
  have hr : Module.finrank k (LinearMap.range (symmetricPrincipalConnecting (k:=k) A hQ)) ≤ 3 := by
    have hh := Submodule.finrank_le (LinearMap.range (symmetricPrincipalConnecting (k:=k) A hQ))
    rwa [symmetric_principal_colon_koszulH1_finrank (k:=k) A hB hQ] at hh
  rw [hker] at h1
  rw [← symmetricPrincipalConnecting_exact] at h2
  omega

section CarrierSocle
variable {H : NumericalSemigroup}

def carrierGenerators (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid) (i : Fin 3) :
    SemigroupAlgebra k H.toAddSubmonoid ⧸ carrierMonomialIdeal k I :=
  carrierMonomialClass (k:=k) I (g i)

abbrev CarrierH0 (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid) :=
  LinearMap.ker (threeKoszulD0 (k:=k) (carrierGenerators (k:=k) I g))

abbrev CarrierSocleDegrees (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid) :=
  {h : H.toAddSubmonoid // (h.val : ℤ) ∉ I ∧ ∀ i, ((h+g i).val : ℤ) ∈ I}

theorem carrierGenerators_mul_class (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid)
    (i : Fin 3) (h : H.toAddSubmonoid) :
    carrierGenerators (k:=k) I g i * carrierMonomialClass (k:=k) I h =
      carrierMonomialClass (k:=k) I (h+g i) := by
  simp only [carrierGenerators,carrierMonomialClass,← map_mul,AddMonoidAlgebra.single_mul_single,one_mul,add_comm]

theorem carrierSocleClass_mem (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid)
    (h : CarrierSocleDegrees I g) :
    carrierMonomialClass (k:=k) I h.val ∈ CarrierH0 (k:=k) I g := by
  ext i
  change carrierGenerators (k:=k) I g i * carrierMonomialClass (k:=k) I h.val = 0
  rw [carrierGenerators_mul_class,carrierMonomialClass_eq_zero_iff]
  exact h.property.2 i

theorem carrierSocle_support (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid)
    (p : SemigroupAlgebra k H.toAddSubmonoid)
    (hp : Ideal.Quotient.mkₐ k (carrierMonomialIdeal k I) p ∈ CarrierH0 (k:=k) I g)
    (h : H.toAddSubmonoid) (hh : (h.val : ℤ) ∉ I) (hc : p.coeff h ≠ 0) :
    ∀ i, ((h+g i).val : ℤ) ∈ I := by
  intro i
  have hz := congrFun hp i
  have hm : AddMonoidAlgebra.single (g i) (1 : k)*p ∈ carrierMonomialIdeal k I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ k (carrierMonomialIdeal k I) _ = 0
    rw [map_mul]
    exact hz
  apply (carrierMonomialIdeal_mem_iff I _).mp hm (h+g i)
  apply Finsupp.mem_support_iff.mpr
  simpa only [add_comm h,AddMonoidAlgebra.coeff_single_mul_add,one_mul] using hc

theorem carrierSocle_span (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid) :
    CarrierH0 (k:=k) I g = Submodule.span k (Set.range (fun h : CarrierSocleDegrees I g =>
      carrierMonomialClass (k:=k) I h.val)) := by
  classical
  apply le_antisymm
  · intro z hz
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mkₐ k (carrierMonomialIdeal k I) p ∈ _
    rw [← AddMonoidAlgebra.sum_coeff_single p,Finsupp.sum,map_sum]
    apply Submodule.sum_mem
    intro h hh
    have he : AddMonoidAlgebra.single h (p.coeff h) = p.coeff h • AddMonoidAlgebra.single h (1 : k) := by simp
    rw [he,map_smul]
    apply Submodule.smul_mem
    by_cases hm : (h.val : ℤ) ∈ I
    · change carrierMonomialClass (k:=k) I h ∈ _
      rw [(carrierMonomialClass_eq_zero_iff I h).mpr hm]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨h,hm,carrierSocle_support I g p hz h hm
        (Finsupp.mem_support_iff.mp hh)⟩,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨h,rfl⟩
    exact carrierSocleClass_mem I g h

theorem carrierSocle_linearIndependent (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid) :
    LinearIndependent k (fun h : CarrierSocleDegrees I g => carrierMonomialClass (k:=k) I h.val) := by
  let f : CarrierSocleDegrees I g → CarrierSurvivingDegrees I := fun h => ⟨h.val,h.property.1⟩
  apply (carrierMonomial_linearIndependent (k:=k) I).comp f
  intro x y he
  exact Subtype.ext (congrArg (fun h : CarrierSurvivingDegrees I => h.val) he)

def carrierSocleBasis (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid) :
    Module.Basis (CarrierSocleDegrees I g) k (CarrierH0 (k:=k) I g) :=
  (Module.Basis.span (carrierSocle_linearIndependent (k:=k) I g)).map
    (LinearEquiv.ofEq _ _ (carrierSocle_span (k:=k) I g).symm)

theorem carrierSocle_finrank (I : RelativeIdeal H) (g : Fin 3 → H.toAddSubmonoid) :
    Module.finrank k (CarrierH0 (k:=k) I g) = Nat.card (CarrierSocleDegrees I g) :=
  Module.finrank_eq_nat_card_basis (carrierSocleBasis (k:=k) I g)

end CarrierSocle

def carrierSocleIntegralMap {H : NumericalSemigroup} (I : RelativeIdeal H)
    (g : Fin 3 → H.toAddSubmonoid)
    (hgen : H.IsGeneratedByThree (g 0).val (g 1).val (g 2).val)
    (hpos : ∀ i, (g i).val ≠ 0) :
    CarrierSocleDegrees I g → {w // IsIntegralSocle I w} := fun h =>
  ⟨h.val.val,⟨h.val.val,h.val.property,rfl⟩,h.property.1,
    ((I.isPseudoFrobenius_iff_add_generators hgen (hpos 0) (hpos 1) (hpos 2) _).mpr
      ⟨h.property.1,by simpa using h.property.2 0,by simpa using h.property.2 1,
        by simpa using h.property.2 2⟩).2⟩

theorem carrierSocleIntegralMap_bijective {H : NumericalSemigroup} (I : RelativeIdeal H)
    (g : Fin 3 → H.toAddSubmonoid)
    (hgen : H.IsGeneratedByThree (g 0).val (g 1).val (g 2).val)
    (hpos : ∀ i, (g i).val ≠ 0) :
    Function.Bijective (carrierSocleIntegralMap I g hgen hpos) := by
  constructor
  · intro x y he
    apply Subtype.ext
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    change (x.val.val : ℤ) = (y.val.val : ℤ) at he'
    exact_mod_cast he'
  · intro w
    obtain ⟨n,hn,he⟩ := w.property.1
    have hp := (I.isPseudoFrobenius_iff_add_generators hgen (hpos 0) (hpos 1) (hpos 2) _).mp
      ⟨w.property.2.1,w.property.2.2⟩
    rw [he] at hp
    refine ⟨⟨⟨n,hn⟩,?_,?_⟩,?_⟩
    · exact hp.1
    · intro i
      fin_cases i
      · change ((n+(g 0).val : ℕ) : ℤ) ∈ I
        simpa only [Nat.cast_add] using hp.2.1
      · change ((n+(g 1).val : ℕ) : ℤ) ∈ I
        simpa only [Nat.cast_add] using hp.2.2.1
      · change ((n+(g 2).val : ℕ) : ℤ) ∈ I
        simpa only [Nat.cast_add] using hp.2.2.2
    · apply Subtype.ext
      exact he.symm

theorem carrierH0_finrank_integralSocle_card {H : NumericalSemigroup} (I : RelativeIdeal H)
    (g : Fin 3 → H.toAddSubmonoid)
    (hgen : H.IsGeneratedByThree (g 0).val (g 1).val (g 2).val)
    (hpos : ∀ i, (g i).val ≠ 0) :
    Module.finrank k (CarrierH0 (k:=k) I g) = Nat.card {w // IsIntegralSocle I w} :=
  (carrierSocle_finrank (k:=k) I g).trans (Nat.card_congr
    (Equiv.ofBijective _ (carrierSocleIntegralMap_bijective I g hgen hpos)))

theorem symmetricTailMonomialDegree_generated (A : SectorBCriticalRoleBranchA P) :
    (routingH P.M.base A.reindex).IsGeneratedByThree
      (symmetricTailMonomialDegree A 0).val (symmetricTailMonomialDegree A 1).val
      (symmetricTailMonomialDegree A 2).val := by
  change (routingH P.M.base A.reindex).IsGeneratedByThree (n0 A) (n1 A) (n2 A)
  rw [← routingA_eq_n0 A,← routingB_eq_n1 A,← routingC_eq_n2 A]
  exact (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base A.reindex)).1

theorem symmetricTailMonomialDegree_ne_zero (A : SectorBCriticalRoleBranchA P)
    (i : Fin 3) : (symmetricTailMonomialDegree A i).val ≠ 0 := by
  fin_cases i
  · exact (branchA_symmetricTailData A).n0_pos.ne'
  · exact (branchA_symmetricTailData A).n1_pos.ne'
  · exact (branchA_symmetricTailData A).n2_pos.ne'

theorem symmetricPrefixH0_finrank_actualSinkCount (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    Module.finrank k (symmetricPrefixH0 (k:=k) A hQ) =
      L5A2B3.actualSinkCount (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
        (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  change Module.finrank k (CarrierH0 (k:=k) (symmetricPrefixIdeal A hQ) (symmetricTailMonomialDegree A)) = _
  rw [carrierH0_finrank_integralSocle_card _ _ (symmetricTailMonomialDegree_generated A)
    (symmetricTailMonomialDegree_ne_zero A)]
  apply Eq.symm
  apply L5A2B3.actualSinkCount_eq_integralSocle_card
  · exact (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base A.reindex)).1
  · exact (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base A.reindex)).1).mpr
        (AddSubmonoid.subset_closure (by simp))
  · rw [routingB_eq_n1 A]
    exact (branchA_symmetricTailData A).n1_pos.ne'
  · rw [routingC_eq_n2 A]
    exact (branchA_symmetricTailData A).n2_pos.ne'

theorem symmetricFinalH0_finrank_actualType (A : SectorBCriticalRoleBranchA P) :
    Module.finrank k (symmetricFinalH0 (k:=k) A) = Gamma.asRelativeIdeal.idealType := by
  change Module.finrank k (CarrierH0 (k:=k) (symmetricFinalIdeal A) (symmetricTailMonomialDegree A)) = _
  rw [carrierH0_finrank_integralSocle_card _ _ (symmetricTailMonomialDegree_generated A)
    (symmetricTailMonomialDegree_ne_zero A)]
  have hi : ∀ z, IsIntegralSocle (symmetricFinalIdeal A) z ↔ IsIntegralSocle (normalizedI P.M.base) z := by
    intro z
    simp only [IsIntegralSocle,symmetricFinalIdeal_mem,NumericalSemigroup.mem_asRelativeIdeal_iff,
      symmetric_routingH_eq_normalizedH A]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hi)]
  rw [← normalizedTail_socle_card Gamma P.M.base.q.val (P.M.base.tailDegrees 0).val
    (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val (L5A2B2.chosenBase_minimalFour P.M.base)]
  exact (fourGenerated_idealType_eq_natCard_socle Gamma P.M.base.q.val
    (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val
    (L5A2B2.chosenBase_minimalFour P.M.base).m_pos (L5A2B2.chosenBase_minimalFour P.M.base).generated).symm

theorem symmetric_principal_socle_gain_le_two (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 2 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    let hQ1 : 1 < actualPrincipalIndex P.M.base := by omega
    Gamma.asRelativeIdeal.idealType ≤
      L5A2B3.actualSinkCount (symmetricPrefixIdeal A hQ1) (routingA P.M.base A.reindex)
        (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _)+2 := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  have hh := symmetric_principal_algebraic_socle_gain_le_two (k:=ℚ) A hB (by omega : 1 < actualPrincipalIndex P.M.base)
  rwa [symmetricFinalH0_finrank_actualType,symmetricPrefixH0_finrank_actualSinkCount] at hh

theorem symmetric_Q_ge_three_actual_type_le_sourceCount
    (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 2 < actualPrincipalIndex P.M.base) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  exact (symmetric_principal_socle_gain_le_two A hB hQ).trans
    (symmetric_prefix_socle_plus_two_le_actual_sourceCount A hB hQ)

theorem symmetric_principal_low_koszul_exact_segment (A : SectorBCriticalRoleBranchA P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (symmetricPrincipalH0Injection (k:=k) A hQ) ∧
      LinearMap.range (symmetricPrincipalH0Injection (k:=k) A hQ) =
        LinearMap.ker (symmetricPrincipalH0Projection (k:=k) A hQ) ∧
      LinearMap.range (symmetricPrincipalH0Projection (k:=k) A hQ) =
        LinearMap.ker (symmetricPrincipalConnecting (k:=k) A hQ) :=
  ⟨symmetricPrincipalH0Injection_injective A hQ,symmetricPrincipalH0Projection_exact A hQ,
    symmetricPrincipalConnecting_exact A hQ⟩

end NS25Lean.L5A2BFinalRepair
