import NS25Lean.P2BranchBK5Rank

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1 MvPolynomial
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3 ToricPresentation
variable {k : Type*} [Field k] {Gamma : NumericalSemigroup} {P : P2Data Gamma}

theorem nonsymmetric_H_eq_normalizedH (R : SectorBCriticalRoleBranchB P) :
    nsH R=normalizedH P.M.base := branchBRoutingH_eq_normalizedH R

def nonsymmetricFinalIdeal (R : SectorBCriticalRoleBranchB P) :
    RelativeIdeal (nsH R) where
  carrier := actualFinalCarrier P.M.base
  nonempty := by rw [← normalizedTailIdeal_eq_actualFinalCarrier]; exact (normalizedI _).nonempty
  bddBelow := by rw [← normalizedTailIdeal_eq_actualFinalCarrier]; exact (normalizedI _).bddBelow
  add_mem := by
    intro z h hz hh
    rw [← normalizedTailIdeal_eq_actualFinalCarrier] at hz ⊢
    rw [nonsymmetric_H_eq_normalizedH R] at hh
    exact (normalizedI P.M.base).add_mem hz hh

theorem nonsymmetricFinalIdeal_mem (R : SectorBCriticalRoleBranchB P) (z : ℤ) :
    z ∈ nonsymmetricFinalIdeal R ↔ z ∈ normalizedI P.M.base := by
  change z ∈ actualFinalCarrier P.M.base ↔ _
  rw [← normalizedTailIdeal_eq_actualFinalCarrier]
  rfl

theorem nonsymmetricFinalIdeal_mem_split (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : ℤ) :
    z ∈ nonsymmetricFinalIdeal R ↔ z ∈ nonsymmetricPrefixIdeal R hQ ∨
      z - (nonsymmetricPrincipalDegree R).val ∈ (nsH R).asRelativeIdeal := by
  change z ∈ finalCarrier _ _ _ ↔ _
  rw [mem_finalCarrier_iff]
  change z ∈ prefixCarrier _ _ _ ∨ z - _ ∈ _ ↔
    z ∈ prefixCarrier (nsH R) _ _ ∨
      z - (actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) ∈
        (nsH R).asRelativeIdeal
  rw [nonsymmetric_H_eq_normalizedH R,Nat.cast_mul]

theorem nonsymmetricFinalIdeal_monomial_eq (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    carrierMonomialIdeal k (nonsymmetricFinalIdeal R) =
      carrierMonomialIdeal k (nonsymmetricPrefixIdeal R hQ) ⊔
        Ideal.span {AddMonoidAlgebra.single (nonsymmetricPrincipalDegree R) (1 : k)} := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨h,hh,rfl⟩
    rcases (nonsymmetricFinalIdeal_mem_split R hQ _).mp hh with hp | ht
    · exact (show carrierMonomialIdeal k (nonsymmetricPrefixIdeal R hQ) ≤ _ from le_sup_left)
        (Ideal.subset_span ⟨h,hp,rfl⟩)
    · obtain ⟨d,hd,he⟩ := ht
      let dH : (nsH R).toAddSubmonoid := ⟨d,hd⟩
      have eh : h = nonsymmetricPrincipalDegree R + dH := by
        apply Subtype.ext
        change h.val = _ + d
        omega
      apply (show Ideal.span {AddMonoidAlgebra.single (nonsymmetricPrincipalDegree R) (1 : k)} ≤ _ from le_sup_right)
      apply Ideal.mem_span_singleton.mpr
      refine ⟨AddMonoidAlgebra.single dH 1,?_⟩
      rw [AddMonoidAlgebra.of'_apply,AddMonoidAlgebra.single_mul_single,one_mul,← eh]
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨h,hh,rfl⟩
      exact Ideal.subset_span ⟨h,(nonsymmetricFinalIdeal_mem_split R hQ _).mpr (Or.inl hh),rfl⟩
    · apply Ideal.span_le.mpr
      rintro _ ⟨rfl⟩
      apply Ideal.subset_span
      refine ⟨nonsymmetricPrincipalDegree R,?_,?_⟩
      · apply (nonsymmetricFinalIdeal_mem_split R hQ _).mpr
        right
        exact ⟨0,(routingH _ _).zero_mem,by simp⟩
      · exact AddMonoidAlgebra.of'_apply _

abbrev nonsymmetricPrincipalFinalQuotient (R : SectorBCriticalRoleBranchB P) :=
  SemigroupAlgebra k (nsH R).toAddSubmonoid ⧸
    carrierMonomialIdeal k (nonsymmetricFinalIdeal R)

def nonsymmetricPrincipalSurgeryEquiv (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  Ideal.quotientEquivAlgOfEq k (nonsymmetricFinalIdeal_monomial_eq (k:=k) R hQ).symm

def nonsymmetricPrincipalFinalProjection (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrincipalPrefixQuotient (k:=k) R hQ →ₗ[k] nonsymmetricPrincipalFinalQuotient (k:=k) R :=
  (nonsymmetricPrincipalSurgeryEquiv (k:=k) R hQ).toLinearEquiv.toLinearMap.comp
    (principalFinalProjection _ (AddMonoidAlgebra.single (nonsymmetricPrincipalDegree R) 1))

theorem nonsymmetricPrincipalFinalProjection_surjective (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Surjective (nonsymmetricPrincipalFinalProjection (k:=k) R hQ) :=
  (nonsymmetricPrincipalSurgeryEquiv R hQ).surjective.comp
    (principalFinalProjection_surjective _ _)

theorem nonsymmetricPrincipalFinalProjection_exact (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.range (nonsymmetricPrincipalInjection (k:=k) R hQ) =
      LinearMap.ker (nonsymmetricPrincipalFinalProjection (k:=k) R hQ) := by
  change LinearMap.range (principalColonInjection (k:=k)
    (carrierMonomialIdeal k (nonsymmetricPrefixIdeal R hQ))
    (AddMonoidAlgebra.single (nonsymmetricPrincipalDegree R) 1)) = _
  rw [principalFinalProjection_exact]
  ext z
  change _ = 0 ↔ (nonsymmetricPrincipalSurgeryEquiv (k:=k) R hQ) _ = 0
  exact (map_eq_zero_iff (nonsymmetricPrincipalSurgeryEquiv (k:=k) R hQ)
    (nonsymmetricPrincipalSurgeryEquiv (k:=k) R hQ).injective).symm

def nonsymmetricFinalGenerators (R : SectorBCriticalRoleBranchB P) (i : Fin 3) :
    nonsymmetricPrincipalFinalQuotient (k:=k) R :=
  Ideal.Quotient.mkₐ k (carrierMonomialIdeal k (nonsymmetricFinalIdeal R))
    (AddMonoidAlgebra.single (nonsymmetricTailMonomialDegree R i) 1)

theorem nonsymmetricPrincipalFinalProjection_mk (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (p : SemigroupAlgebra k (nsH R).toAddSubmonoid) :
    nonsymmetricPrincipalFinalProjection (k:=k) R hQ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ p := by
  simp [nonsymmetricPrincipalFinalProjection,nonsymmetricPrincipalSurgeryEquiv,
    principalFinalProjection,Ideal.quotientEquivAlgOfEq]

theorem nonsymmetricPrincipalFinalProjection_generator (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (i : Fin 3)
    (z : nonsymmetricPrincipalPrefixQuotient (k:=k) R hQ) :
    nonsymmetricPrincipalFinalProjection (k:=k) R hQ (nonsymmetricPrefixGenerators (k:=k) R hQ i*z) =
      nonsymmetricFinalGenerators (k:=k) R i * nonsymmetricPrincipalFinalProjection (k:=k) R hQ z := by
  refine Quotient.inductionOn' z ?_
  intro p
  change nonsymmetricPrincipalFinalProjection (k:=k) R hQ (Ideal.Quotient.mk _ (_*p)) =
    Ideal.Quotient.mk _ _ * nonsymmetricPrincipalFinalProjection (k:=k) R hQ (Ideal.Quotient.mk _ p)
  rw [nonsymmetricPrincipalFinalProjection_mk,nonsymmetricPrincipalFinalProjection_mk,map_mul]

abbrev nonsymmetricPrefixH0 (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :=
  LinearMap.ker (threeKoszulD0 (k:=k) (nonsymmetricPrefixGenerators (k:=k) R hQ))

abbrev nonsymmetricFinalH0 (R : SectorBCriticalRoleBranchB P) :=
  LinearMap.ker (threeKoszulD0 (k:=k) (nonsymmetricFinalGenerators (k:=k) R))

def nonsymmetricPrincipalLinearLift (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrincipalFinalQuotient (k:=k) R →ₗ[k] nonsymmetricPrincipalPrefixQuotient (k:=k) R hQ :=
  ((nonsymmetricPrincipalFinalProjection (k:=k) R hQ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (nonsymmetricPrincipalFinalProjection_surjective R hQ))).choose

theorem nonsymmetricPrincipalLinearLift_spec (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : nonsymmetricPrincipalFinalQuotient (k:=k) R) :
    nonsymmetricPrincipalFinalProjection (k:=k) R hQ (nonsymmetricPrincipalLinearLift (k:=k) R hQ z) = z :=
  LinearMap.congr_fun
    ((nonsymmetricPrincipalFinalProjection (k:=k) R hQ).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (nonsymmetricPrincipalFinalProjection_surjective R hQ))).choose_spec z

theorem nonsymmetricPrincipal_retract_on_kernel (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base)
    (z : nonsymmetricPrincipalPrefixQuotient (k:=k) R hQ)
    (hz : nonsymmetricPrincipalFinalProjection (k:=k) R hQ z = 0) :
    nonsymmetricPrincipalInjection (k:=k) R hQ
      ((nonsymmetricPrincipalInjection (k:=k) R hQ).leftInverse z) = z := by
  have hr : z ∈ LinearMap.range (nonsymmetricPrincipalInjection (k:=k) R hQ) := by
    rw [nonsymmetricPrincipalFinalProjection_exact]
    exact hz
  obtain ⟨w,rfl⟩ := hr
  rw [LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (nonsymmetricPrincipalInjection_injective R hQ))]

def nonsymmetricPrincipalConnectingPre (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricFinalH0 (k:=k) R →ₗ[k] (Fin 3 → nonsymmetricPrincipalColonQuotient k R hQ) where
  toFun := fun z i => (nonsymmetricPrincipalInjection (k:=k) R hQ).leftInverse
    (nonsymmetricPrefixGenerators (k:=k) R hQ i * nonsymmetricPrincipalLinearLift (k:=k) R hQ z.val)
  map_add' := by intro z w; ext i; simp [map_add,mul_add]
  map_smul' := by intro a z; ext i; simp [map_smul,mul_smul_comm]

theorem nonsymmetricPrincipalConnectingPre_image (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : nonsymmetricFinalH0 (k:=k) R) (i : Fin 3) :
    nonsymmetricPrincipalInjection (k:=k) R hQ (nonsymmetricPrincipalConnectingPre (k:=k) R hQ z i) =
      nonsymmetricPrefixGenerators (k:=k) R hQ i * nonsymmetricPrincipalLinearLift (k:=k) R hQ z.val := by
  apply nonsymmetricPrincipal_retract_on_kernel
  rw [nonsymmetricPrincipalFinalProjection_generator,nonsymmetricPrincipalLinearLift_spec]
  exact congrFun z.property i

theorem nonsymmetricPrincipalConnectingPre_cycle (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : nonsymmetricFinalH0 (k:=k) R) :
    threeKoszulD1 (k:=k) (nonsymmetricColonGenerators (k:=k) R hQ)
      (nonsymmetricPrincipalConnectingPre (k:=k) R hQ z) = 0 := by
  have hc : ∀ i j : Fin 3,
      nonsymmetricColonGenerators (k:=k) R hQ j * nonsymmetricPrincipalConnectingPre (k:=k) R hQ z i -
      nonsymmetricColonGenerators (k:=k) R hQ i * nonsymmetricPrincipalConnectingPre (k:=k) R hQ z j = 0 := by
    intro i j
    apply nonsymmetricPrincipalInjection_injective (k:=k) R hQ
    rw [map_sub,map_zero,nonsymmetricPrincipalInjection_generator,nonsymmetricPrincipalInjection_generator,
      nonsymmetricPrincipalConnectingPre_image,nonsymmetricPrincipalConnectingPre_image]
    ring
  ext i
  fin_cases i <;> simpa [threeKoszulD1] using hc _ _

def nonsymmetricPrincipalConnecting (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricFinalH0 (k:=k) R →ₗ[k] nonsymmetricPrincipalColonH1 (k:=k) R hQ :=
  Submodule.mkQ _ ∘ₗ (nonsymmetricPrincipalConnectingPre (k:=k) R hQ).codRestrict _
    (nonsymmetricPrincipalConnectingPre_cycle (k:=k) R hQ)

def nonsymmetricPrincipalH0Projection (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrefixH0 (k:=k) R hQ →ₗ[k] nonsymmetricFinalH0 (k:=k) R :=
  ((nonsymmetricPrincipalFinalProjection (k:=k) R hQ).comp
    (nonsymmetricPrefixH0 (k:=k) R hQ).subtype).codRestrict _ (by
      intro z
      ext i
      change nonsymmetricFinalGenerators (k:=k) R i * nonsymmetricPrincipalFinalProjection (k:=k) R hQ z.val = 0
      rw [← nonsymmetricPrincipalFinalProjection_generator]
      have hz := congrFun z.property i
      change nonsymmetricPrefixGenerators (k:=k) R hQ i*z.val=0 at hz
      rw [hz,map_zero])

theorem nonsymmetricPrincipalConnecting_eq_zero (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : nonsymmetricFinalH0 (k:=k) R) :
    nonsymmetricPrincipalConnecting (k:=k) R hQ z = 0 ↔
      ∃ w : nonsymmetricPrincipalColonQuotient k R hQ,
        threeKoszulD0 (k:=k) (nonsymmetricColonGenerators (k:=k) R hQ) w =
          nonsymmetricPrincipalConnectingPre (k:=k) R hQ z := by
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem nonsymmetricPrincipalConnecting_exact (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.range (nonsymmetricPrincipalH0Projection (k:=k) R hQ) =
      LinearMap.ker (nonsymmetricPrincipalConnecting (k:=k) R hQ) := by
  ext z
  constructor
  · rintro ⟨b,rfl⟩
    rw [LinearMap.mem_ker,nonsymmetricPrincipalConnecting_eq_zero]
    let l := nonsymmetricPrincipalLinearLift (k:=k) R hQ
      (nonsymmetricPrincipalH0Projection (k:=k) R hQ b).val
    let w := (nonsymmetricPrincipalInjection (k:=k) R hQ).leftInverse (l-b.val)
    have hw : nonsymmetricPrincipalInjection (k:=k) R hQ w = l-b.val := by
      apply nonsymmetricPrincipal_retract_on_kernel
      rw [map_sub,nonsymmetricPrincipalLinearLift_spec]
      exact sub_self _
    refine ⟨w,?_⟩
    ext i
    apply nonsymmetricPrincipalInjection_injective (k:=k) R hQ
    change nonsymmetricPrincipalInjection (k:=k) R hQ (nonsymmetricColonGenerators (k:=k) R hQ i*w) = _
    rw [nonsymmetricPrincipalInjection_generator,hw,nonsymmetricPrincipalConnectingPre_image,mul_sub]
    have hb := congrFun b.property i
    change nonsymmetricPrefixGenerators (k:=k) R hQ i*b.val=0 at hb
    rw [hb,sub_zero]
  · intro hz
    obtain ⟨w,hw⟩ := (nonsymmetricPrincipalConnecting_eq_zero R hQ z).mp hz
    let b := nonsymmetricPrincipalLinearLift (k:=k) R hQ z.val - nonsymmetricPrincipalInjection (k:=k) R hQ w
    have hb : b ∈ nonsymmetricPrefixH0 (k:=k) R hQ := by
      ext i
      change nonsymmetricPrefixGenerators (k:=k) R hQ i*b=0
      dsimp [b]
      rw [mul_sub,← nonsymmetricPrincipalInjection_generator]
      have hwi := congrFun hw i
      change nonsymmetricColonGenerators (k:=k) R hQ i*w = _ at hwi
      rw [hwi,nonsymmetricPrincipalConnectingPre_image,sub_self]
    refine ⟨⟨b,hb⟩,?_⟩
    apply Subtype.ext
    change nonsymmetricPrincipalFinalProjection (k:=k) R hQ b = z.val
    dsimp [b]
    rw [map_sub,nonsymmetricPrincipalLinearLift_spec]
    have hi : nonsymmetricPrincipalFinalProjection (k:=k) R hQ (nonsymmetricPrincipalInjection (k:=k) R hQ w)=0 := by
      have hr : nonsymmetricPrincipalInjection (k:=k) R hQ w ∈ LinearMap.range (nonsymmetricPrincipalInjection (k:=k) R hQ) := ⟨w,rfl⟩
      rw [nonsymmetricPrincipalFinalProjection_exact] at hr
      exact hr
    rw [hi,sub_zero]

def nonsymmetricPrincipalH0Injection (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrincipalColonH0 (k:=k) R hQ →ₗ[k] nonsymmetricPrefixH0 (k:=k) R hQ :=
  ((nonsymmetricPrincipalInjection (k:=k) R hQ).comp
    (nonsymmetricPrincipalColonH0 (k:=k) R hQ).subtype).codRestrict _ (by
      intro z
      ext i
      change nonsymmetricPrefixGenerators (k:=k) R hQ i * nonsymmetricPrincipalInjection (k:=k) R hQ z.val=0
      rw [← nonsymmetricPrincipalInjection_generator]
      have hz := congrFun z.property i
      change nonsymmetricColonGenerators (k:=k) R hQ i*z.val=0 at hz
      rw [hz,map_zero])

theorem nonsymmetricPrincipalH0Injection_injective (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricPrincipalH0Injection (k:=k) R hQ) := by
  intro z w he
  apply Subtype.ext
  exact nonsymmetricPrincipalInjection_injective (k:=k) R hQ (congrArg Subtype.val he)

theorem nonsymmetricPrincipalH0Projection_exact (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    LinearMap.range (nonsymmetricPrincipalH0Injection (k:=k) R hQ) =
      LinearMap.ker (nonsymmetricPrincipalH0Projection (k:=k) R hQ) := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    apply Subtype.ext
    have hr : nonsymmetricPrincipalInjection (k:=k) R hQ w.val ∈
        LinearMap.range (nonsymmetricPrincipalInjection (k:=k) R hQ) := ⟨w.val,rfl⟩
    rw [nonsymmetricPrincipalFinalProjection_exact] at hr
    exact hr
  · intro hz
    have hz' : z.val ∈ LinearMap.range (nonsymmetricPrincipalInjection (k:=k) R hQ) := by
      rw [nonsymmetricPrincipalFinalProjection_exact]
      exact congrArg Subtype.val hz
    obtain ⟨w,hw⟩ := hz'
    have hs : w ∈ nonsymmetricPrincipalColonH0 (k:=k) R hQ := by
      ext i
      change nonsymmetricColonGenerators (k:=k) R hQ i*w=0
      apply nonsymmetricPrincipalInjection_injective (k:=k) R hQ
      rw [nonsymmetricPrincipalInjection_generator,hw,map_zero]
      exact congrFun z.property i
    exact ⟨⟨w,hs⟩,Subtype.ext hw⟩


theorem nonsymmetricPrincipalConnecting_comparison_zero (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) (z : nonsymmetricFinalH0 (k:=k) R) :
    nonsymmetricPrincipalComparisonH1 (k:=k) R hQ
      (nonsymmetricPrincipalConnecting (k:=k) R hQ z)=0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (fun i => nonsymmetricPrincipalInjection R hQ
    (nonsymmetricPrincipalConnectingPre R hQ z i)) ∈
      LinearMap.range (threeKoszulD0 (k:=k) (nonsymmetricPrefixGenerators R hQ))
  refine ⟨nonsymmetricPrincipalLinearLift R hQ z.val,?_⟩
  apply funext
  intro i
  exact (nonsymmetricPrincipalConnectingPre_image R hQ z i).symm

theorem nonsymmetric_principal_low_koszul_exact_segment (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Function.Injective (nonsymmetricPrincipalH0Injection (k:=k) R hQ) ∧
    LinearMap.range (nonsymmetricPrincipalH0Injection (k:=k) R hQ)=
      LinearMap.ker (nonsymmetricPrincipalH0Projection (k:=k) R hQ) ∧
    LinearMap.range (nonsymmetricPrincipalH0Projection (k:=k) R hQ)=
      LinearMap.ker (nonsymmetricPrincipalConnecting (k:=k) R hQ) ∧
    LinearMap.range (nonsymmetricPrincipalConnecting (k:=k) R hQ) ≤
      LinearMap.ker (nonsymmetricPrincipalComparisonH1 (k:=k) R hQ) := by
  refine ⟨nonsymmetricPrincipalH0Injection_injective R hQ,
    nonsymmetricPrincipalH0Projection_exact R hQ,nonsymmetricPrincipalConnecting_exact R hQ,?_⟩
  rintro _ ⟨z,rfl⟩
  exact nonsymmetricPrincipalConnecting_comparison_zero R hQ z

/-- Net socle gain uses the actual mixed H1 formula and the actual K5 rank,
not the symmetric pure-power H1 dimension. -/
theorem nonsymmetric_principal_algebraic_socle_gain_le_two (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (nonsymmetricFinalH0 (k:=k) R) ≤
      Module.finrank k (nonsymmetricPrefixH0 (k:=k) R hQ)+2 := by
  letI := carrierMonomialQuotient_finite (k:=k) (nonsymmetricFinalIdeal R)
  letI := carrierMonomialQuotient_finite (k:=k) (nonsymmetricPrefixIdeal R hQ)
  letI := nonsymmetric_colon_H1_finite (k:=k) R hQ
  letI := nonsymmetric_colon_finite (k:=k) R hQ
  have hker : Module.finrank k (LinearMap.ker (nonsymmetricPrincipalH0Projection (k:=k) R hQ))=
      Module.finrank k (nonsymmetricPrincipalColonH0 (k:=k) R hQ) := by
    rw [← nonsymmetricPrincipalH0Projection_exact,
      LinearMap.finrank_range_of_inj (nonsymmetricPrincipalH0Injection_injective R hQ)]
  have hp := LinearMap.finrank_range_add_finrank_ker (nonsymmetricPrincipalH0Projection (k:=k) R hQ)
  have hd := LinearMap.finrank_range_add_finrank_ker (nonsymmetricPrincipalConnecting (k:=k) R hQ)
  have hc := LinearMap.finrank_range_add_finrank_ker (nonsymmetricPrincipalComparisonH1 (k:=k) R hQ)
  have hr := Submodule.finrank_mono (nonsymmetric_principal_low_koszul_exact_segment (k:=k) R hQ).2.2.2
  have hH1 := nonsymmetric_principal_colon_koszulH1_finrank (k:=k) R hB hQ
  have hK5 := nonsymmetric_principal_comparison_rank_lower_bound (k:=k) R hB hQ
  rw [hker] at hp
  rw [← nonsymmetricPrincipalConnecting_exact] at hd
  omega

theorem nonsymmetricTailMonomialDegree_generated (R : SectorBCriticalRoleBranchB P) :
    (nsH R).IsGeneratedByThree (nonsymmetricTailMonomialDegree R 0).val
      (nonsymmetricTailMonomialDegree R 1).val (nonsymmetricTailMonomialDegree R 2).val := by
  change (nsH R).IsGeneratedByThree (nsA R) (nsB R) (nsC R)
  exact (normalizedSemigroup_minimal (L5A2C4H.chosenBase_minimalFour P.M.base (nsReindex R))).1

theorem nonsymmetricTailMonomialDegree_ne_zero (R : SectorBCriticalRoleBranchB P)
    (i : Fin 3) : (nonsymmetricTailMonomialDegree R i).val ≠ 0 := by
  have h := L5A2C4H.chosenBase_minimalFour P.M.base (nsReindex R)
  have hd := tailGcd_dvd (routingN1 P.M.base (nsReindex R))
    (routingN2 P.M.base (nsReindex R)) (routingN3 P.M.base (nsReindex R))
  fin_cases i
  · exact (routingA_pos P.M.base (nsReindex R)).ne'
  · exact (quotient_pos_of_dvd h.n₂_pos hd.2.1).ne'
  · exact (quotient_pos_of_dvd h.n₃_pos hd.2.2).ne'

theorem nonsymmetricPrefixH0_finrank_integralSocle (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Module.finrank k (nonsymmetricPrefixH0 (k:=k) R hQ)=
      Nat.card {w // IsIntegralSocle (nonsymmetricPrefixIdeal R hQ) w} :=
  carrierH0_finrank_integralSocle_card _ _ (nonsymmetricTailMonomialDegree_generated R)
    (nonsymmetricTailMonomialDegree_ne_zero R)

theorem nonsymmetricFinalH0_finrank_actualType (R : SectorBCriticalRoleBranchB P) :
    Module.finrank k (nonsymmetricFinalH0 (k:=k) R)=Gamma.asRelativeIdeal.idealType := by
  change Module.finrank k (CarrierH0 (k:=k) (nonsymmetricFinalIdeal R) (nonsymmetricTailMonomialDegree R))=_
  rw [carrierH0_finrank_integralSocle_card _ _ (nonsymmetricTailMonomialDegree_generated R)
    (nonsymmetricTailMonomialDegree_ne_zero R)]
  have hi : ∀ z, IsIntegralSocle (nonsymmetricFinalIdeal R) z ↔ IsIntegralSocle (normalizedI P.M.base) z := by
    intro z
    simp only [IsIntegralSocle,nonsymmetricFinalIdeal_mem,NumericalSemigroup.mem_asRelativeIdeal_iff,
      nonsymmetric_H_eq_normalizedH R]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hi)]
  rw [← normalizedTail_socle_card Gamma P.M.base.q.val (P.M.base.tailDegrees 0).val
    (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val (L5A2B2.chosenBase_minimalFour P.M.base)]
  exact (fourGenerated_idealType_eq_natCard_socle Gamma P.M.base.q.val
    (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val
    (L5A2B2.chosenBase_minimalFour P.M.base).m_pos (L5A2B2.chosenBase_minimalFour P.M.base).generated).symm

/-- The actual integral-socle/type translation of Delta t <= 2. -/
theorem nonsymmetric_principal_socle_gain_le_two (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    Gamma.asRelativeIdeal.idealType ≤
      Nat.card {w // IsIntegralSocle (nonsymmetricPrefixIdeal R hQ) w}+2 := by
  have hh := nonsymmetric_principal_algebraic_socle_gain_le_two (k:=ℚ) R hB hQ
  rwa [nonsymmetricFinalH0_finrank_actualType,nonsymmetricPrefixH0_finrank_integralSocle] at hh

end NS25Lean.L5A2BFinalRepair

