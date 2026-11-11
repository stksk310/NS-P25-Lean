import NS25Lean.P2BranchBUniformSymmetric

set_option linter.style.header false
set_option maxHeartbeats 300000
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR4R2A L5A2B4AR5A L5A2C4H L5A2C4C
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The reflection center furnished by the actual canonical CI rectangle. -/
abbrev symmetricTailReflection (A : SectorBCriticalRoleBranchA P) : ℤ :=
  (ciH A-1 : ℕ)*n1 A+(ciG A-1 : ℕ)*n2 A-(n0 A : ℤ)

/-- Frobenius symmetry derived from the actual residue rectangle and signed height. -/
theorem symmetric_tail_reflection (A : SectorBCriticalRoleBranchA P) (z : ℤ) :
    z ∉ (routingH P.M.base A.reindex).asRelativeIdeal ↔
      symmetricTailReflection A-z ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  obtain ⟨i,j,hi,hj,he⟩ := branchA_residue_rectangle_localization A
    (z : ZMod (routingA P.M.base A.reindex))
  change i < ciH A at hi
  change j < ciG A at hj
  have hm : (((i : ℤ)*n1 A+j*n2 A : ℤ) : ZMod (routingA P.M.base A.reindex)) = z := by
    simpa only [gridResidue,Int.cast_add,Int.cast_mul,Int.cast_natCast,
      routingB_eq_n1 A,routingC_eq_n2 A] using he.symm
  obtain ⟨l,hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hm
  rw [routingA_eq_n0 A] at hl
  have hz : z=l*n0 A+i*n1 A+j*n2 A := by nlinarith [hl]
  have hci : ciH A-1-i < ciH A := by omega
  have hcj : ciG A-1-j < ciG A := by omega
  have hr : symmetricTailReflection A-z =
      (-l-1)*n0 A+(ciH A-1-i : ℕ)*n1 A+(ciG A-1-j : ℕ)*n2 A := by
    dsimp only [symmetricTailReflection]
    rw [hz,Nat.cast_sub (by omega : i ≤ ciH A-1),Nat.cast_sub (by omega : j ≤ ciG A-1)]
    ring
  have hs : z ∈ (routingH P.M.base A.reindex).asRelativeIdeal ↔ 0 ≤ l := by
    rw [hz]
    exact symmetric_ci_signed_height_mem_iff A hi hj l
  have ht : symmetricTailReflection A-z ∈ (routingH P.M.base A.reindex).asRelativeIdeal ↔
      0 ≤ -l-1 := by
    rw [hr]
    exact symmetric_ci_signed_height_mem_iff A hci hcj (-l-1)
  rw [hs,ht]
  omega

/-- All-Q actual carrier dictionary; no nonempty-prefix assumption. -/
theorem symmetric_final_mem_all_Q (A : SectorBCriticalRoleBranchA P) (z : ℤ) :
    z ∈ symmetricFinalIdeal A ↔
      z ∈ finalCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base) := by
  change z ∈ actualFinalCarrier P.M.base ↔ _
  simp only [actualFinalCarrier,symmetric_routingH_eq_normalizedH A]

theorem symmetric_Q_one_final_mem (A : SectorBCriticalRoleBranchA P)
    (hQ : actualPrincipalIndex P.M.base=1) (z : ℤ) :
    z ∈ symmetricFinalIdeal A ↔
      z-normalizedM P.M.base ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
  rw [symmetric_final_mem_all_Q, hQ, mem_finalCarrier_iff]
  simp only [Nat.cast_one,one_mul,mem_prefixCarrier_iff]
  constructor
  · rintro (⟨ell,hp,hl,_⟩ | hz)
    · omega
    · exact hz
  · exact Or.inr

theorem symmetric_Q_two_final_mem (A : SectorBCriticalRoleBranchA P)
    (hQ : actualPrincipalIndex P.M.base=2) (z : ℤ) :
    z ∈ symmetricFinalIdeal A ↔
      (z ∈ (routingH P.M.base A.reindex).asRelativeIdeal ∧
        z-normalizedM P.M.base ∈ (routingH P.M.base A.reindex).asRelativeIdeal) ∨
      z-2*(normalizedM P.M.base : ℤ) ∈ (routingH P.M.base A.reindex).asRelativeIdeal := by
  rw [symmetric_final_mem_all_Q,hQ,mem_finalCarrier_iff]
  simp only [mem_prefixCarrier_iff,Nat.cast_mul,Nat.cast_ofNat]
  constructor
  · rintro (⟨ell,hp,hl,hz⟩ | hz)
    · have he : ell=1 := by omega
      subst ell
      exact Or.inl (by simpa only [one_mul,mem_returnIdeal_iff] using hz)
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact Or.inl ⟨1,by omega,by omega,by simpa only [one_mul,mem_returnIdeal_iff] using hz⟩
    · exact Or.inr hz

/-- The B86 actual-type dictionary, expressed without an algebra field. -/
theorem symmetric_actual_type_eq_integral_socle_card (A : SectorBCriticalRoleBranchA P) :
    Gamma.asRelativeIdeal.idealType = Nat.card {w // IsIntegralSocle (symmetricFinalIdeal A) w} := by
  rw [← symmetricFinalH0_finrank_actualType (k:=ℚ) A]
  exact carrierH0_finrank_integralSocle_card _ _ (symmetricTailMonomialDegree_generated A)
    (symmetricTailMonomialDegree_ne_zero A)

theorem symmetric_final_sources_finite (A : SectorBCriticalRoleBranchA P) :
    Finite (symmetricFinalSources A) := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  let I := symmetricFinalIdeal A
  have hg := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base A.reindex)).1
  have hs : ∀ s, IsSource (routingH P.M.base A.reindex)
      (finalCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base)) s ↔ I.IsMinimalGenerator s := by
    intro s
    simp only [IsSource,RelativeIdeal.IsMinimalGenerator,symmetric_final_mem_all_Q,I]
  apply Finite.of_injective (fun s : symmetricFinalSources A =>
    (s.val : ZMod (routingA P.M.base A.reindex)))
  intro s t he
  change (s.val : ZMod (routingA P.M.base A.reindex)) =
    (t.val : ZMod (routingA P.M.base A.reindex)) at he
  apply Subtype.ext
  have hsm := I.aperyRepresentative_eq_of_isMinimalGenerator _ _ _ hg ((hs s).mp s.property)
  have htm := I.aperyRepresentative_eq_of_isMinimalGenerator _ _ _ hg ((hs t).mp t.property)
  rw [he] at hsm
  exact hsm.symm.trans htm

theorem symmetric_tail_reflection_not_mem (A : SectorBCriticalRoleBranchA P) :
    symmetricTailReflection A ∉ (routingH P.M.base A.reindex).asRelativeIdeal := by
  intro hf
  have hn := (symmetric_tail_reflection A 0).mpr (by simpa using hf)
  exact hn ⟨0,(routingH P.M.base A.reindex).zero_mem,rfl⟩

theorem symmetric_Q_one_source_eq (A : SectorBCriticalRoleBranchA P)
    (hQ : actualPrincipalIndex P.M.base=1) (s : symmetricFinalSources A) :
    s.val = normalizedM P.M.base := by
  have hm := (symmetric_Q_one_final_mem A hQ s.val).mp
    ((symmetric_final_mem_all_Q A _).mpr s.property.1)
  obtain ⟨t,ht,he⟩ := hm
  by_cases hz : t=0
  · subst t
    omega
  · exfalso
    apply s.property.2 t ht hz
    apply (symmetric_final_mem_all_Q A _).mp
    apply (symmetric_Q_one_final_mem A hQ _).mpr
    have he0 : s.val-t-normalizedM P.M.base=0 := by omega
    rw [he0]
    exact ⟨0,(routingH P.M.base A.reindex).zero_mem,rfl⟩

theorem symmetric_Q_one_socle_eq (A : SectorBCriticalRoleBranchA P)
    (hQ : actualPrincipalIndex P.M.base=1)
    (w : {w // IsIntegralSocle (symmetricFinalIdeal A) w}) :
    w.val = symmetricTailReflection A+normalizedM P.M.base := by
  have hn : w.val-normalizedM P.M.base ∉ (routingH P.M.base A.reindex).asRelativeIdeal :=
    fun hm => w.property.2.1 ((symmetric_Q_one_final_mem A hQ _).mpr hm)
  obtain ⟨t,ht,he⟩ := (symmetric_tail_reflection A _).mp hn
  by_cases hz : t=0
  · subst t
    omega
  · exfalso
    have hs := (symmetric_Q_one_final_mem A hQ _).mp (w.property.2.2 t ht hz)
    have he0 : w.val+t-normalizedM P.M.base=symmetricTailReflection A := by omega
    rw [he0] at hs
    exact symmetric_tail_reflection_not_mem A hs

theorem symmetric_Q_one_actual_type_and_sourceCount (A : SectorBCriticalRoleBranchA P)
    (hQ : actualPrincipalIndex P.M.base=1) :
    Gamma.asRelativeIdeal.idealType=1 ∧ P.sourceCount=1 := by
  have hm : (0 : ℤ) < normalizedM P.M.base := by exact_mod_cast P.M.base.q_positive
  have hnegative : -(normalizedM P.M.base : ℤ) ∉ (routingH P.M.base A.reindex).asRelativeIdeal := by
    rintro ⟨t,ht,he⟩
    omega
  have hwH : symmetricTailReflection A+normalizedM P.M.base ∈
      (routingH P.M.base A.reindex).asRelativeIdeal := by
    simpa using (symmetric_tail_reflection A _).mp hnegative
  have hw : IsIntegralSocle (symmetricFinalIdeal A)
      (symmetricTailReflection A+normalizedM P.M.base) := by
    refine ⟨hwH,?_,?_⟩
    · rw [symmetric_Q_one_final_mem A hQ]
      simpa using symmetric_tail_reflection_not_mem A
    · intro t ht ht0
      rw [symmetric_Q_one_final_mem A hQ]
      have hn : -(t : ℤ) ∉ (routingH P.M.base A.reindex).asRelativeIdeal := by
        rintro ⟨v,hv,he⟩
        have hp : (0 : ℤ)<t := by exact_mod_cast Nat.pos_of_ne_zero ht0
        omega
      convert (symmetric_tail_reflection A _).mp hn using 1 <;> ring
  have htcard : Nat.card {w // IsIntegralSocle (symmetricFinalIdeal A) w}=1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · refine ⟨?_⟩
      intro w z
      exact Subtype.ext ((symmetric_Q_one_socle_eq A hQ w).trans
        (symmetric_Q_one_socle_eq A hQ z).symm)
    · exact ⟨⟨_,hw⟩⟩
  have hscard : Nat.card (symmetricFinalSources A)=1 := by
    rw [Nat.card_eq_one_iff_unique]
    constructor
    · refine ⟨?_⟩
      intro s t
      exact Subtype.ext ((symmetric_Q_one_source_eq A hQ s).trans
        (symmetric_Q_one_source_eq A hQ t).symm)
    · have hs := principal_is_new_source (routingH P.M.base A.reindex)
        (normalizedM P.M.base) P.M.base.q_positive
      have hp : principalIndex (routingH P.M.base A.reindex)
          (normalizedM P.M.base) P.M.base.q_positive=1 := by
        simpa only [symmetric_routingH_eq_normalizedH A] using hQ
      rw [hp,one_mul] at hs
      refine ⟨⟨normalizedM P.M.base,?_⟩⟩
      simpa only [hQ,one_mul] using hs
  exact ⟨(symmetric_actual_type_eq_integral_socle_card A).trans htcard,
    (symmetric_final_sources_card_eq_actual_sourceCount A).symm.trans hscard⟩

/-- At Q=2, reflection sends an actual integral socle to an actual minimal
source of the same final ideal. No source/target or owner identification. -/
theorem symmetric_Q_two_socle_reflect_source (A : SectorBCriticalRoleBranchA P)
    (hQ : actualPrincipalIndex P.M.base=2)
    (w : {w // IsIntegralSocle (symmetricFinalIdeal A) w}) :
    IsSource (routingH P.M.base A.reindex)
      (finalCarrier (routingH P.M.base A.reindex) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base))
      (symmetricTailReflection A+2*(normalizedM P.M.base : ℤ)-w.val) := by
  have hwH := w.property.1
  have hw1 : w.val-normalizedM P.M.base ∉ (routingH P.M.base A.reindex).asRelativeIdeal := by
    intro hh
    exact w.property.2.1 ((symmetric_Q_two_final_mem A hQ _).mpr (Or.inl ⟨hwH,hh⟩))
  have hw2 : w.val-2*(normalizedM P.M.base : ℤ) ∉ (routingH P.M.base A.reindex).asRelativeIdeal := by
    intro hh
    exact w.property.2.1 ((symmetric_Q_two_final_mem A hQ _).mpr (Or.inr hh))
  refine ⟨(symmetric_final_mem_all_Q A _).mp
    ((symmetric_Q_two_final_mem A hQ _).mpr (Or.inl ⟨?_,?_⟩)),?_⟩
  · convert (symmetric_tail_reflection A _).mp hw2 using 1 <;> ring
  · convert (symmetric_tail_reflection A _).mp hw1 using 1 <;> ring
  · intro t ht ht0 hs
    have hs' := (symmetric_Q_two_final_mem A hQ _).mp
      ((symmetric_final_mem_all_Q A _).mpr hs)
    rcases hs' with hpre | hprincipal
    · have hn1 : w.val+t-normalizedM P.M.base ∉ (routingH P.M.base A.reindex).asRelativeIdeal := by
        apply (symmetric_tail_reflection A _).mpr
        convert hpre.2 using 1 <;> ring
      have hn2' : w.val+t-2*(normalizedM P.M.base : ℤ) ∉ (routingH P.M.base A.reindex).asRelativeIdeal := by
        apply (symmetric_tail_reflection A _).mpr
        convert hpre.1 using 1 <;> ring
      rcases (symmetric_Q_two_final_mem A hQ _).mp (w.property.2.2 t ht ht0) with hret | hp
      · exact hn1 hret.2
      · exact hn2' hp
    · have hn : w.val+t ∉ (routingH P.M.base A.reindex).asRelativeIdeal := by
        apply (symmetric_tail_reflection A _).mpr
        convert hprincipal using 1 <;> ring
      exact hn ((routingH P.M.base A.reindex).asRelativeIdeal.add_mem hwH ht)

def symmetricQTwoSocleSourceMap (A : SectorBCriticalRoleBranchA P)
    (hQ : actualPrincipalIndex P.M.base=2) :
    {w // IsIntegralSocle (symmetricFinalIdeal A) w} → symmetricFinalSources A := fun w =>
  ⟨symmetricTailReflection A+2*(normalizedM P.M.base : ℤ)-w.val,
    symmetric_Q_two_socle_reflect_source A hQ w⟩

theorem symmetricQTwoSocleSourceMap_injective (A : SectorBCriticalRoleBranchA P)
    (hQ : actualPrincipalIndex P.M.base=2) :
    Function.Injective (symmetricQTwoSocleSourceMap A hQ) := by
  intro w z he
  apply Subtype.ext
  have hv := congrArg Subtype.val he
  change symmetricTailReflection A+2*(normalizedM P.M.base : ℤ)-w.val =
    symmetricTailReflection A+2*(normalizedM P.M.base : ℤ)-z.val at hv
  omega

theorem symmetric_Q_two_actual_type_le_sourceCount (A : SectorBCriticalRoleBranchA P)
    (hQ : actualPrincipalIndex P.M.base=2) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  letI := symmetric_final_sources_finite A
  have hc := Nat.card_le_card_of_injective _ (symmetricQTwoSocleSourceMap_injective A hQ)
  rwa [← symmetric_actual_type_eq_integral_socle_card A,
    symmetric_final_sources_card_eq_actual_sourceCount A] at hc

theorem symmetric_Q_le_two_actual_type_le_sourceCount
    (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : actualPrincipalIndex P.M.base ≤ 2) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have hp := (actualPrincipalIndex_spec P.M.base).1
  have he : actualPrincipalIndex P.M.base=1 ∨ actualPrincipalIndex P.M.base=2 := by omega
  rcases he with h1 | h2
  · obtain ⟨ht,hs⟩ := symmetric_Q_one_actual_type_and_sourceCount A h1
    omega
  · exact symmetric_Q_two_actual_type_le_sourceCount A h2

theorem symmetric_actual_type_le_sourceCount
    (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have hp := (actualPrincipalIndex_spec P.M.base).1
  by_cases hQ : actualPrincipalIndex P.M.base=1
  · obtain ⟨ht,hs⟩ := symmetric_Q_one_actual_type_and_sourceCount A hQ
    omega
  · exact symmetric_Q_gt_one_actual_type_le_sourceCount_uniform A hB (by omega)

end NS25Lean.L5A2BFinalRepair
