import NS25Lean.P3OriginalTypeBridgeR52

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R54
open ChosenBase L2B L5A2B4AR1 L5A2C4H L5A2C4I CombinatorialCore
variable {Gamma : NumericalSemigroup}

/-- The identity ideal of a numerical semigroup has exactly the minimal generator zero. -/
theorem identity_minimal_iff (H : NumericalSemigroup) (z : ℤ) :
    H.asRelativeIdeal.IsMinimalGenerator z ↔ z = 0 := by
  constructor
  · rintro ⟨hz, hmin⟩
    obtain ⟨n, hn, rfl⟩ := hz
    by_contra hne
    have hn0 : n ≠ 0 := by exact_mod_cast hne
    apply hmin n hn hn0
    exact ⟨0, H.zero_mem, by simp⟩
  · rintro rfl
    refine ⟨⟨0, H.zero_mem, rfl⟩, ?_⟩
    intro n hn hn0 hbad
    obtain ⟨k, hk, he⟩ := hbad
    omega

theorem identity_generatorCount (H : NumericalSemigroup) :
    H.asRelativeIdeal.generatorCount = 1 := by
  let E : {z // H.asRelativeIdeal.IsMinimalGenerator z} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨0, (identity_minimal_iff H 0).mpr rfl⟩
      left_inv := fun z => Subtype.ext ((identity_minimal_iff H z).mp z.property).symm
      right_inv := fun u => by cases u; rfl }
  exact (Nat.card_congr E).trans (by simp)

/-- Conditional downstream step: the prefix is empty at the actual index one. -/
theorem principal_normalizedI (B : Data Gamma) (hq : actualPrincipalIndex B = 1) :
    normalizedI B = (normalizedH B).asRelativeIdeal.translate (normalizedM B) := by
  apply RelativeIdeal.ext
  intro z
  change z ∈ (normalizedI B).carrier ↔ _
  rw [normalizedTailIdeal_eq_actualFinalCarrier]
  simp only [actualFinalCarrier, mem_finalCarrier_iff, hq, one_mul,
    mem_prefixCarrier_iff, RelativeIdeal.mem_translate_iff, Nat.cast_one, one_mul]
  constructor
  · rintro (⟨ell, hpos, hlt, _⟩ | hz)
    · omega
    · exact hz
  · exact Or.inr

theorem principal_normalized_generatorCount (B : Data Gamma)
    (hq : actualPrincipalIndex B = 1) : (normalizedI B).generatorCount = 1 := by
  rw [principal_normalizedI B hq, RelativeIdeal.generatorCount_translate,
    identity_generatorCount]

/-- Every source-target diagonal shift is injective into actual raw sources. -/
theorem sourceTargetBranchCount_le_sourceCount {R : Type*} [Fintype R]
    (D : ResidueData R) : ResidueData.sourceTargetBranchCount D ≤ D.sourceCount := by
  let f : ResidueData.CSourceTargetBranches D → {r // D.IsSource r} :=
    fun s => ⟨D.branchTarget s.val, s.property.2⟩
  apply Nat.card_le_card_of_injective f
  intro s t he
  exact Subtype.ext (D.branchTarget_injective (congrArg Subtype.val he))

theorem exceptionalCount_le_sourceCount {R : Type*} [Fintype R]
    (D : ResidueData R) : ResidueData.cExceptionalCount D ≤ D.sourceCount := by
  have ht := sourceTargetBranchCount_le_sourceCount D
  have hc := ResidueData.c_firstStage_card_identity D
  omega

theorem principal_sourceCount (M : MultiplicityBase Gamma)
    (hq : actualPrincipalIndex M.base = 1) : L2B.sourceCount M.base = 1 := by
  have hn := principal_normalized_generatorCount M.base hq
  have hd := FourGeneratedBridge.normalizedTail_generatorCount Gamma M.base.q.val
    (M.base.tailDegrees 0).val (M.base.tailDegrees 1).val (M.base.tailDegrees 2).val
    (L5A2B2.chosenBase_minimalFour M.base)
  change (normalizedI M.base).generatorCount = _ at hd
  rw [hn] at hd
  rw [L2B.sourceCount, Data.K, chosenBase_tail_eq_generatedThree M.base (Equiv.refl _)]
  exact hd.symm

/-- M02 §9 for every legal role, conditional on the still separate principal-rigidity step. -/
theorem principal_routing_exceptional_le_one (M : MultiplicityBase Gamma)
    (hq : actualPrincipalIndex M.base = 1) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ResidueData.cExceptionalCount (routingData M.base e) ≤ 1 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hc := exceptionalCount_le_sourceCount (routingData M.base e)
  have hs := P3R52Bridge.routing_sourceCount M e
  rw [hs, principal_sourceCount M hq] at hc
  exact hc

theorem principal_type_le_two (M : MultiplicityBase Gamma)
    (hq : actualPrincipalIndex M.base = 1) : Gamma.asRelativeIdeal.idealType ≤ 2 := by
  have hi := P3R52Bridge.type_fake_fresh_identity M (Equiv.refl _)
  have hc := principal_routing_exceptional_le_one M hq (Equiv.refl _)
  rw [principal_sourceCount M hq] at hi
  omega

/-- This is deliberately conditional; original R0 still has to imply `hq`. -/
theorem p3_strong_of_principal_index_one (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hq : actualPrincipalIndex M.base = 1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  have ht := principal_type_le_two M hq
  have hr := sourceCount_add_defect M.base
  rw [hp, principal_sourceCount M hq] at hr
  omega

end NS25Lean.P3R54
