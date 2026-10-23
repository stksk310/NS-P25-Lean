import NS25Lean.P3ActiveClassificationR51
import NS25Lean.P2SectorCFirstStagePairingFreshness
import NS25Lean.P2PrefixDictionary

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R51
open L2B L5A2C4H L5A2C4I L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- Return nesting holds whenever the shift is in the tail, without P2 premises. -/
theorem returnIdeal_add_principal_subset (H : NumericalSemigroup)
    (m q q₀ : ℕ) (hq₀ : q₀ * m ∈ H) :
    (returnIdeal H ((q + q₀) * m)).carrier ⊆ (returnIdeal H (q * m)).carrier := by
  intro x hx
  rcases hx with ⟨hxH, hxshift⟩
  refine ⟨hxH, ?_⟩
  change x - ((q + q₀) * m : ℕ) ∈ H.asRelativeIdeal at hxshift
  have hadd := H.asRelativeIdeal.add_mem hxshift hq₀
  change x - (q * m : ℕ) ∈ H.asRelativeIdeal
  have heq : x - (q * m : ℕ) =
      (x - ((q + q₀) * m : ℕ)) + (q₀ * m : ℕ) := by
    push_cast
    ring
  rw [heq]
  exact hadd

/-- Specialization to the actual normalized tail and its least principal return. -/
theorem multiplicity_return_nesting (M : MultiplicityBase Gamma) (q : ℕ) :
    (returnIdeal (normalizedH M.base)
      ((q + actualPrincipalIndex M.base) * normalizedM M.base)).carrier ⊆
    (returnIdeal (normalizedH M.base) (q * normalizedM M.base)).carrier :=
  returnIdeal_add_principal_subset _ _ _ _ (actualPrincipalIndex_spec M.base).2

/-- The existing injective, nonexceptional pairing specializes to any actual multiplicity base. -/
theorem multiplicity_firstStage_count (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    ResidueData.cUsedFirstStageCount D =
      ResidueData.sourceTargetBranchCount D - ResidueData.cExceptionalCount D := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  exact ResidueData.c_used_eq_sourceTarget_sub_exceptional (routingData M.base e)

/-- Exact used/fresh decomposition, proved using physically distinct reverse-base residues. -/
theorem unused_count_identity {R : Type*} [Fintype R]
    (D : CombinatorialCore.ResidueData R) :
    Nat.card (ResidueData.ExactUnusedMergeBases D) + ResidueData.cExceptionalCount D =
      Nat.card (ResidueData.CFreshUnusedMergeBases D) +
        ResidueData.sourceTargetBranchCount D := by
  letI : Finite (ResidueData.ExactUnusedMergeBases D) := Subtype.finite
  letI : Finite (ResidueData.CUsedFirstStageBases D) := Subtype.finite
  letI : Finite (ResidueData.CFreshUnusedMergeBases D) := Subtype.finite
  have hpart := Nat.card_congr (ResidueData.cUnusedMergeUsedFreshEquiv D)
  rw [Nat.card_sum] at hpart
  have hstage := ResidueData.c_firstStage_card_identity D
  unfold ResidueData.cUsedFirstStageCount at hstage
  omega

/-- This is a closing criterion, not a proof that the geometric compensators exist. -/
theorem fresh_bound_iff_unused_bound {R : Type*} [Fintype R]
    (D : CombinatorialCore.ResidueData R) :
    ResidueData.cExceptionalCount D ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D) + 1 ↔
      ResidueData.sourceTargetBranchCount D ≤ Nat.card (ResidueData.ExactUnusedMergeBases D) + 1 := by
  have h := unused_count_identity D
  omega

end NS25Lean.P3R51
