import NS25Lean.P3FreshProvenanceR52
import NS25Lean.P2SectorCLocalCollisionAccounting

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3CommonFinal
open CombinatorialCore L5A2C4H L5A2C4I

/-- D5 before the first-stage cancellation: both sides use one final datum.
The paired zero diamonds cancel; no endpoint is transported from an old cut. -/
theorem euler_total {R : Type*} [Fintype R] (D : ResidueData R) :
    D.sinkCount + Nat.card (ResidueData.ExactUnusedMergeBases D) =
      D.sourceCount + ResidueData.sourceTargetBranchCount D := by
  have hb := L5A2C4J.ResidueData.branchCount_raw_decomposition D
  have hm := L5A2C4J.ResidueData.mergeCount_raw_decomposition D
  have he := ResidueData.edge_count_balance D.outgoing_edge_count D.incoming_edge_count
  change D.mergeCount = _ + Nat.card (ResidueData.ExactUnusedMergeBases D) at hm
  omega

/-- The two exact partitions share literally the same final used carrier. -/
theorem same_final_partitions {R : Type*} [Fintype R] (D : ResidueData R) :
    ResidueData.sourceTargetBranchCount D =
      Nat.card (ResidueData.CUsedFirstStageBases D) + ResidueData.cExceptionalCount D ∧
    Nat.card (ResidueData.ExactUnusedMergeBases D) =
      Nat.card (ResidueData.CUsedFirstStageBases D) +
        Nat.card (ResidueData.CFreshUnusedMergeBases D) := by
  letI : Finite (ResidueData.ExactUnusedMergeBases D) := Subtype.finite
  letI : Finite (ResidueData.CUsedFirstStageBases D) := Subtype.finite
  letI : Finite (ResidueData.CFreshUnusedMergeBases D) := Subtype.finite
  have hs := ResidueData.c_firstStage_card_identity D
  unfold ResidueData.cUsedFirstStageCount at hs
  have hu := Nat.card_congr (ResidueData.cUnusedMergeUsedFreshEquiv D)
  rw [Nat.card_sum] at hu
  exact ⟨by omega, hu⟩

/-- D5 after cancelling the identical used image, retaining all sinks. -/
theorem euler_fresh {R : Type*} [Fintype R] (D : ResidueData R) :
    D.sinkCount + Nat.card (ResidueData.CFreshUnusedMergeBases D) =
      D.sourceCount + ResidueData.cExceptionalCount D := by
  have ht := euler_total D
  obtain ⟨hs,hu⟩ := same_final_partitions D
  omega

/-- Strong fresh compensation and total UM/ST compensation are equivalent.
This is a finite carrier identity, not an existence assumption on compensators. -/
theorem compensation_iff {R : Type*} [Fintype R] (D : ResidueData R) :
    ResidueData.sourceTargetBranchCount D ≤
      Nat.card (ResidueData.ExactUnusedMergeBases D) + 1 ↔
    ResidueData.cExceptionalCount D ≤
      Nat.card (ResidueData.CFreshUnusedMergeBases D) + 1 := by
  obtain ⟨hs,hu⟩ := same_final_partitions D
  omega
end NS25Lean.P3CommonFinal
