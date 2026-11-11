import NS25Lean.P2BranchBFinalRepairKoszulSurgery

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR4R2A L5A2B4AR5A L5A2C4H L5A2C4C
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Actual principal insertion, using the common algebraic cut for every Q>1. -/
theorem symmetric_principal_socle_gain_le_two_uniform (A : SectorBCriticalRoleBranchA P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base) :
    letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
    Gamma.asRelativeIdeal.idealType ≤
      L5A2B3.actualSinkCount (symmetricPrefixIdeal A hQ) (routingA P.M.base A.reindex)
        (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) (routingHB _ _) (routingHC _ _)+2 := by
  letI : NeZero (routingA P.M.base A.reindex) := ⟨(routingA_pos _ _).ne'⟩
  have hh := symmetric_principal_algebraic_socle_gain_le_two (k:=ℚ) A hB hQ
  rwa [symmetricFinalH0_finrank_actualType,symmetricPrefixH0_finrank_actualSinkCount] at hh

/-- Chart A uses one prefix/resource/principal route, including Q=2. -/
theorem symmetric_Q_gt_one_actual_type_le_sourceCount_uniform
    (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  exact (symmetric_principal_socle_gain_le_two_uniform A hB hQ).trans
    (symmetric_prefix_socle_plus_two_le_actual_sourceCount_uniform A hB hQ)

end NS25Lean.L5A2BFinalRepair
