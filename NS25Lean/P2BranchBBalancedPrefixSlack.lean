import NS25Lean.P2BranchBPrefixNotchCoverage

set_option linter.style.header false
noncomputable section
open scoped Classical
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}
local instance (R : SectorBCriticalRoleBranchB P) : NeZero (nsA R) :=
  ⟨(routingA_pos P.M.base (nsReindex R)).ne'⟩

private theorem b_pos (R : SectorBCriticalRoleBranchB P) : 0 < nsB R :=
  quotient_pos_of_dvd (chosenBase_minimalFour P.M.base (nsReindex R)).n₂_pos
    (tailGcd_dvd (routingN1 P.M.base (nsReindex R))
      (routingN2 P.M.base (nsReindex R)) (routingN3 P.M.base (nsReindex R))).2.1
private theorem c_pos (R : SectorBCriticalRoleBranchB P) : 0 < nsC R :=
  quotient_pos_of_dvd (chosenBase_minimalFour P.M.base (nsReindex R)).n₃_pos
    (tailGcd_dvd (routingN1 P.M.base (nsReindex R))
      (routingN2 P.M.base (nsReindex R)) (routingN3 P.M.base (nsReindex R))).2.2

theorem nonsymmetric_prefix_source_count_dictionary (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    (nonsymmetricPrefixRouting R hQ).sourceCount=(nonsymmetricPrefixIdeal R hQ).generatorCount := by
  have hgen := (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base (nsReindex R))).1
  exact (nonsymmetricPrefixIdeal R hQ).concrete_sourceCount_eq_generatorCount
    (nsA R) (nsB R) (nsC R) hgen (routingHB _ _) (routingHC _ _)
    (b_pos R).ne' (c_pos R).ne'

theorem nonsymmetric_prefix_actual_sink_dictionary (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    L5A2C4H.actualSinkCount (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R)
      (routingHB _ _) (routingHC _ _) =
      Nat.card {w // IsIntegralSocle (nonsymmetricPrefixIdeal R hQ) w} := by
  apply L5A2B3.actualSinkCount_eq_integralSocle_card
  · exact (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base (nsReindex R))).1
  · exact (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base (nsReindex R))).1).mpr
        (AddSubmonoid.subset_closure (by simp))
  · exact (b_pos R).ne'
  · exact (c_pos R).ne'

theorem nonsymmetric_prefix_raw_slack_identity (R : SectorBCriticalRoleBranchB P)
    (hQ : 1 < actualPrincipalIndex P.M.base) :
    nonsymmetricPrefixSlack R hQ =
      (Nat.card (L5A2C4I.ResidueData.CSourceTargetBranches (nonsymmetricPrefixRouting R hQ)) : ℤ)-
      Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases (nonsymmetricPrefixRouting R hQ))-
      Nat.card (FakeSink (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R)
        (routingHB _ _) (routingHC _ _)) := by
  let D := nonsymmetricPrefixRouting R hQ
  have hbalance := CombinatorialCore.ResidueData.edge_count_balance D.outgoing_edge_count D.incoming_edge_count
  have hb := L5A2C4J.ResidueData.branchCount_raw_decomposition D
  have hm := L5A2C4J.ResidueData.mergeCount_raw_decomposition D
  have hs := fullSinkCount_eq_actual_add_fake (nonsymmetricPrefixIdeal R hQ)
    (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)
  change D.sinkCount = L5A2C4H.actualSinkCount (nonsymmetricPrefixIdeal R hQ)
    (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)+
    fakeSinkCount (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R)
      (routingHB _ _) (routingHC _ _) at hs
  unfold L5A2C4J.ResidueData.exactUnusedMergeCount at hm
  rw [nonsymmetric_prefix_actual_sink_dictionary R hQ] at hs
  have hd := nonsymmetric_prefix_source_count_dictionary R hQ
  unfold nonsymmetricPrefixSlack
  dsimp only [D] at hbalance hb hm hs
  change _ = (L5A2C4I.ResidueData.sourceTargetBranchCount (nonsymmetricPrefixRouting R hQ) : ℤ)-_
    -fakeSinkCount (nonsymmetricPrefixIdeal R hQ) (nsA R) (nsB R) (nsC R) (routingHB _ _) (routingHC _ _)
  omega

theorem nonsymmetric_balanced_prefix_slack_bound (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1 < actualPrincipalIndex P.M.base)
    (hbal : NonsymmetricBalancedReturns R hB) :
    nonsymmetricPrefixSlack R hQ ≤ -(nonsymmetricFU R hB : ℤ) := by
  have hc := nonsymmetric_prefix_C_count_bound R hB hQ
  have hn := nonsymmetric_prefix_notch_coverage_bound R hB hQ hbal
  have hu := nonsymmetric_prefix_unused_count_ge_notches_FU R hB hQ hbal
  have he := nonsymmetric_prefix_fake_count_ge_two R hB hQ hbal
  have hs := nonsymmetric_prefix_raw_slack_identity R hQ
  omega

end NS25Lean.L5A2BFinalRepair
