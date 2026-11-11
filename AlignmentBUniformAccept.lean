import NS25Lean.P2BranchBPrefixHeightClosure
import NS25Lean.P2BranchBSymmetricSmallQ

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The actual Q=2 consumer is the uniform prefix/principal route. -/
example (A : SectorBCriticalRoleBranchA P) (hB : SectorB P.M)
    (hQ : actualPrincipalIndex P.M.base=2) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount :=
  symmetric_Q_gt_one_actual_type_le_sourceCount_uniform A hB (by omega)

/-- No BAL, arm choice or Q≥3 guard is present in the actual input. -/
example (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (hQ : 1<actualPrincipalIndex P.M.base) (x y : ℕ) :
    nonsymmetricPrefixDiagramHeight R hB hQ x y=
      BranchBUniformMinPlus.height (nonsymmetricUniformMinPlusData R hB hQ) x y :=
  nonsymmetric_prefix_height_eq_uniform R hB hQ x y

-- The exact old public interfaces remain elaboratable.
#check symmetric_prefix_C_targets_F
#check symmetric_prefix_resource_bounds
#check symmetric_prefix_socle_plus_two_le_actual_sourceCount
#check symmetric_Q_two_actual_type_le_sourceCount
#check symmetric_Q_ge_three_actual_type_le_sourceCount
#check symmetric_actual_type_le_sourceCount
#check nonsymmetric_prefix_diagram_add_b
#check nonsymmetric_prefix_diagram_add_c
#check nonsymmetric_prefix_height_formula

#print axioms BranchBUniformMinPlus.generator_closure
#print axioms BranchBUniformMinPlus.height_zero_iff
#print axioms nonsymmetric_prefix_height_eq_uniform
#print axioms nonsymmetric_prefix_height_formula
#print axioms symmetric_Q_gt_one_actual_type_le_sourceCount_uniform
#print axioms symmetric_actual_type_le_sourceCount

-- These compact proof terms expose the actual final route for review.
#print nonsymmetric_prefix_diagram_outer_b
#print nonsymmetric_prefix_diagram_height_lt_c1
#print symmetric_actual_type_le_sourceCount
#print symmetric_Q_gt_one_actual_type_le_sourceCount_uniform

end NS25Lean.L5A2BFinalRepair
