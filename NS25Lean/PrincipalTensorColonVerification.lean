import NS25Lean.P2BranchBMixedSurgery

set_option linter.style.header false
open NS25Lean
open NS25Lean.PrincipalTensorColon
open NS25Lean.PrincipalTensorColonNegativeControl

#check GradedPresentation
#check principal_tensor_cut_socle_gain_le_two
#check principal_tensor_cut_type_minus_sources
#check mixed_corner_count_le_comparison_rank
#check tensor_poly_operator_packet
#check L5A2BFinalRepair.nonsymmetric_principal_socle_gain_le_two
#check L5A2BFinalRepair.symmetric_principal_socle_gain_le_two

example : Nat.card {n // socle oldIdeal n}=2 := actual_old_type
example : Nat.card {n // socle newIdeal n}=4 := actual_new_type
example : Nat.card {n // source oldIdeal n ∧ 40≤n ∧ inH (n-40)}=1 := actual_erasure_count
example : ¬ ((Nat.card {n // socle newIdeal n}:ℤ)-Nat.card {n // socle oldIdeal n} ≤
    2-Nat.card {n // source oldIdeal n ∧ 40≤n ∧ inH (n-40)}) := actual_overstrong_bound_false

#print axioms principal_tensor_cut_socle_gain_le_two
#print axioms principal_tensor_cut_type_minus_sources
#print axioms L5A2BFinalRepair.nonsymmetric_principal_algebraic_socle_gain_le_two
#print axioms L5A2BFinalRepair.symmetric_principal_algebraic_socle_gain_le_two
#print axioms L5A2BFinalRepair.nonsymmetric_principal_socle_gain_le_two
#print axioms L5A2BFinalRepair.symmetric_principal_socle_gain_le_two
#print axioms actual_overstrong_bound_false
#print axioms H_generated
#print axioms gamma_normalization
