import NS25Lean.ActiveFiberGlobalIdentity

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A2
open NS25Lean.L2B ChosenBase
variable {Gamma : NumericalSemigroup}

/-- MUJ is used only after the independent actual-quotient calculation is closed. -/
theorem chosenDefect_eq_contribution_sum (M : MultiplicityBase Gamma) :
    chosenDefect M.base = ∑ h ∈ activeDegreeFinset M, fiberContribution M h := by
  have he := active_fiber_mu_identity ℚ M
  rw [M.base.muj ℚ] at he
  unfold chosenDefect
  rw [he, Nat.add_sub_cancel_left]

/-- Unconditional multiplicity-base bound; the combinatorial budget is frozen. -/
theorem multiplicity_chosenDefect_le_three (M : MultiplicityBase Gamma) :
    chosenDefect M.base ≤ 3 :=
  defect_range_of_contribution_identity M (chosenDefect_eq_contribution_sum M)

/-- The source's natural-number structural range interface. -/
theorem multiplicity_chosenDefect_range (M : MultiplicityBase Gamma) :
    0 ≤ chosenDefect M.base ∧ chosenDefect M.base ≤ 3 :=
  ⟨Nat.zero_le _, multiplicity_chosenDefect_le_three M⟩

/-- The same range in integers, with the subtraction guarded by the exact identity. -/
theorem multiplicity_integer_defect_range (M : MultiplicityBase Gamma) :
    0 ≤ (Presentation.rho Gamma : ℤ) - (sourceCount M.base : ℤ) ∧
      (Presentation.rho Gamma : ℤ) - (sourceCount M.base : ℤ) ≤ 3 := by
  have he := active_fiber_mu_identity ℚ M
  rw [M.base.muj ℚ] at he
  have hb := multiplicity_chosenDefect_le_three M
  have hs := chosenDefect_eq_contribution_sum M
  omega

end NS25Lean.L2B2A2
