import NS25Lean.P2SectorCAccounting

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C2

open L2B L2C L5A1

variable {Gamma : NumericalSemigroup}

/-- The full contribution-level content of the actual Sector-C witnesses.
No branch or return premise is added: every conclusion is derived from
`SectorC P.M` and the frozen P2 contribution formula. -/
theorem sectorC_actual_signature_data (P : P2Data Gamma) (hC : SectorC P.M) :
    ∃ h g : ℕ, h ≠ g ∧ positiveDegrees P.M = {h, g} ∧
      LocalSignature P.M h 2 0 ∧ LocalSignature P.M g 2 1 ∧
      fiberContribution P.M h = 1 ∧ fiberContribution P.M g = 1 ∧
      (∀ x : ℕ, x ≠ h → x ≠ g → fiberContribution P.M x = 0) := by
  classical
  obtain ⟨h, g, hne, hpositive, hh, hg⟩ := hC
  refine ⟨h, g, hne, hpositive, hh, hg,
    (p2_contribution_one_iff P h).mpr (Or.inl hh),
    (p2_contribution_one_iff P g).mpr (Or.inr hg), ?_⟩
  intro x hxh hxg
  apply contribution_zero_outside_positive
  simp [hpositive, hxh, hxg]

/-- The actual complete-intersection disjunct closes the requested bound.
The proof uses the kernel-verified equality `type = 1` and positivity of the
actual chosen-base source count. -/
theorem sectorC_type_le_sourceCount_of_completeIntersection
    (P : P2Data Gamma) (hCI : L4A.IsCompleteIntersectionFour P.M.base) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have ht := L4B.completeIntersectionFour_type_eq_one P.M.base hCI
  have hS := chosenBase_sourceCount_pos P.M.base
  rw [ht]
  exact hS

/-- A theorem-level, assumption-free exhaustion attached to the same actual
chosen base.  The first two disjuncts contain only already-defined monomial or
one-defect pivot predicates.  In the complete-intersection disjunct the target
is discharged immediately, so no CI membership is hidden in returned data. -/
theorem sectorC_actual_pivot_exhaustion (P : P2Data Gamma) (_hC : SectorC P.M) :
    (∃ i : Fin 4,
      ∀ (k : Type) [Field k], IsMonomialIdeal k ((atPivot P.M.base i).J k)) ∨
    (∃ i : Fin 4, chosenDefect (atPivot P.M.base i) = 1) ∨
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  rcases L4B.base_pivot_trichotomy P.M.base with hmono | hone | hCI
  · left
    obtain ⟨i, hi⟩ := hmono
    exact ⟨i, hi⟩
  · right; left
    obtain ⟨i, hi⟩ := hone
    exact ⟨i, hi⟩
  · right; right
    exact sectorC_type_le_sourceCount_of_completeIntersection P hCI

end NS25Lean.L5A2C2
