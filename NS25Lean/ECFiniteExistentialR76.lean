import NS25Lean.ECFiniteWitnessesR76
import NS25Lean.BasePivotSharp

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.EC.R75
open ChosenBase L2C
variable {Gamma : NumericalSemigroup}

/-- The existential original-pivot criterion uses the sharp trichotomy, not F2 or F3. -/
theorem equality_iff_some_original_certificate (B : ChosenBase.Data Gamma) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      ∃ i : Fin 4, PivotCertificate (atPivot B i) := by
  constructor
  · intro he
    rcases L4B.base_pivot_trichotomy B with hmono | hone | hCI
    · obtain ⟨i,hi⟩ := hmono
      exact ⟨i,Or.inl ((monomial_finite_iff (atPivot B i) (hi ℚ)).mp he)⟩
    · obtain ⟨i,hi⟩ := hone
      exact ⟨i,(defect_one_finite_iff (atPivot B i) hi).mp he⟩
    · have hstrict := L4B.completeIntersectionFour_type_lt_rho_sub_one B hCI
      omega
  · rintro ⟨i,h⟩
    exact pivot_certificate_implies_equality (atPivot B i) h

/-- Reverse implication for any supplied original pivot and its actual witness. -/
theorem original_pivot_certificate_implies_equality (B : ChosenBase.Data Gamma)
    (i : Fin 4) (h : PivotCertificate (atPivot B i)) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 :=
  pivot_certificate_implies_equality (atPivot B i) h

end NS25Lean.EC.R75
