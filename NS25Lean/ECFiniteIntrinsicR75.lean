import NS25Lean.ECFiniteWitnessesR76
import NS25Lean.ECPivotRestrictionR70

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.EC.R75
open ChosenBase L2B L3A
variable {Gamma : NumericalSemigroup}

def FiniteEqualityCertificate (M : L2B.MultiplicityBase Gamma) : Prop :=
  (L2B.chosenDefect M.base = 0 ∧ MonomialFiniteCertificate M.base) ∨
  (L2B.chosenDefect M.base = 1 ∧
    (MonomialFiniteCertificate M.base ∨ OneTieFiniteCertificate M.base))

theorem chosen_pivot_finite_equality_iff (B : ChosenBase.Data Gamma) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      (L2B.chosenDefect B = 0 ∧ MonomialFiniteCertificate B) ∨
      (L2B.chosenDefect B = 1 ∧
        (MonomialFiniteCertificate B ∨ OneTieFiniteCertificate B)) := by
  constructor
  · intro he
    rcases R70.equality_pivot_defect_zero_or_one B he with h0 | h1
    · exact Or.inl ⟨h0,(monomial_finite_iff B (R70.p0_automon ℚ B h0)).mp he⟩
    · exact Or.inr ⟨h1,(defect_one_finite_iff B h1).mp he⟩
  · rintro (⟨_,hm⟩ | ⟨h1,hc⟩)
    · exact monomial_certificate_implies_equality B hm
    · exact (defect_one_finite_iff B h1).mpr hc

/-- No extra hypothesis; Gamma and the multiplicity base M are the originals. -/
theorem finite_intrinsic_equality_iff (Gamma : NumericalSemigroup)
    (M : L2B.MultiplicityBase Gamma) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      FiniteEqualityCertificate M :=
  chosen_pivot_finite_equality_iff M.base

end NS25Lean.EC.R75
