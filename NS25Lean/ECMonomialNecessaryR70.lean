import NS25Lean.MonomialEngineClosure
import NS25Lean.ECZeroDefectR70
import NS25Lean.AppendixAOneDefect

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.EC.R70
open ChosenBase L2B L3A
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]

/-- The integer support-refined loss, using actual minimal generator and socle counts. -/
def monomialTopSlack (B : Data Gamma) : ℤ :=
  (mu (B.J k) : ℤ) + (q_fs (B.J k) : ℤ) - 2 - (quotientType (B.J k) : ℤ)

theorem monomialTopSlack_nonneg (B : Data Gamma) (hJ : IsMonomialIdeal k (B.J k)) :
    0 ≤ monomialTopSlack (k := k) B := by
  let A := chosenArtinianMonomial B MonomialOrder.degLex hJ
  have hb := support_refined_monomial_type_bound A
  have hm := Staircase.main_count_add_two_le A
  rw [← mu_eq_minimal_count A.ideal A.monomial] at hm
  change quotientType (B.J k) ≤ mu (B.J k) + q_fs (B.J k) - 2 at hb
  change _ + 2 ≤ mu (B.J k) at hm
  unfold monomialTopSlack
  omega

/-- EQ-M numerical slack decomposition; no Scarf/Tor interpretation is claimed. -/
theorem monomial_slack_identity (B : Data Gamma) :
    (Presentation.rho Gamma : ℤ) - 1 - (Gamma.asRelativeIdeal.idealType : ℤ) =
      monomialTopSlack (k := k) B + (1 - (q_fs (B.J k) : ℤ)) := by
  have hi := EqualityLossAlgebra.two_loss_identity
    (Presentation.rho Gamma : ℤ) (Gamma.asRelativeIdeal.idealType : ℤ)
    (mu (B.J k) : ℤ) (quotientType (B.J k) : ℤ) (q_fs (B.J k) : ℤ)
  unfold monomialTopSlack EqualityLossAlgebra.bpsLoss
    EqualityLossAlgebra.compensationLoss EqualityLossAlgebra.typeLoss
    EqualityLossAlgebra.generatorLoss at *
  rw [chosen_mu_eq, chosen_type_eq] at *
  simpa only [sub_self, sub_zero, zero_sub, neg_add_eq_sub] using hi

/-- Genuine q_fs=1 necessity for a monomial equality pivot, not a sufficiency claim. -/
theorem equality_monomial_qfs_one (B : Data Gamma) (hJ : IsMonomialIdeal k (B.J k))
    (he : Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1) :
    q_fs (B.J k) = 1 := by
  have hq := chosen_q_fs_le_one B MonomialOrder.degLex hJ
  have hs := monomialTopSlack_nonneg B hJ
  have hm := Staircase.main_count_add_two_le (chosenArtinianMonomial B MonomialOrder.degLex hJ)
  change (Staircase.mainGenerators (B.J k)).ncard + 2 ≤ (minimalExponents (B.J k)).ncard at hm
  rw [← mu_eq_minimal_count (B.J k) hJ, chosen_mu_eq] at hm
  have hi := monomial_slack_identity (k := k) B
  omega

/-- Both numerical monomial losses vanish under original semigroup equality. -/
theorem equality_monomial_slack_zero (B : Data Gamma) (hJ : IsMonomialIdeal k (B.J k))
    (he : Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1) :
    monomialTopSlack (k := k) B = 0 := by
  have hq := equality_monomial_qfs_one B hJ he
  have hm := Staircase.main_count_add_two_le (chosenArtinianMonomial B MonomialOrder.degLex hJ)
  change (Staircase.mainGenerators (B.J k)).ncard + 2 ≤ (minimalExponents (B.J k)).ncard at hm
  rw [← mu_eq_minimal_count (B.J k) hJ, chosen_mu_eq] at hm
  have hi := monomial_slack_identity (k := k) B
  omega

theorem equality_p0_qfs_one (B : Data Gamma) (hp : chosenDefect B = 0)
    (he : Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1) :
    q_fs (B.J k) = 1 :=
  equality_monomial_qfs_one B (p0_automon k B hp) he

/-- Unique-tie equality forces both actual integer losses zero, including q_fs=0.
This is only the numerical intermediate, not the structural EQ.UNIQUE criterion. -/
theorem unique_tie_equality_slacks {M : MultiplicityBase Gamma} {d : ℕ}
    (F : L3B.InternalFrontend k M d) :
    Gamma.asRelativeIdeal.idealType = sourceCount M.base ↔
      L3C.delta_BPS F = 0 ∧ L3C.delta_PCR F = 0 := by
  have hB := L3C.delta_BPS_nonneg F
  have hP := L3C.delta_PCR_nonneg F
  have hi := L3C.one_defect_slack_identity F
  omega

end NS25Lean.EC.R70
