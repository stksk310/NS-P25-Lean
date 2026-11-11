import NS25Lean.AppendixAPCR
import NS25Lean.EqualityLossAlgebra

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- The literal integer loss in the frozen support-refined monomial bound. -/
def delta_BPS (F : InternalFrontend k M h) : ℤ :=
  (L3A.mu F.initial.ideal : ℤ) + (L3A.q_fs F.initial.ideal : ℤ) - 2 -
    (L3A.quotientType F.initial.ideal : ℤ)

/-- The literal integer loss in the now-proved actual PCR. -/
def delta_PCR (F : InternalFrontend k M h) : ℤ :=
  F.delta3 - (F.delta1 + (L3A.q_fs F.initial.ideal : ℤ) - 1)

theorem delta_BPS_nonneg (F : InternalFrontend k M h) : 0 ≤ delta_BPS F := by
  have hb := L3A.support_refined_monomial_type_bound F.initial
  have hm := L3A.Staircase.main_count_add_two_le F.initial
  rw [← L3A.mu_eq_minimal_count F.initial.ideal F.initial.monomial] at hm
  unfold delta_BPS
  omega

theorem delta_PCR_nonneg (F : InternalFrontend k M h) : 0 ≤ delta_PCR F := by
  have hp := pcr F
  unfold delta_PCR
  omega

/-- Section 4's literal slack identity, with the actual source count and type. -/
theorem one_defect_slack_identity (F : InternalFrontend k M h) :
    (sourceCount M.base : ℤ) - (Gamma.asRelativeIdeal.idealType : ℤ) =
      delta_BPS F + delta_PCR F := by
  have hi := EqualityLossAlgebra.two_loss_identity
    ((sourceCount M.base : ℤ) + 1) (Gamma.asRelativeIdeal.idealType : ℤ)
    (L3A.mu F.initial.ideal : ℤ) (L3A.quotientType F.initial.ideal : ℤ)
    (L3A.q_fs F.initial.ideal : ℤ)
  calc
    (sourceCount M.base : ℤ) - (Gamma.asRelativeIdeal.idealType : ℤ) =
        ((sourceCount M.base : ℤ) + 1) - 1 - (Gamma.asRelativeIdeal.idealType : ℤ) := by omega
    _ = EqualityLossAlgebra.bpsLoss (L3A.mu F.initial.ideal)
          (L3A.quotientType F.initial.ideal) (L3A.q_fs F.initial.ideal) +
        EqualityLossAlgebra.compensationLoss ((sourceCount M.base : ℤ) + 1)
          (Gamma.asRelativeIdeal.idealType : ℤ) (L3A.mu F.initial.ideal)
          (L3A.quotientType F.initial.ideal) (L3A.q_fs F.initial.ideal) := hi
    _ = delta_BPS F + delta_PCR F := by
      unfold EqualityLossAlgebra.bpsLoss EqualityLossAlgebra.compensationLoss
        EqualityLossAlgebra.typeLoss EqualityLossAlgebra.generatorLoss
        delta_BPS delta_PCR InternalFrontend.delta1 InternalFrontend.delta3
      ring

theorem internal_type_le_sourceCount (F : InternalFrontend k M h) :
    Gamma.asRelativeIdeal.idealType ≤ sourceCount M.base := by
  have hB := delta_BPS_nonneg F
  have hP := delta_PCR_nonneg F
  have he := one_defect_slack_identity F
  omega

/-- The same literal identity after the frozen actual dilation transfer is undone. -/
theorem chosen_one_defect_slack_identity (B : Data Gamma) (hp : chosenDefect B = 1)
    {d : ℕ} (F : InternalFrontend k (transferBase B) d) :
    (sourceCount B : ℤ) - (Gamma.asRelativeIdeal.idealType : ℤ) =
      delta_BPS F + delta_PCR F := by
  have ht := one_defect_transfer k B hp
  have he := one_defect_slack_identity F
  rw [ht.2.2.2.2.1, ht.2.2.2.2.2.1] at he
  exact he

/-- Both actual frontend branches close at the original chosen source count. -/
theorem chosen_one_defect_type_le_sourceCount (B : Data Gamma) (hp : chosenDefect B = 1) :
    Gamma.asRelativeIdeal.idealType ≤ sourceCount B := by
  obtain ⟨d, _, _, hb | hi, hmono, hinternal⟩ := chosen_one_defect_frontend ℚ B hp
  · exact (hmono hb).2.1
  · obtain ⟨F⟩ := hinternal hi
    have he := chosen_one_defect_slack_identity B hp F
    have hB := delta_BPS_nonneg F
    have hP := delta_PCR_nonneg F
    omega

/-- Section 4's one-defect theorem for an arbitrary actual chosen generator. -/
theorem chosen_one_defect_type_bound (B : Data Gamma) (hp : chosenDefect B = 1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 1 := by
  have ht := chosen_one_defect_type_le_sourceCount B hp
  rw [one_defect_sourceCount B hp] at ht
  exact ht

/-- Paper-facing existential chosen-pivot form of the one-defect theorem. -/
theorem one_defect_type_bound
    (hp : ∃ B : Data Gamma, chosenDefect B = 1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 1 := by
  obtain ⟨B, hB⟩ := hp
  exact chosen_one_defect_type_bound B hB

end NS25Lean.L3C
