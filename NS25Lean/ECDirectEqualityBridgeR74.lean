import NS25Lean.ECDirectStaircaseR74
import NS25Lean.ECMonomialNecessaryR70

set_option autoImplicit false
noncomputable section
namespace NS25Lean.EC.R74
open L3A L3A.Staircase ChosenBase L2B
variable {Gamma : NumericalSemigroup}

theorem monomial_equality_iff_certificate (B : Data Gamma)
    (hJ : IsMonomialIdeal ℚ (B.J ℚ)) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      q_fs (B.J ℚ) = 1 ∧
        (mainGenerators (B.J ℚ)).ncard + 2 = (minimalExponents (B.J ℚ)).ncard ∧
        Function.Surjective (tag (B.J ℚ)) := by
  let A := chosenArtinianMonomial B MonomialOrder.degLex hJ
  have he := bps_slack_zero_iff_tag_saturation A
  change R70.monomialTopSlack (k := ℚ) B = 0 ↔ TagSaturation (B.J ℚ) at he
  have hs := R70.monomial_slack_identity (k := ℚ) B
  constructor
  · intro h
    have hq := R70.equality_monomial_qfs_one B hJ h
    have hz := R70.equality_monomial_slack_zero B hJ h
    exact ⟨hq,(he.mp hz).1,(he.mp hz).2⟩
  · rintro ⟨hq,hg,ht⟩
    have hz := he.mpr ⟨hg,ht⟩
    omega

theorem unique_tie_bps_zero_iff_certificate {M : MultiplicityBase Gamma} {d : ℕ}
    (F : L3B.InternalFrontend ℚ M d) :
    L3C.delta_BPS F = 0 ↔ TagSaturation F.initial.ideal :=
  bps_slack_zero_iff_tag_saturation F.initial

/-- No q_fs=1 premise is introduced in the unique-tie branch. -/
theorem unique_tie_equality_iff_certificate {M : MultiplicityBase Gamma} {d : ℕ}
    (F : L3B.InternalFrontend ℚ M d) :
    Gamma.asRelativeIdeal.idealType = sourceCount M.base ↔
      TagSaturation F.initial.ideal ∧ L3C.delta_PCR F = 0 := by
  rw [R70.unique_tie_equality_slacks F,unique_tie_bps_zero_iff_certificate F]

/-- The actual Ferrers survivor set and actual minimal surviving-wrap count. -/
def PCRCountCertificate {M : MultiplicityBase Gamma} {d : ℕ}
    (F : L3B.InternalFrontend ℚ M d) (G : L3C.NormalizedSources F) : Prop :=
  ((L3C.planarMaxD F G ∩ L3C.planarE F G).ncard : ℤ) =
    (L3C.survivingWraps F G).ncard + (q_fs F.initial.ideal : ℤ) - 1

theorem pcr_zero_iff_survivor_count {M : MultiplicityBase Gamma} {d : ℕ}
    (F : L3B.InternalFrontend ℚ M d) (G : L3C.NormalizedSources F) :
    L3C.delta_PCR F = 0 ↔ PCRCountCertificate F G := by
  have hs := L3C.artificial_socle_formula F G
  have hw := L3C.survivingWraps_card_eq_delta1 F G
  unfold PCRCountCertificate L3C.delta_PCR
  omega

theorem unique_tie_equality_iff_finite_counts {M : MultiplicityBase Gamma} {d : ℕ}
    (F : L3B.InternalFrontend ℚ M d) (G : L3C.NormalizedSources F) :
    Gamma.asRelativeIdeal.idealType = sourceCount M.base ↔
      Function.Surjective (tag F.initial.ideal) ∧ PCRCountCertificate F G := by
  rw [unique_tie_equality_iff_certificate F,tag_saturation_iff_surjective F.initial,
    pcr_zero_iff_survivor_count F G]

/-- Rewrite the actual one-defect source count to the original NS-SHARP target. -/
theorem unique_tie_ns_sharp_iff_finite_counts {M : MultiplicityBase Gamma} {d : ℕ}
    (F : L3B.InternalFrontend ℚ M d) (G : L3C.NormalizedSources F) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      Function.Surjective (tag F.initial.ideal) ∧ PCRCountCertificate F G := by
  rw [← L3B.one_defect_sourceCount M.base F.one_defect]
  exact unique_tie_equality_iff_finite_counts F G

theorem unique_tie_qfs_zero_survivor_count {M : MultiplicityBase Gamma} {d : ℕ}
    (F : L3B.InternalFrontend ℚ M d) (G : L3C.NormalizedSources F)
    (hq : q_fs F.initial.ideal = 0) :
    L3C.delta_PCR F = 0 ↔
      (0 < (L3C.survivingWraps F G).ncard ∧
        (L3C.planarMaxD F G ∩ L3C.planarE F G).ncard + 1 =
          (L3C.survivingWraps F G).ncard) := by
  rw [pcr_zero_iff_survivor_count F G]
  unfold PCRCountCertificate
  rw [hq]
  omega

theorem unique_tie_qfs_one_survivor_count {M : MultiplicityBase Gamma} {d : ℕ}
    (F : L3B.InternalFrontend ℚ M d) (G : L3C.NormalizedSources F)
    (hq : q_fs F.initial.ideal = 1) :
    L3C.delta_PCR F = 0 ↔
      (L3C.planarMaxD F G ∩ L3C.planarE F G).ncard =
        (L3C.survivingWraps F G).ncard := by
  rw [pcr_zero_iff_survivor_count F G]
  unfold PCRCountCertificate
  rw [hq]
  omega

end NS25Lean.EC.R74
