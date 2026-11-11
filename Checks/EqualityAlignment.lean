import NS25Lean.ECFiniteAllPivotsR75
import NS25Lean.ECFiniteExistentialR76
import Mathlib.Algebra.Field.ZMod

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

#check NS25Lean.EqualityLossAlgebra.two_loss_identity
#check NS25Lean.L3A.Staircase.tag_injective_of_spec
#check NS25Lean.EC.R75.PivotCertificate
#check NS25Lean.EC.R75.one_tie_certificate_defect_one
#check NS25Lean.EC.R75.one_tie_certificate_implies_equality_unconditional
#check NS25Lean.EC.R75.equality_iff_some_original_certificate
#check NS25Lean.EC.R75.pivot_certificate_iff_guarded

example {k : Type*} [Field k] (A : NS25Lean.L3A.ArtinianMonomial k) :
    NS25Lean.L3A.quotientType A.ideal + 2 =
      NS25Lean.L3A.mu A.ideal + NS25Lean.L3A.q_fs A.ideal ↔
      Function.Surjective (NS25Lean.L3A.Staircase.tag A.ideal) :=
  NS25Lean.EC.R74.bps_equality_iff_surjective A

example (A : NS25Lean.L3A.ArtinianMonomial (ZMod 2)) :
    NS25Lean.L3A.quotientType A.ideal + 2 =
      NS25Lean.L3A.mu A.ideal + NS25Lean.L3A.q_fs A.ideal ↔
      Function.Surjective (NS25Lean.L3A.Staircase.tag A.ideal) :=
  NS25Lean.EC.R74.bps_equality_iff_surjective A

example {k : Type*} [Field k] (A : NS25Lean.L3A.ArtinianMonomial k)
    (f : NS25Lean.L3A.socleExponents A.ideal → NS25Lean.L3A.Staircase.Tags A.ideal)
    (hf : ∀ p,
      NS25Lean.L3A.Staircase.tagExponent A.ideal (f p) 2 =
        NS25Lean.L3A.Staircase.birth A.ideal p ∧
      NS25Lean.L3A.Staircase.tagExponent A.ideal (f p)
          (NS25Lean.L3A.Staircase.tagCoordinate A.ideal (f p)) =
        p.val (NS25Lean.L3A.Staircase.tagCoordinate A.ideal (f p)) + 1) :
    NS25Lean.L3A.quotientType A.ideal + 2 =
      NS25Lean.L3A.mu A.ideal + NS25Lean.L3A.q_fs A.ideal ↔ Function.Surjective f :=
  NS25Lean.EC.R74.bps_equality_iff_surjective_of_spec A f hf

example (N W : ℕ) :
    (N : ℤ) = (W : ℤ) + 0 - 1 ↔ 0 < W ∧ N + 1 = W :=
  NS25Lean.EqualityLossAlgebra.count_qfs_zero_iff N W

example (N W : ℕ) : (N : ℤ) = (W : ℤ) + 1 - 1 ↔ N = W :=
  NS25Lean.EqualityLossAlgebra.count_qfs_one_iff N W

example (N : ℕ) : ¬ ((N : ℤ) = (0 : ℤ) + 0 - 1) :=
  NS25Lean.EqualityLossAlgebra.count_qfs_zero_wrap_zero_impossible N

example : (0 : ℤ) = (1 : ℤ) + 0 - 1 := by norm_num
example : (0 : ℤ) = (0 : ℤ) + 1 - 1 := by norm_num

example {Gamma : NS25Lean.NumericalSemigroup}
    {M : NS25Lean.L2B.MultiplicityBase Gamma} {d : ℕ}
    (F : NS25Lean.L3B.InternalFrontend ℚ M d) (G : NS25Lean.L3C.NormalizedSources F)
    (hq : NS25Lean.L3A.q_fs F.initial.ideal = 0) :
    NS25Lean.EC.R74.PCRCountCertificate F G ↔
      0 < (NS25Lean.L3C.survivingWraps F G).ncard ∧
        (NS25Lean.L3C.planarMaxD F G ∩ NS25Lean.L3C.planarE F G).ncard + 1 =
          (NS25Lean.L3C.survivingWraps F G).ncard :=
  NS25Lean.EC.R74.pcr_count_qfs_zero_iff F G hq

example {Gamma : NS25Lean.NumericalSemigroup}
    {M : NS25Lean.L2B.MultiplicityBase Gamma} {d : ℕ}
    (F : NS25Lean.L3B.InternalFrontend ℚ M d) (G : NS25Lean.L3C.NormalizedSources F)
    (hq : NS25Lean.L3A.q_fs F.initial.ideal = 1) :
    NS25Lean.EC.R74.PCRCountCertificate F G ↔
      (NS25Lean.L3C.planarMaxD F G ∩ NS25Lean.L3C.planarE F G).ncard =
        (NS25Lean.L3C.survivingWraps F G).ncard :=
  NS25Lean.EC.R74.pcr_count_qfs_one_iff F G hq

example {Gamma : NS25Lean.NumericalSemigroup}
    {M : NS25Lean.L2B.MultiplicityBase Gamma} {d : ℕ}
    (F : NS25Lean.L3B.InternalFrontend ℚ M d) (G : NS25Lean.L3C.NormalizedSources F)
    (hq : NS25Lean.L3A.q_fs F.initial.ideal = 0)
    (hw : (NS25Lean.L3C.survivingWraps F G).ncard = 0) :
    0 < NS25Lean.L3C.delta_PCR F ∧
      ¬ NS25Lean.EC.R74.PCRCountCertificate F G ∧
      Gamma.asRelativeIdeal.idealType ≠ NS25Lean.Presentation.rho Gamma - 1 :=
  ⟨NS25Lean.EC.R74.qfs_zero_wrap_zero_pcr_loss_pos F G hq hw,
    NS25Lean.EC.R74.pcr_count_qfs_zero_wrap_zero_impossible F G hq hw,
    NS25Lean.EC.R74.qfs_zero_wrap_zero_not_equality F G hq hw⟩

example {Gamma : NS25Lean.NumericalSemigroup} (B : NS25Lean.ChosenBase.Data Gamma)
    (h : NS25Lean.EC.R75.OneTieFiniteCertificate B) :
    NS25Lean.L2B.chosenDefect B = 1 ∧
      Gamma.asRelativeIdeal.idealType = NS25Lean.Presentation.rho Gamma - 1 :=
  ⟨NS25Lean.EC.R75.one_tie_certificate_defect_one B h,
    NS25Lean.EC.R75.one_tie_certificate_implies_equality_unconditional B h⟩

example {Gamma : NS25Lean.NumericalSemigroup} (B : NS25Lean.ChosenBase.Data Gamma)
    (hp : NS25Lean.L2B.chosenDefect B = 1) :
    ((NS25Lean.L3B.transferSemigroup B).asRelativeIdeal.idealType =
      NS25Lean.Presentation.rho (NS25Lean.L3B.transferSemigroup B) - 1) ↔
      Gamma.asRelativeIdeal.idealType = NS25Lean.Presentation.rho Gamma - 1 :=
  NS25Lean.EC.R75.one_defect_equality_transfer B (hp := hp)

example {Gamma : NS25Lean.NumericalSemigroup} (B : NS25Lean.ChosenBase.Data Gamma) :
    Gamma.asRelativeIdeal.idealType = NS25Lean.Presentation.rho Gamma - 1 ↔
      ∃ i : Fin 4, NS25Lean.EC.R75.PivotCertificate (NS25Lean.L2C.atPivot B i) :=
  NS25Lean.EC.R75.equality_iff_some_original_certificate B

example {Gamma : NS25Lean.NumericalSemigroup} (B : NS25Lean.ChosenBase.Data Gamma) :
    NS25Lean.EC.R75.PivotCertificate B ↔
      NS25Lean.EC.R75.FiniteEqualityCertificate (NS25Lean.L3B.transferBase B) :=
  (NS25Lean.EC.R75.pivot_certificate_iff_guarded B).trans
    (NS25Lean.EC.R75.pivot_certificate_iff_transferred_certificate B)

#print NS25Lean.EC.R75.MonomialFiniteCertificate
#print NS25Lean.EC.R75.OneTieFiniteCertificate
#print NS25Lean.EC.R74.PCRCountCertificate
#print axioms NS25Lean.EqualityLossAlgebra.two_loss_identity
#print axioms NS25Lean.EqualityLossAlgebra.two_loss_saturation_iff
#print axioms NS25Lean.L3A.Staircase.tag_injective_of_spec
#print axioms NS25Lean.EC.R74.two_loss_equality_iff
#print axioms NS25Lean.EC.R75.one_tie_certificate_implies_equality_unconditional
#print axioms NS25Lean.EC.R75.equality_iff_some_original_certificate
#print axioms NS25Lean.EC.R75.pivot_certificate_iff_guarded
