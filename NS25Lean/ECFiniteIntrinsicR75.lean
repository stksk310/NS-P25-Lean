import NS25Lean.ECDirectEqualityBridgeR74
import NS25Lean.OneDefectFrontend
import NS25Lean.ECPivotRestrictionR70

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.EC.R75
open ChosenBase L2B L3A
variable {Gamma : NumericalSemigroup}

def MonomialFiniteCertificate (B : ChosenBase.Data Gamma) : Prop :=
  L2B.IsMonomialIdeal ℚ (B.J ℚ) ∧ q_fs (B.J ℚ) = 1 ∧
    Function.Surjective (Staircase.tag (B.J ℚ))

def OneTieFiniteCertificate (B : ChosenBase.Data Gamma) : Prop :=
  ∃ d : ℕ, ∃ F : L3B.InternalFrontend ℚ (L3B.transferBase B) d,
    ∃ G : L3C.NormalizedSources F,
      Function.Surjective (Staircase.tag F.initial.ideal) ∧ R74.PCRCountCertificate F G

def FiniteEqualityCertificate (M : L2B.MultiplicityBase Gamma) : Prop :=
  (L2B.chosenDefect M.base = 0 ∧ MonomialFiniteCertificate M.base) ∨
  (L2B.chosenDefect M.base = 1 ∧
    (MonomialFiniteCertificate M.base ∨ OneTieFiniteCertificate M.base))

theorem monomial_finite_iff (B : ChosenBase.Data Gamma)
    (hJ : IsMonomialIdeal ℚ (B.J ℚ)) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      MonomialFiniteCertificate B := by
  have hc := R74.main_count_add_two_eq (chosenArtinianMonomial B MonomialOrder.degLex hJ)
  constructor
  · intro he
    have h := (R74.monomial_equality_iff_certificate B hJ).mp he
    exact ⟨hJ,h.1,h.2.2⟩
  · rintro ⟨_,hq,hs⟩
    exact (R74.monomial_equality_iff_certificate B hJ).mpr ⟨hq,hc,hs⟩

theorem monomial_certificate_implies_equality (B : ChosenBase.Data Gamma)
    (h : MonomialFiniteCertificate B) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 :=
  (monomial_finite_iff B h.1).mpr h

/-- The transferred semigroup is a proof object; the right side remains original. -/
theorem one_defect_equality_transfer (B : ChosenBase.Data Gamma)
    (hp : L2B.chosenDefect B = 1) :
    ((L3B.transferSemigroup B).asRelativeIdeal.idealType =
      Presentation.rho (L3B.transferSemigroup B) - 1) ↔
      Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 := by
  have ht := L3B.one_defect_transfer ℚ B hp
  rw [ht.2.2.2.1,ht.2.2.2.2.1]

theorem one_tie_certificate_implies_equality (B : ChosenBase.Data Gamma)
    (hp : L2B.chosenDefect B = 1) (h : OneTieFiniteCertificate B) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 := by
  obtain ⟨d,F,G,hc⟩ := h
  exact (one_defect_equality_transfer B hp).mp
    ((R74.unique_tie_ns_sharp_iff_finite_counts F G).mpr hc)

theorem defect_one_finite_iff (B : ChosenBase.Data Gamma)
    (hp : L2B.chosenDefect B = 1) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      MonomialFiniteCertificate B ∨ OneTieFiniteCertificate B := by
  constructor
  · intro he
    obtain ⟨d,hh,hz,hsplit,hm,hi⟩ := L3B.chosen_one_defect_frontend ℚ B hp
    rcases hsplit with hb | ht
    · left
      have hJ := (hm hb).1
      rw [(L3B.one_defect_transfer ℚ B hp).2.2.1] at hJ
      exact (monomial_finite_iff B hJ).mp he
    · right
      obtain ⟨F⟩ := hi ht
      obtain ⟨G⟩ := L3C.normalized_sources_exist F
      exact ⟨d,F,G,(R74.unique_tie_ns_sharp_iff_finite_counts F G).mp
        ((one_defect_equality_transfer B hp).mpr he)⟩
  · rintro (hm | ht)
    · exact monomial_certificate_implies_equality B hm
    · exact one_tie_certificate_implies_equality B hp ht

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
