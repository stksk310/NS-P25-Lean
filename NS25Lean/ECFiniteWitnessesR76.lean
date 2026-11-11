import NS25Lean.ECDirectEqualityBridgeR74
import NS25Lean.OneDefectFrontend

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

/-- The unguarded finite certificate contains actual witness conditions, not equality. -/
def PivotCertificate (B : ChosenBase.Data Gamma) : Prop :=
  MonomialFiniteCertificate B ∨ OneTieFiniteCertificate B

/-- General transfer invariants are available before either stronger bound. -/
theorem arbitrary_pivot_transfer_invariants_field (k : Type*) [Field k]
    (B : ChosenBase.Data Gamma) :
    (L3B.transferBase B).base.q.val = B.q.val ∧
    IsMultiplicity (L3B.transferBase B).base ∧
    (L3B.transferBase B).base.J k = B.J k ∧
    Presentation.rho (L3B.transferSemigroup B) = Presentation.rho Gamma ∧
    (L3B.transferSemigroup B).asRelativeIdeal.idealType = Gamma.asRelativeIdeal.idealType ∧
    sourceCount (L3B.transferBase B).base = sourceCount B ∧
    L2B.chosenDefect (L3B.transferBase B).base = L2B.chosenDefect B := by
  have ht := dilation_transfer B (L3B.transferScale B) (L3B.transferScale_gt B)
    (L3B.transferScale_coprime B)
  exact ⟨rfl,ht.1,dilatedData_J k B (L3B.transferScale B) (L3B.transferScale_gt B)
    (L3B.transferScale_coprime B),ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2⟩

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

/-- Equality transports by invariants, without a defect premise or witness identification. -/
theorem arbitrary_pivot_equality_transfer (B : ChosenBase.Data Gamma) :
    ((L3B.transferSemigroup B).asRelativeIdeal.idealType =
      Presentation.rho (L3B.transferSemigroup B) - 1) ↔
      Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 := by
  have ht := arbitrary_pivot_transfer_invariants_field ℚ B
  rw [ht.2.2.2.1,ht.2.2.2.2.1]

/-- Compatibility endpoint for the historical one-defect transfer interface. -/
theorem one_defect_equality_transfer (B : ChosenBase.Data Gamma)
    (hp : L2B.chosenDefect B = 1) :
    ((L3B.transferSemigroup B).asRelativeIdeal.idealType =
      Presentation.rho (L3B.transferSemigroup B) - 1) ↔
      Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 := by
  have ht := L3B.one_defect_transfer ℚ B hp
  rw [ht.2.2.2.1,ht.2.2.2.2.1]

/-- The actual frontend already supplies defect one; it is not an added certificate field. -/
theorem one_tie_certificate_defect_one (B : ChosenBase.Data Gamma)
    (h : OneTieFiniteCertificate B) : L2B.chosenDefect B = 1 := by
  obtain ⟨d,F,G,hc⟩ := h
  have ht := arbitrary_pivot_transfer_invariants_field ℚ B
  exact ht.2.2.2.2.2.2.symm.trans F.one_defect

theorem one_tie_certificate_implies_equality (B : ChosenBase.Data Gamma)
    (hp : L2B.chosenDefect B = 1) (h : OneTieFiniteCertificate B) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 := by
  obtain ⟨d,F,G,hc⟩ := h
  exact (one_defect_equality_transfer B hp).mp
    ((R74.unique_tie_ns_sharp_iff_finite_counts F G).mpr hc)

theorem one_tie_certificate_implies_equality_unconditional (B : ChosenBase.Data Gamma)
    (h : OneTieFiniteCertificate B) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 :=
  one_tie_certificate_implies_equality B (one_tie_certificate_defect_one B h) h

/-- Any actual certificate at any original pivot suffices. -/
theorem pivot_certificate_implies_equality (B : ChosenBase.Data Gamma)
    (h : PivotCertificate B) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 := by
  rcases h with hm | ht
  · exact monomial_certificate_implies_equality B hm
  · exact one_tie_certificate_implies_equality_unconditional B ht

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

end NS25Lean.EC.R75
