import NS25Lean.P2FiveSectorClosureR49

set_option linter.style.header false
set_option autoImplicit false

namespace NS25Lean.P2Strong

/-- P2-STRONG with the original multiplicity-base and defect-two hypotheses. -/
theorem p2_strong {Gamma : NumericalSemigroup} (M : L2B.MultiplicityBase Gamma)
    (hp : L2B.chosenDefect M.base = 2) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 :=
  L5A2R49.p2_type_le_rho_sub_two (L5A1.P2Data.mk M hp)

/-- The same original binder, retaining the source-count bound. -/
theorem p2_strong_sourceCount {Gamma : NumericalSemigroup} (M : L2B.MultiplicityBase Gamma)
    (hp : L2B.chosenDefect M.base = 2) :
    Gamma.asRelativeIdeal.idealType ≤ L2B.sourceCount M.base :=
  L5A2R49.p2_type_le_sourceCount (L5A1.P2Data.mk M hp)

/-- An existential defect-two multiplicity witness suffices; no canonical p is assumed. -/
theorem p2_strong_of_exists {Gamma : NumericalSemigroup}
    (hp : ∃ M : L2B.MultiplicityBase Gamma, L2B.chosenDefect M.base = 2) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  obtain ⟨M, hM⟩ := hp
  exact p2_strong M hM

/-- The existing four-tuple and multiplicity-pivot APIs provide an actual base. -/
theorem exists_multiplicityBase {Gamma : NumericalSemigroup}
    (he : CoarseP25.HasEmbeddingDimensionFour Gamma) :
    Nonempty (L2B.MultiplicityBase Gamma) := by
  obtain ⟨m, a, b, c, h⟩ := he
  exact ⟨L2B.asMultiplicityBase (ChosenBase.Data.ofFourTuple Gamma m a b c h 0)⟩

/-- Displayed four-generator interface, with defect measured at its actual multiplicity pivot. -/
theorem p2_strong_fourTuple {Gamma : NumericalSemigroup} (m a b c : ℕ)
    (h : FourGeneratedBridge.IsMinimallyGeneratedByFour Gamma m a b c)
    (hp : L2B.chosenDefect
      (L2B.asMultiplicityBase (ChosenBase.Data.ofFourTuple Gamma m a b c h 0)).base = 2) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 :=
  p2_strong (L2B.asMultiplicityBase (ChosenBase.Data.ofFourTuple Gamma m a b c h 0)) hp

end NS25Lean.P2Strong
