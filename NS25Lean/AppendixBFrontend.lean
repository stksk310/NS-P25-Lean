import NS25Lean.AppendixBAsymmetric
import NS25Lean.AppendixBCompleteIntersection

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C
variable {Gamma : NumericalSemigroup}

/-- Appendix B's terminal positive-load interface, on the original family and
an actual original pivot, with algebraic complete-intersection evidence. -/
theorem positive_load_interface (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) :
    (∃ i : Fin 4, L2B.chosenDefect (atPivot B i) = 1) ∨ IsCompleteIntersectionFour B := by
  by_cases hone : (purePairDegrees B).card ≤ 1
  · exact Or.inl (zero_or_one_purePair_protected B hpos hone)
  have htwo : (purePairDegrees B).card = 2 := by
    have := purePairDegrees_card_le_two B hpos
    omega
  obtain ⟨N⟩ := normalizedPairs_exists B hpos htwo
  rcases lt_trichotomy N.a N.b with hlt | heq | hgt
  · exact Or.inl ⟨N.perm 0, N.asymmetric_zero_protected hpos hlt⟩
  · exact Or.inr (symmetric_complete_intersection N heq)
  · exact Or.inl ⟨N.perm 1, N.asymmetric_one_protected hpos hgt⟩

/-- The same terminal alternative with its proved rho consequence; the CI payload is retained. -/
theorem positive_load_interface_with_rho (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) :
    (∃ i : Fin 4, L2B.chosenDefect (atPivot B i) = 1) ∨
      (IsCompleteIntersectionFour B ∧ Presentation.rho Gamma = 3) := by
  rcases positive_load_interface B hpos with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, completeIntersectionFour_rho h⟩

end NS25Lean.L4A
