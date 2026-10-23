import NS25Lean.CompleteIntersectionType
import NS25Lean.AppendixBFrontend
import NS25Lean.MonomialEngineClosure
import NS25Lean.AppendixAFrontend

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4B
open ChosenBase L2C FourGeneratedBridge

variable {Gamma : NumericalSemigroup}

/-- Every chosen four-generator base has an actual monomial pivot, an actual
one-defect pivot, or the complete-intersection payload from Appendix B. -/
theorem base_pivot_trichotomy (B : Data Gamma) :
    (∃ i : Fin 4, ∀ (k : Type) [Field k],
      L2B.IsMonomialIdeal k ((atPivot B i).J k)) ∨
    (∃ i : Fin 4, L2B.chosenDefect (atPivot B i) = 1) ∨
    L4A.IsCompleteIntersectionFour B := by
  by_cases hz : ∃ i : Fin 4, internalLoad B i = 0
  · obtain ⟨i, hi⟩ := hz
    exact Or.inl ⟨i, fun k _ => every_pivot_monomial k B i hi⟩
  · have hpos : ∀ i : Fin 4, 0 < internalLoad B i := by
      intro i
      have hne : internalLoad B i ≠ 0 := fun hi => hz ⟨i, hi⟩
      omega
    rcases L4A.positive_load_interface B hpos with hp | hCI
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr hCI)

/-- The complete-intersection branch satisfies the sharp inequality strictly. -/
theorem completeIntersectionFour_type_lt_rho_sub_one (B : Data Gamma)
    (hCI : L4A.IsCompleteIntersectionFour B) :
    Gamma.asRelativeIdeal.idealType < Presentation.rho Gamma - 1 := by
  have ht := completeIntersectionFour_type_eq_one B hCI
  have hrho := L4A.completeIntersectionFour_rho hCI
  omega

/-- Data-level NS-SHARP, obtained by applying the corresponding frozen engine
in each branch of the base-pivot trichotomy. -/
theorem ns_sharp_data (B : Data Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 1 := by
  rcases base_pivot_trichotomy B with hmono | hone | hCI
  · obtain ⟨i, hi⟩ := hmono
    exact L3A.monomial_pivot_type_bound (k := ℚ) (atPivot B i) (hi ℚ)
  · obtain ⟨i, hi⟩ := hone
    exact L3C.chosen_one_defect_type_bound (atPivot B i) hi
  · exact Nat.le_of_lt (completeIntersectionFour_type_lt_rho_sub_one B hCI)

/-- The base-pivot trichotomy for a displayed minimal four-tuple, using its
zero-th generator as the initial chosen pivot. -/
theorem fourTuple_base_pivot_trichotomy (Gamma : NumericalSemigroup)
    (m a b c : ℕ) (h : IsMinimallyGeneratedByFour Gamma m a b c) :
    (∃ i : Fin 4, ∀ (k : Type) [Field k],
      L2B.IsMonomialIdeal k
        ((atPivot (Data.ofFourTuple Gamma m a b c h 0) i).J k)) ∨
    (∃ i : Fin 4,
      L2B.chosenDefect (atPivot (Data.ofFourTuple Gamma m a b c h 0) i) = 1) ∨
    L4A.IsCompleteIntersectionFour (Data.ofFourTuple Gamma m a b c h 0) :=
  base_pivot_trichotomy (Data.ofFourTuple Gamma m a b c h 0)

/-- A minimally four-generated semigroup admits actual chosen-base data with
the full monomial/one-defect/complete-intersection trichotomy. -/
theorem embeddingDimensionFour_base_pivot_trichotomy (Gamma : NumericalSemigroup)
    (he : CoarseP25.HasEmbeddingDimensionFour Gamma) :
    ∃ B : Data Gamma,
      ((∃ i : Fin 4, ∀ (k : Type) [Field k],
        L2B.IsMonomialIdeal k ((atPivot B i).J k)) ∨
      (∃ i : Fin 4, L2B.chosenDefect (atPivot B i) = 1) ∨
      L4A.IsCompleteIntersectionFour B) := by
  obtain ⟨m, a, b, c, h⟩ := he
  let B := Data.ofFourTuple Gamma m a b c h 0
  exact ⟨B, base_pivot_trichotomy B⟩

/-- NS-SHARP for every numerical semigroup of embedding dimension four. -/
theorem ns_sharp (Gamma : NumericalSemigroup)
    (he : CoarseP25.HasEmbeddingDimensionFour Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 1 := by
  obtain ⟨m, a, b, c, h⟩ := he
  exact ns_sharp_data (Data.ofFourTuple Gamma m a b c h 0)

end NS25Lean.L4B
