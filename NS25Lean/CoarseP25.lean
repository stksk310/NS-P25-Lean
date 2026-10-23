import NS25Lean.TailMonomialGenerators

set_option linter.style.header false

/-!
# JoA Section 2: coarse P25 with the displayed algebraic rho

Here the right-hand side is the generator number of the actual four-variable
toric ideal. No identification with `Presentation.rho` is used in this module.
-/

namespace NS25Lean.CoarseP25
open FourGeneratedBridge ToricPresentation

/-- Source-faithful coarse P25 for every field and every displayed minimal four-tuple. -/
theorem fourGenerated_coarseP25_toric (k : Type*) [Field k]
    (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    Gamma.asRelativeIdeal.idealType ≤
      2 * toricGeneratorNumber k Gamma.toAddSubmonoid (fourDegrees Gamma m n₁ n₂ n₃ h) :=
  (fourGenerated_bound_after_normalization Gamma m n₁ n₂ n₃ h).trans
    (Nat.mul_le_mul_left 2
      (fourGenerated_tailGeneratorCount_le_toricGeneratorNumber k Gamma m n₁ n₂ n₃ h))

/-- Existence of an ordinary minimal four-generator presentation. -/
def HasEmbeddingDimensionFour (Gamma : NumericalSemigroup) : Prop :=
  ∃ m n₁ n₂ n₃, IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃

/-- A small existential paper interface: the bound holds for a displayed presentation
of every numerical semigroup of embedding dimension four. -/
theorem exists_fourGenerated_coarseP25_toric (k : Type*) [Field k]
    (Gamma : NumericalSemigroup) (he : HasEmbeddingDimensionFour Gamma) :
    ∃ m n₁ n₂ n₃, ∃ h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃,
      Gamma.asRelativeIdeal.idealType ≤
        2 * toricGeneratorNumber k Gamma.toAddSubmonoid (fourDegrees Gamma m n₁ n₂ n₃ h) := by
  obtain ⟨m, n₁, n₂, n₃, h⟩ := he
  exact ⟨m, n₁, n₂, n₃, h, fourGenerated_coarseP25_toric k Gamma m n₁ n₂ n₃ h⟩

end NS25Lean.CoarseP25
