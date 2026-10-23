import NS25Lean.WeightedInitialEquality
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.RingTheory.MvPolynomial.Ideal

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase MvPolynomial
open scoped MonomialOrder
variable {Gamma : NumericalSemigroup}

/-- A synonym whose order is pulled back from weight-first lexicographic pairs. -/
def WeightedOrderSyn (_B : Data Gamma) (_m : MonomialOrder (Fin 3)) := Fin 3 →₀ ℕ

instance (B : Data Gamma) (m : MonomialOrder (Fin 3)) :
    AddCommMonoid (WeightedOrderSyn B m) := inferInstanceAs (AddCommMonoid (Fin 3 →₀ ℕ))

def weightedOrderKey (B : Data Gamma) (m : MonomialOrder (Fin 3))
    (u : WeightedOrderSyn B m) : Lex (ℕ × m.syn) :=
  toLex (weight B u, m.toSyn u)

theorem weightedOrderKey_injective (B : Data Gamma) (m : MonomialOrder (Fin 3)) :
    Function.Injective (weightedOrderKey B m) := by
  intro u v h
  exact m.toSyn.injective (congrArg (fun z => (ofLex z).2) h)

instance (B : Data Gamma) (m : MonomialOrder (Fin 3)) :
    LinearOrder (WeightedOrderSyn B m) :=
  LinearOrder.lift' (weightedOrderKey B m) (weightedOrderKey_injective B m)

theorem weightedOrder_le_iff (B : Data Gamma) (m : MonomialOrder (Fin 3))
    (u v : WeightedOrderSyn B m) :
    u ≤ v ↔ weight B u < weight B v ∨
      weight B u = weight B v ∧ m.toSyn u ≤ m.toSyn v := by
  exact Prod.Lex.toLex_le_toLex

set_option backward.isDefEq.respectTransparency false in
instance (B : Data Gamma) (m : MonomialOrder (Fin 3)) :
    IsOrderedAddMonoid (WeightedOrderSyn B m) where
  add_le_add_left a b h c := by
    rw [weightedOrder_le_iff] at h ⊢
    rw [(weight B).map_add a c, (weight B).map_add b c,
      m.toSyn.map_add a c, m.toSyn.map_add b c]
    simpa only [add_lt_add_iff_right, add_left_inj, add_le_add_iff_right] using h

instance (B : Data Gamma) (m : MonomialOrder (Fin 3)) :
    WellFoundedLT (WeightedOrderSyn B m) :=
  ⟨InvImage.wf (weightedOrderKey B m) wellFounded_lt⟩

/-- Actual admissible, well-founded, additive weight-first refinement. -/
def weightRefinement (B : Data Gamma) (m : MonomialOrder (Fin 3)) :
    MonomialOrder (Fin 3) where
  syn := WeightedOrderSyn B m
  toSyn := { toEquiv := Equiv.refl _, map_add' := fun _ _ => rfl }
  toSyn_monotone := by
    intro u v huv
    rw [weightedOrder_le_iff]
    have hw : weight B u ≤ weight B v := by
      rw [← add_tsub_cancel_of_le huv, map_add]
      exact Nat.le_add_right _ _
    rcases lt_or_eq_of_le hw with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, m.toSyn_monotone huv⟩

theorem weightRefinement_le_iff (B : Data Gamma) (m : MonomialOrder (Fin 3))
    (u v : Fin 3 →₀ ℕ) :
    u ≼[weightRefinement B m] v ↔ weight B u < weight B v ∨
      weight B u = weight B v ∧ u ≼[m] v :=
  weightedOrder_le_iff B m u v

theorem weightRefinement_lt_iff (B : Data Gamma) (m : MonomialOrder (Fin 3))
    (u v : Fin 3 →₀ ℕ) :
    u ≺[weightRefinement B m] v ↔ weight B u < weight B v ∨
      weight B u = weight B v ∧ u ≺[m] v := by
  exact Prod.Lex.toLex_lt_toLex

def monomialInitialIdeal (k : Type*) [Field k] (m : MonomialOrder (Fin 3))
    (I : Ideal (MvPolynomial (Fin 3) k)) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span (m.leadingTerm '' (I : Set _))

end NS25Lean.L2B
