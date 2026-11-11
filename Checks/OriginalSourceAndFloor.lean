import NS25Lean.OriginalSourceFibers
import NS25Lean.OriginalPivotStrictBounds
import NS25Lean.GenericFloorSentinel

set_option autoImplicit false
noncomputable section
open NS25Lean

/-- Interface check at a freely supplied original pivot and coefficient field. -/
example {Gamma : NumericalSemigroup} (k : Type*) [Field k]
    (B : ChosenBase.Data Gamma) (hp : L2B.chosenDefect B=1)
    (hn : ¬L2B.IsMonomialIdeal k (B.J k)) :
    ∃ d : ℕ, ∃ N : L3B.TieNormalForm B d,
      (∀ s : L2B2A2.Source B, ∀ u v : L2B.FactorizationFiber B s.val,
        L3C.TiePath N u.val v.val) ∧
      (∀ s : L2B2A2.Source B, ∃! u : L2B.FactorizationFiber B s.val,
        u.val (N.perm 0)<N.a) :=
  OriginalSourceFibers.nonmonomial_original_source_law B hp hn

example {Gamma : NumericalSemigroup} (B : ChosenBase.Data Gamma)
    (hp : L2B.chosenDefect B=2) :
    Gamma.asRelativeIdeal.idealType≤L2B.sourceCount B :=
  OriginalPivotStrictBounds.p2_original_source_bound B hp

example {Gamma : NumericalSemigroup} (B : ChosenBase.Data Gamma)
    (hp : L2B.chosenDefect B=3) :
    Gamma.asRelativeIdeal.idealType≤L2B.sourceCount B+1 :=
  OriginalPivotStrictBounds.p3_original_source_bound B hp

#check GenericFloorStaircase.floor_staircase_family
#check GenericFloorStaircase.sentinel_bound
#check GenericFloorStaircase.c_nonexceptional_of_earlier_floor
#check GenericFloorStaircase.b_nonexceptional_of_later_floor
#print axioms OriginalSourceFibers.nonmonomial_original_source_chains
#print axioms OriginalSourceFibers.nonmonomial_original_source_binomials
#print axioms GenericFloorStaircase.sentinel_bound
#print axioms GenericFloorStaircase.c_nonexceptional_of_earlier_floor
#print axioms GenericFloorStaircase.b_nonexceptional_of_later_floor
