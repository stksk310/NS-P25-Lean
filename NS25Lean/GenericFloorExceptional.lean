import NS25Lean.GenericFloorSentinel

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericFloorStaircase
open CombinatorialCore L5A2C4I
variable {H : NumericalSemigroup}

/-- Among an arbitrary floor antichain (including points on either axis),
an actual c-exceptional target has the least first coordinate. -/
theorem c_exceptional_has_least_first (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) (Imax Jmax : ℕ)
    (R : CanonicalRectangle I a b c Imax Jmax) (S : Finset (ℕ × ℕ))
    (hanti : ∀ p ∈ S, ∀ q ∈ S, q.1 ≤ p.1 → q.2 ≤ p.2 → p = q)
    (hbounds : ∀ p ∈ S, p.1 < Imax ∧ p.2 < Jmax)
    (hfloor : ∀ i j : ℕ, i < Imax → j < Jmax →
      ((i : ℤ) * b + j * c ∈ I ↔ ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j))
    (s : ResidueData.CExceptionalBranches (P3R60.idealData I a b c hb hc))
    (p : ℕ × ℕ) (hp : p ∈ S)
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val.val) =
      ((p.1 * b + p.2 * c : ℕ) : ℤ)) : ∀ q ∈ S, p.1 ≤ q.1 := by
  intro q hq
  by_contra hn
  have hx : q.1 < p.1 := by omega
  have hy : p.2 < q.2 := by
    by_contra hn'
    have he := hanti p hp q hq hx.le (by omega)
    have he' := congrArg Prod.fst he
    omega
  exact s.property (c_nonexceptional_of_earlier_floor I a b c hb hc Imax Jmax R S hfloor
    s.val p.1 p.2 q.1 q.2 (hbounds p hp).1 (hbounds q hq).2 hq hx hy ht)

/-- The literal b counterpart has the greatest first coordinate, equivalently
the least second coordinate of a strictly ordered floor antichain. -/
theorem b_exceptional_has_greatest_first (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) (Imax Jmax : ℕ)
    (R : CanonicalRectangle I a b c Imax Jmax) (S : Finset (ℕ × ℕ))
    (hanti : ∀ p ∈ S, ∀ q ∈ S, q.1 ≤ p.1 → q.2 ≤ p.2 → p = q)
    (hbounds : ∀ p ∈ S, p.1 < Imax ∧ p.2 < Jmax)
    (hfloor : ∀ i j : ℕ, i < Imax → j < Jmax →
      ((i : ℤ) * b + j * c ∈ I ↔ ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j))
    (s : ResidueData.BExceptionalBranches (P3R60.idealData I a b c hb hc))
    (p : ℕ × ℕ) (hp : p ∈ S)
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val.val) =
      ((p.1 * b + p.2 * c : ℕ) : ℤ)) : ∀ q ∈ S, q.1 ≤ p.1 := by
  intro q hq
  by_contra hn
  have hx : p.1 < q.1 := by omega
  have hy : q.2 < p.2 := by
    by_contra hn'
    have he := hanti q hq p hp hx.le (by omega)
    have he' := congrArg Prod.fst he
    omega
  exact s.property (b_nonexceptional_of_later_floor I a b c hb hc Imax Jmax R S hfloor
    s.val p.1 p.2 q.1 q.2 (hbounds p hp).2 (hbounds q hq).1 hq hx hy ht)

end NS25Lean.GenericFloorStaircase

#print axioms NS25Lean.GenericFloorStaircase.c_exceptional_has_least_first
#print axioms NS25Lean.GenericFloorStaircase.b_exceptional_has_greatest_first
