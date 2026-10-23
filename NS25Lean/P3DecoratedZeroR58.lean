import NS25Lean.P3ActualReturnZeroR58

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R58
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4OR1 L5A2C4OR3 L5A2C4OR4
variable {Gamma : NumericalSemigroup}

/-- A strict RB return has no exact zero on any canonical point in the critical rectangle.
This is a candidate equation, not an exhaustion theorem for prefix sources. -/
theorem actual_rb_canonical_zero_exclusion (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n s t d i j : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hd : 0 < d) (hdu : d < P3R57.roleCoefficient M hp e 1 0)
    (hbeta : ((P3R57.roleCoefficient M hp e 0 1 + s : ℕ) : ℤ) * routingB M.base e +
      t * routingC M.base e = n * M.base.q.val + d * routingA M.base e)
    (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hcan : IsCanonicalTailGridPoint M.base e i j) :
    rawCandidate M.base e n (gridResidue M.base e i j) ≠ 0 := by
  intro hz
  obtain ⟨I, J, he⟩ := rawCandidate_zero_signed_relation M hp e n
    (P3R57.roleCoefficient M hp e 0 1 + s) t d i j hbeta hcan hz
  have hsum := p3_coefficient_sums M hp e
  have hv := p3_coefficients_positive M hp e 1 2 (by decide)
  rcases actual_signed_rb_cones M hp e d _ _ hd hdu he with h | h
  · simp only [Nat.cast_add] at h
    omega
  · simp only [Nat.cast_add] at h
    omega

/-- The LT counterpart on the same actual semigroup and physical role. -/
theorem actual_lt_canonical_zero_exclusion (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n s t d i j : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hd : 0 < d) (hdw : d < P3R57.roleCoefficient M hp e 2 0)
    (hbeta : (s : ℤ) * routingB M.base e +
      ((P3R57.roleCoefficient M hp e 0 2 + t : ℕ) : ℤ) * routingC M.base e =
        n * M.base.q.val + d * routingA M.base e)
    (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hcan : IsCanonicalTailGridPoint M.base e i j) :
    rawCandidate M.base e n (gridResidue M.base e i j) ≠ 0 := by
  intro hz
  obtain ⟨I, J, he⟩ := rawCandidate_zero_signed_relation M hp e n s
    (P3R57.roleCoefficient M hp e 0 2 + t) d i j hbeta hcan hz
  have hsum := p3_coefficient_sums M hp e
  have hzpos := p3_coefficients_positive M hp e 2 1 (by decide)
  rcases actual_signed_lt_cones M hp e d _ _ hd hdw he with h | h
  · simp only [Nat.cast_add] at h
    omega
  · simp only [Nat.cast_add] at h
    omega

/-- Literal marker locations and bounded ranges from Appendix E, lines 751--826.
This predicate specifies coordinates only; it asserts no source or run classification. -/
def DecoratedTailBase (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (i j : ℕ) : Prop :=
  (i = P3R57.roleCoefficient M hp e 0 1 - 1 ∧
    ∃ t < P3R57.roleCoefficient M hp e 1 2,
      j = P3R57.roleCoefficient M hp e 0 2 + t) ∨
  (i = criticalExponent M.base (e 1) - 1 ∧
    j < P3R57.roleCoefficient M hp e 0 2) ∨
  (i < P3R57.roleCoefficient M hp e 0 1 ∧
    j = criticalExponent M.base (e 2) - 1) ∨
  ((∃ x < P3R57.roleCoefficient M hp e 2 1,
      i = P3R57.roleCoefficient M hp e 0 1 + x) ∧
    j = P3R57.roleCoefficient M hp e 0 2 - 1)

theorem decoratedTailBase_canonical (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i j : ℕ)
    (h : DecoratedTailBase M hp e i j) :
    i < criticalExponent M.base (e 1) ∧ j < criticalExponent M.base (e 2) ∧
      IsCanonicalTailGridPoint M.base e i j := by
  have hsum := p3_coefficient_sums M hp e
  have hp0 := p3_coefficients_positive M hp e 0 1 (by decide)
  have hq0 := p3_coefficients_positive M hp e 0 2 (by decide)
  have hv0 := p3_coefficients_positive M hp e 1 2 (by decide)
  have hz0 := p3_coefficients_positive M hp e 2 1 (by decide)
  have hb : i < criticalExponent M.base (e 1) ∧
      j < criticalExponent M.base (e 2) ∧
      (i < P3R57.roleCoefficient M hp e 0 1 ∨
        j < P3R57.roleCoefficient M hp e 0 2) := by
    rcases h with ⟨hi, t, ht, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨⟨x, hx, hi⟩, hj⟩ <;> omega
  exact ⟨hb.1, hb.2.1, p3_lshape_canonical M hp e i j hb.1 hb.2.1 hb.2.2⟩

/-- All four RB decorated candidates excluded with actual routing representatives. -/
theorem rb_decorated_zero_excluded (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n s t d i j : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hd : 0 < d) (hdu : d < P3R57.roleCoefficient M hp e 1 0)
    (hbeta : ((P3R57.roleCoefficient M hp e 0 1 + s : ℕ) : ℤ) * routingB M.base e +
      t * routingC M.base e = n * M.base.q.val + d * routingA M.base e)
    (hmarker : DecoratedTailBase M hp e i j) :
    rawCandidate M.base e n (gridResidue M.base e i j) ≠ 0 := by
  obtain ⟨hi, hj, hc⟩ := decoratedTailBase_canonical M hp e i j hmarker
  exact actual_rb_canonical_zero_exclusion M hp e n s t d i j hs ht hd hdu hbeta hi hj hc

/-- All four LT decorated candidates excluded with actual routing representatives. -/
theorem lt_decorated_zero_excluded (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n s t d i j : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hd : 0 < d) (hdw : d < P3R57.roleCoefficient M hp e 2 0)
    (hbeta : (s : ℤ) * routingB M.base e +
      ((P3R57.roleCoefficient M hp e 0 2 + t : ℕ) : ℤ) * routingC M.base e =
        n * M.base.q.val + d * routingA M.base e)
    (hmarker : DecoratedTailBase M hp e i j) :
    rawCandidate M.base e n (gridResidue M.base e i j) ≠ 0 := by
  obtain ⟨hi, hj, hc⟩ := decoratedTailBase_canonical M hp e i j hmarker
  exact actual_lt_canonical_zero_exclusion M hp e n s t d i j hs ht hd hdw hbeta hi hj hc

end NS25Lean.P3R58
