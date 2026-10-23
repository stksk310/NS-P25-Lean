import NS25Lean.P3R1TypeR65

set_option linter.style.header false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.P3R66
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- Conditional Q=1 shortcut, with the literal original R3 binders. -/
theorem r3_q1_original_type (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (_hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3)
    (hQ : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive = 1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  exact P3R64.q1_original_type_le_rho_sub_two M hp e hQ

/-- All three original active degrees are internal in R3. -/
theorem r3_internal_eq_positive (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3) :
    P3R51.internalDegrees M = positiveDegrees M := by
  apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
  change (positiveDegrees M).card ≤ (P3R51.internalDegrees M).card
  rw [hR3, P3R51.positiveDegrees_card M hp]

/-- Every physical critical predecessor is live, for each of the actual axes. -/
theorem r3_all_axes_live (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (i k : Fin 3) :
    criticalExponent M.base i * weights M.base i - weights M.base k ∈ M.base.apery := by
  have hin : (P3R55.axisIndex M hp i).val ∈ P3R51.internalDegrees M := by
    rw [r3_internal_eq_positive M hp hR3, ← P3R51.active_eq_positive M hp]
    exact (P3R55.axisIndex M hp i).property
  rw [← P3R55.axisIndex_degree M hp i]
  let R := P3R55.axisRole M hp i
  by_cases hki : k = i
  · obtain ⟨u, hu, he⟩ := P3R55.role_pure_representative R
    apply P3R57.internal_predecessor_apery M hin u k
    simpa [he, R, hki] using (criticalExponent_spec M.base i).1
  · apply P3R57.internal_predecessor_apery M hin R.witness k
    apply P3R55.role_witness_positive R k
    simpa [R] using hki

end NS25Lean.P3R66
