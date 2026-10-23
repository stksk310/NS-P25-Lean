import NS25Lean.P3R2DirectTypeR63

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R64
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- The actual normalized Q=1 shortcut is independent of the internal-degree count. -/
theorem q1_original_type_le_rho_sub_two (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hQ : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive = 1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  exact P3R57.type_of_selected_exceptional_le_one M hp e
    (P3R63.routing_cExceptional_le_one_of_principal_index_one M e hQ)

/-- Q=1 is the same-role principal ideal, with one actual minimal generator. -/
theorem q1_routing_generatorCount (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (hQ : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive = 1) :
    (routingI M.base e).generatorCount = 1 := by
  rw [P3R62.routingI_eq_principal_translate_of_index_one M.base e hQ,
    RelativeIdeal.generatorCount_translate,P3R54.identity_generatorCount]

end NS25Lean.P3R64
