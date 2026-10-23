import NS25Lean.P3R3FullSupportR67
import NS25Lean.P3R3ResidualR67

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- NF.14/TW.13: all cases, on the same original semigroup and multiplicity. -/
theorem r3_fresh_compensation (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3) :
    ∃ e : Fin 3 ≃ Fin 3,
      letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      ResidueData.cExceptionalCount (routingData M.base e) ≤
        Nat.card (ResidueData.CFreshUnusedMergeBases (routingData M.base e)) + 1 := by
  let e : Fin 3 ≃ Fin 3 := Equiv.refl _
  have hpos := (principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive).1
  by_cases hQ : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive = 1
  · exact ⟨e, r3_q1_fresh M e hQ⟩
  have hQgt : 1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive := by omega
  by_cases hfull : PrincipalFullSupport M e
  · exact ⟨e, fullSupport_fresh M hp hR3 e hQgt hfull⟩
  · exact r3_residual_fresh M hp hR3 e hQgt hfull

/-- The original R3 type target through the frozen, same-M R52 bridge. -/
theorem r3_original_type_le_rho_sub_two (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  exact P3R52Bridge.p3_strong_of_fresh_compensation M hp (r3_fresh_compensation M hp hR3)

end NS25Lean.P3R67
