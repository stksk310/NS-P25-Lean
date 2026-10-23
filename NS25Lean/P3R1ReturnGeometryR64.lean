import NS25Lean.P3R1SignatureR64
import NS25Lean.P3CommonArmR59

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R64
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4OR5 L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- The b/c swap retains the actual normalized semigroup and its principal index. -/
theorem routingH_swapBC (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingH B (P3R57.swapRole e) = routingH B e := by
  have extH : ∀ H K : NumericalSemigroup, H.toAddSubmonoid = K.toAddSubmonoid → H = K := by
    intro H K h
    cases H; cases K; cases h; rfl
  apply extH
  ext x
  change x ∈ generatedThree (routingA B (P3R57.swapRole e))
    (routingB B (P3R57.swapRole e)) (routingC B (P3R57.swapRole e)) ↔
    x ∈ generatedThree (routingA B e) (routingB B e) (routingC B e)
  simp only [P3R57.routingA_swap, P3R57.routingB_swap, P3R57.routingC_swap,
    generatedThree, Set.pair_comm]

theorem normalizedRoleWeight_swapBC (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    P3R59.normalizedRoleWeight B (P3R57.swapRole e) ((Equiv.swap 1 2) i) =
      P3R59.normalizedRoleWeight B e i := by
  fin_cases i <;> simp [P3R59.normalizedRoleWeight, Equiv.swap_apply_def]

/-- With a fully live first axis, both other critical fibers miss every nonprincipal return. -/
theorem nonprincipal_boundary_predecessors_absent (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (axis : Fin 3) (haxis : axis ≠ 0) (r : ℕ) (hr : 0 < r)
    (hrq : r < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (i : Fin 3) :
    ((criticalExponent M.base (e axis)*P3R59.normalizedRoleWeight M.base e axis-
      P3R59.normalizedRoleWeight M.base e i : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (r*M.base.q.val) := by
  fin_cases axis
  · exact False.elim (haxis rfl)
  · have hlive' : ∀ k : Fin 3,
        criticalExponent M.base (P3R57.swapRole e 0)*weights M.base (P3R57.swapRole e 0)-
          weights M.base k ∈ M.base.apery := by simpa using hlive
    have hrq' : r < principalIndex (routingH M.base (P3R57.swapRole e))
        M.base.q.val M.base.q_positive := by rwa [routingH_swapBC]
    have h := P3R59.nonprincipal_critical_predecessors_absent M hp
      (P3R57.swapRole e) hlive' r hr hrq' ((Equiv.swap 1 2) i)
    rw [routingH_swapBC, normalizedRoleWeight_swapBC] at h
    change ((criticalExponent M.base (e 1)*routingB M.base e-
      P3R59.normalizedRoleWeight M.base e i : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (r*M.base.q.val)
    simpa only [P3R57.swapRole_two, P3R57.routingC_swap] using h
  · exact P3R59.nonprincipal_critical_predecessors_absent M hp e hlive r hr hrq i

/-- Original R1 supplies the checked first-live/third-boundary binder of the common-arm theorem. -/
theorem r1_oneArmPrefix_exists (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR1 : (P3R51.internalDegrees M).card = 1) :
    ∃ e : Fin 3 ≃ Fin 3, P3R59.OneArmPrefix M hp e := by
  obtain ⟨e, _, hlive, hother⟩ := r1_legal_internal_role M hp hR1
  exact ⟨e, P3R59.oneArmPrefix_of_legal_role M hp e ((hother 2 (by decide)).1).2 hlive⟩

/-- Common-arm and both nonprincipal predecessor barriers hold in the same actual R1 role. -/
theorem r1_common_arm_and_barriers (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR1 : (P3R51.internalDegrees M).card = 1) :
    ∃ e : Fin 3 ≃ Fin 3,
      (∀ k : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
        weights M.base k ∈ M.base.apery) ∧
      (∀ axis : Fin 3, axis ≠ 0 →
        killedCount M (criticalExponent M.base (e axis)*weights M.base (e axis)) = 1) ∧
      P3R59.OneArmPrefix M hp e ∧
      (∀ axis : Fin 3, axis ≠ 0 → ∀ r : ℕ, 0 < r →
        r < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
        ∀ i : Fin 3,
          ((criticalExponent M.base (e axis)*P3R59.normalizedRoleWeight M.base e axis-
            P3R59.normalizedRoleWeight M.base e i : ℕ) : ℤ) ∉
            returnIdeal (routingH M.base e) (r*M.base.q.val)) := by
  obtain ⟨e, _, hlive, hother⟩ := r1_legal_internal_role M hp hR1
  refine ⟨e, hlive, fun axis ha => ((hother axis ha).1).2,
    P3R59.oneArmPrefix_of_legal_role M hp e ((hother 2 (by decide)).1).2 hlive, ?_⟩
  intro axis ha r hr hrq i
  exact nonprincipal_boundary_predecessors_absent M hp e hlive axis ha r hr hrq i

end NS25Lean.P3R64
