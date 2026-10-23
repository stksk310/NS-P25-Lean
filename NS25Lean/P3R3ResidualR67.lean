import NS25Lean.P3R3RBCompensationR67

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1 P3R61
variable {Gamma : NumericalSemigroup}

/-- NF.12: the no-full-support residual has an actual selected-role witness,
constructed from the same original Gamma, M and unchanged multiplicity. -/
theorem r3_residual_fresh (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (hR3 : (P3R51.internalDegrees M).card=3)
    (e : Fin 3 ≃ Fin 3)
    (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hn : ¬ PrincipalFullSupport M e) :
    ∃ f : Fin 3 ≃ Fin 3,
      letI : NeZero (routingA M.base f) := ⟨Nat.ne_of_gt (routingA_pos M.base f)⟩
      ResidueData.cExceptionalCount (routingData M.base f) ≤
        Nat.card (ResidueData.CFreshUnusedMergeBases (routingData M.base f))+1 := by
  obtain ⟨f,hH,hreturns,d,i,j,hl,htau,hprotect⟩ := residual_safe_rb_role M hp hR3 e hQ hn
  have hQf : 1<principalIndex (routingH M.base f) M.base.q.val M.base.q_positive := by
    rw [hH]
    exact hQ
  letI : NeZero (routingA M.base f) := ⟨Nat.ne_of_gt (routingA_pos M.base f)⟩
  have hlevels : ∀ q : ℕ, 0<q →
      q<principalIndex (routingH M.base f) M.base.q.val M.base.q_positive →
      ∃ x y d, RBLevel M hp f q x y d := by
    intro q hq hqQ
    exact rb_level_exists M hp f q (hreturns q hq hqQ)
  obtain ⟨D,hatt,hmax⟩ := exists_max_rb_depth M hp f ⟨1,i,j,d,by omega,hQf,hl⟩
  refine ⟨f,rb_fresh_of_protected M hp f hQf hlevels htau D hatt hmax ?_⟩
  exact hprotect D (hmax 1 i j d (by omega) hQf hl)

/-- Original residual type, using the same original R52 bridge. -/
theorem r3_residual_original_type (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (hR3 : (P3R51.internalDegrees M).card=3)
    (e : Fin 3 ≃ Fin 3)
    (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hn : ¬ PrincipalFullSupport M e) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma-2 := by
  exact P3R52Bridge.p3_strong_of_fresh_compensation M hp
    (r3_residual_fresh M hp hR3 e hQ hn)

end NS25Lean.P3R67
