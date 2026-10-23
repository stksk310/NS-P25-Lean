import NS25Lean.P3R3SignatureR66

set_option linter.style.header false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.P3R66
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open L5A2C4OR3 L5A2C4OR4
variable {Gamma : NumericalSemigroup}

/-- Same-level canonical returns have the same actual coordinates and defect. -/
theorem canonical_return_unique (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (q i j d i' j' d' : ℕ)
    (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hc : IsCanonicalTailGridPoint M.base e i j)
    (hc' : IsCanonicalTailGridPoint M.base e i' j')
    (he : (i : ℤ)*routingB M.base e+j*routingC M.base e =
      q*M.base.q.val+d*routingA M.base e)
    (he' : (i' : ℤ)*routingB M.base e+j'*routingC M.base e =
      q*M.base.q.val+d'*routingA M.base e) : i=i' ∧ j=j' ∧ d=d' := by
  have h := P3R60.return_point_eq_of_canonical M.base e q _ d
    (P3R60.canonical_grid_value M.base e i j hc) he
  have h' := P3R60.return_point_eq_of_canonical M.base e q _ d'
    (P3R60.canonical_grid_value M.base e i' j' hc') he'
  obtain ⟨hij, hjj⟩ := P3R61.subcritical_bc_factorization_unique M.base e i j i' j'
    hi hj (h.1.symm.trans h'.1)
  refine ⟨hij,hjj,?_⟩
  exact_mod_cast h.2.symm.trans h'.2

/-- The two strict arms are mutually exclusive at a fixed actual level. -/
theorem strict_arms_disjoint (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (q : ℕ) :
    ¬ (P3R59.RBReturn M hp e q ∧ P3R59.LTReturn M hp e q) := by
  rintro ⟨⟨s,t,d,hs,hsZ,ht,htT,hd,hdU,he⟩,
    ⟨s',t',d',hs',hsP,ht',htV,hd',hdW,he'⟩⟩
  have sums := P3R58.p3_coefficient_sums M hp e
  have hi : P3R57.roleCoefficient M hp e 0 1+s < criticalExponent M.base (e 1) := by omega
  have hj : t < criticalExponent M.base (e 2) := by omega
  have hi' : s' < criticalExponent M.base (e 1) := by omega
  have hj' : P3R57.roleCoefficient M hp e 0 2+t' < criticalExponent M.base (e 2) := by omega
  have eq := canonical_return_unique M e q _ _ d _ _ d' hi hj
    (P3R58.p3_lshape_canonical M hp e _ _ hi hj (Or.inr htT))
    (P3R58.p3_lshape_canonical M hp e _ _ hi' hj' (Or.inl hsP)) he he'
  omega

/-- R3 supplies an actual strict return at every positive nonprincipal level. -/
theorem r3_strict_return_exists (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    P3R59.RBReturn M hp e q ∨ P3R59.LTReturn M hp e q := by
  exact P3R59.canonical_nonprincipal_return M hp e
    (fun k => r3_all_axes_live M hp hR3 (e 0) k) q hq hpre

/-- Opposite returns add to membership of the actual normalized tail. -/
theorem opposite_returns_tail_member (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (r q : ℕ)
    (hRB : P3R59.RBReturn M hp e r) (hLT : P3R59.LTReturn M hp e q) :
    (r+q)*M.base.q.val ∈ routingH M.base e := by
  obtain ⟨L,A,B,hL,hA,hB,he⟩ := P3R59.opposite_returns_fullsupport M hp e r q hRB hLT
  change _ ∈ generatedThree _ _ _
  exact (mem_generatedThree_iff _ _ _ _).mpr ⟨L,A,B,he⟩

/-- Opposite arms cannot add below the actual principal index; equality is allowed. -/
theorem opposite_returns_principal_le (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (r q : ℕ)
    (hr : 0 < r) (hq : 0 < q)
    (hRB : P3R59.RBReturn M hp e r) (hLT : P3R59.LTReturn M hp e q) :
    principalIndex (routingH M.base e) M.base.q.val M.base.q_positive ≤ r+q := by
  exact principalIndex_min _ _ _ (by omega : 0 < r+q)
    (opposite_returns_tail_member M hp e r q hRB hLT)

/-- LAST-SWITCH: the entire strict prefix before Q-1 stays in level one's arm. -/
theorem r3_last_switch (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    (P3R59.RBReturn M hp e 1 ∧ ∀ q : ℕ, 0 < q →
      q+1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
      P3R59.RBReturn M hp e q) ∨
    (P3R59.LTReturn M hp e 1 ∧ ∀ q : ℕ, 0 < q →
      q+1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
      P3R59.LTReturn M hp e q) := by
  rcases r3_strict_return_exists M hp hR3 e 1 (by omega) hQ with hb | ht
  · left
    refine ⟨hb,?_⟩
    intro q hq hpre
    rcases r3_strict_return_exists M hp hR3 e q hq (by omega) with h | h
    · exact h
    · have := opposite_returns_principal_le M hp e 1 q (by omega) hq hb h
      omega
  · right
    refine ⟨ht,?_⟩
    intro q hq hpre
    rcases r3_strict_return_exists M hp hR3 e q hq (by omega) with h | h
    · have := opposite_returns_principal_le M hp e q 1 hq (by omega) h ht
      omega
    · exact h

/-- Any return opposite to level one occurs exactly at the last nonprincipal level. -/
theorem r3_switch_only_at_last (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (q : ℕ)
    (hq : 0 < q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hswitch : (P3R59.RBReturn M hp e 1 ∧ P3R59.LTReturn M hp e q) ∨
      (P3R59.LTReturn M hp e 1 ∧ P3R59.RBReturn M hp e q)) :
    q+1 = principalIndex (routingH M.base e) M.base.q.val M.base.q_positive := by
  rcases hswitch with ⟨hb,ht⟩ | ⟨ht,hb⟩
  · have := opposite_returns_principal_le M hp e 1 q (by omega) hq hb ht
    omega
  · have := opposite_returns_principal_le M hp e q 1 hq (by omega) hb ht
    omega

end NS25Lean.P3R66
