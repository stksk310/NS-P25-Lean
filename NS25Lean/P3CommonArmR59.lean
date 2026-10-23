import NS25Lean.P3MixedBarrierR59
import NS25Lean.P3CriticalFiberR59
import NS25Lean.P3PrincipalPredecessorR59

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R59
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4OR5 L5A2B4AR1
variable {Gamma : NumericalSemigroup}

theorem nonprincipal_critical_predecessors_absent (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (r : ℕ) (hr : 0 < r)
    (hrq : r < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (i : Fin 3) :
    ((criticalExponent M.base (e 2)*routingC M.base e-
      normalizedRoleWeight M.base e i : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (r*M.base.q.val) := by
  have hnon : r*M.base.q.val ∉ routingH M.base e := by
    intro hmem
    have := principalIndex_min (routingH M.base e) M.base.q.val M.base.q_positive hr hmem
    omega
  have hpoint := canonical_nonprincipal_return M hp e hlive r hr hrq
  have hrel := h3_normalized_relation M hp e
  have hW := P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  have hZ := P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  fin_cases i
  · have hpred : criticalExponent M.base (e 2)*routingC M.base e-
        normalizedRoleWeight M.base e 0 =
        (P3R57.roleCoefficient M hp e 2 0-1)*routingA M.base e+
          P3R57.roleCoefficient M hp e 2 1*routingB M.base e := by
      change criticalExponent M.base (e 2)*routingC M.base e-routingA M.base e = _
      have hsub := Nat.sub_add_cancel (by omega : 1 ≤ P3R57.roleCoefficient M hp e 2 0)
      have hmul := congrArg (fun n : ℕ => n*routingA M.base e) hsub
      have ht : criticalExponent M.base (e 2)*routingC M.base e =
          ((P3R57.roleCoefficient M hp e 2 0-1)*routingA M.base e+
            P3R57.roleCoefficient M hp e 2 1*routingB M.base e)+routingA M.base e := by
        nlinarith only [hrel,hmul]
      omega
    change ((criticalExponent M.base (e 2)*routingC M.base e-
      normalizedRoleWeight M.base e 0 : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (r*M.base.q.val)
    rw [hpred]
    rcases hpoint with hRB | hLT
    · exact mixed_shadow_rb M hp e _ _ r (Nat.sub_le _ _) le_rfl hRB
    · exact mixed_shadow_lt M hp e _ _ r (Nat.sub_le _ _) le_rfl hLT
  · have hpred : criticalExponent M.base (e 2)*routingC M.base e-
        normalizedRoleWeight M.base e 1 =
        P3R57.roleCoefficient M hp e 2 0*routingA M.base e+
          (P3R57.roleCoefficient M hp e 2 1-1)*routingB M.base e := by
      change criticalExponent M.base (e 2)*routingC M.base e-routingB M.base e = _
      have hsub := Nat.sub_add_cancel (by omega : 1 ≤ P3R57.roleCoefficient M hp e 2 1)
      have hmul := congrArg (fun n : ℕ => n*routingB M.base e) hsub
      have ht : criticalExponent M.base (e 2)*routingC M.base e =
          (P3R57.roleCoefficient M hp e 2 0*routingA M.base e+
            (P3R57.roleCoefficient M hp e 2 1-1)*routingB M.base e)+routingB M.base e := by
        nlinarith only [hrel,hmul]
      omega
    change ((criticalExponent M.base (e 2)*routingC M.base e-
      normalizedRoleWeight M.base e 1 : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (r*M.base.q.val)
    rw [hpred]
    rcases hpoint with hRB | hLT
    · exact mixed_shadow_rb M hp e _ _ r le_rfl (Nat.sub_le _ _) hRB
    · exact mixed_shadow_lt M hp e _ _ r le_rfl (Nat.sub_le _ _) hLT
  · change ((criticalExponent M.base (e 2)*routingC M.base e-
      normalizedRoleWeight M.base e 2 : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (r*M.base.q.val)
    rw [normalized_critical_pure_predecessor]
    exact normalized_nonprincipal_misses_pure_predecessor M hp e r hr hnon

/-- The actual R2 boundary flag forbids a full-support principal return.
All original positive returns are covered by normalized finite-prefix reduction. -/
theorem r2_principal_fullsupport_impossible (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hboundary : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery) :
    ¬ ∃ L A B : ℕ, 0<L ∧ 0<A ∧ 0<B ∧
      principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
        L*routingA M.base e+A*routingB M.base e+B*routingC M.base e := by
  rintro ⟨L,A,B,hL,hA,hB,hfull⟩
  have hz := critical_killedCount_zero_of_normalized_predecessors_absent M e (by
    intro i r hr hrq
    by_cases heq : r=principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
    · subst r
      exact principal_fullsupport_predecessors_absent M hp e _ L A B hL hA hB hfull i
    · exact nonprincipal_critical_predecessors_absent M hp e hlive r hr (by omega) i)
  omega

/-- Opposite strict arms give a literal positive three-generator factorization. -/
theorem opposite_returns_fullsupport (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (r q : ℕ)
    (hRB : RBReturn M hp e r) (hLT : LTReturn M hp e q) :
    ∃ L A B : ℕ, 0<L ∧ 0<A ∧ 0<B ∧
      (r+q)*M.base.q.val=L*routingA M.base e+A*routingB M.base e+B*routingC M.base e := by
  rcases hRB with ⟨s,t,d,hs,_,ht,_,_,hd,hRB⟩
  rcases hLT with ⟨s',t',d',hs',_,ht',_,_,hd',hLT⟩
  have hsum := P3R58.p3_coefficient_sums M hp e
  let L := criticalExponent M.base (e 0)-d-d'
  have hL : 0<L := by dsimp [L]; omega
  have hLadd : L+d+d'=criticalExponent M.base (e 0) := by dsimp [L]; omega
  have hmul := congrArg (fun n : ℕ => n*routingA M.base e) hLadd
  have hrel : criticalExponent M.base (e 0)*routingA M.base e =
      P3R57.roleCoefficient M hp e 0 1*routingB M.base e+
        P3R57.roleCoefficient M hp e 0 2*routingC M.base e :=
    (coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)).1
  have heR : (P3R57.roleCoefficient M hp e 0 1+s)*routingB M.base e+t*routingC M.base e=
      r*M.base.q.val+d*routingA M.base e := by exact_mod_cast hRB
  have heL : s'*routingB M.base e+(P3R57.roleCoefficient M hp e 0 2+t')*routingC M.base e=
      q*M.base.q.val+d'*routingA M.base e := by exact_mod_cast hLT
  refine ⟨L,s+s',t+t',hL,by omega,by omega,?_⟩
  nlinarith only [heR,heL,hrel,hmul]

/-- The <=q0 endpoint is included explicitly, rather than silently changed to <q0. -/
theorem opposite_returns_before_or_at_principal_forbidden (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hboundary : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (r q : ℕ) (hr : 0<r) (hq : 0<q)
    (hsum : r+q ≤ principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hRB : RBReturn M hp e r) (hLT : LTReturn M hp e q) : False := by
  obtain ⟨L,A,B,hL,hA,hB,he⟩ := opposite_returns_fullsupport M hp e r q hRB hLT
  by_cases hlt : r+q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  · have hmem : (r+q)*M.base.q.val ∈ routingH M.base e := by
      change _ ∈ generatedThree (routingA M.base e) (routingB M.base e) (routingC M.base e)
      exact (mem_generatedThree_iff _ _ _ _).mpr ⟨L,A,B,he⟩
    have := principalIndex_min (routingH M.base e) M.base.q.val M.base.q_positive
      (by omega : 0<r+q) hmem
    omega
  · have heq : r+q=principalIndex (routingH M.base e) M.base.q.val M.base.q_positive := by omega
    rw [heq] at he
    exact r2_principal_fullsupport_impossible M hp e hboundary hlive ⟨L,A,B,hL,hA,hB,he⟩

theorem oneArmPrefix_of_legal_role (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hboundary : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery) :
    OneArmPrefix M hp e := by
  let q0 := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  have hqpos : 0<q0 := (principalIndex_spec _ _ _).1
  by_cases hq1 : q0=1
  · left
    intro q hq hlt
    change q<q0 at hlt
    omega
  · have hfirst : 1<q0 := by omega
    rcases canonical_nonprincipal_return M hp e hlive 1 (by omega) hfirst with hRB | hLT
    · left
      intro q hq hlt
      by_cases heq : q=1
      · subst q; exact hRB
      · rcases canonical_nonprincipal_return M hp e hlive q hq hlt with hsame | hopp
        · exact hsame
        · exact False.elim (opposite_returns_before_or_at_principal_forbidden M hp e hboundary
            hlive 1 q (by omega) hq (by omega) hRB hopp)
    · right
      intro q hq hlt
      by_cases heq : q=1
      · subst q; exact hLT
      · rcases canonical_nonprincipal_return M hp e hlive q hq hlt with hopp | hsame
        · exact False.elim (opposite_returns_before_or_at_principal_forbidden M hp e hboundary
            hlive q 1 hq (by omega) (by omega) hopp hLT)
        · exact hsame

/-- Exact arbitrary original R2 binder. The role is constructed by the frozen physical dictionary. -/
theorem r2_oneArmPrefix_exists (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR2 : (P3R51.internalDegrees M).card=2) :
    ∃ e : Fin 3 ≃ Fin 3, OneArmPrefix M hp e := by
  obtain ⟨e,hboundary,hlive⟩ := P3R57.r2_legal_boundary_role M hp hR2
  exact ⟨e,oneArmPrefix_of_legal_role M hp e hboundary (hlive 0 (by decide))⟩

end NS25Lean.P3R59
