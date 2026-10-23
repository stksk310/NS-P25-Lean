import NS25Lean.P3R1PrincipalR64

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R65
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2B4AR1 L5A2C4H L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

/-- CU.02, lower window: the original first-live predecessor forbids k≤T. -/
theorem principal_window_lower (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ j : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
      weights M.base j ∈ M.base.apery)
    (k : ℕ)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      k*routingC M.base e) : P3R57.roleCoefficient M hp e 0 2 < k := by
  by_contra hn
  have hkT : k ≤ P3R57.roleCoefficient M hp e 0 2 := by omega
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hr := (coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)).1
  change criticalExponent M.base (e 0)*routingA M.base e =
    P3R57.roleCoefficient M hp e 0 1*routingB M.base e+
      P3R57.roleCoefficient M hp e 0 2*routingC M.base e at hr
  have hQ := (principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive)
  apply P3R63.live_normalized_no_shift M e 0 1 (hlive (e 1)) _
    ((P3R57.roleCoefficient M hp e 0 1-1)*routingB M.base e+
      (P3R57.roleCoefficient M hp e 0 2-k)*routingC M.base e) hQ.1 hQ.2
  · change _ ∈ generatedThree _ _ _
    exact (mem_generatedThree_iff _ _ _ _).mpr
      ⟨0,P3R57.roleCoefficient M hp e 0 1-1,P3R57.roleCoefficient M hp e 0 2-k,by simp⟩
  · change criticalExponent M.base (e 0)*routingA M.base e = _
    have h1 := Nat.sub_add_cancel (show 1≤P3R57.roleCoefficient M hp e 0 1 by omega)
    have h2 := Nat.sub_add_cancel hkT
    simp only [P3R59.normalizedRoleWeight,Matrix.cons_val_one,Matrix.cons_val_zero]
    nlinarith only [hr,ht,congrArg (fun z : ℕ => z*routingB M.base e) h1,
      congrArg (fun z : ℕ => z*routingC M.base e) h2]

/-- CU.02, upper window: the actual b-boundary has a principal predecessor. -/
theorem principal_window_upper (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hb : killedCount M (criticalExponent M.base (e 1)*weights M.base (e 1))=1)
    (hlive : ∀ j : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
      weights M.base j ∈ M.base.apery)
    (k : ℕ) (hk : 0<k)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      k*routingC M.base e) : k ≤ P3R57.roleCoefficient M hp e 1 2 := by
  let f := P3R57.swapRole e
  have hb' : killedCount M (criticalExponent M.base (f 2)*weights M.base (f 2))=1 := by simpa [f] using hb
  have hlive' : ∀ j : Fin 3, criticalExponent M.base (f 0)*weights M.base (f 0)-
      weights M.base j ∈ M.base.apery := by simpa [f] using hlive
  obtain ⟨i,hi⟩ := P3R63.principal_predecessor_exists M hp f hb' hlive'
  obtain ⟨y,hy,hye⟩ := hi.2
  obtain ⟨x,z,w,hyfac⟩ := routingH_factorization M.base f hy
  have hle := P3R59.normalized_generator_le_third_critical M hp f i
  rw [Nat.cast_sub hle] at hye
  have ht' : principalIndex (routingH M.base f) M.base.q.val M.base.q_positive*M.base.q.val =
      k*routingB M.base f := by
    simpa only [f,P3R64.routingH_swapBC,P3R57.routingB_swap] using ht
  have he : criticalExponent M.base (f 2)*routingC M.base f =
      k*routingB M.base f+y+P3R59.normalizedRoleWeight M.base f i := by
    have he' : (criticalExponent M.base (f 2)*routingC M.base f : ℕ) =
        (principalIndex (routingH M.base f) M.base.q.val M.base.q_positive*M.base.q.val : ℕ)+y+
        (P3R59.normalizedRoleWeight M.base f i : ℤ) := by linarith
    rw [ht'] at he'
    exact_mod_cast he'
  rw [hyfac] at he
  have hbound : k ≤ P3R57.roleCoefficient M hp f 2 1 := by
    fin_cases i <;> simp [P3R59.normalizedRoleWeight] at he
    · have hf := P3R59.h3_critical_two_factorizations M hp f (x+1) (k+z) w (by nlinarith only [he])
      rcases hf with ⟨_,hh,_⟩ | ⟨_,hh,_⟩ <;> omega
    · have hf := P3R59.h3_critical_two_factorizations M hp f x (k+z+1) w (by nlinarith only [he])
      rcases hf with ⟨_,hh,_⟩ | ⟨_,hh,_⟩ <;> omega
    · have hf := P3R59.h3_critical_two_factorizations M hp f x (k+z) (w+1) (by nlinarith only [he])
      rcases hf with ⟨_,hh,_⟩ | ⟨_,hh,_⟩ <;> omega
  simpa [f,P3R57.roleCoefficient_swap,Equiv.swap_apply_def] using hbound

/-- The all-Q same-M principal window CU.02. -/
theorem principal_window (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hb : killedCount M (criticalExponent M.base (e 1)*weights M.base (e 1))=1)
    (hlive : ∀ j : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
      weights M.base j ∈ M.base.apery)
    (k : ℕ) (hk : 0<k)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      k*routingC M.base e) :
    P3R57.roleCoefficient M hp e 0 2 < k ∧ k ≤ P3R57.roleCoefficient M hp e 1 2 :=
  ⟨principal_window_lower M hp e hlive k ht,principal_window_upper M hp e hb hlive k hk ht⟩
end NS25Lean.P3R65
