import NS25Lean.P3R1ReturnGeometryR64
import NS25Lean.P3R2PrincipalShapeR63

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R64
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2B4AR1 L5A2C4H L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

/-- A boundary second axis excludes a principal factorization using positive a and b. -/
theorem principal_positive_ab_impossible (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hb : killedCount M (criticalExponent M.base (e 1)*weights M.base (e 1)) = 1)
    (hlive : ∀ k : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
      weights M.base k ∈ M.base.apery)
    (L I : ℕ) (hL : 0 < L) (hI : 0 < I)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      L*routingA M.base e+I*routingB M.base e) : False := by
  have hb' : killedCount M (criticalExponent M.base (P3R57.swapRole e 2)*
      weights M.base (P3R57.swapRole e 2)) = 1 := by simpa using hb
  have hlive' : ∀ k : Fin 3, criticalExponent M.base (P3R57.swapRole e 0)*
      weights M.base (P3R57.swapRole e 0)-weights M.base k ∈ M.base.apery := by
    simpa using hlive
  obtain ⟨i, hi⟩ := P3R63.principal_predecessor_exists M hp (P3R57.swapRole e) hb' hlive'
  obtain ⟨y, hy, hye⟩ := hi.2
  obtain ⟨x,z,w,hyfac⟩ := routingH_factorization M.base (P3R57.swapRole e) hy
  have hle := P3R59.normalized_generator_le_third_critical M hp (P3R57.swapRole e) i
  rw [Nat.cast_sub hle] at hye
  have hnat : criticalExponent M.base (P3R57.swapRole e 2)*routingC M.base (P3R57.swapRole e) =
      L*routingA M.base (P3R57.swapRole e)+I*routingC M.base (P3R57.swapRole e)+
      (x*routingA M.base (P3R57.swapRole e)+z*routingB M.base (P3R57.swapRole e)+
        w*routingC M.base (P3R57.swapRole e))+
      P3R59.normalizedRoleWeight M.base (P3R57.swapRole e) i := by
    have ht' : principalIndex (routingH M.base (P3R57.swapRole e)) M.base.q.val
        M.base.q_positive*M.base.q.val =
        L*routingA M.base (P3R57.swapRole e)+I*routingC M.base (P3R57.swapRole e) := by
      simpa only [routingH_swapBC, P3R57.routingA_swap, P3R57.routingC_swap] using ht
    have he : criticalExponent M.base (P3R57.swapRole e 2)*routingC M.base (P3R57.swapRole e) =
        principalIndex (routingH M.base (P3R57.swapRole e)) M.base.q.val M.base.q_positive*
          M.base.q.val+y+P3R59.normalizedRoleWeight M.base (P3R57.swapRole e) i := by
      exact_mod_cast (by linarith :
        (criticalExponent M.base (P3R57.swapRole e 2)*routingC M.base (P3R57.swapRole e) : ℕ) =
        (principalIndex (routingH M.base (P3R57.swapRole e)) M.base.q.val M.base.q_positive*
          M.base.q.val : ℕ)+y+
        (P3R59.normalizedRoleWeight M.base (P3R57.swapRole e) i : ℤ))
    rw [ht', hyfac] at he
    exact he
  fin_cases i <;> simp [P3R59.normalizedRoleWeight] at hnat
  · have hf := P3R59.h3_critical_two_factorizations M hp (P3R57.swapRole e)
      (L+x+1) z (I+w) (by
        simp only [P3R57.routingA_swap, P3R57.routingB_swap, P3R57.routingC_swap, P3R57.swapRole_two]
        nlinarith only [hnat])
    rcases hf with ⟨_,_,hC⟩ | ⟨hA,_,_⟩ <;> omega
  · have hf := P3R59.h3_critical_two_factorizations M hp (P3R57.swapRole e)
      (L+x) (z+1) (I+w) (by
        simp only [P3R57.routingA_swap, P3R57.routingB_swap, P3R57.routingC_swap, P3R57.swapRole_two]
        nlinarith only [hnat])
    rcases hf with ⟨_,_,hC⟩ | ⟨hA,_,_⟩ <;> omega
  · have hf := P3R59.h3_critical_two_factorizations M hp (P3R57.swapRole e)
      (L+x) z (I+w+1) (by
        simp only [P3R57.routingA_swap, P3R57.routingB_swap, P3R57.routingC_swap, P3R57.swapRole_two]
        nlinarith only [hnat])
    rcases hf with ⟨_,_,hC⟩ | ⟨hA,_,_⟩ <;> omega

/-- Both boundary flags force the actual principal value onto a pure tail axis. -/
theorem principal_pure_tail_of_role (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hb : killedCount M (criticalExponent M.base (e 1)*weights M.base (e 1)) = 1)
    (hc : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2)) = 1)
    (hlive : ∀ k : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
      weights M.base k ∈ M.base.apery) :
    (∃ k : ℕ, 0 < k ∧ k < criticalExponent M.base (e 1) ∧
      principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
        k*routingB M.base e) ∨
    (∃ k : ℕ, 0 < k ∧ k < criticalExponent M.base (e 2) ∧
      principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
        k*routingC M.base e) := by
  let Q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  have hQ : 0 < Q := (principalIndex_spec _ _ _).1
  have hQt : Q*M.base.q.val ∈ routingH M.base e := (principalIndex_spec _ _ _).2
  have htpos : 0 < Q*M.base.q.val := Nat.mul_pos hQ M.base.q_positive
  have hs := P3R58.p3_coefficient_sums M hp e
  have hU := P3R58.p3_coefficients_positive M hp e 1 0 (by decide)
  have hV := P3R58.p3_coefficients_positive M hp e 1 2 (by decide)
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  rcases P3R63.principal_preliminary_shapes M hp e hc hlive with h | ⟨L,I,hL,hI,_,ht⟩
  · exact Or.inr h
  · by_cases hL0 : L = 0
    · left
      refine ⟨I, ?_, by omega, ?_⟩
      · simp only [hL0, zero_mul, zero_add] at ht
        change 0 < Q*M.base.q.val at htpos
        change Q*M.base.q.val = _ at ht
        by_contra hn
        have hz : I = 0 := by omega
        have hzero : Q*M.base.q.val = 0 := by simpa [hz] using ht
        omega
      · simpa [hL0] using ht
    · have hLp : 0 < L := Nat.pos_of_ne_zero hL0
      by_cases hI0 : I = 0
      · exfalso
        apply P3R63.live_normalized_no_shift M e 0 0 (hlive (e 0)) Q
          ((criticalExponent M.base (e 0)-L-1)*routingA M.base e) hQ hQt
        · change _ ∈ generatedThree (routingA M.base e) (routingB M.base e) (routingC M.base e)
          exact (mem_generatedThree_iff _ _ _ _).mpr
            ⟨criticalExponent M.base (e 0)-L-1,0,0,by simp⟩
        · change criticalExponent M.base (e 0)*routingA M.base e = _
          have hsub : criticalExponent M.base (e 0)-L-1+L+1 =
              criticalExponent M.base (e 0) := by omega
          simp only [hI0, zero_mul, add_zero] at ht
          change Q*M.base.q.val = _ at ht
          change criticalExponent M.base (e 0)*routingA M.base e =
            Q*M.base.q.val+(criticalExponent M.base (e 0)-L-1)*routingA M.base e+
              routingA M.base e
          nlinarith only [ht, congrArg (fun z : ℕ => z*routingA M.base e) hsub]
      · exact False.elim (principal_positive_ab_impossible M hp e hb hlive L I hLp
          (Nat.pos_of_ne_zero hI0) ht)

/-- The original R1 binder supplies one physical role carrying the principal pure-tail conclusion. -/
theorem r1_principal_pure_tail_exists (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR1 : (P3R51.internalDegrees M).card = 1) :
    ∃ e : Fin 3 ≃ Fin 3,
      (∀ k : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
        weights M.base k ∈ M.base.apery) ∧
      (∀ axis : Fin 3, axis ≠ 0 →
        killedCount M (criticalExponent M.base (e axis)*weights M.base (e axis)) = 1) ∧
      P3R59.OneArmPrefix M hp e ∧
      ((∃ k : ℕ, 0 < k ∧ k < criticalExponent M.base (e 1) ∧
        principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
          k*routingB M.base e) ∨
       (∃ k : ℕ, 0 < k ∧ k < criticalExponent M.base (e 2) ∧
        principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
          k*routingC M.base e)) := by
  obtain ⟨e,hlive,hbound,harm,_⟩ := r1_common_arm_and_barriers M hp hR1
  exact ⟨e,hlive,hbound,harm,principal_pure_tail_of_role M hp e
    (hbound 1 (by decide)) (hbound 2 (by decide)) hlive⟩

/-- The pure principal tail can be placed in c while retaining the actual first-live role. -/
theorem r1_principal_pure_c_exists (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR1 : (P3R51.internalDegrees M).card = 1) :
    ∃ e : Fin 3 ≃ Fin 3,
      (∀ k : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
        weights M.base k ∈ M.base.apery) ∧
      (∀ axis : Fin 3, axis ≠ 0 →
        killedCount M (criticalExponent M.base (e axis)*weights M.base (e axis)) = 1) ∧
      P3R59.OneArmPrefix M hp e ∧
      (∃ k : ℕ, 0 < k ∧ k < criticalExponent M.base (e 2) ∧
        principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
          k*routingC M.base e) := by
  obtain ⟨e, hlive, hbound, harm, hshape⟩ := r1_principal_pure_tail_exists M hp hR1
  rcases hshape with hb | hc
  · let f := P3R57.swapRole e
    have hlive' : ∀ k : Fin 3, criticalExponent M.base (f 0)*weights M.base (f 0)-
        weights M.base k ∈ M.base.apery := by simpa [f] using hlive
    have hbound' : ∀ axis : Fin 3, axis ≠ 0 →
        killedCount M (criticalExponent M.base (f axis)*weights M.base (f axis)) = 1 := by
      intro axis ha
      fin_cases axis
      · exact False.elim (ha rfl)
      · simpa [f] using hbound 2 (by decide)
      · simpa [f] using hbound 1 (by decide)
    refine ⟨f, hlive', hbound',
      P3R59.oneArmPrefix_of_legal_role M hp f (hbound' 2 (by decide)) hlive', ?_⟩
    obtain ⟨k, hk, hkc, ht⟩ := hb
    refine ⟨k, hk, ?_, ?_⟩
    · simpa [f] using hkc
    · simpa only [f, routingH_swapBC, P3R57.routingC_swap] using ht
  · exact ⟨e, hlive, hbound, harm, hc⟩

end NS25Lean.P3R64
