import NS25Lean.P3CommonArmR59

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R63
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2B4AR1 L5A2C4A L5A2C4D L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

/-- Principal shapes are conclusions about the actual first principal value. -/
def PrincipalPureShape (M : MultiplicityBase Gamma) (hp : chosenDefect M.base=3)
    (e : Fin 3 ≃ Fin 3) : Prop :=
  ∃ k : ℕ, P3R57.roleCoefficient M hp e 0 2 < k ∧
    P3R57.roleCoefficient M hp e 1 2 < k ∧
    k < criticalExponent M.base (e 2) ∧
    principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      k*routingC M.base e

def PrincipalMixedShape (M : MultiplicityBase Gamma) (hp : chosenDefect M.base=3)
    (e : Fin 3 ≃ Fin 3) : Prop :=
  ∃ L I : ℕ, 0<L ∧ L≤P3R57.roleCoefficient M hp e 2 0 ∧
    0<I ∧ I≤P3R57.roleCoefficient M hp e 2 1 ∧
    (L<P3R57.roleCoefficient M hp e 2 0 ∨ I<P3R57.roleCoefficient M hp e 2 1) ∧
    principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      L*routingA M.base e+I*routingB M.base e

/-- A live original critical axis excludes every positive normalized return predecessor. -/
theorem live_normalized_predecessor_absent (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) (axis i : Fin 3)
    (hlive : criticalExponent M.base (e axis)*weights M.base (e axis)-
      weights M.base (e i) ∈ M.base.apery)
    (n : ℕ) (hn : 0<n) :
    ((criticalExponent M.base (e axis)*P3R59.normalizedRoleWeight M.base e axis-
      P3R59.normalizedRoleWeight M.base e i : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (n*M.base.q.val) := by
  intro hret
  have hk := (P3R59.original_K_iff_normalized_positive_return M.base e _).mpr ⟨n,hn,hret⟩
  have he : routingD M.base e *
      (criticalExponent M.base (e axis)*P3R59.normalizedRoleWeight M.base e axis-
        P3R59.normalizedRoleWeight M.base e i) =
      criticalExponent M.base (e axis)*weights M.base (e axis)-weights M.base (e i) := by
    rw [Nat.mul_sub_left_distrib, ← P3R59.normalizedRoleWeight_scale M.base e axis,
      ← P3R59.normalizedRoleWeight_scale M.base e i]
    ring
  rw [he] at hk
  exact (M.base.apery_eq_compl ▸ hlive).2 hk

/-- A convenient positive-shift version, with a represented predecessor. -/
theorem live_normalized_no_shift (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) (axis i : Fin 3)
    (hlive : criticalExponent M.base (e axis)*weights M.base (e axis)-
      weights M.base (e i) ∈ M.base.apery)
    (n y : ℕ) (hn : 0<n) (hnmem : n*M.base.q.val ∈ routingH M.base e)
    (hy : y ∈ routingH M.base e)
    (he : criticalExponent M.base (e axis)*P3R59.normalizedRoleWeight M.base e axis =
      n*M.base.q.val+y+P3R59.normalizedRoleWeight M.base e i) : False := by
  apply live_normalized_predecessor_absent M e axis i hlive n hn
  have hpred : criticalExponent M.base (e axis)*P3R59.normalizedRoleWeight M.base e axis-
      P3R59.normalizedRoleWeight M.base e i = n*M.base.q.val+y := by omega
  rw [hpred]
  constructor
  · exact ⟨n*M.base.q.val+y, (routingH M.base e).add_mem hnmem hy, rfl⟩
  · exact ⟨y,hy,by push_cast; ring⟩

/-- The killed flag first forces an actual principal predecessor. -/
theorem principal_predecessor_exists (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (hboundary : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive : ∀ k : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
      weights M.base k ∈ M.base.apery) :
    ∃ i : Fin 3,
      ((criticalExponent M.base (e 2)*routingC M.base e-
        P3R59.normalizedRoleWeight M.base e i : ℕ) : ℤ) ∈
      returnIdeal (routingH M.base e)
        (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val) := by
  by_contra! habs
  have hz := P3R59.critical_killedCount_zero_of_normalized_predecessors_absent M e (by
    intro i n hn hnq
    by_cases heq : n=principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
    · subst n; exact habs i
    · exact P3R59.nonprincipal_critical_predecessors_absent M hp e hlive n hn (by omega) i)
  omega

/-- Critical-fiber comparison gives the two preliminary divisor shapes. -/
theorem principal_preliminary_shapes (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (hboundary : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive : ∀ k : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
      weights M.base k ∈ M.base.apery) :
    (∃ k : ℕ, 0<k ∧ k<criticalExponent M.base (e 2) ∧
      principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
        k*routingC M.base e) ∨
    (∃ L I : ℕ, L≤P3R57.roleCoefficient M hp e 2 0 ∧
      I≤P3R57.roleCoefficient M hp e 2 1 ∧
      (L<P3R57.roleCoefficient M hp e 2 0 ∨ I<P3R57.roleCoefficient M hp e 2 1) ∧
      principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
        L*routingA M.base e+I*routingB M.base e) := by
  obtain ⟨i,hi⟩ := principal_predecessor_exists M hp e hboundary hlive
  obtain ⟨y,hy,hye⟩ := hi.2
  obtain ⟨A,B,C,hfac⟩ := routingH_factorization M.base e
    (principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive).2
  obtain ⟨x,z,w,hyfac⟩ := routingH_factorization M.base e hy
  have hle := P3R59.normalized_generator_le_third_critical M hp e i
  have hnat : criticalExponent M.base (e 2)*routingC M.base e =
      A*routingA M.base e+B*routingB M.base e+C*routingC M.base e+
      (x*routingA M.base e+z*routingB M.base e+w*routingC M.base e)+
      P3R59.normalizedRoleWeight M.base e i := by
    rw [Nat.cast_sub hle] at hye
    have he : criticalExponent M.base (e 2)*routingC M.base e =
      principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val+y+
      P3R59.normalizedRoleWeight M.base e i := by exact_mod_cast (by linarith :
        (criticalExponent M.base (e 2)*routingC M.base e : ℕ) =
        (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val : ℕ)+y+
        (P3R59.normalizedRoleWeight M.base e i : ℤ))
    rw [hfac,hyfac] at he
    exact he
  have htpos : 0 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val :=
    Nat.mul_pos (principalIndex_spec _ _ _).1 M.base.q_positive
  fin_cases i <;> simp [P3R59.normalizedRoleWeight] at hnat
  · have hf := P3R59.h3_critical_two_factorizations M hp e (A+x+1) (B+z) (C+w)
      (by nlinarith only [hnat])
    rcases hf with ⟨hA,hB,hC⟩ | ⟨hA,hB,hC⟩
    · right; refine ⟨A,B,by omega,by omega,Or.inl (by omega),?_⟩
      have hc : C=0 := by omega
      simpa [hc] using hfac
    · omega
  · have hf := P3R59.h3_critical_two_factorizations M hp e (A+x) (B+z+1) (C+w)
      (by nlinarith only [hnat])
    rcases hf with ⟨hA,hB,hC⟩ | ⟨hA,hB,hC⟩
    · right; refine ⟨A,B,by omega,by omega,Or.inr (by omega),?_⟩
      have hc : C=0 := by omega
      simpa [hc] using hfac
    · omega
  · have hf := P3R59.h3_critical_two_factorizations M hp e (A+x) (B+z) (C+w+1)
      (by nlinarith only [hnat])
    rcases hf with ⟨hA,hB,hC⟩ | ⟨hA,hB,hC⟩
    · omega
    · left
      have ha : A=0 := by omega
      have hb : B=0 := by omega
      refine ⟨C,?_,by omega,?_⟩
      · by_contra hn
        have hc : C=0 := by omega
        have hzero : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=0 := by
          simpa only [ha,hb,hc,zero_mul,zero_add] using hfac
        omega
      · simpa [ha,hb] using hfac

/-- The legal killed-third, live-first-two role forces the principal alternatives. -/
theorem principal_shapes_of_legal_role (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (hboundary : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive1 : ∀ k : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-
      weights M.base k ∈ M.base.apery)
    (hlive2 : ∀ k : Fin 3, criticalExponent M.base (e 1)*weights M.base (e 1)-
      weights M.base k ∈ M.base.apery) :
    PrincipalPureShape M hp e ∨ PrincipalMixedShape M hp e := by
  let Q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  have hQ : 0<Q := (principalIndex_spec _ _ _).1
  have hQt : Q*M.base.q.val ∈ routingH M.base e := (principalIndex_spec _ _ _).2
  have hmem (A B C : ℕ) : A*routingA M.base e+B*routingB M.base e+C*routingC M.base e ∈ routingH M.base e := by
    change _ ∈ generatedThree _ _ _
    exact (mem_generatedThree_iff _ _ _ _).mpr ⟨A,B,C,rfl⟩
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hU := P3R58.p3_coefficients_positive M hp e 1 0 (by decide)
  have hs := P3R58.p3_coefficient_sums M hp e
  have hrels := coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)
  change criticalExponent M.base (e 0)*routingA M.base e=
      P3R57.roleCoefficient M hp e 0 1*routingB M.base e+
      P3R57.roleCoefficient M hp e 0 2*routingC M.base e ∧
      criticalExponent M.base (e 1)*routingB M.base e=
      P3R57.roleCoefficient M hp e 1 0*routingA M.base e+
      P3R57.roleCoefficient M hp e 1 2*routingC M.base e ∧ _ at hrels
  rcases principal_preliminary_shapes M hp e hboundary hlive1 with ⟨k,hk0,hk,ht⟩ | ⟨L,I,hL,hI,hstrict,ht⟩
  · left
    refine ⟨k,?_,?_,hk,ht⟩
    · by_contra hn
      have hkT : k≤P3R57.roleCoefficient M hp e 0 2 := by omega
      apply live_normalized_no_shift M e 0 1 (hlive1 (e 1)) Q
        ((P3R57.roleCoefficient M hp e 0 1-1)*routingB M.base e+
          (P3R57.roleCoefficient M hp e 0 2-k)*routingC M.base e) hQ hQt
        (by simpa using (hmem 0 (P3R57.roleCoefficient M hp e 0 1 - 1) (P3R57.roleCoefficient M hp e 0 2 - k)))
      change criticalExponent M.base (e 0)*routingA M.base e=_
      have h1 := Nat.sub_add_cancel (show 1≤P3R57.roleCoefficient M hp e 0 1 by omega)
      have h2 := Nat.sub_add_cancel hkT
      simp [P3R59.normalizedRoleWeight,Q]
      nlinarith only [hrels.1,ht,congrArg (fun z : ℕ => z*routingB M.base e) h1,
        congrArg (fun z : ℕ => z*routingC M.base e) h2]
    · by_contra hn
      have hkV : k≤P3R57.roleCoefficient M hp e 1 2 := by omega
      apply live_normalized_no_shift M e 1 0 (hlive2 (e 0)) Q
        ((P3R57.roleCoefficient M hp e 1 0-1)*routingA M.base e+
          (P3R57.roleCoefficient M hp e 1 2-k)*routingC M.base e) hQ hQt
        (by simpa using (hmem (P3R57.roleCoefficient M hp e 1 0 - 1) 0 (P3R57.roleCoefficient M hp e 1 2 - k)))
      change criticalExponent M.base (e 1)*routingB M.base e=_
      have h1 := Nat.sub_add_cancel (show 1≤P3R57.roleCoefficient M hp e 1 0 by omega)
      have h2 := Nat.sub_add_cancel hkV
      simp [P3R59.normalizedRoleWeight,Q]
      nlinarith only [hrels.2.1,ht,congrArg (fun z : ℕ => z*routingA M.base e) h1,
        congrArg (fun z : ℕ => z*routingC M.base e) h2]
  · right
    refine ⟨L,I,?_,hL,?_,hI,hstrict,ht⟩
    · by_contra hn
      have hL0 : L=0 := by omega
      apply live_normalized_no_shift M e 1 1 (hlive2 (e 1)) Q
        ((criticalExponent M.base (e 1)-I-1)*routingB M.base e) hQ hQt
        (by simpa using hmem 0 (criticalExponent M.base (e 1)-I-1) 0)
      change criticalExponent M.base (e 1)*routingB M.base e=_
      have hc : criticalExponent M.base (e 1)-I-1+I+1=criticalExponent M.base (e 1) := by omega
      simp only [hL0,zero_mul,zero_add] at ht
      simp [P3R59.normalizedRoleWeight,Q]
      nlinarith only [ht,congrArg (fun z : ℕ => z*routingB M.base e) hc]
    · by_contra hn
      have hI0 : I=0 := by omega
      apply live_normalized_no_shift M e 0 0 (hlive1 (e 0)) Q
        ((criticalExponent M.base (e 0)-L-1)*routingA M.base e) hQ hQt
        (by simpa using hmem (criticalExponent M.base (e 0)-L-1) 0 0)
      change criticalExponent M.base (e 0)*routingA M.base e=_
      have hc : criticalExponent M.base (e 0)-L-1+L+1=criticalExponent M.base (e 0) := by omega
      simp only [hI0,zero_mul,add_zero] at ht
      simp [P3R59.normalizedRoleWeight,Q]
      nlinarith only [ht,congrArg (fun z : ℕ => z*routingA M.base e) hc]

end NS25Lean.P3R63










