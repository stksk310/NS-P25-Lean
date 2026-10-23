import NS25Lean.P3R3LastSwitchR66

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

/-- NF.13: the actual Q=1 role has fresh compensation, conditionally only. -/
theorem r3_q1_fresh (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (hQ : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive = 1) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ResidueData.cExceptionalCount (routingData M.base e) ≤
      Nat.card (ResidueData.CFreshUnusedMergeBases (routingData M.base e)) + 1 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have h := P3R63.routing_cExceptional_le_one_of_principal_index_one M e hQ
  omega

/-- TW.11/NF.11: cancellation uses exactly the SAME final first-stage image. -/
theorem final_fresh_iff_total_unused (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ResidueData.cExceptionalCount (routingData M.base e) ≤
      Nat.card (ResidueData.CFreshUnusedMergeBases (routingData M.base e)) + 1 ↔
    ResidueData.sourceTargetBranchCount (routingData M.base e) ≤
      Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e)) + 1 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  exact P3R51.fresh_bound_iff_unused_bound (routingData M.base e)

/-- Actual single all-positive principal factorization; this is not support union. -/
def PrincipalFullSupport (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) : Prop :=
  ∃ L I J : ℕ, 0 < L ∧ 0 < I ∧ 0 < J ∧
    principalIndex (routingH M.base e) M.base.q.val M.base.q_positive * M.base.q.val =
      L * routingA M.base e + I * routingB M.base e + J * routingC M.base e

/-- The single full-support condition is exactly a SIGNED semigroup difference. -/
theorem principal_fullSupport_iff_signed (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    PrincipalFullSupport M e ↔
      ((principalIndex (routingH M.base e) M.base.q.val M.base.q_positive * M.base.q.val : ℕ) : ℤ)
        - routingA M.base e - routingB M.base e - routingC M.base e ∈
          (routingH M.base e).asRelativeIdeal := by
  constructor
  · rintro ⟨L,I,J,hL,hI,hJ,he⟩
    refine ⟨(L-1)*routingA M.base e+(I-1)*routingB M.base e+(J-1)*routingC M.base e, ?_, ?_⟩
    · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨L-1,I-1,J-1,rfl⟩
    · rw [he]
      push_cast [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_sub (by omega : 1 ≤ I), Nat.cast_sub (by omega : 1 ≤ J)]
      ring
  · rintro ⟨n,hn,he⟩
    obtain ⟨L,I,J,hfac⟩ := (mem_generatedThree_iff _ _ _ _).mp hn
    refine ⟨L+1,I+1,J+1,by omega,by omega,by omega,?_⟩
    have he' : ((principalIndex (routingH M.base e) M.base.q.val M.base.q_positive * M.base.q.val : ℕ) : ℤ) =
      n + routingA M.base e + routingB M.base e + routingC M.base e := by omega
    have hn' : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive * M.base.q.val =
      n + routingA M.base e + routingB M.base e + routingC M.base e := by exact_mod_cast he'
    rw [hn',hfac]
    ring

/-- Opposite strict returns have the interior coefficient bounds used by TW.02. -/
theorem opposite_returns_interior (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (r q : ℕ)
    (hRB : P3R59.RBReturn M hp e r) (hLT : P3R59.LTReturn M hp e q) :
    ∃ L I J : ℕ, 2 ≤ L ∧ L ≤ criticalExponent M.base (e 0)-2 ∧
      2 ≤ I ∧ I ≤ criticalExponent M.base (e 1)-2 ∧
      2 ≤ J ∧ J ≤ criticalExponent M.base (e 2)-2 ∧
      (r+q)*M.base.q.val=L*routingA M.base e+I*routingB M.base e+J*routingC M.base e := by
  rcases hRB with ⟨s,t,d,hs,hsZ,ht,htT,hd,hdU,heR⟩
  rcases hLT with ⟨s',t',d',hs',hsP,ht',htV,hd',hdW,heL⟩
  have sums := P3R58.p3_coefficient_sums M hp e
  let L := criticalExponent M.base (e 0)-d-d'
  have hLadd : L+d+d'=criticalExponent M.base (e 0) := by dsimp [L]; omega
  have hmul := congrArg (fun n : ℕ => n*routingA M.base e) hLadd
  have hrel : criticalExponent M.base (e 0)*routingA M.base e =
      P3R57.roleCoefficient M hp e 0 1*routingB M.base e+
        P3R57.roleCoefficient M hp e 0 2*routingC M.base e :=
    (coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)).1
  have heRN : (P3R57.roleCoefficient M hp e 0 1+s)*routingB M.base e+t*routingC M.base e=
      r*M.base.q.val+d*routingA M.base e := by exact_mod_cast heR
  have heLN : s'*routingB M.base e+(P3R57.roleCoefficient M hp e 0 2+t')*routingC M.base e=
      q*M.base.q.val+d'*routingA M.base e := by exact_mod_cast heL
  refine ⟨L,s+s',t+t',by dsimp [L]; omega,by dsimp [L]; omega,
    by omega,by omega,by omega,by omega,?_⟩
  nlinarith only [heRN,heLN,hrel,hmul]

/-- TW.02: both actual arms force a SINGLE full-support principal factorization. -/
theorem two_arm_principal_fullSupport (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3)
    (hRB : ∃ r : ℕ, 0<r ∧ r<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive ∧ P3R59.RBReturn M hp e r)
    (hLT : ∃ q : ℕ, 0<q ∧ q<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive ∧ P3R59.LTReturn M hp e q) :
    PrincipalFullSupport M e := by
  obtain ⟨r,hr,hrQ,hbr⟩ := hRB
  obtain ⟨q,hq,hqQ,htq⟩ := hLT
  have hQ : 1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive := by omega
  rcases P3R66.r3_strict_return_exists M hp hR3 e 1 (by omega) hQ with hb | ht
  · have hlast := P3R66.r3_switch_only_at_last M hp e q hq hqQ (Or.inl ⟨hb,htq⟩)
    obtain ⟨L,I,J,hL,hI,hJ,he⟩ := P3R59.opposite_returns_fullsupport M hp e 1 q hb htq
    refine ⟨L,I,J,hL,hI,hJ,?_⟩
    simpa only [Nat.add_comm 1 q, hlast] using he
  · have hlast := P3R66.r3_switch_only_at_last M hp e r hr hrQ (Or.inr ⟨ht,hbr⟩)
    obtain ⟨L,I,J,hL,hI,hJ,he⟩ := P3R59.opposite_returns_fullsupport M hp e r 1 hbr ht
    exact ⟨L,I,J,hL,hI,hJ,hlast ▸ he⟩

/-- NF.01, before orientation: the no-full-support residual has one common arm. -/
theorem no_fullSupport_one_arm (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hn : ¬ PrincipalFullSupport M e) : P3R59.OneArmPrefix M hp e := by
  rcases P3R66.r3_strict_return_exists M hp hR3 e 1 (by omega) hQ with hb | ht
  · left
    intro q hq hqQ
    rcases P3R66.r3_strict_return_exists M hp hR3 e q hq hqQ with h | h
    · exact h
    · exact False.elim (hn (two_arm_principal_fullSupport M hp hR3 e
        ⟨1,by omega,hQ,hb⟩ ⟨q,hq,hqQ,h⟩))
  · right
    intro q hq hqQ
    rcases P3R66.r3_strict_return_exists M hp hR3 e q hq hqQ with h | h
    · exact False.elim (hn (two_arm_principal_fullSupport M hp hR3 e
        ⟨q,hq,hqQ,h⟩ ⟨1,by omega,hQ,ht⟩))
    · exact h

end NS25Lean.P3R67
