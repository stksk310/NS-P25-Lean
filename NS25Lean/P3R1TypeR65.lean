import NS25Lean.P3R1ComplementR65
import NS25Lean.P3R1TargetExclusionR65
import NS25Lean.P3R1SeamR65
import NS25Lean.P3Q1TypeR64

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R65
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open P3R61 L5A2C4OR3 CombinatorialCore
variable {Gamma : NumericalSemigroup}

/-- CU.13: the literal selected pure-c role, for every Q≥1 and the original M. -/
theorem selected_role_cExceptional_le_one (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (hb : killedCount M (criticalExponent M.base (e 1)*weights M.base (e 1))=1)
    (hc : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive : ∀ j : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base j ∈ M.base.apery)
    (k : ℕ) (hk : 0<k) (hkC : k<criticalExponent M.base (e 2))
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=k*routingC M.base e) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ResidueData.cExceptionalCount (routingData M.base e) ≤ 1 := by
  let a := routingA M.base e
  let b := routingB M.base e
  let c := routingC M.base e
  let Q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  let Z := P3R57.roleCoefficient M hp e 2 1
  let W := P3R57.roleCoefficient M hp e 2 0
  let B := criticalExponent M.base (e 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hQpos : 0<Q := (principalIndex_spec _ _ _).1
  by_cases hQ1 : Q=1
  · exact P3R63.routing_cExceptional_le_one_of_principal_index_one M e hQ1
  have hQ : 1<Q := by omega
  have hlevels : ∀ n, 0<n → n<Q → ∃ i j d, LTLevel M hp e n i j d := by
    intro n hn hnQ
    exact lt_level_exists M hp e n (all_nonprincipal_lt M hp e hb hc hlive k hk ht n hn hnQ)
  have hdeep : ∀ n i j d, 0<n → n<Q → LTLevel M hp e n i j d → j<k := by
    intro n i j d hn hnQ hl
    exact (deep_lt_level M hp e hb hc hlive k hk ht n i j d hn hnQ hl).2
  have hprincipal : ((k*c : ℕ) : ℤ) ∈ routingI M.base e := by
    simpa [ht,c] using (P3R62.routing_principal_isMinimalGenerator M.base e).1
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hwindow := principal_window M hp e hb hlive k hk ht
  apply routing_cExceptional_le_one_of_x_targets M hp e k hkC hprincipal
  intro s
  let t : ResidueData.CSourceTargetBranches (routingData M.base e) := s.val
  have hminS := normalizedSemigroup_minimal (chosenBase_minimalFour M.base e)
  have hbpos : 0<b := quotient_pos_of_dvd (chosenBase_minimalFour M.base e).n₂_pos (tailGcd_dvd _ _ _).2.1
  have hcpos : 0<c := quotient_pos_of_dvd (chosenBase_minimalFour M.base e).n₃_pos (tailGcd_dvd _ _ _).2.2
  have hmin : (routingI M.base e).IsMinimalGenerator
      ((routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget t.val)) :=
    ((routingI M.base e).concrete_isSource_iff_isMinimalGenerator a b c hminS.1
      (routingHB M.base e) (routingHC M.base e) (Nat.ne_of_gt hbpos) (Nat.ne_of_gt hcpos) _).mp t.property.2
  rcases final_lt_generator_cover M hp e hQ hlevels _ hmin with hprincipalTarget | ⟨n,i,j,d,hn,hnQ,hl,hw⟩
  · exact (final_principal_not_target M hp e hQ k hwindow.1 hwindow.2 ht
      (by intro n hn hnQ; obtain ⟨i,j,d,hl⟩ := hlevels n hn hnQ
          exact ⟨i,j,d,hl,hdeep n i j d hn hnQ hl⟩)
      t.val t.property hprincipalTarget).elim
  · have hjk := hdeep n i j d hn hnQ hl
    rcases hw with hF | hX | hY
    · exact (s.property (final_f_nonexceptional M hp e k hkC ht n i j d hl hjk t hF)).elim
    · exact ⟨n,i,j,d,hl,hX⟩
    · exact (final_y_not_target M hp e hQ k ht hlevels n i j d hn hnQ hl hjk
        t.val t.property hY).elim

/-- Exact original R64 universal fresh gate, proved rather than assumed. -/
theorem pure_tail_final_fresh (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (hR1 : (P3R51.internalDegrees M).card=1)
    (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ j : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base j ∈ M.base.apery)
    (hbound : ∀ j : Fin 3, j≠0 → killedCount M (criticalExponent M.base (e j)*weights M.base (e j))=1)
    (k : ℕ) (hk : 0<k) (hkC : k<criticalExponent M.base (e 2))
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=k*routingC M.base e) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    ResidueData.cExceptionalCount D ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D)+1 := by
  have hh := selected_role_cExceptional_le_one M hp e (hbound 1 (by decide))
    (hbound 2 (by decide)) hlive k hk hkC ht
  exact le_trans hh (by omega)

/-- The unchanged original R1 binder gives an actual final fresh compensation. -/
theorem r1_fresh_compensation (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (hR1 : (P3R51.internalDegrees M).card=1) :
    ∃ e : Fin 3 ≃ Fin 3,
      letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      let D := routingData M.base e
      ResidueData.cExceptionalCount D ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D)+1 := by
  obtain ⟨e,hlive,hbound,_,k,hk,hkC,ht⟩ := P3R64.r1_principal_pure_c_exists M hp hR1
  exact ⟨e,pure_tail_final_fresh M hp hR1 e hlive hbound k hk hkC ht⟩

/-- Original R1 type inequality, same Gamma, M and original multiplicity. -/
theorem r1_original_type_le_rho_sub_two (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (hR1 : (P3R51.internalDegrees M).card=1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma-2 := by
  exact P3R52Bridge.p3_strong_of_fresh_compensation M hp (r1_fresh_compensation M hp hR1)
end NS25Lean.P3R65
