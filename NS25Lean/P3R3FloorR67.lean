import NS25Lean.P3R3FinalCoverR67

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1 P3R61
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive

/-- The repaired NF.07 principal exclusion only needs tau-a in H. -/
theorem canonical_principal_residual_absent
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (i j : ℕ) (hi : i<criticalExponent M.base (e 1))
    (hj : j<criticalExponent M.base (e 2))
    (hc : i<P3R57.roleCoefficient M hp e 0 1 ∨ j<P3R57.roleCoefficient M hp e 0 2) :
    (i : ℤ)*b+j*c-(Q*M.base.q.val : ℕ) ∉ (routingH M.base e).asRelativeIdeal := by
  intro hm
  have hadd := ideal_add_int (routingH M.base e).asRelativeIdeal htau hm
  apply canonical_not_positive_a M hp e i j hi hj hc 1 (by omega)
    (((Q*M.base.q.val : ℕ)-(a : ℤ))+((i : ℤ)*b+j*c-(Q*M.base.q.val : ℕ))) hadd
  ring

/-- Exact FINAL RB floor in the selected residual role, under the repaired hypothesis. -/
theorem final_rb_canonical_membership (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ x y d, RBLevel M hp e n x y d)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (i j : ℕ) (hi : i<criticalExponent M.base (e 1))
    (hj : j<criticalExponent M.base (e 2))
    (hc : i<P3R57.roleCoefficient M hp e 0 1 ∨ j<P3R57.roleCoefficient M hp e 0 2) :
    ((i : ℤ)*b+j*c ∈ routingI M.base e) ↔
      ∃ n x y d, 0<n ∧ n<Q ∧ RBLevel M hp e n x y d ∧ x ≤ i ∧ y ≤ j := by
  constructor
  · intro hm
    rw [P3R62.routingI_eq_inserted_ideal M.base e hQ] at hm
    rcases hm with hm | hm
    · obtain ⟨n,x,y,d,hn,hnq,hl,hx,hy⟩ := rb_canonical_prefix_divisor M hp e (Q-1)
        (by omega) (by intro n hn hnq; exact hlevels n hn (by omega)) i j hi hj hc hm
      exact ⟨n,x,y,d,hn,by omega,hl,hx,hy⟩
    · exact (canonical_principal_residual_absent M hp e htau i j hi hj hc hm).elim
  · rintro ⟨n,x,y,d,hn,hnq,hl,hx,hy⟩
    have hm := P3R63.completed_prefix_subset_final M.base e hQ _
      (rb_level_beta_mem M hp e (Q-1) (by omega) n x y d hn (by omega) hl)
    have hadd := ideal_add_int (routingI M.base e) hm
      (routing_combination_mem M.base e 0 ((i : ℤ)-x) ((j : ℤ)-y) (by omega) (by omega) (by omega))
    convert hadd using 1 <;> ring

/-- The same exact FINAL criterion on an all-LT role. -/
theorem final_lt_canonical_membership (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ x y d, LTLevel M hp e n x y d)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (i j : ℕ) (hi : i<criticalExponent M.base (e 1))
    (hj : j<criticalExponent M.base (e 2))
    (hc : i<P3R57.roleCoefficient M hp e 0 1 ∨ j<P3R57.roleCoefficient M hp e 0 2) :
    ((i : ℤ)*b+j*c ∈ routingI M.base e) ↔
      ∃ n x y d, 0<n ∧ n<Q ∧ LTLevel M hp e n x y d ∧ x ≤ i ∧ y ≤ j := by
  constructor
  · intro hm
    rw [P3R62.routingI_eq_inserted_ideal M.base e hQ] at hm
    rcases hm with hm | hm
    · obtain ⟨n,x,y,d,hn,hnq,hl,hx,hy⟩ := lt_canonical_prefix_divisor M hp e (Q-1)
        (by omega) (by intro n hn hnq; exact hlevels n hn (by omega)) i j hi hj hc hm
      exact ⟨n,x,y,d,hn,by omega,hl,hx,hy⟩
    · exact (canonical_principal_residual_absent M hp e htau i j hi hj hc hm).elim
  · rintro ⟨n,x,y,d,hn,hnq,hl,hx,hy⟩
    have hm := P3R63.completed_prefix_subset_final M.base e hQ _
      (lt_level_beta_mem M hp e (Q-1) (by omega) n x y d hn (by omega) hl)
    have hadd := ideal_add_int (routingI M.base e) hm
      (routing_combination_mem M.base e 0 ((i : ℤ)-x) ((j : ℤ)-y) (by omega) (by omega) (by omega))
    convert hadd using 1 <;> ring
/-- A divisor containing a cannot divide any canonical a-Apéry value. -/
theorem canonical_residual_absent_of_a_predecessor
    (g : ℤ) (hg : g-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (i j : ℕ) (hi : i<criticalExponent M.base (e 1))
    (hj : j<criticalExponent M.base (e 2))
    (hc : i<P3R57.roleCoefficient M hp e 0 1 ∨ j<P3R57.roleCoefficient M hp e 0 2) :
    (i : ℤ)*b+j*c-g ∉ (routingH M.base e).asRelativeIdeal := by
  intro hm
  have hadd := ideal_add_int (routingH M.base e).asRelativeIdeal hg hm
  apply canonical_not_positive_a M hp e i j hi hj hc 1 (by omega)
    ((g-(a : ℤ))+((i : ℤ)*b+j*c-g)) hadd
  ring

/-- Both strict-RB seam candidates have positive a-support. -/
theorem rb_axes_a_predecessor_mem (n i j d : ℕ) (hl : RBLevel M hp e n i j d) :
    rbAxisA M hp e i j d-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal ∧
    rbAxisB M hp e i j d-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal := by
  obtain ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩ := hl
  have hs := P3R58.p3_coefficient_sums M hp e
  constructor
  · have hm := routing_combination_mem M.base e
      ((criticalExponent M.base (e 0) : ℤ)-d-1)
      ((i : ℤ)-P3R57.roleCoefficient M hp e 0 1) 0 (by omega) (by omega) (by omega)
    convert hm using 1 <;> unfold rbAxisA <;> ring
  · have hm := routing_combination_mem M.base e
      ((P3R57.roleCoefficient M hp e 1 0 : ℤ)-d-1)
      0 ((j : ℤ)+P3R57.roleCoefficient M hp e 1 2) (by omega) (by omega) (by omega)
    convert hm using 1 <;> unfold rbAxisB <;> ring

/-- Both strict-LT seam candidates have positive a-support. -/
theorem lt_axes_a_predecessor_mem (n i j d : ℕ) (hl : LTLevel M hp e n i j d) :
    ltAxisA M hp e i j d-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal ∧
    ltAxisB M hp e i j d-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal := by
  obtain ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩ := hl
  have hs := P3R58.p3_coefficient_sums M hp e
  constructor
  · have hm := routing_combination_mem M.base e
      ((P3R57.roleCoefficient M hp e 2 0 : ℤ)-d-1)
      ((i : ℤ)+P3R57.roleCoefficient M hp e 2 1) 0 (by omega) (by omega) (by omega)
    convert hm using 1 <;> unfold ltAxisA <;> ring
  · have hm := routing_combination_mem M.base e
      ((criticalExponent M.base (e 0) : ℤ)-d-1)
      0 ((j : ℤ)-P3R57.roleCoefficient M hp e 0 2) (by omega) (by omega) (by omega)
    convert hm using 1 <;> unfold ltAxisB <;> ring

/-- TW.04 / NF.07: the genuine final floor for arbitrary mixtures of strict arms. -/
theorem final_r3_canonical_membership (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (i j : ℕ) (hi : i<criticalExponent M.base (e 1))
    (hj : j<criticalExponent M.base (e 2))
    (hc : i<P3R57.roleCoefficient M hp e 0 1 ∨ j<P3R57.roleCoefficient M hp e 0 2) :
    ((i : ℤ)*b+j*c ∈ routingI M.base e) ↔
      ∃ n x y d, 0<n ∧ n<Q ∧
        (RBLevel M hp e n x y d ∨ LTLevel M hp e n x y d) ∧ x ≤ i ∧ y ≤ j := by
  constructor
  · intro hm
    obtain ⟨n,hn,hm⟩ := (L5A2C4OR3.mem_routingI_iff_positive_return M.base e _).mp hm
    have hm' : (i : ℤ)*b+j*c ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) := by
      simpa [L5A2C4OR1.routingM] using hm
    obtain ⟨n,hn,hnQ,hret⟩ := P3R59.positive_return_reduces _ _ M.base.q_positive _ n hn hm'
    by_cases hneq : n=Q
    · exact (canonical_principal_residual_absent M hp e htau i j hi hj hc
        (by simpa [hneq] using hret.2)).elim
    · have hnpre : n<Q := by omega
      rcases P3R66.r3_strict_return_exists M hp hR3 e n hn hnpre with hRB | hLT
      · obtain ⟨x,y,d,hl⟩ := rb_level_exists M hp e n hRB
        have haxes := rb_axes_a_predecessor_mem M hp e n x y d hl
        have hdata := hl
        obtain ⟨hx0,hy0,hd0,hx,hy,hxb,hyb,hd,he⟩ := hdata
        have hr := (rb_return_three_generators M hp e n x y d hx0 hy0 hd0 hx hy hxb hyb hd he _).mp hret
        rcases hr with hr | hr | hr
        · obtain ⟨hxi,hyj⟩ := canonical_residual_coordinates M.base e i j x y hi hj
            (P3R60.canonical_grid_value M.base e i j (P3R58.p3_lshape_canonical M hp e i j hi hj hc)) hr
          exact ⟨n,x,y,d,hn,hnpre,Or.inl hl,hxi,hyj⟩
        · exact (canonical_residual_absent_of_a_predecessor M hp e _ haxes.1 i j hi hj hc hr).elim
        · exact (canonical_residual_absent_of_a_predecessor M hp e _ haxes.2 i j hi hj hc hr).elim
      · obtain ⟨x,y,d,hl⟩ := lt_level_exists M hp e n hLT
        have haxes := lt_axes_a_predecessor_mem M hp e n x y d hl
        have hdata := hl
        obtain ⟨hx0,hy0,hd0,hx,hy,hxb,hyb,hd,he⟩ := hdata
        have hr := (lt_return_three_generators M hp e n x y d hx0 hy0 hd0 hx hy hxb hyb hd he _).mp hret
        rcases hr with hr | hr | hr
        · obtain ⟨hxi,hyj⟩ := canonical_residual_coordinates M.base e i j x y hi hj
            (P3R60.canonical_grid_value M.base e i j (P3R58.p3_lshape_canonical M hp e i j hi hj hc)) hr
          exact ⟨n,x,y,d,hn,hnpre,Or.inr hl,hxi,hyj⟩
        · exact (canonical_residual_absent_of_a_predecessor M hp e _ haxes.1 i j hi hj hc hr).elim
        · exact (canonical_residual_absent_of_a_predecessor M hp e _ haxes.2 i j hi hj hc hr).elim
  · rintro ⟨n,x,y,d,hn,hnQ,hl,hxi,hyj⟩
    have he : (x : ℤ)*b+y*c-(n*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal := by
      have heq : (x : ℤ)*b+y*c = (n*M.base.q.val : ℕ)+(d : ℤ)*a := by
        rcases hl with hl | hl <;> exact hl.2.2.2.2.2.2.2.2
      rw [heq]
      convert routing_combination_mem M.base e d 0 0 (by omega) (by omega) (by omega) using 1 <;> ring
    have hm := return_subset_final M e n hn _
      (show (x : ℤ)*b+y*c ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) from
        ⟨by simpa using routing_combination_mem M.base e 0 x y (by omega) (by omega) (by omega),he⟩)
    have hadd := ideal_add_int (routingI M.base e) hm
      (routing_combination_mem M.base e 0 ((i : ℤ)-x) ((j : ℤ)-y) (by omega) (by omega) (by omega))
    convert hadd using 1 <;> ring
/-- Literal eta=0 form of the mixed-arm final floor criterion. -/
theorem final_r3_height_zero_iff (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (i j : ℕ) (hi : i<criticalExponent M.base (e 1))
    (hj : j<criticalExponent M.base (e 2))
    (hc : i<P3R57.roleCoefficient M hp e 0 1 ∨ j<P3R57.roleCoefficient M hp e 0 2) :
    letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    idealHeight (routingI M.base e) a (P3R63.routing_ideal_subset M.base e)
        (((i : ℤ)*b+j*c : ℤ) : ZMod a)=0 ↔
      ∃ n x y d, 0<n ∧ n<Q ∧
        (RBLevel M hp e n x y d ∨ LTLevel M hp e n x y d) ∧ x ≤ i ∧ y ≤ j := by
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hcan := P3R60.canonical_grid_value M.base e i j (P3R58.p3_lshape_canonical M hp e i j hi hj hc)
  have hcan' : (routingH M.base e).asRelativeIdeal.aperyRepresentative a
      (((i : ℤ)*b+j*c : ℤ) : ZMod a)=(i : ℤ)*b+j*c := hcan
  rw [← final_r3_canonical_membership M hp e hR3 htau i j hi hj hc]
  constructor
  · intro hz
    have hm := canonical_mem_of_height_zero (routingI M.base e) a
      (P3R63.routing_ideal_subset M.base e) _ hz
    rwa [hcan'] at hm
  · exact canonical_height_zero (routingI M.base e) a (P3R63.routing_ideal_subset M.base e) _ hcan'
end
end NS25Lean.P3R67



