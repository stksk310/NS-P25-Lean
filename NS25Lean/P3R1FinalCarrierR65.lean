import NS25Lean.P3R2FinalCarrierR63

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R65
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open L5A2C4OR3 P3R61
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive

/-- CU.05: each actual LT candidate belongs to the final ideal. -/
theorem final_lt_candidates_mem (hQ : 1<Q) (n i j d : ℕ)
    (hn : 0<n) (hnQ : n < Q) (hl : LTLevel M hp e n i j d) :
    (i : ℤ)*b+j*c ∈ routingI M.base e ∧
    ltAxisA M hp e i j d ∈ routingI M.base e ∧
    ltAxisB M hp e i j d ∈ routingI M.base e := by
  have hb := lt_level_beta_mem M hp e (Q-1) (by omega) n i j d hn (by omega) hl
  have hx := lt_level_axes_mem M hp e (Q-1) (by omega) n i j d hn (by omega) hl
  exact ⟨P3R63.completed_prefix_subset_final M.base e hQ _ hb,
    P3R63.completed_prefix_subset_final M.base e hQ _ hx.1,
    P3R63.completed_prefix_subset_final M.base e hQ _ hx.2⟩

/-- CU.06: exhaustive FINAL minimal-generator cover, including the principal. -/
theorem final_lt_generator_cover (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n < Q → ∃ i j d, LTLevel M hp e n i j d)
    (w : ℤ) (hw : (routingI M.base e).IsMinimalGenerator w) :
    w = (Q*M.base.q.val : ℕ) ∨
      ∃ n i j d, 0<n ∧ n < Q ∧ LTLevel M hp e n i j d ∧
        (w=(i : ℤ)*b+j*c ∨ w=ltAxisA M hp e i j d ∨ w=ltAxisB M hp e i j d) := by
  have hm := hw.1
  rw [P3R62.routingI_eq_inserted_ideal M.base e hQ] at hm
  rcases hm with hpre | hprincipal
  · obtain ⟨n,i,j,d,hn,hnq,hl,hr⟩ := lt_prefix_cover M hp e (Q-1) (by omega)
      (by intro n hn hnq; exact hlevels n hn (by omega)) w hpre
    right
    refine ⟨n,i,j,d,hn,by omega,hl,?_⟩
    have hc := final_lt_candidates_mem M hp e hQ n i j d hn (by omega) hl
    rcases hr with hr | hr | hr
    · exact Or.inl (minimal_generator_eq_of_residual _ w _ hw hc.1 hr)
    · exact Or.inr (Or.inl (minimal_generator_eq_of_residual _ w _ hw hc.2.1 hr))
    · exact Or.inr (Or.inr (minimal_generator_eq_of_residual _ w _ hw hc.2.2 hr))
  · left
    exact minimal_generator_eq_of_residual _ w _ hw
      (P3R62.routing_principal_isMinimalGenerator M.base e).1 hprincipal

/-- CU.07: final canonical membership has exactly the principal or LT-floor divisor. -/
theorem final_lt_canonical_membership (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n < Q → ∃ x y d, LTLevel M hp e n x y d)
    (k : ℕ) (ht : Q*M.base.q.val=k*c)
    (i j : ℕ) (hi : i<criticalExponent M.base (e 1))
    (hj : j<criticalExponent M.base (e 2))
    (hc : i<P3R57.roleCoefficient M hp e 0 1 ∨ j<P3R57.roleCoefficient M hp e 0 2) :
    ((i : ℤ)*b+j*c ∈ routingI M.base e) ↔
      k ≤ j ∨ ∃ n x y d, 0<n ∧ n < Q ∧ LTLevel M hp e n x y d ∧ x ≤ i ∧ y ≤ j := by
  constructor
  · intro hm
    rw [P3R62.routingI_eq_inserted_ideal M.base e hQ] at hm
    rcases hm with hpre | hprincipal
    · right
      obtain ⟨n,x,y,d,hn,hnq,hl,hx,hy⟩ := lt_canonical_prefix_divisor M hp e (Q-1)
        (by omega) (by intro n hn hnq; exact hlevels n hn (by omega)) i j hi hj hc hpre
      exact ⟨n,x,y,d,hn,by omega,hl,hx,hy⟩
    · left
      change (i : ℤ)*b+j*c-(Q*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal at hprincipal
      rw [ht] at hprincipal
      exact (canonical_residual_coordinates M.base e i j 0 k hi hj
        (P3R60.canonical_grid_value M.base e i j (P3R58.p3_lshape_canonical M hp e i j hi hj hc))
        (by simpa using hprincipal)).2
  · rintro (hkj | ⟨n,x,y,d,hn,hnQ,hl,hxi,hyj⟩)
    · have hm := (P3R62.routing_principal_isMinimalGenerator M.base e).1
      have hres := int_grid_mem M.base e (i : ℤ) ((j : ℤ)-k) (by omega) (by omega)
      have hadd := ideal_add_int (routingI M.base e) hm hres
      rw [ht] at hadd
      convert hadd using 1 <;> push_cast <;> ring
    · have hm := (final_lt_candidates_mem M hp e hQ n x y d hn hnQ hl).1
      have hres := int_grid_mem M.base e ((i : ℤ)-x) ((j : ℤ)-y) (by omega) (by omega)
      have hadd := ideal_add_int (routingI M.base e) hm hres
      convert hadd using 1 <;> ring
end
end NS25Lean.P3R65
