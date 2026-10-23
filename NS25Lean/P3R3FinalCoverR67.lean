import NS25Lean.P3R3LastSwitchR66

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open L5A2C4OR1 L5A2C4OR3 P3R61
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
  (hR3 : (P3R51.internalDegrees M).card = 3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive

/-- Every positive return up to the first principal is an actual FINAL member. -/
theorem return_subset_final (q : ℕ) (hq : 0<q) (x : ℤ)
    (hx : x ∈ returnIdeal (routingH M.base e) (q*M.base.q.val)) :
    x ∈ routingI M.base e := by
  exact (mem_routingI_iff_positive_return M.base e x).mpr ⟨q,hq,by simpa [routingM] using hx⟩

/-- TW.03 support separation quantifies over every removable generator of x
and every removable generator of its return remainder. -/
theorem final_minimal_return_support_disjoint (w : ℤ)
    (hw : (routingI M.base e).IsMinimalGenerator w)
    (q g : ℕ) (hq : 0<q) (hg : g ∈ routingH M.base e) (hg0 : g≠0)
    (hleft : w-g ∈ (routingH M.base e).asRelativeIdeal)
    (hright : w-(q*M.base.q.val : ℕ)-g ∈ (routingH M.base e).asRelativeIdeal) : False := by
  apply hw.2 g hg hg0
  apply return_subset_final M e q hq
  refine ⟨hleft,?_⟩
  change w-g-(q*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal
  convert hright using 1 <;> ring
include hR3 in
/-- TW.03: exhaustive final cover; candidates may coincide or be redundant. -/
theorem final_r3_generator_cover (w : ℤ) (hw : (routingI M.base e).IsMinimalGenerator w) :
    w = (Q*M.base.q.val : ℕ) ∨
      ∃ q i j d, 0<q ∧ q<Q ∧
        ((RBLevel M hp e q i j d ∧
          (w=(i : ℤ)*b+j*c ∨ w=rbAxisA M hp e i j d ∨ w=rbAxisB M hp e i j d)) ∨
        (LTLevel M hp e q i j d ∧
          (w=(i : ℤ)*b+j*c ∨ w=ltAxisA M hp e i j d ∨ w=ltAxisB M hp e i j d))) := by
  obtain ⟨n,hn,hwn⟩ := (mem_routingI_iff_positive_return M.base e w).mp hw.1
  have hwn' : w ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) := by
    simpa [routingM] using hwn
  obtain ⟨q,hq,hqQ,hret⟩ := P3R59.positive_return_reduces _ _ M.base.q_positive w n hn hwn'
  by_cases hqeq : q=Q
  · left
    have hprincipal := (P3R62.routing_principal_isMinimalGenerator M.base e).1
    exact minimal_generator_eq_of_residual _ w _ hw hprincipal (by simpa [hqeq] using hret.2)
  · right
    have hqpre : q<Q := by omega
    rcases P3R66.r3_strict_return_exists M hp hR3 e q hq hqpre with hRB | hLT
    · obtain ⟨i,j,d,hl⟩ := rb_level_exists M hp e q hRB
      refine ⟨q,i,j,d,hq,hqpre,Or.inl ⟨hl,?_⟩⟩
      rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
      have hcover := (rb_return_three_generators M hp e q i j d hi0 hj0 hd0 hi hj hib hjb hd he w).mp hret
      have haxes := rb_axes_mem M hp e q i j d hi0 hj0 hd0 hi hj hib hjb hd he
      have hbeta : (i : ℤ)*b+j*c ∈ returnIdeal (routingH M.base e) (q*M.base.q.val) := by
        refine ⟨?_,?_⟩
        · simpa using routing_combination_mem M.base e 0 i j le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        · change (i : ℤ)*b+j*c-(q*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal
          rw [he]
          convert routing_combination_mem M.base e d 0 0 (Nat.cast_nonneg _) le_rfl le_rfl using 1 <;> ring
      rcases hcover with h | h | h
      · exact Or.inl (minimal_generator_eq_of_residual _ w _ hw (return_subset_final M e q hq _ hbeta) h)
      · exact Or.inr (Or.inl (minimal_generator_eq_of_residual _ w _ hw (return_subset_final M e q hq _ haxes.1) h))
      · exact Or.inr (Or.inr (minimal_generator_eq_of_residual _ w _ hw (return_subset_final M e q hq _ haxes.2) h))
    · obtain ⟨i,j,d,hl⟩ := lt_level_exists M hp e q hLT
      refine ⟨q,i,j,d,hq,hqpre,Or.inr ⟨hl,?_⟩⟩
      rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
      have hcover := (lt_return_three_generators M hp e q i j d hi0 hj0 hd0 hi hj hib hjb hd he w).mp hret
      have haxes := lt_axes_mem M hp e q i j d hi0 hj0 hd0 hi hj hib hjb hd he
      have hbeta : (i : ℤ)*b+j*c ∈ returnIdeal (routingH M.base e) (q*M.base.q.val) := by
        refine ⟨?_,?_⟩
        · simpa using routing_combination_mem M.base e 0 i j le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        · change (i : ℤ)*b+j*c-(q*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal
          rw [he]
          convert routing_combination_mem M.base e d 0 0 (Nat.cast_nonneg _) le_rfl le_rfl using 1 <;> ring
      rcases hcover with h | h | h
      · exact Or.inl (minimal_generator_eq_of_residual _ w _ hw (return_subset_final M e q hq _ hbeta) h)
      · exact Or.inr (Or.inl (minimal_generator_eq_of_residual _ w _ hw (return_subset_final M e q hq _ haxes.1) h))
      · exact Or.inr (Or.inr (minimal_generator_eq_of_residual _ w _ hw (return_subset_final M e q hq _ haxes.2) h))
include hR3 in
/-- TW.03 exact ideal cover, retaining residual divisibility for arbitrary members. -/
theorem final_r3_membership_cover (w : ℤ) (hw : w ∈ routingI M.base e) :
    w-(Q*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal ∨
      ∃ q i j d, 0<q ∧ q<Q ∧
        ((RBLevel M hp e q i j d ∧
          (w-((i : ℤ)*b+j*c) ∈ (routingH M.base e).asRelativeIdeal ∨
           w-rbAxisA M hp e i j d ∈ (routingH M.base e).asRelativeIdeal ∨
           w-rbAxisB M hp e i j d ∈ (routingH M.base e).asRelativeIdeal)) ∨
        (LTLevel M hp e q i j d ∧
          (w-((i : ℤ)*b+j*c) ∈ (routingH M.base e).asRelativeIdeal ∨
           w-ltAxisA M hp e i j d ∈ (routingH M.base e).asRelativeIdeal ∨
           w-ltAxisB M hp e i j d ∈ (routingH M.base e).asRelativeIdeal))) := by
  obtain ⟨n,hn,hwn⟩ := (mem_routingI_iff_positive_return M.base e w).mp hw
  have hwn' : w ∈ returnIdeal (routingH M.base e) (n*M.base.q.val) := by
    simpa [routingM] using hwn
  obtain ⟨q,hq,hqQ,hret⟩ := P3R59.positive_return_reduces _ _ M.base.q_positive w n hn hwn'
  by_cases hqeq : q=Q
  · exact Or.inl (by simpa [hqeq] using hret.2)
  · right
    have hqpre : q<Q := by omega
    rcases P3R66.r3_strict_return_exists M hp hR3 e q hq hqpre with hRB | hLT
    · obtain ⟨i,j,d,hl⟩ := rb_level_exists M hp e q hRB
      refine ⟨q,i,j,d,hq,hqpre,Or.inl ⟨hl,?_⟩⟩
      rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
      exact (rb_return_three_generators M hp e q i j d hi0 hj0 hd0 hi hj hib hjb hd he w).mp hret
    · obtain ⟨i,j,d,hl⟩ := lt_level_exists M hp e q hLT
      refine ⟨q,i,j,d,hq,hqpre,Or.inr ⟨hl,?_⟩⟩
      rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
      exact (lt_return_three_generators M hp e q i j d hi0 hj0 hd0 hi hj hib hjb hd he w).mp hret

/-- Exact all-RB membership cover without a principal-shape assumption. -/
theorem final_rb_membership_cover (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, RBLevel M hp e n i j d)
    (w : ℤ) (hw : w ∈ routingI M.base e) :
    w-(Q*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal ∨
      ∃ q i j d, 0<q ∧ q<Q ∧ RBLevel M hp e q i j d ∧
        (w-((i : ℤ)*b+j*c) ∈ (routingH M.base e).asRelativeIdeal ∨
         w-rbAxisA M hp e i j d ∈ (routingH M.base e).asRelativeIdeal ∨
         w-rbAxisB M hp e i j d ∈ (routingH M.base e).asRelativeIdeal) := by
  have hm := hw
  rw [P3R62.routingI_eq_inserted_ideal M.base e hQ] at hm
  rcases hm with hpre | hprincipal
  · right
    obtain ⟨q,i,j,d,hq,hqQ,hl,hr⟩ := rb_prefix_cover M hp e (Q-1) (by omega)
      (by intro n hn hnq; exact hlevels n hn (by omega)) w hpre
    exact ⟨q,i,j,d,hq,by omega,hl,hr⟩
  · exact Or.inl hprincipal
end
end NS25Lean.P3R67




