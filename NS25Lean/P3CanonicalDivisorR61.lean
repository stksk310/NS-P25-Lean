import NS25Lean.P3CanonicalCoordinatesR61
import NS25Lean.P3ReturnGeneratorsR61
import NS25Lean.P3PrefixRoutingR60
set_option linter.style.header false
set_option maxHeartbeats 800000
noncomputable section
namespace NS25Lean.P3R61
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2B4AR1
open L5A2C4OR3 L5A2C4OR4
variable {Gamma : NumericalSemigroup}

def LTLevel (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (n i j d : ℕ) : Prop :=
  0 < i ∧ 0 < j ∧ 0 < d ∧ i < P3R57.roleCoefficient M hp e 0 1 ∧ P3R57.roleCoefficient M hp e 0 2 < j ∧
  i < criticalExponent M.base (e 1) ∧ j < criticalExponent M.base (e 2) ∧
  d < P3R57.roleCoefficient M hp e 2 0 ∧
  (i : ℤ)*routingB M.base e+j*routingC M.base e =
    (n*M.base.q.val : ℕ)+d*routingA M.base e

theorem lt_level_exists (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (n : ℕ) (hret : P3R59.LTReturn M hp e n) :
    ∃ i j d, LTLevel M hp e n i j d := by
  obtain ⟨s,t,d,hs,hsp,ht,htp,hd,hdp,he⟩ := hret
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  refine ⟨s, (P3R57.roleCoefficient M hp e 0 2+t), d, ?_⟩
  unfold LTLevel
  refine ⟨by omega, by omega, hd, by omega, by omega, by omega, by omega, hdp, ?_⟩
  simpa only [Nat.cast_mul] using he

theorem lt_level_axes_mem (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q) (n i j d : ℕ)
    (hn : 0 < n) (hnq : n ≤ q) (hlevel : LTLevel M hp e n i j d) :
    ltAxisA M hp e i j d ∈ P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq ∧
    ltAxisB M hp e i j d ∈ P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq := by
  rcases hlevel with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  obtain ⟨hA,hB⟩ := lt_axes_mem M hp e n i j d hi0 hj0 hd0 hi hj hib hjb hd he
  exact ⟨⟨n,hn,by omega,hA⟩,⟨n,hn,by omega,hB⟩⟩

theorem lt_prefix_cover (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q)
    (hlevels : ∀ n, 0 < n → n ≤ q → ∃ i j d, LTLevel M hp e n i j d)
    (x : ℤ) (hx : x ∈ P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq) :
    ∃ n i j d, 0 < n ∧ n ≤ q ∧ LTLevel M hp e n i j d ∧
      (x-((i : ℤ)*routingB M.base e+j*routingC M.base e) ∈ (routingH M.base e).asRelativeIdeal ∨
      x-ltAxisA M hp e i j d ∈ (routingH M.base e).asRelativeIdeal ∨
      x-ltAxisB M hp e i j d ∈ (routingH M.base e).asRelativeIdeal) := by
  obtain ⟨n,hn,hnq,hx⟩ := hx
  obtain ⟨i,j,d,hl⟩ := hlevels n hn (by omega)
  refine ⟨n,i,j,d,hn,by omega,hl,?_⟩
  rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  exact (lt_return_three_generators M hp e n i j d hi0 hj0 hd0 hi hj hib hjb hd he x).mp hx

def RBLevel (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (n i j d : ℕ) : Prop :=
  0 < i ∧ 0 < j ∧ 0 < d ∧ P3R57.roleCoefficient M hp e 0 1 < i ∧ j < P3R57.roleCoefficient M hp e 0 2 ∧
  i < criticalExponent M.base (e 1) ∧ j < criticalExponent M.base (e 2) ∧
  d < P3R57.roleCoefficient M hp e 1 0 ∧
  (i : ℤ)*routingB M.base e+j*routingC M.base e =
    (n*M.base.q.val : ℕ)+d*routingA M.base e

theorem rb_level_exists (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (n : ℕ) (hret : P3R59.RBReturn M hp e n) :
    ∃ i j d, RBLevel M hp e n i j d := by
  obtain ⟨s,t,d,hs,hsp,ht,htp,hd,hdp,he⟩ := hret
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  refine ⟨(P3R57.roleCoefficient M hp e 0 1+s), t, d, ?_⟩
  unfold RBLevel
  refine ⟨by omega, by omega, hd, by omega, by omega, by omega, by omega, hdp, ?_⟩
  simpa only [Nat.cast_mul] using he

theorem rb_level_axes_mem (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q) (n i j d : ℕ)
    (hn : 0 < n) (hnq : n ≤ q) (hlevel : RBLevel M hp e n i j d) :
    rbAxisA M hp e i j d ∈ P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq ∧
    rbAxisB M hp e i j d ∈ P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq := by
  rcases hlevel with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  obtain ⟨hA,hB⟩ := rb_axes_mem M hp e n i j d hi0 hj0 hd0 hi hj hib hjb hd he
  exact ⟨⟨n,hn,by omega,hA⟩,⟨n,hn,by omega,hB⟩⟩

theorem rb_prefix_cover (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q)
    (hlevels : ∀ n, 0 < n → n ≤ q → ∃ i j d, RBLevel M hp e n i j d)
    (x : ℤ) (hx : x ∈ P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq) :
    ∃ n i j d, 0 < n ∧ n ≤ q ∧ RBLevel M hp e n i j d ∧
      (x-((i : ℤ)*routingB M.base e+j*routingC M.base e) ∈ (routingH M.base e).asRelativeIdeal ∨
      x-rbAxisA M hp e i j d ∈ (routingH M.base e).asRelativeIdeal ∨
      x-rbAxisB M hp e i j d ∈ (routingH M.base e).asRelativeIdeal) := by
  obtain ⟨n,hn,hnq,hx⟩ := hx
  obtain ⟨i,j,d,hl⟩ := hlevels n hn (by omega)
  refine ⟨n,i,j,d,hn,by omega,hl,?_⟩
  rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  exact (rb_return_three_generators M hp e n i j d hi0 hj0 hd0 hi hj hib hjb hd he x).mp hx



theorem lt_level_beta_mem (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q) (n i j d : ℕ)
    (hn : 0 < n) (hnq : n ≤ q) (hlevel : LTLevel M hp e n i j d) :
    (i : ℤ)*routingB M.base e+j*routingC M.base e ∈
      P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq := by
  rcases hlevel with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  refine ⟨n,hn,by omega,?_⟩
  rw [mem_returnIdeal_iff]
  refine ⟨?_,?_⟩
  · simpa using routing_combination_mem M.base e 0 i j le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [he]
    convert routing_combination_mem M.base e d 0 0 (Nat.cast_nonneg _) le_rfl le_rfl using 1 <;> ring

theorem lt_canonical_prefix_divisor (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q)
    (hlevels : ∀ n, 0 < n → n ≤ q → ∃ x y d, LTLevel M hp e n x y d)
    (i j : ℕ) (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hc : i < P3R57.roleCoefficient M hp e 0 1 ∨ j < P3R57.roleCoefficient M hp e 0 2)
    (hm : (i : ℤ)*routingB M.base e+j*routingC M.base e ∈
      P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq) :
    ∃ n x y d, 0 < n ∧ n ≤ q ∧ LTLevel M hp e n x y d ∧ x ≤ i ∧ y ≤ j := by
  obtain ⟨n,x,y,d,hn,hnq,hl,hr⟩ := lt_prefix_cover M hp e q hq hlevels _ hm
  refine ⟨n,x,y,d,hn,hnq,hl,?_⟩
  have hcan := P3R60.canonical_grid_value M.base e i j (P3R58.p3_lshape_canonical M hp e i j hi hj hc)
  rcases hr with hr | hr | hr
  · exact canonical_residual_coordinates M.base e i j x y hi hj hcan hr
  · exfalso
    rcases hl with ⟨hx0,hy0,hd0,hx,hy,hxb,hyb,hd,he⟩
    have hs := P3R58.p3_coefficient_sums M hp e
    have hkp : (0 : ℤ) < (P3R57.roleCoefficient M hp e 2 0 : ℤ)-d := by
      have hdI : (d : ℤ) < P3R57.roleCoefficient M hp e 2 0 := by exact_mod_cast (show d < P3R57.roleCoefficient M hp e 2 0 by omega)
      omega
    have htail := routing_combination_mem M.base e 0 ((x : ℤ)+P3R57.roleCoefficient M hp e 2 1) 0 le_rfl (by exact_mod_cast (show 0 ≤ ((x : ℤ)+P3R57.roleCoefficient M hp e 2 1) by omega)) le_rfl
    have hadd := ideal_add_int (routingH M.base e).asRelativeIdeal htail hr
    apply canonical_not_positive_a M hp e i j hi hj hc ((P3R57.roleCoefficient M hp e 2 0 : ℤ)-d) hkp
      (((x : ℤ)+P3R57.roleCoefficient M hp e 2 1)*routingB M.base e+((i : ℤ)*routingB M.base e+j*routingC M.base e-ltAxisA M hp e x y d))
      (by simpa only [zero_mul, zero_add, add_zero] using hadd)
    unfold ltAxisA
    ring
  · exfalso
    rcases hl with ⟨hx0,hy0,hd0,hx,hy,hxb,hyb,hd,he⟩
    have hs := P3R58.p3_coefficient_sums M hp e
    have hkp : (0 : ℤ) < (criticalExponent M.base (e 0) : ℤ)-d := by
      have hdI : (d : ℤ) < criticalExponent M.base (e 0) := by exact_mod_cast (show d < criticalExponent M.base (e 0) by omega)
      omega
    have htail := routing_combination_mem M.base e 0 0 ((y : ℤ)-P3R57.roleCoefficient M hp e 0 2) le_rfl le_rfl (by exact_mod_cast (show 0 ≤ ((y : ℤ)-P3R57.roleCoefficient M hp e 0 2) by omega))
    have hadd := ideal_add_int (routingH M.base e).asRelativeIdeal htail hr
    apply canonical_not_positive_a M hp e i j hi hj hc ((criticalExponent M.base (e 0) : ℤ)-d) hkp
      (((y : ℤ)-P3R57.roleCoefficient M hp e 0 2)*routingC M.base e+((i : ℤ)*routingB M.base e+j*routingC M.base e-ltAxisB M hp e x y d))
      (by simpa only [zero_mul, zero_add, add_zero] using hadd)
    unfold ltAxisB
    ring

theorem rb_level_beta_mem (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q) (n i j d : ℕ)
    (hn : 0 < n) (hnq : n ≤ q) (hlevel : RBLevel M hp e n i j d) :
    (i : ℤ)*routingB M.base e+j*routingC M.base e ∈
      P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq := by
  rcases hlevel with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  refine ⟨n,hn,by omega,?_⟩
  rw [mem_returnIdeal_iff]
  refine ⟨?_,?_⟩
  · simpa using routing_combination_mem M.base e 0 i j le_rfl (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [he]
    convert routing_combination_mem M.base e d 0 0 (Nat.cast_nonneg _) le_rfl le_rfl using 1 <;> ring

theorem rb_canonical_prefix_divisor (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (q : ℕ) (hq : 0 < q)
    (hlevels : ∀ n, 0 < n → n ≤ q → ∃ x y d, RBLevel M hp e n x y d)
    (i j : ℕ) (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hc : i < P3R57.roleCoefficient M hp e 0 1 ∨ j < P3R57.roleCoefficient M hp e 0 2)
    (hm : (i : ℤ)*routingB M.base e+j*routingC M.base e ∈
      P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq) :
    ∃ n x y d, 0 < n ∧ n ≤ q ∧ RBLevel M hp e n x y d ∧ x ≤ i ∧ y ≤ j := by
  obtain ⟨n,x,y,d,hn,hnq,hl,hr⟩ := rb_prefix_cover M hp e q hq hlevels _ hm
  refine ⟨n,x,y,d,hn,hnq,hl,?_⟩
  have hcan := P3R60.canonical_grid_value M.base e i j (P3R58.p3_lshape_canonical M hp e i j hi hj hc)
  rcases hr with hr | hr | hr
  · exact canonical_residual_coordinates M.base e i j x y hi hj hcan hr
  · exfalso
    rcases hl with ⟨hx0,hy0,hd0,hx,hy,hxb,hyb,hd,he⟩
    have hs := P3R58.p3_coefficient_sums M hp e
    have hkp : (0 : ℤ) < (criticalExponent M.base (e 0) : ℤ)-d := by
      have hdI : (d : ℤ) < criticalExponent M.base (e 0) := by exact_mod_cast (show d < criticalExponent M.base (e 0) by omega)
      omega
    have htail := routing_combination_mem M.base e 0 ((x : ℤ)-P3R57.roleCoefficient M hp e 0 1) 0 le_rfl (by exact_mod_cast (show 0 ≤ ((x : ℤ)-P3R57.roleCoefficient M hp e 0 1) by omega)) le_rfl
    have hadd := ideal_add_int (routingH M.base e).asRelativeIdeal htail hr
    apply canonical_not_positive_a M hp e i j hi hj hc ((criticalExponent M.base (e 0) : ℤ)-d) hkp
      (((x : ℤ)-P3R57.roleCoefficient M hp e 0 1)*routingB M.base e+((i : ℤ)*routingB M.base e+j*routingC M.base e-rbAxisA M hp e x y d))
      (by simpa only [zero_mul, zero_add, add_zero] using hadd)
    unfold rbAxisA
    ring
  · exfalso
    rcases hl with ⟨hx0,hy0,hd0,hx,hy,hxb,hyb,hd,he⟩
    have hs := P3R58.p3_coefficient_sums M hp e
    have hkp : (0 : ℤ) < (P3R57.roleCoefficient M hp e 1 0 : ℤ)-d := by
      have hdI : (d : ℤ) < P3R57.roleCoefficient M hp e 1 0 := by exact_mod_cast (show d < P3R57.roleCoefficient M hp e 1 0 by omega)
      omega
    have htail := routing_combination_mem M.base e 0 0 ((y : ℤ)+P3R57.roleCoefficient M hp e 1 2) le_rfl le_rfl (by exact_mod_cast (show 0 ≤ ((y : ℤ)+P3R57.roleCoefficient M hp e 1 2) by omega))
    have hadd := ideal_add_int (routingH M.base e).asRelativeIdeal htail hr
    apply canonical_not_positive_a M hp e i j hi hj hc ((P3R57.roleCoefficient M hp e 1 0 : ℤ)-d) hkp
      (((y : ℤ)+P3R57.roleCoefficient M hp e 1 2)*routingC M.base e+((i : ℤ)*routingB M.base e+j*routingC M.base e-rbAxisB M hp e x y d))
      (by simpa only [zero_mul, zero_add, add_zero] using hadd)
    unfold rbAxisB
    ring
end NS25Lean.P3R61




