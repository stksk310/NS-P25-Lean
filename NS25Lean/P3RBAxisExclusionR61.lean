import NS25Lean.P3CanonicalDivisorR61
import NS25Lean.P3HerzogGridR61
import NS25Lean.P3IdealHeightsR61

set_option linter.style.header false
set_option maxHeartbeats 800000
noncomputable section
namespace NS25Lean.P3R61
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2B4AR1
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "P" => P3R57.roleCoefficient M hp e 0 1
local notation "T" => P3R57.roleCoefficient M hp e 0 2
local notation "U" => P3R57.roleCoefficient M hp e 1 0
local notation "V" => P3R57.roleCoefficient M hp e 1 2
local notation "C1" => criticalExponent M.base (e 0)
local notation "C2" => criticalExponent M.base (e 1)
local notation "C3" => criticalExponent M.base (e 2)
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

def rbSeedA (i : ℕ) : ℤ := ((i-1 : ℕ) : ℤ)*b+((T-1 : ℕ) : ℤ)*c

def rbSeedB (j : ℕ) : ℤ := ((C2-1 : ℕ) : ℤ)*b+((j-1 : ℕ) : ℤ)*c

theorem rb_axisA_no_double_zero (q : ℕ) (hq : 0<q)
    (hlevels : ∀ n, 0<n → n≤q → ∃ i j d, RBLevel M hp e n i j d)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤q) (hl : RBLevel M hp e n i j d)
    (hu : (P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq).aperyStepQuotient
      a b (routingHB M.base e) (rbSeedA M hp e i : ZMod a) = 0)
    (hv : (P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq).aperyStepQuotient
      a c (routingHC M.base e) (rbSeedA M hp e i : ZMod a) = 0) : False := by
  let I := P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq
  let x := rbSeedA M hp e i
  let y : ℤ := ((i : ℤ)-P-1)*b
  have hsub := birthIdeal_subset (routingH M.base e) M.base.q.val q hq
  have hbeta := rb_level_beta_mem M hp e q hq n i j d hn hnq hl
  rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  have hs := P3R58.p3_coefficient_sums M hp e
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hV := P3R58.p3_coefficients_positive M hp e 1 2 (by decide)
  have hi1 : ((i-1 : ℕ) : ℤ) = (i : ℤ)-1 := by omega
  have hT1 : ((T-1 : ℕ) : ℤ) = (T : ℤ)-1 := by omega
  have hxb : x+b = (i : ℤ)*b+((T-1 : ℕ) : ℤ)*c := by
    dsimp only [x,rbSeedA]; rw [hi1]; ring
  have hcanB := canonical_int_grid M hp e i ((T-1 : ℕ) : ℤ) (by omega) (by omega)
    (by exact_mod_cast hib) (by omega) (Or.inr (by omega))
  change (routingH M.base e).asRelativeIdeal.aperyRepresentative a
    (((i : ℤ)*b+(T-1 : ℕ)*c : ℤ) : ZMod a) = _ at hcanB
  rw [← hxb] at hcanB
  have hmemB : x+b ∈ I := by
    have hm := ideal_add_int I hbeta
      (routing_combination_mem M.base e 0 0 ((T-1 : ℕ)-j : ℤ) (by omega) (by omega) (by omega))
    convert hm using 1
    rw [hxb]
    push_cast
    ring
  have hseed := zero_b_seed_mem I a b hsub (routingHB M.base e) x hcanB hmemB hu
  change ((i-1 : ℕ) : ℤ)*b+((T-1 : ℕ) : ℤ)*c ∈ I at hseed
  obtain ⟨r,ir,jr,dr,hr,hrq,hrl,hir,hjr⟩ := rb_canonical_prefix_divisor M hp e q hq hlevels
    (i-1) (T-1) (by omega) (by omega) (Or.inr (by omega)) hseed
  have haxis := (rb_level_axes_mem M hp e q hq r ir jr dr hr hrq hrl).1
  rcases hrl with ⟨hir0,hjr0,hdr0,hirP,hjrT,hirC,hjrC,hdr,her⟩
  have hdrC : dr ≤ C1 := by omega
  have hcand : y+(a : ℤ)*((C1-dr : ℕ) : ℤ) ∈ I := by
    have hm := ideal_add_int I haxis
      (routing_combination_mem M.base e 0 ((i : ℤ)-1-ir) 0 (by omega) (by omega) (by omega))
    convert hm using 1
    dsimp only [y,rbAxisA]
    rw [Nat.cast_sub hdrC]
    push_cast
    ring
  have hopp : x+c = y+(a : ℤ)*C1 := by
    have hr := (normalized_relations M hp e).1
    dsimp only [x,rbSeedA,y]
    rw [hi1,hT1]
    nlinarith only [hr]
  exact stencil_zero_b_contradiction I a b c hsub (routingHB M.base e) (routingHC M.base e)
    x y C1 (C1-dr) hcanB hmemB hopp hu hv hcand (by omega)

theorem rb_axisB_no_double_zero (q : ℕ) (hq : 0<q)
    (hlevels : ∀ n, 0<n → n≤q → ∃ i j d, RBLevel M hp e n i j d)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤q) (hl : RBLevel M hp e n i j d)
    (hu : (P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq).aperyStepQuotient
      a b (routingHB M.base e) (rbSeedB M e j : ZMod a) = 0)
    (hv : (P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq).aperyStepQuotient
      a c (routingHC M.base e) (rbSeedB M e j : ZMod a) = 0) : False := by
  let I := P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq
  let x := rbSeedB M e j
  let y : ℤ := ((j : ℤ)+V-1)*c
  have hsub := birthIdeal_subset (routingH M.base e) M.base.q.val q hq
  have hbeta := rb_level_beta_mem M hp e q hq n i j d hn hnq hl
  rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  have hs := P3R58.p3_coefficient_sums M hp e
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hZ := P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  have hC21 : ((C2-1 : ℕ) : ℤ) = (C2 : ℤ)-1 := by omega
  have hj1 : ((j-1 : ℕ) : ℤ) = (j : ℤ)-1 := by omega
  have hxc : x+c = ((C2-1 : ℕ) : ℤ)*b+(j : ℤ)*c := by
    dsimp only [x,rbSeedB]; rw [hj1]; ring
  have hcanC := canonical_int_grid M hp e ((C2-1 : ℕ) : ℤ) j (by omega) (by omega)
    (by omega) (by exact_mod_cast hjb) (Or.inr (by exact_mod_cast hj))
  change (routingH M.base e).asRelativeIdeal.aperyRepresentative a
    ((((C2-1 : ℕ) : ℤ)*b+(j : ℤ)*c : ℤ) : ZMod a) = _ at hcanC
  rw [← hxc] at hcanC
  have hmemC : x+c ∈ I := by
    have hm := ideal_add_int I hbeta
      (routing_combination_mem M.base e 0 ((C2-1 : ℕ)-i : ℤ) 0 (by omega) (by omega) (by omega))
    convert hm using 1
    rw [hxc]
    push_cast
    ring
  have hseed := zero_c_seed_mem I a c hsub (routingHC M.base e) x hcanC hmemC hv
  change ((C2-1 : ℕ) : ℤ)*b+((j-1 : ℕ) : ℤ)*c ∈ I at hseed
  obtain ⟨r,ir,jr,dr,hr,hrq,hrl,hir,hjr⟩ := rb_canonical_prefix_divisor M hp e q hq hlevels
    (C2-1) (j-1) (by omega) (by omega) (Or.inr (by omega)) hseed
  have haxis := (rb_level_axes_mem M hp e q hq r ir jr dr hr hrq hrl).2
  rcases hrl with ⟨hir0,hjr0,hdr0,hirP,hjrT,hirC,hjrC,hdr,her⟩
  have hdrU : dr ≤ U := by omega
  have hcand : y+(a : ℤ)*((U-dr : ℕ) : ℤ) ∈ I := by
    have hm := ideal_add_int I haxis
      (routing_combination_mem M.base e 0 0 ((j : ℤ)-1-jr) (by omega) (by omega) (by omega))
    convert hm using 1
    dsimp only [y,rbAxisB]
    rw [Nat.cast_sub hdrU]
    push_cast
    ring
  have hopp : x+b = y+(a : ℤ)*U := by
    have hr := (normalized_relations M hp e).2.1
    dsimp only [x,rbSeedB,y]
    rw [hC21,hj1]
    nlinarith only [hr]
  exact stencil_zero_c_contradiction I a b c hsub (routingHB M.base e) (routingHC M.base e)
    x y U (U-dr) hcanC hmemC hopp hu hv hcand (by omega)

theorem rb_axisA_not_target (q : ℕ) (hq : 0<q)
    (hlevels : ∀ n, 0<n → n≤q → ∃ i j d, RBLevel M hp e n i j d)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤q) (hl : RBLevel M hp e n i j d)
    (s : ZMod a)
    (hs : L5A2C4I.ResidueData.SourceTargetBranch (P3R60.birthData M.base e q hq) s)
    (hw : (P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq).aperyRepresentative
      a ((P3R60.birthData M.base e q hq).branchTarget s) = rbAxisA M hp e i j d) : False := by
  have hi0 := hl.1
  have hj := hl.2.2.2.2.1
  have hT : 0<T := by omega
  have hi1 : ((i-1 : ℕ) : ℤ) = (i : ℤ)-1 := by omega
  have hT1 : ((T-1 : ℕ) : ℤ) = (T : ℤ)-1 := by omega
  have hweight : rbAxisA M hp e i j d =
      rbSeedA M hp e i+b+c+(-(d : ℤ))*a := by
    have hr := (normalized_relations M hp e).1
    dsimp only [rbAxisA,rbSeedA]
    rw [hi1,hT1]
    nlinarith only [hr]
  have hz := zero_edges_at_target_residue M.base e q hq s hs
    (rbSeedA M hp e i) (-(d : ℤ)) (hw.trans hweight)
  exact rb_axisA_no_double_zero M hp e q hq hlevels n i j d hn hnq hl hz.2.1 hz.2.2

theorem rb_axisB_not_target (q : ℕ) (hq : 0<q)
    (hlevels : ∀ n, 0<n → n≤q → ∃ i j d, RBLevel M hp e n i j d)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤q) (hl : RBLevel M hp e n i j d)
    (s : ZMod a)
    (hs : L5A2C4I.ResidueData.SourceTargetBranch (P3R60.birthData M.base e q hq) s)
    (hw : (P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq).aperyRepresentative
      a ((P3R60.birthData M.base e q hq).branchTarget s) = rbAxisB M hp e i j d) : False := by
  have hj0 := hl.2.1
  have hib := hl.2.2.2.2.2.1
  have hC2 : 0<C2 := by omega
  have hC21 : ((C2-1 : ℕ) : ℤ) = (C2 : ℤ)-1 := by omega
  have hj1 : ((j-1 : ℕ) : ℤ) = (j : ℤ)-1 := by omega
  have hweight : rbAxisB M hp e i j d =
      rbSeedB M e j+b+c+(-(d : ℤ))*a := by
    have hr := (normalized_relations M hp e).2.1
    dsimp only [rbAxisB,rbSeedB]
    rw [hC21,hj1]
    nlinarith only [hr]
  have hz := zero_edges_at_target_residue M.base e q hq s hs
    (rbSeedB M e j) (-(d : ℤ)) (hw.trans hweight)
  exact rb_axisB_no_double_zero M hp e q hq hlevels n i j d hn hnq hl hz.2.1 hz.2.2

end
end NS25Lean.P3R61



