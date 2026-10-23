import NS25Lean.P3R3SeamR67
import NS25Lean.P3CanonicalDivisorR61
import NS25Lean.P3HerzogGridR61
import NS25Lean.P3IdealHeightsR61

set_option linter.style.header false
set_option maxHeartbeats 800000
noncomputable section
namespace NS25Lean.P3R67
open P3R61 P3R63 L5A2C4I
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
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

theorem mixed_rb_axisA_no_double_zero (q : ℕ) (hq : 0<q)
(I : RelativeIdeal (routingH M.base e))
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ (routingH M.base e).asRelativeIdeal)
    (hprefix : ∀ x : ℤ, x ∈ P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq → x ∈ I)
    (hdivisor : ∀ x y : ℕ, x < C2 → y < T →
      (x : ℤ)*b+y*c ∈ I →
      ∃ r ir jr dr, 0<r ∧ r≤q ∧ RBLevel M hp e r ir jr dr ∧ ir≤x ∧ jr≤y)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤q) (hl : RBLevel M hp e n i j d)
    (hu : I.aperyStepQuotient
      a b (routingHB M.base e) (finalRBSeedA M hp e i : ZMod a) = 0)
    (hv : I.aperyStepQuotient
      a c (routingHC M.base e) (finalRBSeedA M hp e i : ZMod a) = 0) : False := by
  let x := finalRBSeedA M hp e i
  let y : ℤ := ((i : ℤ)-P-1)*b
  have hbeta := hprefix _ (rb_level_beta_mem M hp e q hq n i j d hn hnq hl)
  rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  have hs := P3R58.p3_coefficient_sums M hp e
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hV := P3R58.p3_coefficients_positive M hp e 1 2 (by decide)
  have hi1 : ((i-1 : ℕ) : ℤ) = (i : ℤ)-1 := by omega
  have hT1 : ((T-1 : ℕ) : ℤ) = (T : ℤ)-1 := by omega
  have hxb : x+b = (i : ℤ)*b+((T-1 : ℕ) : ℤ)*c := by
    dsimp only [x,finalRBSeedA]; rw [hi1]; ring
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
  obtain ⟨r,ir,jr,dr,hr,hrq,hrl,hir,hjr⟩ := hdivisor (i-1) (T-1) (by omega) (by omega) hseed
  have haxis := hprefix _ (rb_level_axes_mem M hp e q hq r ir jr dr hr hrq hrl).1
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
    dsimp only [x,finalRBSeedA,y]
    rw [hi1,hT1]
    nlinarith only [hr]
  exact stencil_zero_b_contradiction I a b c hsub (routingHB M.base e) (routingHC M.base e)
    x y C1 (C1-dr) hcanB hmemB hopp hu hv hcand (by omega)

theorem mixed_rb_axisB_no_double_zero (q : ℕ) (hq : 0<q)
(I : RelativeIdeal (routingH M.base e))
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ (routingH M.base e).asRelativeIdeal)
    (hprefix : ∀ x : ℤ, x ∈ P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq → x ∈ I)
    (hdivisor : ∀ x y : ℕ, x < C2 → y < T →
      (x : ℤ)*b+y*c ∈ I →
      ∃ r ir jr dr, 0<r ∧ r≤q ∧ RBLevel M hp e r ir jr dr ∧ ir≤x ∧ jr≤y)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤q) (hl : RBLevel M hp e n i j d)
    (hu : I.aperyStepQuotient
      a b (routingHB M.base e) (finalRBSeedB M e j : ZMod a) = 0)
    (hv : I.aperyStepQuotient
      a c (routingHC M.base e) (finalRBSeedB M e j : ZMod a) = 0) : False := by
  let x := finalRBSeedB M e j
  let y : ℤ := ((j : ℤ)+V-1)*c
  have hbeta := hprefix _ (rb_level_beta_mem M hp e q hq n i j d hn hnq hl)
  rcases hl with ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩
  have hs := P3R58.p3_coefficient_sums M hp e
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hZ := P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  have hC21 : ((C2-1 : ℕ) : ℤ) = (C2 : ℤ)-1 := by omega
  have hj1 : ((j-1 : ℕ) : ℤ) = (j : ℤ)-1 := by omega
  have hxc : x+c = ((C2-1 : ℕ) : ℤ)*b+(j : ℤ)*c := by
    dsimp only [x,finalRBSeedB]; rw [hj1]; ring
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
  obtain ⟨r,ir,jr,dr,hr,hrq,hrl,hir,hjr⟩ := hdivisor (C2-1) (j-1) (by omega) (by omega) hseed
  have haxis := hprefix _ (rb_level_axes_mem M hp e q hq r ir jr dr hr hrq hrl).2
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
    dsimp only [x,finalRBSeedB,y]
    rw [hC21,hj1]
    nlinarith only [hr]
  exact stencil_zero_c_contradiction I a b c hsub (routingHB M.base e) (routingHC M.base e)
    x y U (U-dr) hcanC hmemC hopp hu hv hcand (by omega)

theorem mixed_rb_axisA_not_target (hQ : 1<Q)
    (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤Q-1) (hl : RBLevel M hp e n i j d)
    (s : ZMod a)
    (hs : L5A2C4I.ResidueData.SourceTargetBranch (routingData M.base e) s)
    (hw : (routingI M.base e).aperyRepresentative
      a ((routingData M.base e).branchTarget s) = rbAxisA M hp e i j d) : False := by
  have hi0 := hl.1
  have hj := hl.2.2.2.2.1
  have hT : 0<T := by omega
  have hi1 : ((i-1 : ℕ) : ℤ) = (i : ℤ)-1 := by omega
  have hT1 : ((T-1 : ℕ) : ℤ) = (T : ℤ)-1 := by omega
  have hweight : rbAxisA M hp e i j d =
      finalRBSeedA M hp e i+b+c+(-(d : ℤ))*a := by
    have hr := (normalized_relations M hp e).1
    dsimp only [rbAxisA,finalRBSeedA]
    rw [hi1,hT1]
    nlinarith only [hr]
  have hz := routing_zero_edges_at_target M e s hs
    (finalRBSeedA M hp e i) (-(d : ℤ)) (hw.trans hweight)
  exact mixed_rb_axisA_no_double_zero M hp e (Q-1) (by omega) (routingI M.base e)
    (routing_ideal_subset M.base e) (completed_prefix_subset_final M.base e hQ)
    (by
      intro x y hx hy hm
      obtain ⟨r,ir,jr,dr,hr,hrq,hlr,hir,hjr⟩ :=
        (final_r3_canonical_membership M hp e hR3 htau x y hx
          (by have hs := P3R58.p3_coefficient_sums M hp e; omega) (Or.inr hy)).mp hm
      have hlRB : RBLevel M hp e r ir jr dr := by
        rcases hlr with hlr | hlr
        · exact hlr
        · have hjT := hlr.2.2.2.2.1
          omega
      exact ⟨r,ir,jr,dr,hr,by omega,hlRB,hir,hjr⟩)
    n i j d hn hnq hl hz.2.1 hz.2.2

theorem mixed_rb_axisB_not_target (hQ : 1<Q)
    (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤Q-1) (hl : RBLevel M hp e n i j d)
    (s : ZMod a)
    (hs : L5A2C4I.ResidueData.SourceTargetBranch (routingData M.base e) s)
    (hw : (routingI M.base e).aperyRepresentative
      a ((routingData M.base e).branchTarget s) = rbAxisB M hp e i j d) : False := by
  have hj0 := hl.2.1
  have hib := hl.2.2.2.2.2.1
  have hC2 : 0<C2 := by omega
  have hC21 : ((C2-1 : ℕ) : ℤ) = (C2 : ℤ)-1 := by omega
  have hj1 : ((j-1 : ℕ) : ℤ) = (j : ℤ)-1 := by omega
  have hweight : rbAxisB M hp e i j d =
      finalRBSeedB M e j+b+c+(-(d : ℤ))*a := by
    have hr := (normalized_relations M hp e).2.1
    dsimp only [rbAxisB,finalRBSeedB]
    rw [hC21,hj1]
    nlinarith only [hr]
  have hz := routing_zero_edges_at_target M e s hs
    (finalRBSeedB M e j) (-(d : ℤ)) (hw.trans hweight)
  exact mixed_rb_axisB_no_double_zero M hp e (Q-1) (by omega) (routingI M.base e)
    (routing_ideal_subset M.base e) (completed_prefix_subset_final M.base e hQ)
    (by
      intro x y hx hy hm
      obtain ⟨r,ir,jr,dr,hr,hrq,hlr,hir,hjr⟩ :=
        (final_r3_canonical_membership M hp e hR3 htau x y hx
          (by have hs := P3R58.p3_coefficient_sums M hp e; omega) (Or.inr hy)).mp hm
      have hlRB : RBLevel M hp e r ir jr dr := by
        rcases hlr with hlr | hlr
        · exact hlr
        · have hjT := hlr.2.2.2.2.1
          omega
      exact ⟨r,ir,jr,dr,hr,by omega,hlRB,hir,hjr⟩)
    n i j d hn hnq hl hz.2.1 hz.2.2

end

theorem mixed_lt_axisB_not_target (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val : ℕ)-(routingA M.base e : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (n i j d : ℕ) (hn : 0 < n) (hnq : n < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) (hl : LTLevel M hp e n i j d)
    (s : ZMod (routingA M.base e))
    (hs : ResidueData.SourceTargetBranch (routingData M.base e) s)
    (hw : (routingI M.base e).aperyRepresentative
      (routingA M.base e) ((routingData M.base e).branchTarget s) =
      ltAxisB M hp e i j d) : False := by
  let a := routingA M.base e
  let b := routingB M.base e
  let c := routingC M.base e
  let P := P3R57.roleCoefficient M hp e 0 1
  let T := P3R57.roleCoefficient M hp e 0 2
  let C1 := criticalExponent M.base (e 0)
  let I := routingI M.base e
  let x : ℤ := ((P : ℤ)-1)*b+((j : ℤ)-1)*c
  let y : ℤ := ((j : ℤ)-T-1)*c
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hdata := hl
  obtain ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩ := hdata
  have hr := normalized_relations M hp e
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hP0 := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hw' : I.aperyRepresentative a ((routingData M.base e).branchTarget s) =
      x+b+c+(-(d : ℤ))*a := by
    rw [hw]
    dsimp only [ltAxisB,x,a,b,c,P,T,C1]
    nlinarith only [hr.1]
  obtain ⟨_,hu,hv⟩ := P3R63.routing_zero_edges_at_target M e s hs x (-(d : ℤ)) hw'
  have hcanC : P3R60.CanonicalValue M.base e (x+c) := by
    have hh := canonical_int_grid M hp e ((P : ℤ)-1) (j : ℤ)
      (by dsimp only [P]; omega) (by omega) (by dsimp only [P]; omega)
      (by exact_mod_cast hjb) (Or.inl (by dsimp only [P]; omega))
    convert hh using 1 <;> dsimp only [x,b,c] <;> ring
  have hbeta : (i : ℤ)*b+j*c ∈ I := (P3R65.final_lt_candidates_mem M hp e hQ n i j d hn hnq hl).1
  have hmemC : x+c ∈ I := by
    have hm := ideal_add_int I hbeta (int_grid_mem M.base e ((P : ℤ)-1-i) 0
      (by dsimp only [P]; omega) le_rfl)
    convert hm using 1 <;> dsimp only [x,b,c] <;> ring
  have hx : x ∈ I := zero_c_seed_mem I a c
    (P3R63.routing_ideal_subset M.base e) (routingHC M.base e) x hcanC hmemC hv
  have hseed : ((P-1 : ℕ) : ℤ)*b+((j-1 : ℕ) : ℤ)*c ∈ I := by
    convert hx using 1
    dsimp only [x]
    rw [Nat.cast_sub (by dsimp only [P]; omega : 1 ≤ P),Nat.cast_sub (by omega : 1 ≤ j)]
    push_cast
    ring
  obtain ⟨r,ri,rj,rd,hr0,hrq,harm,hri,hrj⟩ :=
    (final_r3_canonical_membership M hp e hR3 htau
      (P-1) (j-1) (by dsimp only [P]; omega) (by omega)
      (Or.inl (by dsimp only [P]; omega))).mp hseed
  have hrl : LTLevel M hp e r ri rj rd := by
    rcases harm with harm | harm
    · have hriP := harm.2.2.2.1
      dsimp only [P] at hri
      omega
    · exact harm
  have hrdata := hrl
  obtain ⟨_,_,hrd0,_,hrjT,_,_,hrd,_⟩ := hrdata
  have haxis : ltAxisB M hp e ri rj rd ∈ I :=
    (P3R65.final_lt_candidates_mem M hp e hQ r ri rj rd hr0 hrq hrl).2.2
  have hcand : y+(a : ℤ)*(C1-rd : ℕ) ∈ I := by
    have hm := ideal_add_int I haxis (int_grid_mem M.base e 0 ((j : ℤ)-1-rj)
      le_rfl (by omega))
    convert hm using 1
    dsimp only [y,ltAxisB,a,b,c,C1,T]
    rw [Nat.cast_sub (by omega : rd ≤ criticalExponent M.base (e 0))]
    push_cast
    ring
  have hopp : x+b = y+(a : ℤ)*C1 := by
    dsimp only [x,y,a,b,c,P,T,C1]
    nlinarith only [hr.1]
  exact stencil_zero_c_contradiction I a b c (P3R63.routing_ideal_subset M.base e)
    (routingHB M.base e) (routingHC M.base e) x y C1 (C1-rd) hcanC hmemC hopp
    hu hv hcand (by dsimp only [C1]; omega)


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
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

/-- LT X seam exclusion on the actual mixed final floor, including its c-wrap. -/
theorem mixed_lt_axisA_not_target (hQ : 1<Q)
    (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (n i j d : ℕ) (hn : 0<n) (hnq : n<Q) (hl : LTLevel M hp e n i j d)
    (s : ZMod a) (hs : ResidueData.SourceTargetBranch (routingData M.base e) s)
    (hw : (routingI M.base e).aperyRepresentative a
      ((routingData M.base e).branchTarget s)=ltAxisA M hp e i j d) : False := by
  let I := routingI M.base e
  let Z := P3R57.roleCoefficient M hp e 2 1
  let W := P3R57.roleCoefficient M hp e 2 0
  let x : ℤ := ((i : ℤ)-1)*b+((C3 : ℤ)-1)*c
  let y : ℤ := ((i : ℤ)+Z-1)*b
  have hdata := hl
  obtain ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩ := hdata
  have hr := normalized_relations M hp e
  have hw' : I.aperyRepresentative a ((routingData M.base e).branchTarget s)=
      x+b+c+(-(d : ℤ))*a := by
    rw [hw]
    dsimp only [ltAxisA,x]
    nlinarith only [hr.2.2]
  obtain ⟨_,hu,hv⟩ := routing_zero_edges_at_target M e s hs x (-(d : ℤ)) hw'
  have hcanB : P3R60.CanonicalValue M.base e (x+b) := by
    have hh := canonical_int_grid M hp e (i : ℤ) ((C3 : ℤ)-1)
      (by omega) (by omega) (by exact_mod_cast hib) (by omega) (Or.inl (by exact_mod_cast hi))
    convert hh using 1 <;> dsimp only [x] <;> ring
  have hbeta : (i : ℤ)*b+j*c ∈ I := (P3R65.final_lt_candidates_mem M hp e hQ n i j d hn hnq hl).1
  have hmemB : x+b ∈ I := by
    have hm := ideal_add_int I hbeta (int_grid_mem M.base e 0 ((C3 : ℤ)-1-j) (by omega) (by omega))
    convert hm using 1 <;> dsimp only [x] <;> ring
  have hx : x ∈ I := zero_b_seed_mem I a b (routing_ideal_subset M.base e)
    (routingHB M.base e) x hcanB hmemB hu
  have hseed : ((i-1 : ℕ) : ℤ)*b+((C3-1 : ℕ) : ℤ)*c ∈ I := by
    convert hx using 1
    dsimp only [x]
    rw [Nat.cast_sub (by omega : 1 ≤ i),Nat.cast_sub (by omega : 1 ≤ C3)]
    push_cast
    ring
  obtain ⟨r,ri,rj,rd,hr0,hrq,harm,hri,hrj⟩ :=
    (final_r3_canonical_membership M hp e hR3 htau (i-1) (C3-1)
      (by omega) (by omega) (Or.inl (by omega))).mp hseed
  have hrl : LTLevel M hp e r ri rj rd := by
    rcases harm with harm | harm
    · have hriP := harm.2.2.2.1
      omega
    · exact harm
  have hrdata := hrl
  obtain ⟨_,_,hrd0,_,_,_,_,hrd,_⟩ := hrdata
  have haxis : ltAxisA M hp e ri rj rd ∈ I :=
    (P3R65.final_lt_candidates_mem M hp e hQ r ri rj rd hr0 hrq hrl).2.1
  have hcand : y+(a : ℤ)*(W-rd : ℕ) ∈ I := by
    have hm := ideal_add_int I haxis (int_grid_mem M.base e ((i : ℤ)-1-ri) 0 (by omega) (by omega))
    convert hm using 1
    dsimp only [y,ltAxisA,W,Z]
    rw [Nat.cast_sub (by omega : rd ≤ P3R57.roleCoefficient M hp e 2 0)]
    push_cast
    ring
  have hopp : x+c=y+(a : ℤ)*W := by
    dsimp only [x,y,W,Z]
    nlinarith only [hr.2.2]
  exact stencil_zero_b_contradiction I a b c (routing_ideal_subset M.base e)
    (routingHB M.base e) (routingHC M.base e) x y W (W-rd) hcanB hmemB hopp hu hv hcand
    (by dsimp only [W]; omega)
/-- TW.05: every actual final ST target is tau or an actual F return,
for arbitrary mixtures of the two strict arms. -/
theorem mixed_final_target_cover (hQ : 1<Q)
    (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (s : ZMod a) (hs : ResidueData.SourceTargetBranch (routingData M.base e) s) :
    (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s)=
      (Q*M.base.q.val : ℕ) ∨
    ∃ n i j d, 0<n ∧ n<Q ∧ (RBLevel M hp e n i j d ∨ LTLevel M hp e n i j d) ∧
      (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s)=
        (i : ℤ)*b+j*c := by
  have hmin := (P3R62.routing_source_iff_minimal M.base e _).mp hs.2
  rcases final_r3_generator_cover M hp hR3 e _ hmin with ht | ⟨n,i,j,d,hn,hnQ,harm⟩
  · exact Or.inl ht
  · right
    rcases harm with ⟨hl,hw⟩ | ⟨hl,hw⟩
    · rcases hw with hw | hw | hw
      · exact ⟨n,i,j,d,hn,hnQ,Or.inl hl,hw⟩
      · exact (mixed_rb_axisA_not_target M hp e hQ hR3 htau n i j d hn (by omega) hl s hs hw).elim
      · exact (mixed_rb_axisB_not_target M hp e hQ hR3 htau n i j d hn (by omega) hl s hs hw).elim
    · rcases hw with hw | hw | hw
      · exact ⟨n,i,j,d,hn,hnQ,Or.inr hl,hw⟩
      · exact (mixed_lt_axisA_not_target M hp e hQ hR3 htau n i j d hn hnQ hl s hs hw).elim
      · exact (mixed_lt_axisB_not_target M hp e hQ hR3 htau n i j d hn hnQ hl s hs hw).elim
end
end NS25Lean.P3R67






