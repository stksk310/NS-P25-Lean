import NS25Lean.P3CanonicalDivisorR61
import NS25Lean.P3IdealHeightsR61
import NS25Lean.P3HerzogGridR61

set_option linter.style.header false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
noncomputable section
namespace NS25Lean.P3R61
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4I L5A2B4AR1
variable {Gamma : NumericalSemigroup}

theorem lt_axisA_not_target (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (hq : 0 < q)
    (hlevels : ∀ n : ℕ, 0 < n → n ≤ q → ∃ i j d : ℕ, LTLevel M hp e n i j d)
    (n i j d : ℕ) (hn : 0 < n) (hnq : n ≤ q) (hl : LTLevel M hp e n i j d)
    (s : ZMod (routingA M.base e))
    (hs : ResidueData.SourceTargetBranch (P3R60.birthData M.base e q hq) s)
    (hw : (P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq).aperyRepresentative
      (routingA M.base e) ((P3R60.birthData M.base e q hq).branchTarget s) =
      ltAxisA M hp e i j d) : False := by
  let a := routingA M.base e
  let b := routingB M.base e
  let c := routingC M.base e
  let W := P3R57.roleCoefficient M hp e 2 0
  let Z := P3R57.roleCoefficient M hp e 2 1
  let C3 := criticalExponent M.base (e 2)
  let I := P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq
  let x : ℤ := ((i : ℤ)-1)*b+((C3 : ℤ)-1)*c
  let y : ℤ := ((i : ℤ)+Z-1)*b
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hdata := hl
  obtain ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩ := hdata
  have hr := normalized_relations M hp e
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hw' : I.aperyRepresentative a ((P3R60.birthData M.base e q hq).branchTarget s) =
      x+b+c+(-(d : ℤ))*a := by
    rw [hw]
    dsimp only [ltAxisA,x,a,b,c,C3]
    nlinarith only [hr.2.2]
  obtain ⟨_,hu,hv⟩ := zero_edges_at_target_residue M.base e q hq s hs x (-(d : ℤ)) hw'
  have hcanB : P3R60.CanonicalValue M.base e (x+b) := by
    have hh := canonical_int_grid M hp e (i : ℤ) ((C3 : ℤ)-1)
      (by omega) (by dsimp only [C3]; omega) (by exact_mod_cast hib)
      (by dsimp only [C3]; omega) (Or.inl (by exact_mod_cast hi))
    convert hh using 1 <;> dsimp only [x,b,c] <;> ring
  have hbeta : (i : ℤ)*b+j*c ∈ I := lt_level_beta_mem M hp e q hq n i j d hn hnq hl
  have hmemB : x+b ∈ I := by
    have hm := ideal_add_int I hbeta (int_grid_mem M.base e 0 ((C3 : ℤ)-1-j)
      le_rfl (by dsimp only [C3]; omega))
    convert hm using 1 <;> dsimp only [x,b,c] <;> ring
  have hx : x ∈ I := zero_b_seed_mem I a b
    (birthIdeal_subset _ _ _ _) (routingHB M.base e) x hcanB hmemB hu
  have hseed : ((i-1 : ℕ) : ℤ)*b+((C3-1 : ℕ) : ℤ)*c ∈ I := by
    convert hx using 1
    dsimp only [x]
    rw [Nat.cast_sub (by omega : 1 ≤ i),Nat.cast_sub (by dsimp only [C3]; omega : 1 ≤ C3)]
    push_cast
    ring
  obtain ⟨r,ri,rj,rd,hr0,hrq,hrl,hri,hrj⟩ := lt_canonical_prefix_divisor M hp e q hq hlevels
    (i-1) (C3-1) (by omega) (by dsimp only [C3]; omega) (Or.inl (by omega)) hseed
  have hrdata := hrl
  obtain ⟨_,_,hrd0,_,_,_,_,hrd,_⟩ := hrdata
  have haxis : ltAxisA M hp e ri rj rd ∈ I :=
    (lt_level_axes_mem M hp e q hq r ri rj rd hr0 hrq hrl).1
  have hcand : y+(a : ℤ)*(W-rd : ℕ) ∈ I := by
    have hm := ideal_add_int I haxis (int_grid_mem M.base e ((i : ℤ)-1-ri) 0
      (by omega) le_rfl)
    convert hm using 1
    dsimp only [y,ltAxisA,a,b,c,W,Z]
    rw [Nat.cast_sub (by exact hrd.le)]
    push_cast
    ring
  have hopp : x+c = y+(a : ℤ)*W := by
    dsimp only [x,y,a,b,c,C3,W,Z]
    nlinarith only [hr.2.2]
  exact stencil_zero_b_contradiction I a b c (birthIdeal_subset _ _ _ _)
    (routingHB M.base e) (routingHC M.base e) x y W (W-rd) hcanB hmemB hopp
    hu hv hcand (by dsimp only [W]; omega)

theorem lt_axisB_not_target (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (hq : 0 < q)
    (hlevels : ∀ n : ℕ, 0 < n → n ≤ q → ∃ i j d : ℕ, LTLevel M hp e n i j d)
    (n i j d : ℕ) (hn : 0 < n) (hnq : n ≤ q) (hl : LTLevel M hp e n i j d)
    (s : ZMod (routingA M.base e))
    (hs : ResidueData.SourceTargetBranch (P3R60.birthData M.base e q hq) s)
    (hw : (P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq).aperyRepresentative
      (routingA M.base e) ((P3R60.birthData M.base e q hq).branchTarget s) =
      ltAxisB M hp e i j d) : False := by
  let a := routingA M.base e
  let b := routingB M.base e
  let c := routingC M.base e
  let P := P3R57.roleCoefficient M hp e 0 1
  let T := P3R57.roleCoefficient M hp e 0 2
  let C1 := criticalExponent M.base (e 0)
  let I := P3R60.birthIdeal (routingH M.base e) M.base.q.val q hq
  let x : ℤ := ((P : ℤ)-1)*b+((j : ℤ)-1)*c
  let y : ℤ := ((j : ℤ)-T-1)*c
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hdata := hl
  obtain ⟨hi0,hj0,hd0,hi,hj,hib,hjb,hd,he⟩ := hdata
  have hr := normalized_relations M hp e
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hP0 := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hw' : I.aperyRepresentative a ((P3R60.birthData M.base e q hq).branchTarget s) =
      x+b+c+(-(d : ℤ))*a := by
    rw [hw]
    dsimp only [ltAxisB,x,a,b,c,P,T,C1]
    nlinarith only [hr.1]
  obtain ⟨_,hu,hv⟩ := zero_edges_at_target_residue M.base e q hq s hs x (-(d : ℤ)) hw'
  have hcanC : P3R60.CanonicalValue M.base e (x+c) := by
    have hh := canonical_int_grid M hp e ((P : ℤ)-1) (j : ℤ)
      (by dsimp only [P]; omega) (by omega) (by dsimp only [P]; omega)
      (by exact_mod_cast hjb) (Or.inl (by dsimp only [P]; omega))
    convert hh using 1 <;> dsimp only [x,b,c] <;> ring
  have hbeta : (i : ℤ)*b+j*c ∈ I := lt_level_beta_mem M hp e q hq n i j d hn hnq hl
  have hmemC : x+c ∈ I := by
    have hm := ideal_add_int I hbeta (int_grid_mem M.base e ((P : ℤ)-1-i) 0
      (by dsimp only [P]; omega) le_rfl)
    convert hm using 1 <;> dsimp only [x,b,c] <;> ring
  have hx : x ∈ I := zero_c_seed_mem I a c
    (birthIdeal_subset _ _ _ _) (routingHC M.base e) x hcanC hmemC hv
  have hseed : ((P-1 : ℕ) : ℤ)*b+((j-1 : ℕ) : ℤ)*c ∈ I := by
    convert hx using 1
    dsimp only [x]
    rw [Nat.cast_sub (by dsimp only [P]; omega : 1 ≤ P),Nat.cast_sub (by omega : 1 ≤ j)]
    push_cast
    ring
  obtain ⟨r,ri,rj,rd,hr0,hrq,hrl,hri,hrj⟩ := lt_canonical_prefix_divisor M hp e q hq hlevels
    (P-1) (j-1) (by dsimp only [P]; omega) (by omega) (Or.inl (by dsimp only [P]; omega)) hseed
  have hrdata := hrl
  obtain ⟨_,_,hrd0,_,hrjT,_,_,hrd,_⟩ := hrdata
  have haxis : ltAxisB M hp e ri rj rd ∈ I :=
    (lt_level_axes_mem M hp e q hq r ri rj rd hr0 hrq hrl).2
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
  exact stencil_zero_c_contradiction I a b c (birthIdeal_subset _ _ _ _)
    (routingHB M.base e) (routingHC M.base e) x y C1 (C1-rd) hcanC hmemC hopp
    hu hv hcand (by dsimp only [C1]; omega)

end NS25Lean.P3R61
