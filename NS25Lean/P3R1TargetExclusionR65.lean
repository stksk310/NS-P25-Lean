import NS25Lean.P3R1FinalCarrierR65
import NS25Lean.P3R2ZeroRectangleR63
set_option linter.style.header false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R65
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open P3R61 L5A2C4OR3
variable {Gamma : NumericalSemigroup}
theorem final_y_not_target (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hQ : 1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (k : ℕ) (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=k*routingC M.base e)
    (hlevels : ∀ n : ℕ, 0 < n → n < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive → ∃ i j d : ℕ, LTLevel M hp e n i j d)
    (n i j d : ℕ) (hn : 0 < n) (hnq : n < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) (hl : LTLevel M hp e n i j d)
    (hjk : j < k)
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
  have hbeta : (i : ℤ)*b+j*c ∈ I := (final_lt_candidates_mem M hp e hQ n i j d hn hnq hl).1
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
  have hdiv := (final_lt_canonical_membership M hp e hQ hlevels k ht
    (P-1) (j-1) (by dsimp only [P]; omega) (by omega)
    (Or.inl (by dsimp only [P]; omega))).mp hseed
  rcases hdiv with hprincipal | ⟨r,ri,rj,rd,hr0,hrq,hrl,hri,hrj⟩
  · omega
  · have hrdata := hrl
    obtain ⟨_,_,hrd0,_,hrjT,_,_,hrd,_⟩ := hrdata
    have haxis : ltAxisB M hp e ri rj rd ∈ I :=
      (final_lt_candidates_mem M hp e hQ r ri rj rd hr0 hrq hrl).2.2
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
local notation "V" => P3R57.roleCoefficient M hp e 1 2
local notation "A" => criticalExponent M.base (e 0)
local notation "C" => criticalExponent M.base (e 2)
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

/-- CU.08: F-targets use the actual first-zero endpoint and are nonexceptional. -/
theorem final_f_nonexceptional (k : ℕ) (hkC : k<C) (ht : Q*M.base.q.val=k*c)
    (n i j d : ℕ) (hl : LTLevel M hp e n i j d) (hjk : j<k)
    (s : ResidueData.CSourceTargetBranches (routingData M.base e))
    (hw : (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s.val)=
      (i : ℤ)*b+j*c) : ResidueData.CFirstStageNonexceptional (routingData M.base e) s := by
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hcan : ∀ x y : ℕ, x<P → y<C →
      (routingH M.base e).asRelativeIdeal.aperyRepresentative a
        (((x*b+y*c : ℕ) : ℤ) : ZMod a)=((x*b+y*c : ℕ) : ℤ) := by
    intro x y hx hy
    have hh := P3R60.canonical_grid_value M.base e x y
      (P3R58.p3_lshape_canonical M hp e x y (by omega) hy (Or.inl hx))
    simpa only [P3R60.CanonicalValue,physicalAlpha,Nat.cast_add,Nat.cast_mul] using hh
  have hmem : ((0*b+k*c : ℕ) : ℤ) ∈ routingI M.base e := by
    simpa [ht] using (P3R62.routing_principal_isMinimalGenerator M.base e).1
  apply P3R63.c_nonexceptional_of_left_target (routingI M.base e) a b c
    (routingHB M.base e) (routingHC M.base e) (P3R63.routing_ideal_subset M.base e)
    P C hcan s i j 0 k hl.1 hl.2.1 hl.2.2.2.1 hkC hl.1 hjk
  · simpa only [P3R60.idealData,routingData,Nat.cast_add,Nat.cast_mul] using hw
  · exact hmem

/-- CU.10: for Q>1 the actual pure-c principal generator cannot be a target. -/
theorem final_principal_not_target (hQ : 1<Q)
    (k : ℕ) (hkT : T<k) (hkV : k≤V) (ht : Q*M.base.q.val=k*c)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, LTLevel M hp e n i j d ∧ j<k)
    (s : ZMod a) (hs : ResidueData.SourceTargetBranch (routingData M.base e) s)
    (hw : (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s)=
      (Q*M.base.q.val : ℕ)) : False := by
  let I := routingI M.base e
  let x : ℤ := ((P : ℤ)-1)*b+((k : ℤ)+T-1)*c
  let y : ℤ := ((k : ℤ)-1)*c
  have hr := normalized_relations M hp e
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hw' : I.aperyRepresentative a ((routingData M.base e).branchTarget s)=
      x+b+c+(-(A : ℤ))*a := by
    rw [hw,ht]
    change (k : ℤ)*c = ((P : ℤ)-1)*b+((k : ℤ)+T-1)*c+b+c+(-(A : ℤ))*a
    nlinarith only [hr.1]
  obtain ⟨_,hu,hv⟩ := P3R63.routing_zero_edges_at_target M e s hs x (-(A : ℤ)) hw'
  have hcan : P3R60.CanonicalValue M.base e x := by
    exact canonical_int_grid M hp e ((P : ℤ)-1) ((k : ℤ)+T-1)
      (by omega) (by omega) (by omega) (by omega) (Or.inl (by omega))
  have hx : x ∈ I := by
    have hm := (P3R62.routing_principal_isMinimalGenerator M.base e).1
    rw [ht] at hm
    have hh := ideal_add_int I hm (int_grid_mem M.base e ((P : ℤ)-1) ((T : ℤ)-1)
      (by omega) (by omega))
    convert hh using 1 <;> dsimp only [x] <;> push_cast <;> ring
  obtain ⟨i,j,d,hl,hjk⟩ := hlevels 1 (by omega) (by omega)
  have hd := hl.2.2.1
  have hdb := hl.2.2.2.2.2.2.2.1
  have haxis := (final_lt_candidates_mem M hp e hQ 1 i j d (by omega) (by omega) hl).2.2
  have hcand : y+(a : ℤ)*(A-d : ℕ) ∈ I := by
    have hm := ideal_add_int I haxis (int_grid_mem M.base e 0 ((k : ℤ)+T-1-j)
      le_rfl (by omega))
    convert hm using 1
    dsimp only [y,ltAxisB]
    rw [Nat.cast_sub (by omega : d≤A)]
    push_cast
    ring
  have hopp : x+b=y+(a : ℤ)*A := by
    dsimp only [x,y]
    nlinarith only [hr.1]
  exact P3R63.canonical_zero_edge_contradiction I a b
    (P3R63.routing_ideal_subset M.base e) (routingHB M.base e) x y A (A-d)
    hcan hx hopp hu hcand (by omega)
end
end NS25Lean.P3R65
