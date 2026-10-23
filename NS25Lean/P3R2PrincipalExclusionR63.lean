import NS25Lean.P3R2FinalCarrierR63
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R63
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1 P3R61
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
local notation "Z" => P3R57.roleCoefficient M hp e 2 1
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local notation "C1" => criticalExponent M.base (e 0)
local notation "C2" => criticalExponent M.base (e 1)
local notation "C3" => criticalExponent M.base (e 2)
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

theorem rb_mixed_principal_not_target (hQ : 1<Q)
    (L K : ℕ) (hK : 0<K) (hKZ : K≤Z)
    (ht : (Q*M.base.q.val : ℕ) = (L : ℤ)*a+K*b)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤Q-1)
    (hl : RBLevel M hp e n i j d) (hiK : i<K)
    (s : ZMod a) (hs : ResidueData.SourceTargetBranch (routingData M.base e) s)
    (hw : (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s)=
      (Q*M.base.q.val : ℕ)) : False := by
  let I := routingI M.base e
  let x : ℤ := ((P+K-1 : ℕ) : ℤ)*b+((T-1 : ℕ) : ℤ)*c
  let y : ℤ := ((K-1 : ℕ) : ℤ)*b
  have hdata := hl
  rcases hdata with ⟨hi0,hj0,hd0,hiP,hjT,hiC,hjC,hdU,he⟩
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hPk : ((P+K-1 : ℕ) : ℤ)=(P : ℤ)+K-1 := by omega
  have hT1 : ((T-1 : ℕ) : ℤ)=(T : ℤ)-1 := by omega
  have hK1 : ((K-1 : ℕ) : ℤ)=(K : ℤ)-1 := by omega
  have hcan := canonical_int_grid M hp e (P+K-1 : ℕ) (T-1 : ℕ)
    (by positivity) (by positivity) (by omega) (by omega) (Or.inr (by omega))
  have hmem : x ∈ I := by
    have hb := completed_prefix_subset_final M.base e hQ _
      (rb_level_beta_mem M hp e (Q-1) (by omega) n i j d hn hnq hl)
    have hm := ideal_add_int I hb (routing_combination_mem M.base e 0
      ((P+K-1 : ℕ)-i : ℤ) ((T-1 : ℕ)-j : ℤ) (by omega) (by omega) (by omega))
    convert hm using 1
    dsimp only [x]; push_cast; ring
  have hopp : x+c=y+(a : ℤ)*C1 := by
    have hr := (normalized_relations M hp e).1
    dsimp only [x,y]; rw [hPk,hT1,hK1]; nlinarith only [hr]
  have hweight : (Q*M.base.q.val : ℕ)=x+b+c+((L : ℤ)-C1)*a := by
    have hr := (normalized_relations M hp e).1
    rw [ht]; dsimp only [x]; rw [hPk,hT1]; nlinarith only [hr]
  have hz := routing_zero_edges_at_target M e s hs x ((L : ℤ)-C1) (hw.trans hweight)
  have hdC : d≤C1 := by omega
  have hcand : y+(a : ℤ)*((C1-d : ℕ) : ℤ) ∈ I := by
    have ha := completed_prefix_subset_final M.base e hQ _
      (rb_level_axes_mem M hp e (Q-1) (by omega) n i j d hn hnq hl).1
    have hm := ideal_add_int I ha (routing_combination_mem M.base e 0
      ((K : ℤ)-1-i+P) 0 (by omega) (by omega) (by omega))
    convert hm using 1
    dsimp only [y,rbAxisA]; rw [hK1,Nat.cast_sub hdC]; push_cast; ring
  exact canonical_zero_edge_contradiction I a c (routing_ideal_subset M.base e)
    (routingHC M.base e) x y C1 (C1-d) hcan hmem hopp hz.2.2 hcand (by omega)

theorem rb_pure_principal_not_target (hQ : 1<Q)
    (k : ℕ) (hkV : V<k) (hkC : k<C3)
    (ht : (Q*M.base.q.val : ℕ) = (k : ℤ)*c)
    (n i j d : ℕ) (hn : 0<n) (hnq : n≤Q-1)
    (hl : RBLevel M hp e n i j d) (hiZ : i<Z) (hjk : j+V<k)
    (s : ZMod a) (hs : ResidueData.SourceTargetBranch (routingData M.base e) s)
    (hw : (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s)=
      (Q*M.base.q.val : ℕ)) : False := by
  let I := routingI M.base e
  let x : ℤ := ((C2-1 : ℕ) : ℤ)*b+((k-V-1 : ℕ) : ℤ)*c
  let y : ℤ := ((k-1 : ℕ) : ℤ)*c
  have hdata := hl
  rcases hdata with ⟨hi0,hj0,hd0,hiP,hjT,hiC,hjC,hdU,he⟩
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hC21 : ((C2-1 : ℕ) : ℤ)=(C2 : ℤ)-1 := by omega
  have hkV1 : ((k-V-1 : ℕ) : ℤ)=(k : ℤ)-V-1 := by omega
  have hk1 : ((k-1 : ℕ) : ℤ)=(k : ℤ)-1 := by omega
  have hcan := canonical_int_grid M hp e (C2-1 : ℕ) (k-V-1 : ℕ)
    (by positivity) (by positivity) (by omega) (by omega) (Or.inr (by omega))
  have hmem : x ∈ I := by
    have hb := completed_prefix_subset_final M.base e hQ _
      (rb_level_beta_mem M hp e (Q-1) (by omega) n i j d hn hnq hl)
    have hm := ideal_add_int I hb (routing_combination_mem M.base e 0
      ((C2-1 : ℕ)-i : ℤ) ((k-V-1 : ℕ)-j : ℤ) (by omega) (by omega) (by omega))
    convert hm using 1
    dsimp only [x]; push_cast; ring
  have hopp : x+b=y+(a : ℤ)*U := by
    have hr := (normalized_relations M hp e).2.1
    dsimp only [x,y]; rw [hC21,hkV1,hk1]; nlinarith only [hr]
  have hweight : (Q*M.base.q.val : ℕ)=x+b+c+(-(U : ℤ))*a := by
    have hr := (normalized_relations M hp e).2.1
    rw [ht]; dsimp only [x]; rw [hC21,hkV1]; nlinarith only [hr]
  have hz := routing_zero_edges_at_target M e s hs x (-(U : ℤ)) (hw.trans hweight)
  have hdU' : d≤U := by omega
  have hcand : y+(a : ℤ)*((U-d : ℕ) : ℤ) ∈ I := by
    have ha := completed_prefix_subset_final M.base e hQ _
      (rb_level_axes_mem M hp e (Q-1) (by omega) n i j d hn hnq hl).2
    have hm := ideal_add_int I ha (routing_combination_mem M.base e 0 0
      ((k : ℤ)-1-j-V) (by omega) (by omega) (by omega))
    convert hm using 1
    dsimp only [y,rbAxisB]; rw [hk1,Nat.cast_sub hdU']; push_cast; ring
  exact canonical_zero_edge_contradiction I a b (routing_ideal_subset M.base e)
    (routingHB M.base e) x y U (U-d) hcan hmem hopp hz.2.1 hcand (by omega)
end
end NS25Lean.P3R63
