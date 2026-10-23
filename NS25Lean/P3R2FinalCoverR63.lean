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
local notation "T" => P3R57.roleCoefficient M hp e 0 2
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local notation "C2" => criticalExponent M.base (e 1)
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
theorem rb_final_axisA_not_target (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d)
    (hshape : (∃ L I : ℕ, 0<L ∧ (Q*M.base.q.val : ℕ) = (L : ℤ)*a+I*b) ∨
      (∃ k : ℕ, T<k ∧ (Q*M.base.q.val : ℕ) = (k : ℤ)*c))
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
  exact rb_final_axisA_no_double_zero M hp e (Q-1) (by omega) hlevels (routingI M.base e)
    (routing_ideal_subset M.base e) (completed_prefix_subset_final M.base e hQ)
    (rb_final_canonical_divisor M hp e hQ hlevels hshape)
    n i j d hn hnq hl hz.2.1 hz.2.2

theorem rb_final_axisB_not_target (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d)
    (hshape : (∃ L I : ℕ, 0<L ∧ (Q*M.base.q.val : ℕ) = (L : ℤ)*a+I*b) ∨
      (∃ k : ℕ, T<k ∧ (Q*M.base.q.val : ℕ) = (k : ℤ)*c))
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
  exact rb_final_axisB_no_double_zero M hp e (Q-1) (by omega) hlevels (routingI M.base e)
    (routing_ideal_subset M.base e) (completed_prefix_subset_final M.base e hQ)
    (rb_final_canonical_divisor M hp e hQ hlevels hshape)
    n i j d hn hnq hl hz.2.1 hz.2.2

theorem final_rb_target_is_return (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d)
    (hshape : (∃ L K : ℕ, 0<L ∧ (Q*M.base.q.val : ℕ) = (L : ℤ)*a+K*b) ∨
      (∃ k : ℕ, T<k ∧ (Q*M.base.q.val : ℕ) = (k : ℤ)*c))
    (hnot : ∀ s : ZMod a, ResidueData.SourceTargetBranch (routingData M.base e) s →
      (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s) ≠
        (Q*M.base.q.val : ℕ))
    (s : ZMod a) (hs : ResidueData.SourceTargetBranch (routingData M.base e) s) :
    ∃ n i j d, 0<n ∧ n≤Q-1 ∧ RBLevel M hp e n i j d ∧
      (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s) =
        (i : ℤ)*b+j*c := by
  let I := routingI M.base e
  let J := P3R60.birthIdeal (routingH M.base e) M.base.q.val (Q-1) (by omega)
  let w := I.aperyRepresentative a ((routingData M.base e).branchTarget s)
  have hmin : I.IsMinimalGenerator w := (P3R62.routing_source_iff_minimal M.base e _).mp hs.2
  have hprefixmin := P3R62.routing_old_source_is_completed_source M.base e hQ w hmin (hnot s hs)
  obtain ⟨n,i,j,d,hn,hnq,hl,hres⟩ := rb_prefix_cover M hp e (Q-1) (by omega) hlevels w hprefixmin.1
  rcases hres with hres | hres | hres
  · have hbeta := completed_prefix_subset_final M.base e hQ _
      (rb_level_beta_mem M hp e (Q-1) (by omega) n i j d hn hnq hl)
    exact ⟨n,i,j,d,hn,hnq,hl,minimal_generator_eq_of_residual I w _ hmin hbeta hres⟩
  · have haxis := completed_prefix_subset_final M.base e hQ _
      (rb_level_axes_mem M hp e (Q-1) (by omega) n i j d hn hnq hl).1
    have heq := minimal_generator_eq_of_residual I w _ hmin haxis hres
    exact (rb_final_axisA_not_target M hp e hQ hlevels hshape n i j d hn hnq hl s hs heq).elim
  · have haxis := completed_prefix_subset_final M.base e hQ _
      (rb_level_axes_mem M hp e (Q-1) (by omega) n i j d hn hnq hl).2
    have heq := minimal_generator_eq_of_residual I w _ hmin haxis hres
    exact (rb_final_axisB_not_target M hp e hQ hlevels hshape n i j d hn hnq hl s hs heq).elim
end
end NS25Lean.P3R63
