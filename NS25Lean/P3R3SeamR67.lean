import NS25Lean.P3R3FloorR67
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R67
open P3R63
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
  exact rb_final_axisA_no_double_zero M hp e (Q-1) (by omega) hlevels (routingI M.base e)
    (routing_ideal_subset M.base e) (completed_prefix_subset_final M.base e hQ)
    (by
      intro x y hx hy hm
      obtain ⟨r,ir,jr,dr,hr,hrq,hlr,hir,hjr⟩ :=
        (final_rb_canonical_membership M hp e hQ
          (by intro n hn hnQ; exact hlevels n hn (by omega)) htau x y hx
          (by have hs := P3R58.p3_coefficient_sums M hp e; omega) (Or.inr hy)).mp hm
      exact ⟨r,ir,jr,dr,hr,by omega,hlr,hir,hjr⟩)
    n i j d hn hnq hl hz.2.1 hz.2.2

theorem rb_final_axisB_not_target (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d)
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
  exact rb_final_axisB_no_double_zero M hp e (Q-1) (by omega) hlevels (routingI M.base e)
    (routing_ideal_subset M.base e) (completed_prefix_subset_final M.base e hQ)
    (by
      intro x y hx hy hm
      obtain ⟨r,ir,jr,dr,hr,hrq,hlr,hir,hjr⟩ :=
        (final_rb_canonical_membership M hp e hQ
          (by intro n hn hnQ; exact hlevels n hn (by omega)) htau x y hx
          (by have hs := P3R58.p3_coefficient_sums M hp e; omega) (Or.inr hy)).mp hm
      exact ⟨r,ir,jr,dr,hr,by omega,hlr,hir,hjr⟩)
    n i j d hn hnq hl hz.2.1 hz.2.2

/-- NF.08: actual final branch targets lie among F-candidates and possibly tau. -/
theorem final_rb_target_cover (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, RBLevel M hp e n i j d)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (s : ZMod a) (hs : ResidueData.SourceTargetBranch (routingData M.base e) s) :
    (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s) =
      (Q*M.base.q.val : ℕ) ∨
    ∃ n i j d, 0<n ∧ n<Q ∧ RBLevel M hp e n i j d ∧
      (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s) =
        (i : ℤ)*b+j*c := by
  let w := (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s)
  have hmin : (routingI M.base e).IsMinimalGenerator w :=
    (P3R62.routing_source_iff_minimal M.base e _).mp hs.2
  by_cases heq : w=(Q*M.base.q.val : ℕ)
  · exact Or.inl heq
  · right
    have hpre := P3R62.routing_old_source_is_completed_source M.base e hQ w hmin heq
    obtain ⟨n,i,j,d,hn,hnq,hl,hr⟩ := rb_prefix_cover M hp e (Q-1) (by omega)
      (by intro n hn hnq; exact hlevels n hn (by omega)) w hpre.1
    have hlevels' : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d := by
      intro n hn hnq; exact hlevels n hn (by omega)
    rcases hr with hr | hr | hr
    · have hm := completed_prefix_subset_final M.base e hQ _
        (rb_level_beta_mem M hp e (Q-1) (by omega) n i j d hn hnq hl)
      exact ⟨n,i,j,d,hn,by omega,hl,minimal_generator_eq_of_residual _ w _ hmin hm hr⟩
    · have hm := completed_prefix_subset_final M.base e hQ _
        (rb_level_axes_mem M hp e (Q-1) (by omega) n i j d hn hnq hl).1
      exact (rb_final_axisA_not_target M hp e hQ hlevels' htau n i j d hn hnq hl s hs
        (minimal_generator_eq_of_residual _ w _ hmin hm hr)).elim
    · have hm := completed_prefix_subset_final M.base e hQ _
        (rb_level_axes_mem M hp e (Q-1) (by omega) n i j d hn hnq hl).2
      exact (rb_final_axisB_not_target M hp e hQ hlevels' htau n i j d hn hnq hl s hs
        (minimal_generator_eq_of_residual _ w _ hmin hm hr)).elim
end
end NS25Lean.P3R67


