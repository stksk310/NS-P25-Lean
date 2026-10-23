import NS25Lean.P3R3MixedCountR67
import NS25Lean.P3R3MixedCornersR67
import NS25Lean.P3R3MergeFamilyR67

set_option autoImplicit false
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open L5A2C4OR3 L5A2C4OR4 P3R61 CombinatorialCore
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "B" => criticalExponent M.base (e 1)
local notation "C" => criticalExponent M.base (e 2)
local notation "P" => P3R57.roleCoefficient M hp e 0 1
local notation "T" => P3R57.roleCoefficient M hp e 0 2
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

/-- The single full-support factorization supplies the repaired signed floor premise. -/
theorem fullSupport_tau_a_mem (hfull : PrincipalFullSupport M e) :
    (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal := by
  obtain ⟨L,I,J,hL,hI,hJ,he⟩ := hfull
  rw [he]
  convert routing_combination_mem M.base e ((L : ℤ)-1) I J (by omega) (by omega) (by omega) using 1 <;> push_cast <;> ring

/-- The occupied RB antichain and its actual corner produce a bounded physical family. -/
theorem fullSupport_rb_family (hR3 : (P3R51.internalDegrees M).card=3)
    (hfull : PrincipalFullSupport M e) (hS : (rbFloorPoints M hp e).Nonempty) :
    ∃ f : (Fin ((coordinateMinima (rbFloorPoints M hp e)).card-1) ⊕ Unit) → ZMod a,
      Function.Injective f ∧
      (∀ k, ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (f k)) ∧
      (∀ k, ∃ i j : ℕ, i<B ∧ j<T ∧ 0≤j ∧
        f k=(((i : ℤ)*b+j*c : ℤ) : ZMod a)) := by
  have sums := P3R58.p3_coefficient_sums M hp e
  have htau := fullSupport_tau_a_mem M e hfull
  have hoccupied : ∃ n i j d, 0<n ∧ n<Q ∧ RBLevel M hp e n i j d := by
    obtain ⟨p,hp'⟩ := hS
    obtain ⟨n,d,hn,hnQ,hl⟩ := (mem_rbFloorPoints M hp e p).mp hp'
    exact ⟨n,p.1,p.2,d,hn,hnQ,hl⟩
  have hcorner := mixed_rb_corner_of_occupied M hp e hR3 hfull hoccupied
  apply rectangular_unused_family M hp e B T 0 (rbFloorPoints M hp e) hS
    le_rfl (by omega) (Or.inr le_rfl)
    (by intro p hp'; have h := rbFloorPoints_bounds M hp e p hp'; omega)
    (by intro i j hi hj; exact mixed_rb_rectangle_membership M hp e hR3 htau i j hi hj)
  simpa only [gridResidue,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hcorner

/-- The occupied LT antichain and its actual corner produce a disjoint-height family. -/
theorem fullSupport_lt_family (hR3 : (P3R51.internalDegrees M).card=3)
    (hfull : PrincipalFullSupport M e) (hS : (ltFloorPoints M hp e).Nonempty) :
    ∃ f : (Fin ((coordinateMinima (ltFloorPoints M hp e)).card-1) ⊕ Unit) → ZMod a,
      Function.Injective f ∧
      (∀ k, ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (f k)) ∧
      (∀ k, ∃ i j : ℕ, i<P ∧ j<C ∧ T≤j ∧
        f k=(((i : ℤ)*b+j*c : ℤ) : ZMod a)) := by
  have sums := P3R58.p3_coefficient_sums M hp e
  have htau := fullSupport_tau_a_mem M e hfull
  have hoccupied : ∃ n i j d, 0<n ∧ n<Q ∧ LTLevel M hp e n i j d := by
    obtain ⟨p,hp'⟩ := hS
    obtain ⟨n,d,hn,hnQ,hl⟩ := (mem_ltFloorPoints M hp e p).mp hp'
    exact ⟨n,p.1,p.2,d,hn,hnQ,hl⟩
  have hcorner := mixed_lt_corner_of_occupied M hp e hR3 hfull hoccupied
  apply rectangular_unused_family M hp e P C T (ltFloorPoints M hp e) hS
    (by omega) le_rfl (Or.inl le_rfl)
    (by intro p hp'; have h := ltFloorPoints_bounds M hp e p hp'; have h' := ltFloorPoints_arm_bounds M hp e p hp'; omega)
    (by intro i j hi hj; exact mixed_lt_rectangle_membership M hp e hR3 htau i j hi hj)
  simpa only [gridResidue,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hcorner

/-- Nonempty antichains count their staircase plus one occupied corner exactly. -/
theorem occupied_family_domain_card (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) :
    Nat.card (Fin ((coordinateMinima S).card-1) ⊕ Unit)=(coordinateMinima S).card := by
  have hpos := Finset.card_pos.mpr (coordinate_minima_nonempty S hS)
  simp only [Nat.card_sum,Nat.card_fin]
  have hu : Nat.card Unit=1 := by simp [Nat.card_eq_fintype_card]
  rw [hu]
  omega

/-- TW.10: all distinct RB and LT minimal floor points are paid by TOTAL merges
in the same actual final graph, with the empty-arm cases included. -/
theorem fullSupport_unused_count (hR3 : (P3R51.internalDegrees M).card=3)
    (hfull : PrincipalFullSupport M e) :
    (coordinateMinima (rbFloorPoints M hp e)).card+
      (coordinateMinima (ltFloorPoints M hp e)).card ≤
      Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e)) := by
  classical
  have sums := P3R58.p3_coefficient_sums M hp e
  by_cases hR : (rbFloorPoints M hp e).Nonempty
  · obtain ⟨f,hf,hfm,hfg⟩ := fullSupport_rb_family M hp e hR3 hfull hR
    by_cases hL : (ltFloorPoints M hp e).Nonempty
    · obtain ⟨g,hg,hgm,hgg⟩ := fullSupport_lt_family M hp e hR3 hfull hL
      have hdis : ∀ i j, f i≠g j := by
        intro k l he
        obtain ⟨i,j,hi,hj,_,hfi⟩ := hfg k
        obtain ⟨i',j',hi',hj',hTj',hgj⟩ := hgg l
        rw [hfi,hgj] at he
        obtain ⟨_,hjj⟩ := canonical_grid_residue_injective M hp e i j i' j' hi (by omega)
          (P3R58.p3_lshape_canonical M hp e i j hi (by omega) (Or.inr hj))
          (P3R58.p3_lshape_canonical M hp e i' j' (by omega) hj' (Or.inl hi')) he
        omega
      have hc := unused_count_two_families (routingData M.base e) f g hf hg hfm hgm hdis
      rw [occupied_family_domain_card _ hR,occupied_family_domain_card _ hL] at hc
      exact hc
    · have hL0 : (coordinateMinima (ltFloorPoints M hp e)).card=0 := by
        simp [coordinateMinima,Finset.not_nonempty_iff_eq_empty.mp hL]
      have hc := unused_count_of_injective_bases (routingData M.base e) f hf hfm
      rw [occupied_family_domain_card _ hR] at hc
      omega
  · have hR0 : (coordinateMinima (rbFloorPoints M hp e)).card=0 := by
      simp [coordinateMinima,Finset.not_nonempty_iff_eq_empty.mp hR]
    by_cases hL : (ltFloorPoints M hp e).Nonempty
    · obtain ⟨g,hg,hgm,hgg⟩ := fullSupport_lt_family M hp e hR3 hfull hL
      have hc := unused_count_of_injective_bases (routingData M.base e) g hg hgm
      rw [occupied_family_domain_card _ hL] at hc
      omega
    · have hL0 : (coordinateMinima (ltFloorPoints M hp e)).card=0 := by
        simp [coordinateMinima,Finset.not_nonempty_iff_eq_empty.mp hL]
      omega

include hp in
/-- TW.13: every actual role with a single full-support principal has fresh
compensation on its actual FINAL routing data. -/
theorem fullSupport_fresh_role (hR3 : (P3R51.internalDegrees M).card=3)
    (hQ : 1<Q) (hfull : PrincipalFullSupport M e) :
    ResidueData.cExceptionalCount (routingData M.base e) ≤
      Nat.card (ResidueData.CFreshUnusedMergeBases (routingData M.base e))+1 := by
  apply (final_fresh_iff_total_unused M e).mpr
  have hs := mixed_target_count_le_minima_add_one M hp e hQ hR3 (fullSupport_tau_a_mem M e hfull)
  have hu := fullSupport_unused_count M hp e hR3 hfull
  omega
end

/-- TW.13 with the literal original object, arbitrary actual role and a single
full-support factorization; no preselected favorable role is assumed. -/
theorem fullSupport_fresh (M : MultiplicityBase Gamma) (hp : chosenDefect M.base=3)
    (hR3 : (P3R51.internalDegrees M).card=3) (e : Fin 3 ≃ Fin 3)
    (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hfull : PrincipalFullSupport M e) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ResidueData.cExceptionalCount (routingData M.base e) ≤
      Nat.card (ResidueData.CFreshUnusedMergeBases (routingData M.base e))+1 := by
  exact fullSupport_fresh_role M hp e hR3 hQ hfull
end NS25Lean.P3R67

