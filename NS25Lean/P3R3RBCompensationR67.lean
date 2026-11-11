import NS25Lean.P3R3TargetCountR67
import NS25Lean.P3R3StaircaseCountR67
import NS25Lean.P3R3CornersR67
import NS25Lean.P3R3MixedCornersR67

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open L5A2C4OR3 L5A2C4OR4 P3R61
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "B" => criticalExponent M.base (e 1)
local notation "T" => P3R57.roleCoefficient M hp e 0 2
local notation "U" => P3R57.roleCoefficient M hp e 1 0
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

/-- Maximum of genuine occupied RB depths, not a historical RECORD owner. -/
theorem exists_max_rb_depth
    (hocc : ∃ q i j d, 0<q ∧ q<Q ∧ RBLevel M hp e q i j d) :
    ∃ D : ℕ, (∃ q i j, 0<q ∧ q<Q ∧ RBLevel M hp e q i j D) ∧
      (∀ q i j d, 0<q → q<Q → RBLevel M hp e q i j d → d≤D) := by
  classical
  let S := (Finset.range U).filter (fun d => ∃ q i j, 0<q ∧ q<Q ∧ RBLevel M hp e q i j d)
  obtain ⟨q,i,j,d,hq,hqQ,hl⟩ := hocc
  have hSne : S.Nonempty := ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl.2.2.2.2.2.2.2.1, q,i,j,hq,hqQ,hl⟩⟩
  refine ⟨S.max' hSne,(Finset.mem_filter.mp (Finset.max'_mem S hSne)).2,?_⟩
  intro q i j d hq hqQ hl
  exact Finset.le_max' S d (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl.2.2.2.2.2.2.2.1,q,i,j,hq,hqQ,hl⟩)

/-- NF.10 actual RB antichain/corner TOTAL unused-merge lower bound. -/
theorem rb_unused_count_ge_minima (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, RBLevel M hp e n i j d)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (hcorner : ResidueData.ExactUnusedMergeReverseBase (routingData M.base e)
      (gridResidue M.base e (B-1) (T-1))) :
    (coordinateMinima (rbFloorPoints M hp e)).card ≤
      Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e)) := by
  have sums := P3R58.p3_coefficient_sums M hp e
  have hT := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  apply rectangular_staircase_unused_bound M hp e B T (rbFloorPoints M hp e)
    (rbFloorPoints_nonempty M hp e hQ hlevels) le_rfl (by omega) (Or.inr le_rfl)
    (by
      intro p hmem
      obtain ⟨hp1,hp2,hpB,hpT⟩ := rbFloorPoints_bounds M hp e p hmem
      exact ⟨hp1,hpB,hp2,hpT⟩)
    (by
      intro i j hi hj
      exact rb_canonical_membership_iff_floorPoint M hp e hQ hlevels htau i j hi
        (by omega) (Or.inr hj))
    (T-1) (by omega) (Or.inr (by omega))
  simpa only [gridResidue,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hcorner

/-- NF.11: cancel the SAME final baseline after actual source and TOTAL merge counts. -/
theorem rb_fresh_of_actual_corner (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, RBLevel M hp e n i j d)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (hcorner : ResidueData.ExactUnusedMergeReverseBase (routingData M.base e)
      (gridResidue M.base e (B-1) (T-1))) :
    ResidueData.cExceptionalCount (routingData M.base e) ≤
      Nat.card (ResidueData.CFreshUnusedMergeBases (routingData M.base e))+1 := by
  apply (final_fresh_iff_total_unused M e).mpr
  have hs := rb_target_count_le_minima_add_one M hp e hQ hlevels htau
  have hu := rb_unused_count_ge_minima M hp e hQ hlevels htau hcorner
  omega

/-- NF.07–NF.11 on the exact protected physical role constructed by NF.06. -/
theorem rb_fresh_of_protected (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, RBLevel M hp e n i j d)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (D : ℕ) (hatt : ∃ n i j, 0<n ∧ n<Q ∧ RBLevel M hp e n i j D)
    (hmax : ∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D)
    (hprotect : (omegaDegree M hp e : ℤ)-(Q*M.base.q.val : ℕ)-D*a ∉ (routingH M.base e).asRelativeIdeal) :
    ResidueData.cExceptionalCount (routingData M.base e) ≤
      Nat.card (ResidueData.CFreshUnusedMergeBases (routingData M.base e))+1 := by
  exact rb_fresh_of_actual_corner M hp e hQ hlevels htau
    (protected_rb_corner M hp e hQ hlevels D hatt hmax hprotect)

/-- NF uses exactly the same protected-corner core as TW, with both-arm
interference proved once and the final carrier kept literal. -/
theorem rb_fresh_of_shared_protected
    (hR3 : (P3R51.internalDegrees M).card=3) (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n<Q → ∃ i j d, RBLevel M hp e n i j d)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (D : ℕ) (hatt : ∃ n i j, 0<n ∧ n<Q ∧ RBLevel M hp e n i j D)
    (hmax : ∀ n i j d, 0<n → n<Q → RBLevel M hp e n i j d → d≤D)
    (hprotect : (omegaDegree M hp e : ℤ)-(Q*M.base.q.val : ℕ)-D*a ∉ (routingH M.base e).asRelativeIdeal) :
    ResidueData.cExceptionalCount (routingData M.base e) ≤
      Nat.card (ResidueData.CFreshUnusedMergeBases (routingData M.base e))+1 := by
  exact rb_fresh_of_actual_corner M hp e hQ hlevels htau
    (shared_protected_rb_corner M hp e hR3 D hatt hmax hprotect)

end
end NS25Lean.P3R67
