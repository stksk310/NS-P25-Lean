import NS25Lean.P3R3MixedTargetsR67
import NS25Lean.P3R3TargetCountR67
import NS25Lean.P3R3AntichainR67

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1
open P3R61 CombinatorialCore
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local notation "B" => criticalExponent M.base (e 1)
local notation "C" => criticalExponent M.base (e 2)
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

/-- Distinct actual nonprincipal LT floor coordinates, with duplicates removed. -/
def ltFloorPoints : Finset (ℕ × ℕ) := by
  classical
  exact
  ((Finset.range B).product (Finset.range C)).filter
    (fun p => ∃ q d, 0<q ∧ q<Q ∧ LTLevel M hp e q p.1 p.2 d)

theorem mem_ltFloorPoints (p : ℕ × ℕ) :
    p ∈ ltFloorPoints M hp e ↔ ∃ q d, 0<q ∧ q<Q ∧ LTLevel M hp e q p.1 p.2 d := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨q,d,hq,hqQ,hl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hl.2.2.2.2.2.1,
      Finset.mem_range.mpr hl.2.2.2.2.2.2.1⟩,q,d,hq,hqQ,hl⟩
theorem ltFloorPoints_bounds (p : ℕ × ℕ) (hp' : p ∈ ltFloorPoints M hp e) :
    0<p.1 ∧ 0<p.2 ∧ p.1<P3R57.roleCoefficient M hp e 0 1 ∧ p.2<C := by
  obtain ⟨q,d,hq,hqQ,hl⟩ := (mem_ltFloorPoints M hp e p).mp hp'
  exact ⟨hl.1,hl.2.1,hl.2.2.2.1,hl.2.2.2.2.2.2.1⟩
theorem lt_floorpoint_mem_final (p : ℕ × ℕ) (hp' : p ∈ ltFloorPoints M hp e) :
    (p.1 : ℤ)*b+p.2*c ∈ routingI M.base e := by
  obtain ⟨q,d,hq,hqQ,hl⟩ := (mem_ltFloorPoints M hp e p).mp hp'
  apply return_subset_final M e q hq
  refine ⟨?_,?_⟩
  · simpa using routing_combination_mem M.base e 0 p.1 p.2 (by omega) (by omega) (by omega)
  · change (p.1 : ℤ)*b+p.2*c-(q*M.base.q.val : ℕ) ∈ (routingH M.base e).asRelativeIdeal
    rw [hl.2.2.2.2.2.2.2.2]
    convert routing_combination_mem M.base e d 0 0 (by omega) (by omega) (by omega) using 1 <;> ring

/-- An actual minimal final generator represented by an LT floor point
must be coordinatewise minimal among the actual floor points. -/
theorem lt_floorpoint_minimal_coordinates (p : ℕ × ℕ) (hp' : p ∈ ltFloorPoints M hp e)
    (hmin : (routingI M.base e).IsMinimalGenerator ((p.1 : ℤ)*b+p.2*c)) :
    p ∈ coordinateMinima (ltFloorPoints M hp e) := by
  apply (mem_coordinateMinima _ _).mpr
  refine ⟨hp',?_⟩
  intro y hy hy1 hy2
  have hm := lt_floorpoint_mem_final M hp e y hy
  have hres : (p.1 : ℤ)*b+p.2*c-((y.1 : ℤ)*b+y.2*c) ∈ (routingH M.base e).asRelativeIdeal := by
    convert routing_combination_mem M.base e 0 ((p.1 : ℤ)-y.1) ((p.2 : ℤ)-y.2)
      (by omega) (by omega) (by omega) using 1 <;> ring
  have he := minimal_generator_eq_of_residual _ _ _ hmin hm hres
  obtain ⟨q,d,hq,hqQ,hl⟩ := (mem_ltFloorPoints M hp e p).mp hp'
  obtain ⟨h1,h2⟩ := subcritical_bc_factorization_unique M.base e p.1 p.2 y.1 y.2
    hl.2.2.2.2.2.1 hl.2.2.2.2.2.2.1 he
  exact Prod.ext h1 h2

/-- Actual RB points lie strictly to the right of the notch. -/
theorem rbFloorPoints_arm_bounds (p : ℕ × ℕ) (hp' : p∈rbFloorPoints M hp e) :
    P3R57.roleCoefficient M hp e 0 1<p.1 ∧ p.2<P3R57.roleCoefficient M hp e 0 2 := by
  obtain ⟨q,d,hq,hqQ,hl⟩ := (mem_rbFloorPoints M hp e p).mp hp'
  exact ⟨hl.2.2.2.1,hl.2.2.2.2.1⟩

/-- Actual LT points lie strictly above the notch. -/
theorem ltFloorPoints_arm_bounds (p : ℕ × ℕ) (hp' : p∈ltFloorPoints M hp e) :
    p.1<P3R57.roleCoefficient M hp e 0 1 ∧ P3R57.roleCoefficient M hp e 0 2<p.2 := by
  obtain ⟨q,d,hq,hqQ,hl⟩ := (mem_ltFloorPoints M hp e p).mp hp'
  exact ⟨hl.2.2.2.1,hl.2.2.2.2.1⟩

/-- A canonical RB-rectangle cell sees exactly the RB floor antichain. -/
theorem mixed_rb_rectangle_membership (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (i j : ℕ) (hi : i<B) (hj : j<P3R57.roleCoefficient M hp e 0 2) :
    ((i : ℤ)*b+j*c ∈ routingI M.base e) ↔
      ∃ p∈rbFloorPoints M hp e, p.1 ≤ i ∧ p.2 ≤ j := by
  have sums := P3R58.p3_coefficient_sums M hp e
  rw [final_r3_canonical_membership M hp e hR3 htau i j hi (by omega) (Or.inr hj)]
  constructor
  · rintro ⟨q,x,y,d,hq,hqQ,harm,hx,hy⟩
    have hl : RBLevel M hp e q x y d := by
      rcases harm with harm | harm
      · exact harm
      · have := harm.2.2.2.2.1
        omega
    exact ⟨(x,y),(mem_rbFloorPoints M hp e _).mpr ⟨q,d,hq,hqQ,hl⟩,hx,hy⟩
  · rintro ⟨p,hp',hx,hy⟩
    obtain ⟨q,d,hq,hqQ,hl⟩ := (mem_rbFloorPoints M hp e p).mp hp'
    exact ⟨q,p.1,p.2,d,hq,hqQ,Or.inl hl,hx,hy⟩

/-- A canonical LT-rectangle cell sees exactly the LT floor antichain. -/
theorem mixed_lt_rectangle_membership (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal)
    (i j : ℕ) (hi : i<P3R57.roleCoefficient M hp e 0 1) (hj : j<C) :
    ((i : ℤ)*b+j*c ∈ routingI M.base e) ↔
      ∃ p∈ltFloorPoints M hp e, p.1 ≤ i ∧ p.2 ≤ j := by
  have sums := P3R58.p3_coefficient_sums M hp e
  rw [final_r3_canonical_membership M hp e hR3 htau i j (by omega) hj (Or.inl hi)]
  constructor
  · rintro ⟨q,x,y,d,hq,hqQ,harm,hx,hy⟩
    have hl : LTLevel M hp e q x y d := by
      rcases harm with harm | harm
      · have := harm.2.2.2.1
        omega
      · exact harm
    exact ⟨(x,y),(mem_ltFloorPoints M hp e _).mpr ⟨q,d,hq,hqQ,hl⟩,hx,hy⟩
  · rintro ⟨p,hp',hx,hy⟩
    obtain ⟨q,d,hq,hqQ,hl⟩ := (mem_ltFloorPoints M hp e p).mp hp'
    exact ⟨q,p.1,p.2,d,hq,hqQ,Or.inr hl,hx,hy⟩

/-- Any actual RB return supplies a point; no nonempty arm is postulated. -/
theorem rbFloorPoints_nonempty_of_return (q : ℕ) (hq : 0<q) (hqQ : q<Q)
    (hr : P3R59.RBReturn M hp e q) : (rbFloorPoints M hp e).Nonempty := by
  obtain ⟨i,j,d,hl⟩ := rb_level_exists M hp e q hr
  exact ⟨(i,j),(mem_rbFloorPoints M hp e _).mpr ⟨q,d,hq,hqQ,hl⟩⟩

theorem ltFloorPoints_nonempty_of_return (q : ℕ) (hq : 0<q) (hqQ : q<Q)
    (hr : P3R59.LTReturn M hp e q) : (ltFloorPoints M hp e).Nonempty := by
  obtain ⟨i,j,d,hl⟩ := lt_level_exists M hp e q hr
  exact ⟨(i,j),(mem_ltFloorPoints M hp e _).mpr ⟨q,d,hq,hqQ,hl⟩⟩
/-- TW.06: separate distinct RB and LT antichains bound the SAME actual final ST. -/
theorem mixed_target_count_le_minima_add_one (hQ : 1<Q)
    (hR3 : (P3R51.internalDegrees M).card=3)
    (htau : (Q*M.base.q.val : ℕ)-(a : ℤ) ∈ (routingH M.base e).asRelativeIdeal) :
    ResidueData.sourceTargetBranchCount (routingData M.base e) ≤
      (coordinateMinima (rbFloorPoints M hp e)).card+
      (coordinateMinima (ltFloorPoints M hp e)).card+1 := by
  classical
  let ER := coordinateMinima (rbFloorPoints M hp e)
  let EL := coordinateMinima (ltFloorPoints M hp e)
  let ST := ResidueData.CSourceTargetBranches (routingData M.base e)
  let Labels := Option ({p // p∈ER} ⊕ {p // p∈EL})
  let value : Labels → ℤ := fun z => match z with
    | none => (Q*M.base.q.val : ℕ)
    | some (Sum.inl p) => (p.val.1 : ℤ)*b+p.val.2*c
    | some (Sum.inr p) => (p.val.1 : ℤ)*b+p.val.2*c
  have hex : ∀ s : ST, ∃ z : Labels,
      (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s.val)=value z := by
    intro s
    rcases mixed_final_target_cover M hp e hQ hR3 htau s.val s.property with ht | ⟨n,i,j,d,hn,hnQ,harm,he⟩
    · exact ⟨none,ht⟩
    · have hmin := (P3R62.routing_source_iff_minimal M.base e _).mp s.property.2
      rw [he] at hmin
      rcases harm with hl | hl
      · have hp' : (i,j)∈rbFloorPoints M hp e := (mem_rbFloorPoints M hp e _).mpr ⟨n,d,hn,hnQ,hl⟩
        have hE : (i,j)∈ER := rb_floorpoint_minimal_coordinates M hp e (i,j) hp' hmin
        exact ⟨some (Sum.inl ⟨(i,j),hE⟩),he⟩
      · have hp' : (i,j)∈ltFloorPoints M hp e := (mem_ltFloorPoints M hp e _).mpr ⟨n,d,hn,hnQ,hl⟩
        have hE : (i,j)∈EL := lt_floorpoint_minimal_coordinates M hp e (i,j) hp' hmin
        exact ⟨some (Sum.inr ⟨(i,j),hE⟩),he⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro s t he
    have hrep := (hf s).trans ((congrArg value he).trans (hf t).symm)
    have hmod := congrArg (fun z : ℤ => (z : ZMod a)) hrep
    rw [(routingI M.base e).aperyRepresentative_mod,(routingI M.base e).aperyRepresentative_mod] at hmod
    exact Subtype.ext ((routingData M.base e).branchTarget_injective hmod)
  have hc := Nat.card_le_card_of_injective f hinj
  change Nat.card ST ≤ ER.card+EL.card+1
  simpa [Nat.card_eq_fintype_card,Labels] using hc
end
end NS25Lean.P3R67

