import NS25Lean.P3R2DirectTypeR63
import NS25Lean.P3R3StaircaseCountR67
import NS25Lean.P3R3TargetCountR67

set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.P3R63
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1 P3R61
open L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6 CombinatorialCore
variable {Gamma : NumericalSemigroup}
section
variable (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
local notation "a" => routingA M.base e
local notation "b" => routingB M.base e
local notation "c" => routingC M.base e
local notation "P" => P3R57.roleCoefficient M hp e 0 1
local notation "T" => P3R57.roleCoefficient M hp e 0 2
local notation "Q" => principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
local instance : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩

/-- The reduced R2 route counts every minimal floor point, rather than only
the subset which happens to be an ST target. Its southwest staircase is
formed in the actual final cut. -/
theorem rb_total_compensation_of_actual_targets (hQ : 1<Q)
    (hlevels : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d)
    (hshape : (∃ L K : ℕ, 0<L ∧ (Q*M.base.q.val : ℕ)=(L : ℤ)*a+K*b) ∨
      (∃ k : ℕ, T<k ∧ (Q*M.base.q.val : ℕ)=(k : ℤ)*c))
    (htargets : ∀ s : ResidueData.CSourceTargetBranches (routingData M.base e),
      ∃ n i j d, 0<n ∧ n≤Q-1 ∧ RBLevel M hp e n i j d ∧
        (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s.val)=
          (i : ℤ)*b+j*c) :
    ResidueData.sourceTargetBranchCount (routingData M.base e) ≤
      Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e))+1 := by
  classical
  let E := P3R67.coordinateMinima (P3R67.rbFloorPoints M hp e)
  let ST := ResidueData.CSourceTargetBranches (routingData M.base e)
  have hex : ∀ s : ST, ∃ p : {p // p∈E},
      (routingI M.base e).aperyRepresentative a ((routingData M.base e).branchTarget s.val)=
        (p.val.1:ℤ)*b+p.val.2*c := by
    intro s
    obtain ⟨n,i,j,d,hn,hnQ,hl,he⟩ := htargets s
    have hp' : (i,j)∈P3R67.rbFloorPoints M hp e :=
      (P3R67.mem_rbFloorPoints M hp e _).mpr ⟨n,d,hn,by omega,hl⟩
    have hmin := (P3R62.routing_source_iff_minimal M.base e _).mp s.property.2
    rw [he] at hmin
    exact ⟨⟨(i,j),P3R67.rb_floorpoint_minimal_coordinates M hp e _ hp' hmin⟩,he⟩
  choose f hf using hex
  have hST : ResidueData.sourceTargetBranchCount (routingData M.base e) ≤ E.card := by
    have hinj : Function.Injective f := by
      intro s t he
      have hrep := (hf s).trans ((congrArg (fun p : {p // p∈E} =>
        (p.val.1:ℤ)*b+p.val.2*c) he).trans (hf t).symm)
      have hmod := congrArg (fun z : ℤ => (z:ZMod a)) hrep
      rw [(routingI M.base e).aperyRepresentative_mod,
        (routingI M.base e).aperyRepresentative_mod] at hmod
      exact Subtype.ext ((routingData M.base e).branchTarget_injective hmod)
    have hc := Nat.card_le_card_of_injective f hinj
    change Nat.card ST ≤ E.card
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hc
  have sums := P3R58.p3_coefficient_sums M hp e
  have hS : (P3R67.rbFloorPoints M hp e).Nonempty := by
    obtain ⟨i,j,d,hl⟩ := hlevels 1 (by omega) (by omega)
    exact ⟨(i,j),(P3R67.mem_rbFloorPoints M hp e _).mpr ⟨1,d,by omega,by omega,hl⟩⟩
  have hUM := P3R67.floor_staircase_unused_bound M hp e
    (criticalExponent M.base (e 1)) T (P3R67.rbFloorPoints M hp e) hS le_rfl
    (by omega) (Or.inr le_rfl) (by
      intro p hp'
      have hb := P3R67.rbFloorPoints_bounds M hp e p hp'
      exact ⟨hb.2.2.1,hb.2.1,hb.2.2.2⟩) (by
      intro i j hi hj
      constructor
      · intro hm
        obtain ⟨n,x,y,d,hn,hnQ,hl,hxi,hyj⟩ :=
          rb_final_canonical_divisor M hp e hQ hlevels hshape i j hi hj hm
        exact ⟨(x,y),(P3R67.mem_rbFloorPoints M hp e _).mpr
          ⟨n,d,hn,by omega,hl⟩,hxi,hyj⟩
      · rintro ⟨p,hp',hpi,hpj⟩
        have hm := P3R67.rb_floorpoint_mem_final M hp e p hp'
        have ha := ideal_add_int (routingI M.base e) hm
          (routing_combination_mem M.base e 0 ((i:ℤ)-p.1) ((j:ℤ)-p.2)
            (by omega) (by omega) (by omega))
        convert ha using 1 <;> ring)
  change E.card-1 ≤ _ at hUM
  omega

theorem legal_rb_total_compensation (hlegal : LegalRole M e)
    (hRB : ∀ n : ℕ, 0<n → n<Q → P3R59.RBReturn M hp e n) :
    ResidueData.sourceTargetBranchCount (routingData M.base e) ≤
      Nat.card (ResidueData.ExactUnusedMergeBases (routingData M.base e))+1 := by
  by_cases hQ : Q=1
  · apply (P3CommonFinal.compensation_iff (routingData M.base e)).mpr
    have hc := routing_cExceptional_le_one_of_principal_index_one M e hQ
    omega
  have hpos := (principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive).1
  have hQgt : 1<Q := by omega
  have hlevels : ∀ n, 0<n → n≤Q-1 → ∃ i j d, RBLevel M hp e n i j d := by
    intro n hn hnq
    exact rb_level_exists M hp e n (hRB n hn (by omega))
  have hshape := principal_shapes_of_legal_role M hp e hlegal.1
    (hlegal.2 0 (by decide)) (hlegal.2 1 (by decide))
  have hsimple : (∃ L K : ℕ, 0<L ∧ (Q*M.base.q.val : ℕ)=(L : ℤ)*a+K*b) ∨
      (∃ k : ℕ, T<k ∧ (Q*M.base.q.val : ℕ)=(k : ℤ)*c) := by
    rcases hshape with ⟨k,hkT,hkV,hkC,ht⟩ | ⟨L,K,hL,hLW,hK,hKZ,hstrict,ht⟩
    · exact Or.inr ⟨k,hkT,by exact_mod_cast ht⟩
    · exact Or.inl ⟨L,K,hL,by exact_mod_cast ht⟩
  apply rb_total_compensation_of_actual_targets M hp e hQgt hlevels hsimple
  intro s
  exact final_rb_target_is_return M hp e hQgt hlevels hsimple
    (rb_principal_not_final_target M hp e hQgt hlevels hshape) s.val s.property

end
/-- The selected actual R2 role closes by the reduced total-floor staircase
route. The old stronger directional interface remains independently available. -/
theorem r2_original_type_via_final_staircase (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (hR2 : (P3R51.internalDegrees M).card=2) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma-2 := by
  obtain ⟨e,he,hRB⟩ := r2_legal_rb_role_exists M hp hR2
  have htotal := legal_rb_total_compensation M hp e he hRB
  have ht := P3R52Bridge.type_le_source_add_one_of_total_compensation M e htotal
  have hr := sourceCount_add_defect M.base
  omega
end NS25Lean.P3R63
