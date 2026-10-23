import NS25Lean.P2BranchBSemanticIncidence

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B2A2 L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2C4H L5A2C4I

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Exact change of routing-source chart through the common chosen-base
source.  No equality between the two reindexings is asserted. -/
noncomputable def branchBSourceChartEquiv
    (R : SectorBCriticalRoleBranchB P) :
    let e₁ := R.reindex
    let e₂ := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e₁) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₁)⟩
    letI : NeZero (routingA P.M.base e₂) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₂)⟩
    {r // (routingData P.M.base e₁).IsSource r} ≃
      {r // (routingData P.M.base e₂).IsSource r} := by
  let e₁ := R.reindex
  let e₂ := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e₁) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e₁)⟩
  letI : NeZero (routingA P.M.base e₂) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e₂)⟩
  exact (routingSourceEquivChosenSource P.M.base e₁).trans
    (routingSourceEquivChosenSource P.M.base e₂).symm

/-- The B26 source constructed in the coherent Herzog chart and the source
target of the actual exceptional branch are the same chosen source after
the exact chart change. -/
theorem branchB_actualExceptional_reverseX_source_identification
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val) :
    let e₁ := R.reindex
    let e₂ := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e₁) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₁)⟩
    letI : NeZero (routingA P.M.base e₂) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₂)⟩
    let D := branchBActualFinalRoutingSource R hsx
    let r := branchBActualExceptionalRoutingSource P R x
    branchBSourceChartEquiv R D = r ∧
      (routingI P.M.base e₁).aperyRepresentative
          (routingA P.M.base e₁) D.val =
        (branchBActualExceptionalNormalizedSource P R x).val ∧
      (routingI P.M.base e₂).aperyRepresentative
          (routingA P.M.base e₂) r.val =
        (branchBActualExceptionalNormalizedSource P R x).val := by
  let e₁ := R.reindex
  let e₂ := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e₁) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e₁)⟩
  letI : NeZero (routingA P.M.base e₂) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e₂)⟩
  let D := branchBActualFinalRoutingSource R hsx
  let r := branchBActualExceptionalRoutingSource P R x
  have hmain := branchB_actual_final_routing_source_spec R hsx
  have hinactive := branchB_actualExceptional_source_packet P R x
  have hchosen : chosenSourceOfNormalizedFinalSource P.M.base hsx.1 =
      branchBActualExceptionalChosenSource P R x := by
    rw [← chosenSourceOfNormalizedFinalSource_of_chosenSource P.M.base
      (branchBActualExceptionalChosenSource P R x)]
    congr
  have hchart : branchBSourceChartEquiv R D = r := by
    apply (routingSourceEquivChosenSource P.M.base e₂).injective
    simpa only [e₁, e₂, branchBSourceChartEquiv, Equiv.trans_apply,
      id_eq, Equiv.apply_symm_apply, D, r, branchBActualFinalRoutingSource,
      branchBActualExceptionalChosenSource] using hchosen
  exact ⟨hchart, hmain.2, hinactive.2.2.2.1.symm⟩

/-- Final branch incidence comes from the actual exceptional branch witness
itself; no source-to-branch converse is used. -/
theorem branchB_actualExceptional_final_branch_incidence
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let G := routingData P.M.base e
    let A := x.val.val.val
    let r := branchBActualExceptionalRoutingSource P R x
    G.IsBranch A ∧ G.branchTarget A = r.val := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let G := routingData P.M.base e
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  exact ⟨x.val.val.property.1, rfl⟩

/-- The principal TARGET channel is preserved.  On the complementary
nonprincipal channel, the B26 source is exactly the chart transport of the
actual exceptional branch target, and the final branch incidence is already
present in the witness `x`. -/
theorem branchB_actualExceptional_principal_or_identified_final_branch
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    let s := branchBActualExceptionalNormalizedSource P R x
    s.val = (actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) ∨
      ∃ hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
          (actualPrincipalIndex P.M.base) s.val,
        let e₁ := R.reindex
        let e₂ := branchBInactiveReindex R
        letI : NeZero (routingA P.M.base e₁) :=
          ⟨Nat.ne_of_gt (routingA_pos P.M.base e₁)⟩
        letI : NeZero (routingA P.M.base e₂) :=
          ⟨Nat.ne_of_gt (routingA_pos P.M.base e₂)⟩
        let D := branchBActualFinalRoutingSource R hsx
        let r := branchBActualExceptionalRoutingSource P R x
        let G₂ := routingData P.M.base e₂
        let A := x.val.val.val
        branchBSourceChartEquiv R D = r ∧
          G₂.IsBranch A ∧ G₂.branchTarget A = r.val := by
  let s := branchBActualExceptionalNormalizedSource P R x
  rcases branchB_actualExceptional_source_principal_or_birth P R x with
      hprincipal | hsx
  · exact Or.inl hprincipal
  · refine Or.inr ⟨hsx, ?_⟩
    let e₁ := R.reindex
    let e₂ := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e₁) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₁)⟩
    letI : NeZero (routingA P.M.base e₂) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₂)⟩
    let D := branchBActualFinalRoutingSource R hsx
    let r := branchBActualExceptionalRoutingSource P R x
    let G₂ := routingData P.M.base e₂
    let A := x.val.val.val
    have hid := branchB_actualExceptional_reverseX_source_identification R x hsx
    have hinc := branchB_actualExceptional_final_branch_incidence P R x
    exact ⟨hid.1, hinc.1, hinc.2⟩

/-- Silver+ B27 packet: a nonprincipal actual exceptional branch target is
the chart transport of the B26 reverse-X source, carries the actual final
branch incidence, and retains the frozen B24--B26 coordinate/value data. -/
theorem branchB_actualExceptional_positive_center_pureB_reverseX_final_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hsx
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let e₁ := R.reindex
    let e₂ := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e₁) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₁)⟩
    letI : NeZero (routingA P.M.base e₂) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₂)⟩
    let D := branchBActualFinalRoutingSource R hsx
    let r := branchBActualExceptionalRoutingSource P R x
    let G₂ := routingData P.M.base e₂
    let A := x.val.val.val
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
    let candidateNumerator : ℤ :=
      (C.data.ell * normalizedM P.M.base : ℕ) +
        ((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) -
          C.data.sourceValue
    branchBSourceChartEquiv R D = r ∧
      G₂.IsBranch A ∧ G₂.branchTarget A = r.val ∧
      D.val = gridResidue P.M.base e₁ (i + zH R) 0 ∧
      C.source_coordinate.i = (i + zH R : ℕ) ∧
      C.source_coordinate.j = 0 ∧ C.source_coordinate.level = 0 ∧
      candidateNumerator = -(C.data.returnedX : ℤ) * normalizedA R := by
  let e₁ := R.reindex
  let e₂ := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e₁) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e₁)⟩
  letI : NeZero (routingA P.M.base e₂) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e₂)⟩
  let D := branchBActualFinalRoutingSource R hsx
  let r := branchBActualExceptionalRoutingSource P R x
  let G₂ := routingData P.M.base e₂
  let A := x.val.val.val
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  let candidateNumerator : ℤ :=
    (C.data.ell * normalizedM P.M.base : ℕ) +
      ((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) -
        C.data.sourceValue
  have hid := branchB_actualExceptional_reverseX_source_identification R x hsx
  have hinc := branchB_actualExceptional_final_branch_incidence P R x
  have hB26 := branchB_positive_center_pureB_reverseX_actual_source_state
    R hB hsx i j hcenter hroute
  exact ⟨hid.1, hinc.1, hinc.2, hB26.2.1,
    hB26.2.2.2.1, hB26.2.2.2.2.1, hB26.2.2.2.2.2.1,
    hB26.2.2.2.2.2.2⟩

end NS25Lean.L5A2B4AR5B
