import NS25Lean.P2BranchBPrincipalSurgeryChannel

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B2A2 L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2C4H

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- B29 kernel checkpoint.  Under the OLD alternative, the prefix branch,
its source target, and the positive cross all belong to the very same
diamond based at `A`.  The remaining clauses attach the frozen B27
reverse-X source coordinates to that same target residue through the exact
chosen-source chart equivalence.

This statement deliberately does not call the reverse-X source an X target:
the current API has no prefix target-family classifier. -/
theorem branchB_positive_center_pureB_reverseX_old_same_diamond_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = i ∧ S.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hOld : IsOldActualBranch R x hsx) :
    let e₁ := R.reindex
    let e₂ := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e₁) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₁)⟩
    letI : NeZero (routingA P.M.base e₂) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e₂)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let G := routingData P.M.base e₂
    let A := x.val.val.val
    let r := branchBActualExceptionalRoutingSource P R x
    let D := branchBActualFinalRoutingSource R hsx
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
    let candidateNumerator : ℤ :=
      (C.data.ell * normalizedM P.M.base : ℕ) +
        ((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) -
          C.data.sourceValue
    Gminus.IsBranch A ∧
      Gminus.branchTarget A = r.val ∧
      Gminus.IsSource r.val ∧
      0 < Gminus.u (Gminus.c A) ∧
      0 < Gminus.v (Gminus.b A) ∧
      Gminus.u (Gminus.c A) = Gminus.v (Gminus.b A) ∧
      G.IsBranch A ∧ G.branchTarget A = r.val ∧
      branchBSourceChartEquiv R D = r ∧
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
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let G := routingData P.M.base e₂
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let D := branchBActualFinalRoutingSource R hsx
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  let candidateNumerator : ℤ :=
    (C.data.ell * normalizedM P.M.base : ℕ) +
      ((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) -
        C.data.sourceValue
  change Gminus.IsSource r.val ∧ _ at hOld
  have hsource : Gminus.IsSource r.val := hOld.1
  have hbranch : Gminus.IsBranch A := hOld.2.2.2.1
  have htarget : Gminus.branchTarget A = r.val := hOld.2.2.2.2.1
  have hfinalBranch : G.IsBranch A := hOld.2.2.2.2.2.1
  have hfinalTarget : G.branchTarget A = r.val := hOld.2.2.2.2.2.2
  have hcross : Gminus.v (Gminus.b A) = Gminus.u (Gminus.c A) :=
    Gminus.cross_eq_of_isBranch hbranch
  have hbInv : Gminus.b.symm r.val = Gminus.c A := by
    apply Gminus.b.injective
    rw [Gminus.b.apply_symm_apply]
    rw [← htarget]
    exact Gminus.commute A |>.symm
  have hcInv : Gminus.c.symm r.val = Gminus.b A := by
    apply Gminus.c.injective
    rw [Gminus.c.apply_symm_apply]
    rw [← htarget]
    rfl
  have huNe : Gminus.u (Gminus.c A) ≠ 0 := by
    rw [← hbInv]
    exact hsource.1
  have hvNe : Gminus.v (Gminus.b A) ≠ 0 := by
    rw [← hcInv]
    exact hsource.2
  have hB27 :=
    branchB_actualExceptional_positive_center_pureB_reverseX_final_packet
      R hB x hsx i j hcenter hroute
  exact ⟨hbranch, htarget, hsource, Nat.pos_of_ne_zero huNe,
    Nat.pos_of_ne_zero hvNe, hcross.symm, hfinalBranch, hfinalTarget,
    hB27.1, hB27.2.2.2.1, hB27.2.2.2.2.1,
    hB27.2.2.2.2.2.1, hB27.2.2.2.2.2.2.1,
    hB27.2.2.2.2.2.2.2⟩

end NS25Lean.L5A2B4AR5B
