import NS25Lean.P2BranchBReverseXOldExclusion

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L2B2A2 L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2C4H CombinatorialCore

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- In the inactive Branch-B chart, the routing modulus is the completed
third normalized generator. -/
@[simp] theorem branchB_inactive_routingA_eq_normalizedC
    (R : SectorBCriticalRoleBranchB P) :
    routingA P.M.base (branchBInactiveReindex R) = normalizedC R := by
  change weights P.M.base (branchBInactiveReindex R 0) /
      routingD P.M.base (branchBInactiveReindex R) =
    weights P.M.base (R.reindex 2) /
      tailGcd (P.M.base.tailDegrees 0).val
        (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val
  rw [branchBInactiveReindex_zero, routingD_eq_chosenTailGcd]

/-- The inactive chart's first step is the Branch-B normalized `a`. -/
@[simp] theorem branchB_inactive_routingB_eq_normalizedA
    (R : SectorBCriticalRoleBranchB P) :
    routingB P.M.base (branchBInactiveReindex R) = normalizedA R := by
  change weights P.M.base (branchBInactiveReindex R 1) /
      routingD P.M.base (branchBInactiveReindex R) =
    weights P.M.base (R.reindex 0) /
      tailGcd (P.M.base.tailDegrees 0).val
        (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val
  rw [branchBInactiveReindex_one, routingD_eq_chosenTailGcd]

/-- The inactive chart's second step is the Branch-B normalized `b`. -/
@[simp] theorem branchB_inactive_routingC_eq_normalizedB
    (R : SectorBCriticalRoleBranchB P) :
    routingC P.M.base (branchBInactiveReindex R) = normalizedB R := by
  change weights P.M.base (branchBInactiveReindex R 2) /
      routingD P.M.base (branchBInactiveReindex R) =
    weights P.M.base (R.reindex 1) /
      tailGcd (P.M.base.tailDegrees 0).val
        (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val
  rw [branchBInactiveReindex_two, routingD_eq_chosenTailGcd]

/-- B30 SILVER: the exact prefix Apéry diamond underlying the B29 OLD
packet.  The four displayed equations are direct specializations of the
two defining Apéry step equations; the reverse-X equality identifies the
opposite representative with the actual numeric source. -/
theorem branchB_positive_center_pureB_reverseX_old_prefix_apery_diamond_packet
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
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Iminus := branchBActualPrefixIdeal R x hsx
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    let r := branchBActualExceptionalRoutingSource P R x
    let s := branchBActualExceptionalNormalizedSource P R x
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
    let h := Gminus.u (Gminus.c A)
    0 < h ∧
      Gminus.v (Gminus.b A) = h ∧
      Iminus.aperyRepresentative (routingA P.M.base e) r.val = s.val ∧
      Iminus.aperyRepresentative (routingA P.M.base e) r.val =
        (C.data.sourceValue : ℤ) ∧
      C.data.sourceValue = (i + zH R) * normalizedB R ∧
      Iminus.aperyRepresentative (routingA P.M.base e) A +
          routingB P.M.base e =
        Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.b A) ∧
      Iminus.aperyRepresentative (routingA P.M.base e) A +
          routingC P.M.base e =
        Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.c A) ∧
      Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.c A) +
          routingB P.M.base e =
        Iminus.aperyRepresentative (routingA P.M.base e) r.val +
          routingA P.M.base e * h ∧
      Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.b A) +
          routingC P.M.base e =
        Iminus.aperyRepresentative (routingA P.M.base e) r.val +
          routingA P.M.base e * h := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Iminus := branchBActualPrefixIdeal R x hsx
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let s := branchBActualExceptionalNormalizedSource P R x
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  let h := Gminus.u (Gminus.c A)
  have hold := branchB_positive_center_pureB_reverseX_old_same_diamond_packet
    R hB x hsx i j hcenter hroute hOld
  change Gminus.IsBranch A ∧ Gminus.branchTarget A = r.val ∧
      Gminus.IsSource r.val ∧ 0 < Gminus.u (Gminus.c A) ∧
      0 < Gminus.v (Gminus.b A) ∧
      Gminus.u (Gminus.c A) = Gminus.v (Gminus.b A) ∧ _ at hold
  have hbranch : Gminus.IsBranch A := hold.1
  have htarget : Gminus.branchTarget A = r.val := hold.2.1
  have hpositive : 0 < h := hold.2.2.2.1
  have hcross : Gminus.v (Gminus.b A) = h := hold.2.2.2.2.2.1.symm
  have hrepSource : Iminus.aperyRepresentative (routingA P.M.base e) r.val =
      s.val := hOld.2.1
  have hvalue := branchB_positive_center_pureB_reverseX_value_packet
    R hB hsx i j hcenter hroute
  change C.data.returnedY = 0 ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
      C.data.sourceValue = (i + zH R) * normalizedB R ∧ _ at hvalue
  have hsourceValue : C.data.sourceValue =
      (i + zH R) * normalizedB R := hvalue.2.2.2.2.2.2.1
  have hrepValue : Iminus.aperyRepresentative (routingA P.M.base e) r.val =
      (C.data.sourceValue : ℤ) := hrepSource.trans C.data.source_eq.symm
  have hbA := Iminus.apery_step_eq (routingA P.M.base e)
    (routingB P.M.base e) (routingHB P.M.base e) A
  have hcA := Iminus.apery_step_eq (routingA P.M.base e)
    (routingC P.M.base e) (routingHC P.M.base e) A
  have hbC := Iminus.apery_step_eq (routingA P.M.base e)
    (routingB P.M.base e) (routingHB P.M.base e) (Gminus.c A)
  have hcB := Iminus.apery_step_eq (routingA P.M.base e)
    (routingC P.M.base e) (routingHC P.M.base e) (Gminus.b A)
  change Iminus.aperyRepresentative (routingA P.M.base e) A +
      routingB P.M.base e =
    Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.b A) +
      routingA P.M.base e * Gminus.u A at hbA
  change Iminus.aperyRepresentative (routingA P.M.base e) A +
      routingC P.M.base e =
    Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.c A) +
      routingA P.M.base e * Gminus.v A at hcA
  change Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.c A) +
      routingB P.M.base e =
    Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.b (Gminus.c A)) +
      routingA P.M.base e * h at hbC
  change Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.b A) +
      routingC P.M.base e =
    Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.c (Gminus.b A)) +
      routingA P.M.base e * Gminus.v (Gminus.b A) at hcB
  have hbZero : Gminus.u A = 0 := hbranch.1
  have hcZero : Gminus.v A = 0 := hbranch.2
  have hbBase : Iminus.aperyRepresentative (routingA P.M.base e) A +
      routingB P.M.base e =
      Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.b A) := by
    simpa [hbZero] using hbA
  have hcBase : Iminus.aperyRepresentative (routingA P.M.base e) A +
      routingC P.M.base e =
      Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.c A) := by
    simpa [hcZero] using hcA
  have hbTop : Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.c A) +
      routingB P.M.base e =
      Iminus.aperyRepresentative (routingA P.M.base e) r.val +
        routingA P.M.base e * h := by
    rw [← htarget]
    simpa [ResidueData.branchTarget, Gminus.commute A] using hbC
  have hcTop : Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.b A) +
      routingC P.M.base e =
      Iminus.aperyRepresentative (routingA P.M.base e) r.val +
        routingA P.M.base e * h := by
    rw [← htarget]
    simpa [ResidueData.branchTarget, hcross] using hcB
  exact ⟨hpositive, hcross, hrepSource, hrepValue, hsourceValue,
    hbBase, hcBase, hbTop, hcTop⟩

/-- The four-cell packet collapsed to the exact numeric reverse-X balance.
This is the strongest equality supplied by the local OLD diamond alone. -/
theorem branchB_positive_center_pureB_reverseX_old_prefix_apery_balance
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
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Iminus := branchBActualPrefixIdeal R x hsx
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    let h := Gminus.u (Gminus.c A)
    Iminus.aperyRepresentative (routingA P.M.base e) A + normalizedA R +
        normalizedB R =
      ((i + zH R) * normalizedB R : ℕ) + normalizedC R * h := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Iminus := branchBActualPrefixIdeal R x hsx
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  let h := Gminus.u (Gminus.c A)
  have hp :=
    branchB_positive_center_pureB_reverseX_old_prefix_apery_diamond_packet
      R hB x hsx i j hcenter hroute hOld
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hp
  rcases hp with ⟨_hpos, _hcross, _hrepSource, hrepValue, hsourceValue,
    _hbBase, hcBase, hbTop, _hcTop⟩
  have hra : routingA P.M.base e = normalizedC R := by
    simpa [e] using branchB_inactive_routingA_eq_normalizedC R
  have hrb : routingB P.M.base e = normalizedA R := by
    simpa [e] using branchB_inactive_routingB_eq_normalizedA R
  have hrc : routingC P.M.base e = normalizedB R := by
    simpa [e] using branchB_inactive_routingC_eq_normalizedB R
  calc
    Iminus.aperyRepresentative (routingA P.M.base e) A + normalizedA R +
        normalizedB R =
        Iminus.aperyRepresentative (routingA P.M.base e) A +
          routingC P.M.base e + routingB P.M.base e := by
            rw [hrb, hrc]
            abel
    _ = Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.c A) +
          routingB P.M.base e := by rw [hcBase]
    _ = Iminus.aperyRepresentative (routingA P.M.base e) r.val +
          routingA P.M.base e * h := hbTop
    _ = (C.data.sourceValue : ℤ) + routingA P.M.base e * h := by
          rw [hrepValue]
    _ = ((i + zH R) * normalizedB R : ℕ) + normalizedC R * h := by
          rw [hsourceValue]
          rw [hra]

end NS25Lean.L5A2B4AR5B
