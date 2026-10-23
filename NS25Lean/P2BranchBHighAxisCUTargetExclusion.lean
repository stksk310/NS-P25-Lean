import NS25Lean.P2BranchBHighAxisCATailClamp
import NS25Lean.P2BranchBActualZeroEdgeBSP
import NS25Lean.P2BranchBInactiveGateExposedPF
import NS25Lean.P2BranchBPrefixHeightDictionary

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2B4AR4R2B L5A2C4C L5A2C4H L5A2C4OR3
open L5A2C4OR1 L5A2C4OR4 L5A2C4OR6

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The pure-`c` inward predecessor of the second actual critical relation
is live in the inactive cyclic chart.  This is the exact Lean form of the
`eta(0,c3-1) >= 1` input used by the repaired high-seam argument. -/
theorem branchB_inactive_second_pure_height_pos
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :
    0 < eta P.M.base (branchBInactiveReindex R) 0 (c2 R - 1) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  by_contra hnot
  have heta : eta B e 0 (c2 R - 1) = 0 := Nat.eq_zero_of_not_pos hnot
  have hK : gridDegree B e 0 0 (c2 R - 1) ∈ B.K :=
    (eta_eq_zero_iff B e 0 (c2 R - 1)).mp heta
  apply branchB_second_pure_boundary_exclusion R hB
  have hc2pos : 0 < c2 R := by
    have hp := (branchB_actual_herzog_coordinates R).cross_positive.1
    have hz := (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    omega
  have hdegree : R.secondDegree = c2 R * weights B (R.reindex 1) := by
    simpa [B, c2, R.reindex_one] using R.second.degree_eq_critical
  rw [hdegree]
  change c2 R * weights B (R.reindex 1) - weights B (R.reindex 1) ∈ B.K
  have hsplit : c2 R = 1 + (c2 R - 1) := by omega
  rw [hsplit, Nat.add_mul]
  simpa [e, gridDegree, branchBInactiveReindex_two, Nat.add_assoc] using hK

/-- The first arithmetic cap in the repaired B53 proof.  On the actual
high-axis-`c` packet, the selected depth is strictly below the inactive
Herzog coefficient `p = r31`.  It is derived from actual second-gate
liveness, rather than stored in the event or assumed by the U classifier. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (_hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let A := branchB_actual_selected_return_anchor_v2 R hB hsx
      A.coordinate.i = 0 ∧
      qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R) :
    (branchB_actual_selected_return_anchor_v2 R hB hsx).depth < r31 R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hsx
  change A.coordinate.i = 0 ∧ qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R at haxis
  let j := A.coordinate.j.toNat
  have hj0 : (0 : ℤ) ≤ A.coordinate.j := by omega
  have hj : A.coordinate.j = (j : ℤ) := (Int.toNat_of_nonneg hj0).symm
  have hjlt : j < c3 R := by
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    rw [hj] at haxis
    exact_mod_cast (show (j : ℤ) < c3 R by omega)
  change A.depth < r31 R
  by_contra hnot
  have hpd : r31 R ≤ A.depth := le_of_not_gt hnot
  let B := P.M.base
  let e := branchBInactiveReindex R
  have hAeq : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hBeq : routingB B e = normalizedA R := by
    simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hCeq : routingC B e = normalizedB R := by
    simpa [B, e] using branchB_inactive_routingC_eq_normalizedB R
  have haH : routingA B e ∈ routingH B e :=
    (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
        (AddSubmonoid.subset_closure (by simp))
  have hgen (a b c : ℕ) :
      a * routingA B e + b * routingB B e + c * routingC B e ∈
        routingH B e := by
    have ha := (routingH B e).toAddSubmonoid.nsmul_mem haH a
    have hb := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e) b
    have hc := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e) c
    simpa [nsmul_eq_mul, Nat.add_assoc] using
      (routingH B e).add_mem ((routingH B e).add_mem ha hb) hc
  let z : ℕ := (c2 R - 1) * normalizedB R
  have hzI : (z : ℤ) ∈ routingI B e := by
    apply (mem_routingI_iff_positive_return B e (z : ℤ)).2
    refine ⟨A.ell, A.ell_pos, ?_, ?_⟩
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨z, ?_, rfl⟩
      simpa [z, hAeq, hBeq, hCeq, Nat.zero_mul, Nat.zero_add] using
        hgen 0 0 (c2 R - 1)
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      let tail : ℕ := (c3 R - j) * normalizedC R +
        (A.depth - r31 R) * normalizedA R +
        (r12 R - 1) * normalizedB R
      refine ⟨tail, ?_, ?_⟩
      · simpa [tail, hAeq, hBeq, hCeq, Nat.add_assoc] using
          hgen (c3 R - j) (A.depth - r31 R) (r12 R - 1)
      · have hn : A.n = A.ell * normalizedM B := A.n_eq
        have hanchor : A.n + normalizedA R * A.depth =
            j * normalizedC R := by
          exact_mod_cast (show (A.n : ℤ) + normalizedA R * A.depth =
            (j : ℤ) * normalizedC R by simpa [hj] using haxis.2.2.2.2)
        have hrel : c3 R * normalizedC R =
            r31 R * normalizedA R + r32 R * normalizedB R := by
          simpa using
            (branchB_actual_herzog_coordinates R).normalized_relations.2.2
        have hsum2 : c2 R = r12 R + r32 R := by
          simpa using
            (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
        have hr12pos : 0 < r12 R := by
          simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
        have hc3pos : 0 < c3 R := by
          have hq := (branchB_actual_herzog_coordinates R).cross_positive.2.1
          have hv := (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.1
          have hs := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
          omega
        have hc3split : c3 R = j + (c3 R - j) := by omega
        have hdepthsplit : A.depth = r31 R + (A.depth - r31 R) := by omega
        have hr12split : r12 R = 1 + (r12 R - 1) := by omega
        have hc2predsplit : c2 R - 1 = (r12 R - 1) + r32 R := by
          omega
        have hc3mul : c3 R * normalizedC R =
            j * normalizedC R + (c3 R - j) * normalizedC R := by
          calc
            c3 R * normalizedC R =
                (j + (c3 R - j)) * normalizedC R :=
              congrArg (fun t => t * normalizedC R) hc3split
            _ = j * normalizedC R +
                (c3 R - j) * normalizedC R := Nat.add_mul ..
        have hdepthmul : A.depth * normalizedA R =
            r31 R * normalizedA R +
              (A.depth - r31 R) * normalizedA R := by
          calc
            A.depth * normalizedA R =
                (r31 R + (A.depth - r31 R)) * normalizedA R := by
                  exact congrArg (fun t => t * normalizedA R) hdepthsplit
            _ = r31 R * normalizedA R +
                (A.depth - r31 R) * normalizedA R := Nat.add_mul ..
        have hc2predmul : (c2 R - 1) * normalizedB R =
            (r12 R - 1) * normalizedB R + r32 R * normalizedB R := by
          rw [hc2predsplit, Nat.add_mul]
        have hcalc : z = A.n + tail := by
          dsimp [z, tail]
          have hanchor' : A.n + A.depth * normalizedA R =
              j * normalizedC R := by simpa [Nat.mul_comm] using hanchor
          omega
        rw [hcalc, hn]
        push_cast
        ring
  have heta0 : eta B e 0 (c2 R - 1) = 0 := by
    have hle := (normalizedGrid_mem_iff_eta_le B e 0 0 (c2 R - 1)).1
      (by simpa [z, normalizedGrid, hAeq, hBeq, hCeq] using hzI)
    omega
  exact (Nat.ne_of_gt (branchB_inactive_second_pure_height_pos R hB)) heta0

private theorem routing_b_gridResidue
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingData B e).b (gridResidue B e i j) =
      gridResidue B e (i + 1) j := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change gridResidue B e i j + routingB B e = gridResidue B e (i + 1) j
  exact (gridResidue_add_b B e i j).symm

private theorem routing_c_gridResidue
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingData B e).c (gridResidue B e i j) =
      gridResidue B e i (j + 1) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change gridResidue B e i j + routingC B e = gridResidue B e i (j + 1)
  exact (gridResidue_add_c B e i j).symm

private theorem routing_branchTarget_gridResidue
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingData B e).branchTarget (gridResidue B e i j) =
      gridResidue B e (i + 1) (j + 1) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  rw [CombinatorialCore.ResidueData.branchTarget,
    routing_b_gridResidue, routing_c_gridResidue]

/-- Exact inverse diamond for the dangerous U target.  All coordinates are
in the inactive chart; in particular its local `(p,q,u,v,w,z)` are
`(r31,r32,r13,r12,r23,r21)` in the frozen Branch-B names. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_U_inverse_diamond
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let G := routingData P.M.base e
    let A := x.val.val.val
    A = gridResidue P.M.base e (r31 R - S.depth - 1) (c2 R - 1) ∧
      G.b A = gridResidue P.M.base e (r31 R - S.depth) (c2 R - 1) ∧
      G.c A = gridResidue P.M.base e (c1 R - S.depth - 1) 0 ∧
      G.branchTarget A = gridResidue P.M.base e (c1 R - S.depth) 0 := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let G := routingData B e
  let A := x.val.val.val
  change A = gridResidue B e (r31 R - S.depth - 1) (c2 R - 1) ∧
      G.b A = gridResidue B e (r31 R - S.depth) (c2 R - 1) ∧
      G.c A = gridResidue B e (c1 R - S.depth - 1) 0 ∧
      G.branchTarget A = gridResidue B e (c1 R - S.depth) 0
  change (branchBActualExceptionalRoutingSource P R x).val =
      gridResidue B e (c1 R - S.depth) 0 at hU
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hp : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hv : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hD : G.branchTarget A = gridResidue B e (c1 R - S.depth) 0 :=
    hbirth.2.2.2.2.2.2.trans hU
  let A0 := gridResidue B e (r31 R - S.depth - 1) (c2 R - 1)
  have hcoord1 : r31 R - S.depth - 1 + 1 = r31 R - S.depth := by omega
  have hc2pos : 0 < c2 R := by
    have hz : 0 < r32 R := by
      simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
    omega
  have hcoord2 : c2 R - 1 + 1 = c2 R := by omega
  have hcandidateTarget : G.branchTarget A0 =
      gridResidue B e (c1 R - S.depth) 0 := by
    rw [routing_branchTarget_gridResidue, hcoord1, hcoord2]
    simp only [gridResidue]
    have hrel := (branchB_actual_herzog_coordinates R).normalized_relations.2.1
    have hAeq : routingA B e = normalizedC R := by
      simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
    have hBeq : routingB B e = normalizedA R := by
      simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
    have hCeq : routingC B e = normalizedB R := by
      simpa [B, e] using branchB_inactive_routingC_eq_normalizedB R
    rw [hAeq, hBeq, hCeq]
    have hrel' : c2 R * normalizedB R =
        r21 R * normalizedA R + r23 R * normalizedC R := by
      simpa using hrel
    have hsub : c1 R - S.depth = r21 R + (r31 R - S.depth) := by
      omega
    have hsubmul : (c1 R - S.depth) * normalizedA R =
        r21 R * normalizedA R +
          (r31 R - S.depth) * normalizedA R := by
      calc
        (c1 R - S.depth) * normalizedA R =
            (r21 R + (r31 R - S.depth)) * normalizedA R :=
          congrArg (fun t => t * normalizedA R) hsub
        _ = _ := Nat.add_mul ..
    have hnat :
        (r31 R - S.depth) * normalizedA R + c2 R * normalizedB R =
          ((c1 R - S.depth) * normalizedA R + 0 * normalizedB R) +
            r23 R * normalizedC R := by omega
    have hnatZ :
        ((((r31 R - S.depth) * normalizedA R +
          c2 R * normalizedB R : ℕ) : ℤ)) =
          ((((c1 R - S.depth) * normalizedA R +
            0 * normalizedB R : ℕ) : ℤ)) +
            (r23 R : ℤ) * normalizedC R := by exact_mod_cast hnat
    have hmod : Int.ModEq (normalizedC R)
        (((r31 R - S.depth) * normalizedA R +
          c2 R * normalizedB R : ℕ) : ℤ)
        (((c1 R - S.depth) * normalizedA R +
          0 * normalizedB R : ℕ) : ℤ) := by
      rw [Int.modEq_iff_dvd]
      refine ⟨-(r23 R : ℤ), ?_⟩
      rw [hnatZ]
      ring
    have hz := (ZMod.intCast_eq_intCast_iff
      (((r31 R - S.depth) * normalizedA R + c2 R * normalizedB R : ℕ) : ℤ)
      (((c1 R - S.depth) * normalizedA R + 0 * normalizedB R : ℕ) : ℤ)
      (normalizedC R)).2 hmod
    exact_mod_cast hz
  have hA : A = A0 := by
    exact G.b.injective (G.c.injective (hD.trans hcandidateTarget.symm))
  rw [hA]
  refine ⟨rfl, ?_, ?_, hcandidateTarget⟩
  · rw [routing_b_gridResidue, hcoord1]
  · rw [routing_c_gridResidue]
    simp only [gridResidue]
    have hrel := (branchB_actual_herzog_coordinates R).normalized_relations.2.1
    have hAeq : routingA B e = normalizedC R := by
      simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
    have hBeq : routingB B e = normalizedA R := by
      simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
    have hCeq : routingC B e = normalizedB R := by
      simpa [B, e] using branchB_inactive_routingC_eq_normalizedB R
    rw [hAeq, hBeq, hCeq]
    have hrel' : c2 R * normalizedB R =
        r21 R * normalizedA R + r23 R * normalizedC R := by
      simpa using hrel
    have hsub : c1 R - S.depth - 1 =
        r21 R + (r31 R - S.depth - 1) := by omega
    have hsubmul : (c1 R - S.depth - 1) * normalizedA R =
        r21 R * normalizedA R +
          (r31 R - S.depth - 1) * normalizedA R := by
      calc
        (c1 R - S.depth - 1) * normalizedA R =
            (r21 R + (r31 R - S.depth - 1)) * normalizedA R :=
          congrArg (fun t => t * normalizedA R) hsub
        _ = _ := Nat.add_mul ..
    have hnat :
        (r31 R - S.depth - 1) * normalizedA R +
            (c2 R - 1 + 1) * normalizedB R =
          ((c1 R - S.depth - 1) * normalizedA R +
            0 * normalizedB R) + r23 R * normalizedC R := by
      rw [hcoord2]
      omega
    have hnatZ :
        ((((r31 R - S.depth - 1) * normalizedA R +
          (c2 R - 1 + 1) * normalizedB R : ℕ) : ℤ)) =
          ((((c1 R - S.depth - 1) * normalizedA R +
            0 * normalizedB R : ℕ) : ℤ)) +
            (r23 R : ℤ) * normalizedC R := by exact_mod_cast hnat
    have hmod : Int.ModEq (normalizedC R)
        (((r31 R - S.depth - 1) * normalizedA R +
          (c2 R - 1 + 1) * normalizedB R : ℕ) : ℤ)
        (((c1 R - S.depth - 1) * normalizedA R +
          0 * normalizedB R : ℕ) : ℤ) := by
      rw [hcoord2]
      rw [Int.modEq_iff_dvd]
      refine ⟨-(r23 R : ℤ), ?_⟩
      rw [show (((r31 R - S.depth - 1) * normalizedA R +
          c2 R * normalizedB R : ℕ) : ℤ) =
          (((c1 R - S.depth - 1) * normalizedA R +
            0 * normalizedB R : ℕ) : ℤ) +
            (r23 R : ℤ) * normalizedC R by
        simpa [hcoord2] using hnatZ]
      ring
    have hz := (ZMod.intCast_eq_intCast_iff
      (((r31 R - S.depth - 1) * normalizedA R +
        (c2 R - 1 + 1) * normalizedB R : ℕ) : ℤ)
      (((c1 R - S.depth - 1) * normalizedA R +
        0 * normalizedB R : ℕ) : ℤ)
      (normalizedC R)).2 hmod
    exact_mod_cast hz

/-!
The selected B/C packet below is the B54 kernel bridge.  It compares the
canonical prefix representative with the ambient representative, transports
prefix membership to the final routing ideal, and keeps the actual source
separate from the selected anchor.
-/
private theorem branchB_prefixHeight_le_of_canonical_mem
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j n : ℕ)
    (hcanonical : IsCanonicalTailGridPoint P.M.base
      (branchBInactiveReindex R) i j)
    (hmem : (normalizedGrid P.M.base (branchBInactiveReindex R) n i j : ℤ) ∈
      branchBActualPrefixIdeal R x hsx) :
    branchBPrefixHeight R x hsx
      (gridResidue P.M.base (branchBInactiveReindex R) i j) ≤ n := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let r := gridResidue B e i j
  let Iminus := branchBActualPrefixIdeal R x hsx
  have hle := Iminus.aperyRepresentative_le (routingA B e) r hmem
    (by simpa [r] using normalizedGrid_mod B e n i j)
  have hdict := branchB_prefix_apery_eq_ambient_apery_add_height_mul
    R x hsx r
  have hlift0 :=
    (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e i j).mp hcanonical
  have hgrid := normalizedGrid_eq_physicalAlpha_add B e n i j
  rw [hlift0] at hgrid
  simp only [Nat.cast_zero, zero_add] at hgrid
  change (normalizedGrid B e n i j : ℤ) =
    branchBPrefixAlpha R r + routingA B e * n at hgrid
  rw [hdict, hgrid] at hle
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  dsimp only [B, e] at hle ha
  have hmul :
      (routingA P.M.base (branchBInactiveReindex R) : ℤ) *
          (branchBPrefixHeight R x hsx r : ℤ) ≤
        (routingA P.M.base (branchBInactiveReindex R) : ℤ) * n := by
    linarith only [hle]
  have hheight : (branchBPrefixHeight R x hsx r : ℤ) ≤ n :=
    (Int.mul_le_mul_left ha).mp hmul
  exact_mod_cast hheight

private theorem branchB_prefix_mem_final
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    {z : ℤ} (hz : z ∈ branchBActualPrefixIdeal R x hsx) :
    z ∈ routingI P.M.base (branchBInactiveReindex R) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  change ∃ ell : ℕ, 0 < ell ∧ ell < actualPrincipalIndex B ∧
    z ∈ returnIdeal (routingH B e) (ell * normalizedM B) at hz
  obtain ⟨ell, hell, _hellq, hz⟩ := hz
  exact (mem_routingI_iff_positive_return B e z).2
    ⟨ell, hell, hz.1, hz.2⟩

/-!
The next three lemmas are the B55 envelope interface.  They compare the
prefix and final ideals only through their Apéry representatives; no owner or
provenance identification is used.
-/
private theorem branchB_final_height_step_b_with_ambient_carry
    (R : SectorBCriticalRoleBranchB P)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    physicalHeight P.M.base e r + branchBPrefixAmbientU R r =
      physicalHeight P.M.base e (r + routingB P.M.base e) +
        (routingData P.M.base e).u r := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hl0 := physicalHeight_spec B e r
  have hl1 := physicalHeight_spec B e (r + routingB B e)
  have hfinal := (routingI B e).apery_step_eq (routingA B e)
    (routingB B e) (routingHB B e) r
  have hambient := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e) r
  change (routingI B e).aperyRepresentative (routingA B e) r =
    branchBPrefixAlpha R r + (routingA B e : ℤ) * physicalHeight B e r at hl0
  change (routingI B e).aperyRepresentative (routingA B e)
      (r + routingB B e) =
    branchBPrefixAlpha R (r + routingB B e) +
      (routingA B e : ℤ) * physicalHeight B e (r + routingB B e) at hl1
  change branchBPrefixAlpha R r + routingB B e =
    branchBPrefixAlpha R (r + routingB B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientU R r at hambient
  change (routingI B e).aperyRepresentative (routingA B e) r + routingB B e =
    (routingI B e).aperyRepresentative (routingA B e) (r + routingB B e) +
      (routingA B e : ℤ) * (routingData B e).u r at hfinal
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hprod :
      (routingA B e : ℤ) *
          ((physicalHeight B e r : ℤ) + branchBPrefixAmbientU R r) =
        (routingA B e : ℤ) *
          (physicalHeight B e (r + routingB B e) + (routingData B e).u r) := by
    linear_combination hfinal - hl0 + hl1 - hambient
  have hcast :
      (physicalHeight B e r : ℤ) + branchBPrefixAmbientU R r =
        physicalHeight B e (r + routingB B e) + (routingData B e).u r :=
    mul_left_cancel₀ (ne_of_gt ha) hprod
  exact_mod_cast hcast

private theorem branchB_final_height_step_c_with_ambient_carry
    (R : SectorBCriticalRoleBranchB P)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    physicalHeight P.M.base e r + branchBPrefixAmbientV R r =
      physicalHeight P.M.base e (r + routingC P.M.base e) +
        (routingData P.M.base e).v r := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hl0 := physicalHeight_spec B e r
  have hl1 := physicalHeight_spec B e (r + routingC B e)
  have hfinal := (routingI B e).apery_step_eq (routingA B e)
    (routingC B e) (routingHC B e) r
  have hambient := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) r
  change (routingI B e).aperyRepresentative (routingA B e) r =
    branchBPrefixAlpha R r + (routingA B e : ℤ) * physicalHeight B e r at hl0
  change (routingI B e).aperyRepresentative (routingA B e)
      (r + routingC B e) =
    branchBPrefixAlpha R (r + routingC B e) +
      (routingA B e : ℤ) * physicalHeight B e (r + routingC B e) at hl1
  change branchBPrefixAlpha R r + routingC B e =
    branchBPrefixAlpha R (r + routingC B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientV R r at hambient
  change (routingI B e).aperyRepresentative (routingA B e) r + routingC B e =
    (routingI B e).aperyRepresentative (routingA B e) (r + routingC B e) +
      (routingA B e : ℤ) * (routingData B e).v r at hfinal
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hprod :
      (routingA B e : ℤ) *
          ((physicalHeight B e r : ℤ) + branchBPrefixAmbientV R r) =
        (routingA B e : ℤ) *
          (physicalHeight B e (r + routingC B e) + (routingData B e).v r) := by
    linear_combination hfinal - hl0 + hl1 - hambient
  have hcast :
      (physicalHeight B e r : ℤ) + branchBPrefixAmbientV R r =
        physicalHeight B e (r + routingC B e) + (routingData B e).v r :=
    mul_left_cancel₀ (ne_of_gt ha) hprod
  exact_mod_cast hcast

private theorem branchB_finalHeight_le_prefixHeight
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    physicalHeight P.M.base e r ≤ branchBPrefixHeight R x hsx r := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Iminus := branchBActualPrefixIdeal R x hsx
  have hpref : Iminus.aperyRepresentative (routingA B e) r ∈ Iminus :=
    Iminus.aperyRepresentative_mem (routingA B e) r
  have hprefFinal := branchB_prefix_mem_final R x hsx hpref
  have hle := (routingI B e).aperyRepresentative_le (routingA B e) r
    hprefFinal (Iminus.aperyRepresentative_mod (routingA B e) r)
  have hfinal := physicalHeight_spec B e r
  have hprefix := branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx r
  change (routingI B e).aperyRepresentative (routingA B e) r =
    branchBPrefixAlpha R r + (routingA B e : ℤ) * physicalHeight B e r at hfinal
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  rw [hfinal, hprefix] at hle
  have hcast : (physicalHeight B e r : ℤ) ≤ branchBPrefixHeight R x hsx r := by
    nlinarith
  exact_mod_cast hcast

/-- The selected nonprincipal return evaluated at the B/C corners of the U
diamond.  This packet keeps the selected return separate from the actual
source: it only exports the prefix/final envelope inequalities it really
implies. -/
theorem branchB_high_seam_target_U_selected_BC_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let e := branchBInactiveReindex R
    let Bc := gridResidue P.M.base e (r31 R - S.depth) (c2 R - 1)
    let Cc := gridResidue P.M.base e (c1 R - S.depth - 1) 0
    branchBPrefixHeight R x hsx Bc = 0 ∧
      eta P.M.base e (r31 R - S.depth) (c2 R - 1) = 0 ∧
      eta P.M.base e (c1 R - S.depth - 1) 0 ≤
        S.coordinate.j.toNat := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let Bc := gridResidue B e (r31 R - S.depth) (c2 R - 1)
  let Cc := gridResidue B e (c1 R - S.depth - 1) 0
  let j := S.coordinate.j.toNat
  change S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R at haxis
  have hj0 : (0 : ℤ) ≤ S.coordinate.j := by omega
  have hj : S.coordinate.j = (j : ℤ) := (Int.toNat_of_nonneg hj0).symm
  have hjlt : j < c3 R := by
    have hs := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    rw [hj] at haxis
    exact_mod_cast (show (j : ℤ) < c3 R by omega)
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hdpos : 0 < S.depth := S.depth_pos
  let D := branchB_inactive_coherentHerzogData R
  have hBdomain : L5A2C4OR5.HerzogLShapeDomain D
      (r31 R - S.depth) (c2 R - 1) := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change r31 R - S.depth < L5A2C4A.c2 B e ∧
      c2 R - 1 < L5A2C4A.c3 B e ∧
        (r31 R - S.depth < L5A2C4D.cr12 D ∨
          c2 R - 1 < L5A2C4D.cr13 D)
    dsimp only [B, e]
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
    have hmap := branchB_inactive_coherent_coefficients R
    dsimp only [D, B, e] at hmap
    obtain ⟨h12, h13, h21, h23, h31, h32⟩ := hmap
    rw [h12, h13]
    have hsum1 : c1 R = r21 R + r31 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
    have hsum2 : c2 R = r12 R + r32 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    have hr31 : 0 < r31 R := by
      simpa using
        (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
    have hr21 : 0 < r21 R := by
      simpa using
        (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
    have hr12 : 0 < r12 R := by
      simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
    have hc2pos : 0 < c2 R := by omega
    have hsub_lt : r31 R - S.depth < r31 R :=
      Nat.sub_lt hr31 hdpos
    exact ⟨by omega, by omega, Or.inl hsub_lt⟩
  have hCdomain : L5A2C4OR5.HerzogLShapeDomain D
      (c1 R - S.depth - 1) 0 := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change c1 R - S.depth - 1 < L5A2C4A.c2 B e ∧
      0 < L5A2C4A.c3 B e ∧
        (c1 R - S.depth - 1 < L5A2C4D.cr12 D ∨
          0 < L5A2C4D.cr13 D)
    dsimp only [B, e]
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
    have hmap := branchB_inactive_coherent_coefficients R
    dsimp only [D, B, e] at hmap
    obtain ⟨h12, h13, h21, h23, h31, h32⟩ := hmap
    rw [h12, h13]
    have hsum1 : c1 R = r21 R + r31 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
    have hsum2 : c2 R = r12 R + r32 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    have hr31 : 0 < r31 R := by
      simpa using
        (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
    have hr32 : 0 < r32 R := by
      simpa using
        (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
    have hr12 : 0 < r12 R := by
      simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
    omega
  have hBcanon := herzogLShapeCanonicality B e D _ _ hBdomain
  have hCcanon := herzogLShapeCanonicality B e D _ _ hCdomain
  have hAeq : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hBeq : routingB B e = normalizedA R := by
    simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hCeq : routingC B e = normalizedB R := by
    simpa [B, e] using branchB_inactive_routingC_eq_normalizedB R
  have haH : routingA B e ∈ routingH B e :=
    (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
        (AddSubmonoid.subset_closure (by simp))
  have hgen (a b c : ℕ) :
      a * routingA B e + b * routingB B e + c * routingC B e ∈
        routingH B e := by
    have ha := (routingH B e).toAddSubmonoid.nsmul_mem haH a
    have hb := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e) b
    have hc := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e) c
    simpa [nsmul_eq_mul, Nat.add_assoc] using
      (routingH B e).add_mem ((routingH B e).add_mem ha hb) hc
  have hBmem : (normalizedGrid B e 0 (r31 R - S.depth) (c2 R - 1) : ℤ) ∈
      branchBActualPrefixIdeal R x hsx := by
    change ∃ ell : ℕ, 0 < ell ∧ ell < actualPrincipalIndex B ∧
      (normalizedGrid B e 0 (r31 R - S.depth) (c2 R - 1) : ℤ) ∈
        returnIdeal (routingH B e) (ell * normalizedM B)
    refine ⟨S.ell, S.ell_pos, S.ell_lt_principal, ?_⟩
    rw [mem_returnIdeal_iff]
    constructor
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨normalizedGrid B e 0 (r31 R - S.depth) (c2 R - 1), ?_, rfl⟩
      simpa [normalizedGrid] using hgen 0 (r31 R - S.depth) (c2 R - 1)
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      let tail := (c3 R - j) * normalizedC R +
        (r12 R - 1) * normalizedB R
      refine ⟨tail, ?_, ?_⟩
      · simpa [tail, hAeq, hBeq, hCeq, Nat.add_assoc] using
          hgen (c3 R - j) 0 (r12 R - 1)
      · have hn : S.n = S.ell * normalizedM B := S.n_eq
        have hanchor : S.n + normalizedA R * S.depth =
            j * normalizedC R := by
          exact_mod_cast (show (S.n : ℤ) + normalizedA R * S.depth =
            (j : ℤ) * normalizedC R by simpa [hj] using haxis.2.2.2.2)
        have hrel : c3 R * normalizedC R =
            r31 R * normalizedA R + r32 R * normalizedB R := by
          simpa using (branchB_actual_herzog_coordinates R).normalized_relations.2.2
        have hsum : c2 R = r12 R + r32 R := by
          simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
        have hr12 : 0 < r12 R := by
          simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
        have hcalc : normalizedGrid B e 0 (r31 R - S.depth) (c2 R - 1) =
            S.n + tail := by
          dsimp [normalizedGrid, tail]
          rw [hAeq, hBeq, hCeq]
          have hc3split : c3 R = j + (c3 R - j) := by omega
          have hc2split : c2 R - 1 = (r12 R - 1) + r32 R := by omega
          have hr31split : r31 R = S.depth + (r31 R - S.depth) := by omega
          have hc3mul : c3 R * normalizedC R =
              j * normalizedC R + (c3 R - j) * normalizedC R := by
            calc
              c3 R * normalizedC R =
                  (j + (c3 R - j)) * normalizedC R :=
                congrArg (fun t => t * normalizedC R) hc3split
              _ = j * normalizedC R +
                  (c3 R - j) * normalizedC R := Nat.add_mul ..
          have hc2mul : (c2 R - 1) * normalizedB R =
              (r12 R - 1) * normalizedB R +
                r32 R * normalizedB R := by
            calc
              (c2 R - 1) * normalizedB R =
                  ((r12 R - 1) + r32 R) * normalizedB R :=
                congrArg (fun t => t * normalizedB R) hc2split
              _ = (r12 R - 1) * normalizedB R +
                  r32 R * normalizedB R := Nat.add_mul ..
          have hr31mul : r31 R * normalizedA R =
              S.depth * normalizedA R +
                (r31 R - S.depth) * normalizedA R := by
            calc
              r31 R * normalizedA R =
                  (S.depth + (r31 R - S.depth)) * normalizedA R :=
                congrArg (fun t => t * normalizedA R) hr31split
              _ = S.depth * normalizedA R +
                  (r31 R - S.depth) * normalizedA R := Nat.add_mul ..
          have hanchor' : S.n + S.depth * normalizedA R =
              j * normalizedC R := by
            simpa [Nat.mul_comm] using hanchor
          omega
        rw [hcalc, hn]
        push_cast
        ring
  have hCmem : (normalizedGrid B e j (c1 R - S.depth - 1) 0 : ℤ) ∈
      branchBActualPrefixIdeal R x hsx := by
    change ∃ ell : ℕ, 0 < ell ∧ ell < actualPrincipalIndex B ∧
      (normalizedGrid B e j (c1 R - S.depth - 1) 0 : ℤ) ∈
        returnIdeal (routingH B e) (ell * normalizedM B)
    refine ⟨S.ell, S.ell_pos, S.ell_lt_principal, ?_⟩
    rw [mem_returnIdeal_iff]
    constructor
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨normalizedGrid B e j (c1 R - S.depth - 1) 0, ?_, rfl⟩
      simpa [normalizedGrid] using hgen j (c1 R - S.depth - 1) 0
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨(c1 R - 1) * normalizedA R, ?_, ?_⟩
      · simpa [hAeq, hBeq, hCeq, Nat.add_assoc] using
          hgen 0 (c1 R - 1) 0
      · have hn : S.n = S.ell * normalizedM B := S.n_eq
        have hanchor : S.n + normalizedA R * S.depth =
            j * normalizedC R := by
          exact_mod_cast (show (S.n : ℤ) + normalizedA R * S.depth =
            (j : ℤ) * normalizedC R by simpa [hj] using haxis.2.2.2.2)
        have hcalc : normalizedGrid B e j (c1 R - S.depth - 1) 0 =
            S.n + (c1 R - 1) * normalizedA R := by
          dsimp [normalizedGrid]
          rw [hAeq, hBeq, hCeq]
          have hsum1 : c1 R = r21 R + r31 R := by
            simpa using
              (branchB_actual_herzog_coordinates R).coefficient_sums.1
          have hc1split : c1 R - 1 =
              S.depth + (c1 R - S.depth - 1) := by omega
          have hc1mul : (c1 R - 1) * normalizedA R =
              S.depth * normalizedA R +
                (c1 R - S.depth - 1) * normalizedA R := by
            calc
              (c1 R - 1) * normalizedA R =
                  (S.depth + (c1 R - S.depth - 1)) * normalizedA R :=
                congrArg (fun t => t * normalizedA R) hc1split
              _ = S.depth * normalizedA R +
                  (c1 R - S.depth - 1) * normalizedA R := Nat.add_mul ..
          have hanchor' : S.n + S.depth * normalizedA R =
              j * normalizedC R := by
            simpa [Nat.mul_comm] using hanchor
          omega
        rw [hcalc, hn]
        push_cast
        ring
  have hPrefixB := branchB_prefixHeight_le_of_canonical_mem
    R x hsx (r31 R - S.depth) (c2 R - 1) 0 hBcanon hBmem
  have hFinalBmem := branchB_prefix_mem_final R x hsx hBmem
  have hFinalCmem := branchB_prefix_mem_final R x hsx hCmem
  have hFinalB := (normalizedGrid_mem_iff_eta_le B e 0
    (r31 R - S.depth) (c2 R - 1)).1 hFinalBmem
  have hFinalC := (normalizedGrid_mem_iff_eta_le B e j
    (c1 R - S.depth - 1) 0).1 hFinalCmem
  exact ⟨Nat.eq_zero_of_le_zero hPrefixB, Nat.eq_zero_of_le_zero hFinalB,
    hFinalC⟩

/-! ### B55: exact U-diamond heights and the principal zero -/

private theorem branchB_high_seam_target_U_canonical_and_carries
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Ac := gridResidue P.M.base e (r31 R - S.depth - 1) (c2 R - 1)
    let Bc := gridResidue P.M.base e (r31 R - S.depth) (c2 R - 1)
    let Cc := gridResidue P.M.base e (c1 R - S.depth - 1) 0
    IsCanonicalTailGridPoint P.M.base e
        (r31 R - S.depth - 1) (c2 R - 1) ∧
      IsCanonicalTailGridPoint P.M.base e
        (r31 R - S.depth) (c2 R - 1) ∧
      IsCanonicalTailGridPoint P.M.base e
        (c1 R - S.depth - 1) 0 ∧
      branchBPrefixAmbientU R Ac = 0 ∧
      branchBPrefixAmbientV R Ac = r23 R ∧
      Ac + routingB P.M.base e = Bc ∧
      Ac + routingC P.M.base e = Cc := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Ac := gridResidue B e (r31 R - S.depth - 1) (c2 R - 1)
  let Bc := gridResidue B e (r31 R - S.depth) (c2 R - 1)
  let Cc := gridResidue B e (c1 R - S.depth - 1) 0
  let D := branchB_inactive_coherentHerzogData R
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hdpos : 0 < S.depth := S.depth_pos
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hr31 : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr21 : 0 < r21 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hr32 : 0 < r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hdomain (i j : ℕ)
      (hi : i < r31 R) (hj : j < c2 R) :
      L5A2C4OR5.HerzogLShapeDomain D i j := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change i < L5A2C4A.c2 B e ∧ j < L5A2C4A.c3 B e ∧
      (i < L5A2C4D.cr12 D ∨ j < L5A2C4D.cr13 D)
    dsimp only [B, e]
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
    have hmap := branchB_inactive_coherent_coefficients R
    dsimp only [D, B, e] at hmap
    obtain ⟨h12, h13, _h21, _h23, _h31, _h32⟩ := hmap
    rw [h12, h13]
    exact ⟨by omega, hj, Or.inl hi⟩
  have hAi : r31 R - S.depth - 1 < r31 R := by omega
  have hBi : r31 R - S.depth < r31 R := Nat.sub_lt hr31 hdpos
  have hBj : c2 R - 1 < c2 R := by omega
  have hAcanon := herzogLShapeCanonicality B e D _ _ (hdomain _ _ hAi hBj)
  have hBcanon := herzogLShapeCanonicality B e D _ _ (hdomain _ _ hBi hBj)
  have hCdomain : L5A2C4OR5.HerzogLShapeDomain D
      (c1 R - S.depth - 1) 0 := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change c1 R - S.depth - 1 < L5A2C4A.c2 B e ∧
      0 < L5A2C4A.c3 B e ∧
      (c1 R - S.depth - 1 < L5A2C4D.cr12 D ∨
        0 < L5A2C4D.cr13 D)
    dsimp only [B, e]
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
    have hmap := branchB_inactive_coherent_coefficients R
    dsimp only [D, B, e] at hmap
    obtain ⟨h12, h13, _h21, _h23, _h31, _h32⟩ := hmap
    rw [h12, h13]
    exact ⟨by omega, by omega, Or.inr (by omega)⟩
  have hCcanon := herzogLShapeCanonicality B e D _ _ hCdomain
  have hcoord : r31 R - S.depth - 1 + 1 = r31 R - S.depth := by omega
  have hAB : Ac + routingB B e = Bc := by
    simpa [Ac, Bc, hcoord] using
      (gridResidue_add_b B e (r31 R - S.depth - 1) (c2 R - 1)).symm
  have hdiamond := branchB_actualZeroEdgeBirth_high_seam_target_U_inverse_diamond
    R hB x hsx hbirth haxis hU
  have hbase : x.val.val.val = Ac := by
    simpa [S, B, e, Ac] using hdiamond.1
  have hAC : Ac + routingC B e = Cc := by
    change (routingData B e).c Ac = Cc
    calc
      (routingData B e).c Ac = (routingData B e).c x.val.val.val := by rw [hbase]
      _ = Cc := by simpa [S, B, e, Cc] using hdiamond.2.2.1
  have halpha (i j : ℕ) (hcanon : IsCanonicalTailGridPoint B e i j) :
      branchBPrefixAlpha R (gridResidue B e i j) = normalizedGrid B e 0 i j := by
    have hlift :=
      (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e i j).mp hcanon
    have hgrid := normalizedGrid_eq_physicalAlpha_add B e 0 i j
    rw [hlift] at hgrid
    simp only [zero_add, Nat.cast_zero, mul_zero] at hgrid
    simpa [branchBPrefixAlpha, physicalAlpha, B, e] using hgrid.symm
  have hambU := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e) Ac
  change branchBPrefixAlpha R Ac + routingB B e =
    branchBPrefixAlpha R (Ac + routingB B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientU R Ac at hambU
  rw [hAB, halpha _ _ hAcanon, halpha _ _ hBcanon] at hambU
  have hUcarry : branchBPrefixAmbientU R Ac = 0 := by
    have hambUNat :
        normalizedGrid B e 0 (r31 R - S.depth - 1) (c2 R - 1) +
            routingB B e =
          normalizedGrid B e 0 (r31 R - S.depth) (c2 R - 1) +
            routingA B e * branchBPrefixAmbientU R Ac := by
      exact_mod_cast hambU
    dsimp [normalizedGrid] at hambUNat
    have hbaseeq :
        (r31 R - S.depth - 1) * routingB B e + routingB B e =
          (r31 R - S.depth) * routingB B e := by
      calc
        _ = (r31 R - S.depth - 1 + 1) * routingB B e := by ring
        _ = _ := by rw [hcoord]
    have hprod : routingA B e * branchBPrefixAmbientU R Ac = 0 := by
      omega
    exact (Nat.mul_eq_zero.mp hprod).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  have hambV := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) Ac
  change branchBPrefixAlpha R Ac + routingC B e =
    branchBPrefixAlpha R (Ac + routingC B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientV R Ac at hambV
  rw [hAC, halpha _ _ hAcanon, halpha _ _ hCcanon] at hambV
  have hAeq : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hBeq : routingB B e = normalizedA R := by
    simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hCeq : routingC B e = normalizedB R := by
    simpa [B, e] using branchB_inactive_routingC_eq_normalizedB R
  have hrel : c2 R * normalizedB R =
      r21 R * normalizedA R + r23 R * normalizedC R := by
    simpa using (branchB_actual_herzog_coordinates R).normalized_relations.2.1
  have hVcarry : branchBPrefixAmbientV R Ac = r23 R := by
    have hambVNat :
        normalizedGrid B e 0 (r31 R - S.depth - 1) (c2 R - 1) +
            routingC B e =
          normalizedGrid B e 0 (c1 R - S.depth - 1) 0 +
            routingA B e * branchBPrefixAmbientV R Ac := by
      exact_mod_cast hambV
    dsimp [normalizedGrid] at hambVNat
    rw [hAeq, hBeq, hCeq] at hambVNat
    have hraw :
        (r31 R - S.depth - 1) * normalizedA R +
            (c2 R - 1) * normalizedB R + normalizedB R =
          (c1 R - S.depth - 1) * normalizedA R +
            normalizedC R * r23 R := by
      have hc2pred :
          (c2 R - 1) * normalizedB R + normalizedB R =
            c2 R * normalizedB R := by
        calc
          _ = (c2 R - 1 + 1) * normalizedB R := by ring
          _ = _ := by congr 1; omega
      have hci : c1 R - S.depth - 1 =
          r21 R + (r31 R - S.depth - 1) := by omega
      calc
        _ = (r31 R - S.depth - 1) * normalizedA R +
              c2 R * normalizedB R := by rw [Nat.add_assoc, hc2pred]
        _ = (r31 R - S.depth - 1) * normalizedA R +
              (r21 R * normalizedA R + r23 R * normalizedC R) := by rw [hrel]
        _ = (r21 R + (r31 R - S.depth - 1)) * normalizedA R +
              normalizedC R * r23 R := by ring
        _ = _ := by rw [← hci]
    have ha : 0 < normalizedC R := by
      rw [← hAeq]
      exact routingA_pos B e
    have hprod : normalizedC R * branchBPrefixAmbientV R Ac =
        normalizedC R * r23 R := by omega
    exact Nat.eq_of_mul_eq_mul_left ha hprod
  exact ⟨hAcanon, hBcanon, hCcanon, hUcarry, hVcarry, hAB, hAC⟩

/-- B55 final U-diamond height packet.  The source authority denotes the
`A -> C` ambient carry by `w`; under the frozen inactive reindexing this is
`r23`, as recorded by `branchB_inactive_coherent_coefficients`. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_U_final_height_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let e := branchBInactiveReindex R
    eta P.M.base e (r31 R - S.depth - 1) (c2 R - 1) = 0 ∧
      eta P.M.base e (r31 R - S.depth) (c2 R - 1) = 0 ∧
      eta P.M.base e (c1 R - S.depth - 1) 0 = r23 R ∧
      r23 R ≤ S.coordinate.j.toNat := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Ac := gridResidue B e (r31 R - S.depth - 1) (c2 R - 1)
  let Bc := gridResidue B e (r31 R - S.depth) (c2 R - 1)
  let Cc := gridResidue B e (c1 R - S.depth - 1) 0
  have hpacket := branchB_high_seam_target_U_canonical_and_carries
    R hB x hsx hbirth haxis hU
  rcases hpacket with ⟨hAcanon, hBcanon, hCcanon, hUcarry, hVcarry,
    hAB, hAC⟩
  have hselected := branchB_high_seam_target_U_selected_BC_packet
    R hB x hsx hbirth haxis
  change branchBPrefixHeight R x hsx Bc = 0 ∧
      eta B e (r31 R - S.depth) (c2 R - 1) = 0 ∧
      eta B e (c1 R - S.depth - 1) 0 ≤ S.coordinate.j.toNat at hselected
  have hdiamond := branchB_actualZeroEdgeBirth_high_seam_target_U_inverse_diamond
    R hB x hsx hbirth haxis hU
  have hbase : x.val.val.val = Ac := by
    simpa [S, B, e, Ac] using hdiamond.1
  have hbranch : (routingData B e).IsBranch Ac := by
    rw [← hbase]
    exact hbirth.2.2.2.2.2.1
  have hAheight : physicalHeight B e Ac = 0 := by
    have hstep := branchB_final_height_step_b_with_ambient_carry R Ac
    change physicalHeight B e Ac + branchBPrefixAmbientU R Ac =
      physicalHeight B e (Ac + routingB B e) + (routingData B e).u Ac at hstep
    rw [hUcarry, hAB, hbranch.1] at hstep
    have hBheight := eta_eq_physicalHeight_of_isCanonical B e _ _ hBcanon
    change eta B e (r31 R - S.depth) (c2 R - 1) =
      physicalHeight B e Bc at hBheight
    have hBzero : eta B e (r31 R - S.depth) (c2 R - 1) = 0 := by
      exact hselected.2.1
    have hBheight0 : physicalHeight B e Bc = 0 := by
      rw [← hBheight]
      exact hBzero
    rw [hBheight0] at hstep
    omega
  have hCheight : physicalHeight B e Cc = r23 R := by
    have hstep := branchB_final_height_step_c_with_ambient_carry R Ac
    change physicalHeight B e Ac + branchBPrefixAmbientV R Ac =
      physicalHeight B e (Ac + routingC B e) + (routingData B e).v Ac at hstep
    rw [hAheight, hVcarry, hAC, hbranch.2] at hstep
    change physicalHeight B e
      (gridResidue B e (c1 R - S.depth - 1) 0) = r23 R
    simpa [Cc] using hstep.symm
  have hAeta := eta_eq_physicalHeight_of_isCanonical B e _ _ hAcanon
  have hCeta := eta_eq_physicalHeight_of_isCanonical B e _ _ hCcanon
  change eta B e (r31 R - S.depth - 1) (c2 R - 1) =
    physicalHeight B e Ac at hAeta
  have hCeta' : eta B e (c1 R - S.depth - 1) 0 = physicalHeight B e Cc := by
    simpa [Cc] using hCeta
  have hBzero : eta B e (r31 R - S.depth) (c2 R - 1) = 0 := by
    exact hselected.2.1
  have hAle : eta B e (c1 R - S.depth - 1) 0 ≤ S.coordinate.j.toNat := by
    exact hselected.2.2
  have hCvalue : eta B e (c1 R - S.depth - 1) 0 = r23 R :=
    hCeta'.trans hCheight
  have hr23le : r23 R ≤ S.coordinate.j.toNat := by
    rw [← hCvalue]
    exact hAle
  exact ⟨hAeta.trans hAheight, hBzero,
    hCvalue, hr23le⟩

/-- B55 prefix positivity at the actual U-diamond base.  Prefix and final
routing are compared only via the inclusion of their return ideals. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_U_prefix_A_pos
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let e := branchBInactiveReindex R
    let Ac := gridResidue P.M.base e (r31 R - S.depth - 1) (c2 R - 1)
    0 < branchBPrefixHeight R x hsx Ac := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Ac := gridResidue B e (r31 R - S.depth - 1) (c2 R - 1)
  let Bc := gridResidue B e (r31 R - S.depth) (c2 R - 1)
  let Cc := gridResidue B e (c1 R - S.depth - 1) 0
  let Gminus := branchBActualPrefixRoutingData R x hsx
  have hgeom := branchB_high_seam_target_U_canonical_and_carries
    R hB x hsx hbirth haxis hU
  rcases hgeom with ⟨hAcanon, hBcanon, hCcanon, hUcarry, hVcarry,
    hAB, hAC⟩
  have hselected := branchB_high_seam_target_U_selected_BC_packet
    R hB x hsx hbirth haxis
  change branchBPrefixHeight R x hsx Bc = 0 ∧
      eta B e (r31 R - S.depth) (c2 R - 1) = 0 ∧
      eta B e (c1 R - S.depth - 1) 0 ≤ S.coordinate.j.toNat at hselected
  have hfinal := branchB_actualZeroEdgeBirth_high_seam_target_U_final_height_packet
    R hB x hsx hbirth haxis hU
  change eta B e (r31 R - S.depth - 1) (c2 R - 1) = 0 ∧
      eta B e (r31 R - S.depth) (c2 R - 1) = 0 ∧
      eta B e (c1 R - S.depth - 1) 0 = r23 R ∧
      r23 R ≤ S.coordinate.j.toNat at hfinal
  have hCphysical := eta_eq_physicalHeight_of_isCanonical B e _ _ hCcanon
  have hCphysical' : physicalHeight B e Cc = r23 R := by
    have : eta B e (c1 R - S.depth - 1) 0 = physicalHeight B e Cc := by
      simpa [Cc] using hCphysical
    omega
  have hCle := branchB_finalHeight_le_prefixHeight R x hsx Cc
  have hPrefixC : r23 R ≤ branchBPrefixHeight R x hsx Cc := by
    rw [← hCphysical']
    exact hCle
  by_contra hnot
  have hPrefixA : branchBPrefixHeight R x hsx Ac = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hb := branchB_prefix_height_step_b_with_ambient_carry R x hsx Ac
  change branchBPrefixHeight R x hsx Ac + branchBPrefixAmbientU R Ac =
    branchBPrefixHeight R x hsx (Ac + routingB B e) + Gminus.u Ac at hb
  rw [hPrefixA, hUcarry, hAB, hselected.1] at hb
  have hu0 : Gminus.u Ac = 0 := by omega
  have hc := branchB_prefix_height_step_c_with_ambient_carry R x hsx Ac
  change branchBPrefixHeight R x hsx Ac + branchBPrefixAmbientV R Ac =
    branchBPrefixHeight R x hsx (Ac + routingC B e) + Gminus.v Ac at hc
  rw [hPrefixA, hVcarry, hAC] at hc
  have hc' : r23 R = branchBPrefixHeight R x hsx Cc + Gminus.v Ac := by
    simpa [S, B, e, Cc] using hc
  have hv0 : Gminus.v Ac = 0 := by omega
  have hdiamond := branchB_actualZeroEdgeBirth_high_seam_target_U_inverse_diamond
    R hB x hsx hbirth haxis hU
  have hbase : x.val.val.val = Ac := by
    simpa [S, B, e, Ac] using hdiamond.1
  apply hbirth.2.2.2.1
  rw [hbase]
  exact ⟨hu0, hv0⟩

private theorem branchB_prefix_candidate_pos_of_prefixHeight_pos
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R)))
    (hheight : 0 < branchBPrefixHeight R x hsx r)
    {q : ℕ} (hq : 0 < q) (hqlt : q < actualPrincipalIndex P.M.base) :
    0 < rawCandidate P.M.base (branchBInactiveReindex R) q r := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let H := routingH B e
  let Iminus := branchBActualPrefixIdeal R x hsx
  by_contra hnot
  have hcand : rawCandidate B e q r ≤ 0 := le_of_not_gt hnot
  have hsub := (rawCandidate_threshold B e r hq 0).2 hcand
  have hsub' : physicalAlpha B e r - q * routingM B e ∈ H.asRelativeIdeal := by
    simpa [H] using hsub
  have halphaH : physicalAlpha B e r ∈ H.asRelativeIdeal :=
    H.asRelativeIdeal.aperyRepresentative_mem (routingA B e) r
  have hreturn : physicalAlpha B e r ∈ returnIdeal H (q * routingM B e) := by
    rw [mem_returnIdeal_iff]
    exact ⟨halphaH, hsub'⟩
  have hpref : physicalAlpha B e r ∈ Iminus := by
    change ∃ ell : ℕ, 0 < ell ∧ ell < actualPrincipalIndex B ∧
      physicalAlpha B e r ∈ returnIdeal H (ell * normalizedM B)
    refine ⟨q, hq, hqlt, ?_⟩
    simpa [routingM, normalizedM, B, e] using hreturn
  have hle := Iminus.aperyRepresentative_le (routingA B e) r hpref (by
    change ((physicalAlpha B e r : ℤ) : ZMod (routingA B e)) = r
    exact H.asRelativeIdeal.aperyRepresentative_mod (routingA B e) r)
  have hambient := branchB_prefix_alpha_le R x hsx r
  have heq : Iminus.aperyRepresentative (routingA B e) r =
      branchBPrefixAlpha R r := le_antisymm hle hambient
  have hdict := branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx r
  change Iminus.aperyRepresentative (routingA B e) r =
    branchBPrefixAlpha R r +
      (routingA B e : ℤ) * branchBPrefixHeight R x hsx r at hdict
  rw [heq] at hdict
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hzero : branchBPrefixHeight R x hsx r = 0 := by
    have : (routingA B e : ℤ) * branchBPrefixHeight R x hsx r = 0 := by
      linarith
    exact_mod_cast (mul_eq_zero.mp this |>.resolve_left (ne_of_gt ha))
  exact (Nat.ne_of_gt hheight) hzero

/-- B55 event-specific principal incidence at the U-diamond base.  This is
proved by excluding every strict-prefix minimizer and then using the generic
principal-candidate nonnegativity theorem; branch-birth itself is never used
as a principal-incidence premise. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_U_principal_base_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let e := branchBInactiveReindex R
    let Ac := gridResidue P.M.base e (r31 R - S.depth - 1) (c2 R - 1)
    rawCandidate P.M.base e (actualPrincipalIndex P.M.base) Ac = 0 := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Ac := gridResidue B e (r31 R - S.depth - 1) (c2 R - 1)
  have hprefix : 0 < branchBPrefixHeight R x hsx Ac :=
    branchB_actualZeroEdgeBirth_high_seam_target_U_prefix_A_pos
      R hB x hsx hbirth haxis hU
  have hfinal := branchB_actualZeroEdgeBirth_high_seam_target_U_final_height_packet
    R hB x hsx hbirth haxis hU
  change eta B e (r31 R - S.depth - 1) (c2 R - 1) = 0 ∧
      eta B e (r31 R - S.depth) (c2 R - 1) = 0 ∧
      eta B e (c1 R - S.depth - 1) 0 = r23 R ∧
      r23 R ≤ S.coordinate.j.toNat at hfinal
  have hgeom := branchB_high_seam_target_U_canonical_and_carries
    R hB x hsx hbirth haxis hU
  have hAphysical := eta_eq_physicalHeight_of_isCanonical B e _ _ hgeom.1
  change eta B e (r31 R - S.depth - 1) (c2 R - 1) =
    physicalHeight B e Ac at hAphysical
  have hheight0 : physicalHeight B e Ac = 0 := by omega
  have hheightMin := physicalHeight_eq_max_rawMinimum B e Ac
  have hmin : rawMinimum B e Ac ≤ 0 := by
    rw [hheight0] at hheightMin
    omega
  let k := currentSelector B e Ac
  have hkpos : 0 < k := currentSelector_pos B e Ac
  have hkvalue : rawCandidate B e k Ac ≤ 0 := by
    rw [rawCandidate_currentSelector B e Ac]
    exact hmin
  obtain ⟨j, hjpos, hjle, hjvalue⟩ :=
    branchB_candidate_reduce_to_first_principal_block R Ac hkpos
  have hjnonpos : rawCandidate B e j Ac ≤ 0 := hjvalue.trans hkvalue
  have hjeq : j = actualPrincipalIndex B := by
    by_contra hne
    have hjlt : j < actualPrincipalIndex B := Nat.lt_of_le_of_ne hjle hne
    have hjstrict := branchB_prefix_candidate_pos_of_prefixHeight_pos
      R x hsx Ac hprefix hjpos hjlt
    have hjstrict' : 0 < rawCandidate B e j Ac := by
      simpa [B, e] using hjstrict
    exact (not_lt_of_ge hjnonpos) hjstrict'
  have hle : rawCandidate B e (actualPrincipalIndex B) Ac ≤ 0 := by
    simpa [hjeq] using hjnonpos
  have hge := branchB_principal_rawCandidate_nonnegative R Ac
  exact le_antisymm hle hge

/-! ### B56: principal transport and the complementary active-pure cell -/

/-- The pure inward predecessor of the first actual critical relation is not
boundary-killed.  This is the first-coordinate dual of the already exported
second-pure exclusion, proved directly from the actual Sector-B fibres. -/
theorem branchB_first_pure_boundary_exclusion
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :
    R.firstDegree - weights P.M.base (R.reindex 0) ∉ P.M.base.K := by
  classical
  obtain ⟨h, g, _hne, hdegrees, _hhcount, _hgcount, _hhzero, _hgzero,
    hhgenuine, hggenuine⟩ := L5A2B3.sectorB_actualFiberData P hB
  have hgenuine (d : ℕ) (hd : d ∈ positiveDegrees P.M)
      (C : FiberComponent P.M.base d) : ¬BoundaryKilled P.M d C := by
    rw [hdegrees] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact hhgenuine C
    · exact hggenuine C
  have hfirst : R.firstDegree ∈ positiveDegrees P.M := by
    rw [R.positiveDegrees_eq]
    simp
  intro hmem
  apply hgenuine R.firstDegree hfirst R.first.pureComponent
  obtain ⟨pureWitness, hpureComponent, hpurePos⟩ :=
    (mem_componentSupport P.M.base R.firstDegree R.first.pureComponent
      (R.reindex 0)).mp (by rw [R.reindex_zero, R.first.pureSupport]; simp)
  exact ⟨pureWitness, hpureComponent, R.reindex 0, hpurePos, hmem⟩

/-- The complementary active-pure cell used by B56 is live in the inactive
chart.  Under the frozen cyclic reindex this is authority's
`X2 = (c2_local-1,0)`, hence the current coordinate `(c1-1,0)`. -/
theorem branchB_inactive_first_pure_height_pos
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :
    0 < eta P.M.base (branchBInactiveReindex R) (c1 R - 1) 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  by_contra hnot
  have heta : eta B e (c1 R - 1) 0 = 0 := Nat.eq_zero_of_not_pos hnot
  have hK : gridDegree B e 0 (c1 R - 1) 0 ∈ B.K :=
    (eta_eq_zero_iff B e (c1 R - 1) 0).mp heta
  apply branchB_first_pure_boundary_exclusion R hB
  have hc1pos : 0 < c1 R := by
    have hp := (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
    have hz := (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.1
    omega
  have hdegree : R.firstDegree = c1 R * weights B (R.reindex 0) := by
    simpa [B, c1, R.reindex_zero] using R.first.degree_eq_critical
  rw [hdegree]
  change c1 R * weights B (R.reindex 0) - weights B (R.reindex 0) ∈ B.K
  have hsplit : c1 R = 1 + (c1 R - 1) := by omega
  rw [hsplit, Nat.add_mul]
  simpa [e, gridDegree, branchBInactiveReindex_one, Nat.add_assoc] using hK

/-- Exact ambient Apéry top-wrap on the actual U diamond.  In the inactive
chart the step from `A` to `C` is the routing-`c` step and its carry is the
source-exact coefficient `r23`. -/
private theorem branchB_high_seam_target_U_top_wrap_apery
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let Ac := gridResidue B e (r31 R - S.depth - 1) (c2 R - 1)
    let Cc := gridResidue B e (c1 R - S.depth - 1) 0
    physicalAlpha B e Ac + routingC B e =
      physicalAlpha B e Cc + (routingA B e : ℤ) * r23 R := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Ac := gridResidue B e (r31 R - S.depth - 1) (c2 R - 1)
  let Cc := gridResidue B e (c1 R - S.depth - 1) 0
  have hgeom := branchB_high_seam_target_U_canonical_and_carries
    R hB x hsx hbirth haxis hU
  have hstep := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) Ac
  change branchBPrefixAlpha R Ac + routingC B e =
    branchBPrefixAlpha R (Ac + routingC B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientV R Ac at hstep
  rw [hgeom.2.2.2.2.1, hgeom.2.2.2.2.2.2] at hstep
  simpa [branchBPrefixAlpha, physicalAlpha, B, e, Cc] using hstep

/-- B56 principal candidate transported from the genuine base tie to the
`C` corner of the same actual U diamond. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_U_principal_C_eq_r23
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let Cc := gridResidue B e (c1 R - S.depth - 1) 0
    rawCandidate B e (actualPrincipalIndex B) Cc = r23 R := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let Q := actualPrincipalIndex B
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Ac := gridResidue B e (r31 R - S.depth - 1) (c2 R - 1)
  let Cc := gridResidue B e (c1 R - S.depth - 1) 0
  let At := Ac - (Q * routingM B e : ℕ)
  let Ct := Cc - (Q * routingM B e : ℕ)
  have hgeom := branchB_high_seam_target_U_canonical_and_carries
    R hB x hsx hbirth haxis hU
  have hAC : Ac + routingC B e = Cc := hgeom.2.2.2.2.2.2
  have htranslated : At + routingC B e = Ct := by
    dsimp only [At, Ct]
    calc
      Ac - (Q * routingM B e : ℕ) + routingC B e =
          (Ac + routingC B e) - (Q * routingM B e : ℕ) := by abel
      _ = Cc - (Q * routingM B e : ℕ) := by rw [hAC]
  have htranslatedStep := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) At
  change physicalAlpha B e At + routingC B e =
    physicalAlpha B e (At + routingC B e) +
      (routingA B e : ℤ) *
        (routingH B e).asRelativeIdeal.aperyStepQuotient
          (routingA B e) (routingC B e) (routingHC B e) At at htranslatedStep
  rw [htranslated] at htranslatedStep
  have htransle : physicalAlpha B e Ct ≤
      physicalAlpha B e At + routingC B e := by
    rw [htranslatedStep]
    apply le_add_of_nonneg_right
    positivity
  have hbaseZero :=
    branchB_actualZeroEdgeBirth_high_seam_target_U_principal_base_zero
      R hB x hsx hbirth haxis hU
  change rawCandidate B e Q Ac = 0 at hbaseZero
  have hspecA := rawCandidate_spec B e Q Ac
  change (Q : ℤ) * routingM B e + physicalAlpha B e At -
      physicalAlpha B e Ac =
        (routingA B e : ℤ) * rawCandidate B e Q Ac at hspecA
  rw [hbaseZero, mul_zero] at hspecA
  have htop := branchB_high_seam_target_U_top_wrap_apery
    R hB x hsx hbirth haxis hU
  change physicalAlpha B e Ac + routingC B e =
    physicalAlpha B e Cc + (routingA B e : ℤ) * r23 R at htop
  have hspecC := rawCandidate_spec B e Q Cc
  change (Q : ℤ) * routingM B e + physicalAlpha B e Ct -
      physicalAlpha B e Cc =
        (routingA B e : ℤ) * rawCandidate B e Q Cc at hspecC
  have ha : (0 : ℤ) < routingA B e := by
    exact_mod_cast routingA_pos B e
  have hcandLe : rawCandidate B e Q Cc ≤ r23 R := by
    nlinarith
  have hfinal :=
    branchB_actualZeroEdgeBirth_high_seam_target_U_final_height_packet
      R hB x hsx hbirth haxis hU
  change eta B e (r31 R - S.depth - 1) (c2 R - 1) = 0 ∧
      eta B e (r31 R - S.depth) (c2 R - 1) = 0 ∧
      eta B e (c1 R - S.depth - 1) 0 = r23 R ∧
      r23 R ≤ S.coordinate.j.toNat at hfinal
  have hCphysical := eta_eq_physicalHeight_of_isCanonical B e _ _ hgeom.2.2.1
  have hheight : physicalHeight B e Cc = r23 R := by
    change eta B e (c1 R - S.depth - 1) 0 = physicalHeight B e Cc at hCphysical
    omega
  have hr23pos : 0 < r23 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.1
  have hheightMin := physicalHeight_eq_max_rawMinimum B e Cc
  have hmin : rawMinimum B e Cc = r23 R := by
    rw [hheight] at hheightMin
    omega
  have hQpos : 0 < Q := by
    dsimp only [Q]
    exact (actualPrincipalIndex_spec B).1
  have hcandGe : (r23 R : ℤ) ≤ rawCandidate B e Q Cc := by
    rw [← hmin]
    exact rawMinimum_le B e Cc hQpos
  exact le_antisymm hcandLe hcandGe

/-- Canonical grid points have their literal normalized-grid value as their
ambient Apéry representative. -/
private theorem branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ)
    (hcanon : IsCanonicalTailGridPoint B e i j) :
    physicalAlpha B e (gridResidue B e i j) = normalizedGrid B e 0 i j := by
  exact hcanon.symm

/-- Authority's complementary cell, translated through the frozen inactive
cyclic reindex, is the current grid point `(c1-1,0)`. -/
private theorem branchB_high_seam_target_U_X2_canonical
    (R : SectorBCriticalRoleBranchB P) :
    IsCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
      (c1 R - 1) 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  have hc1pos : 0 < c1 R := by
    have hp := (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
    have hz := (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.1
    omega
  have hc2pos : 0 < c2 R := by
    have hp := (branchB_actual_herzog_coordinates R).cross_positive.1
    have hz := (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    omega
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  apply herzogLShapeCanonicality B e D
  simp only [L5A2C4OR5.HerzogLShapeDomain]
  change c1 R - 1 < L5A2C4A.c2 B e ∧
    0 < L5A2C4A.c3 B e ∧
    (c1 R - 1 < L5A2C4D.cr12 D ∨ 0 < L5A2C4D.cr13 D)
  dsimp only [B, e]
  rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
  have hmap := branchB_inactive_coherent_coefficients R
  dsimp only [D, B, e] at hmap
  obtain ⟨_h12, h13, _h21, _h23, _h31, _h32⟩ := hmap
  rw [h13]
  exact ⟨by omega, hc2pos, Or.inr hr32⟩

set_option maxHeartbeats 800000 in
-- The proof normalizes two large ZMod residue identities before its final
-- integer cancellation; the project default is too small for that reduction.
/-- Complementary-index transport on the actual U event.  Besides the exact
candidate value, the theorem exports that the complementary index really is
inside the strict prefix window. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_U_complement_X2
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let Q := actualPrincipalIndex B
    let k := Q - S.ell
    let X2 := gridResidue B e (c1 R - 1) 0
    1 ≤ k ∧ k < Q ∧
      rawCandidate B e k X2 = (r23 R : ℤ) - S.coordinate.j := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let Q := actualPrincipalIndex B
  let k := Q - S.ell
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Cc := gridResidue B e (c1 R - S.depth - 1) 0
  let X2 := gridResidue B e (c1 R - 1) 0
  change S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R at haxis
  have hellpos : 0 < S.ell := S.ell_pos
  have helllt : S.ell < Q := S.ell_lt_principal
  have hkpos : 1 ≤ k := by
    dsimp only [k, Q]
    omega
  have hklt : k < Q := by
    dsimp only [k, Q]
    omega
  refine ⟨hkpos, hklt, ?_⟩
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hCcanon :=
    (branchB_high_seam_target_U_canonical_and_carries
      R hB x hsx hbirth haxis hU).2.2.1
  have hXcanon := branchB_high_seam_target_U_X2_canonical R
  have hcoord : c1 R - S.depth - 1 + S.depth = c1 R - 1 := by
    omega
  have halphaC :=
    branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e (c1 R - S.depth - 1) 0 hCcanon
  have halphaX :=
    branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e (c1 R - 1) 0 hXcanon
  have halphaXC : physicalAlpha B e X2 =
      physicalAlpha B e Cc + (S.depth : ℤ) * routingB B e := by
    change physicalAlpha B e (gridResidue B e (c1 R - 1) 0) =
      physicalAlpha B e (gridResidue B e (c1 R - S.depth - 1) 0) +
        (S.depth : ℤ) * routingB B e
    rw [halphaX, halphaC]
    exact_mod_cast (show normalizedGrid B e 0 (c1 R - 1) 0 =
        normalizedGrid B e 0 (c1 R - S.depth - 1) 0 +
          S.depth * routingB B e by
      simp only [normalizedGrid, zero_mul, zero_add]
      rw [← hcoord]
      ring)
  have hresXC : X2 = Cc + S.depth * (routingB B e : ZMod (routingA B e)) := by
    dsimp only [X2, Cc, gridResidue]
    rw [← hcoord]
    push_cast
    ring
  have hAeq : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hBeq : routingB B e = normalizedA R := by
    simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hMeq : routingM B e = normalizedM B := by
    simp [B, e, routingM]
  have hn : S.n = S.ell * routingM B e := by
    rw [S.n_eq, hMeq]
  have haxisInt : (S.ell : ℤ) * routingM B e +
      (S.depth : ℤ) * routingB B e =
        S.coordinate.j * routingA B e := by
    have hbal := haxis.2.2.2.2
    have hnInt : (S.n : ℤ) = S.ell * routingM B e := by exact_mod_cast hn
    rw [hnInt] at hbal
    rw [hAeq, hBeq]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbal
  have hselected : (S.depth : ZMod (routingA B e)) * routingB B e +
      S.ell * routingM B e = 0 := by
    have hcast :=
      congrArg (fun z : ℤ => (z : ZMod (routingA B e))) haxisInt
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hcast
    rw [show (routingA B e : ZMod (routingA B e)) = 0 by simp,
      mul_zero] at hcast
    simpa only [add_comm] using hcast
  have hQsplit : Q = k + S.ell := by
    dsimp only [k]
    omega
  have htranslated : X2 - (k * routingM B e : ℕ) =
      Cc - (Q * routingM B e : ℕ) := by
    rw [hresXC, hQsplit]
    push_cast
    linear_combination hselected
  have htranslatedAlpha :
      physicalAlpha B e (X2 - (k * routingM B e : ℕ)) =
        physicalAlpha B e (Cc - (Q * routingM B e : ℕ)) := by
    rw [htranslated]
  have hprincipal :=
    branchB_actualZeroEdgeBirth_high_seam_target_U_principal_C_eq_r23
      R hB x hsx hbirth haxis hU
  change rawCandidate B e Q Cc = r23 R at hprincipal
  have hspecX := rawCandidate_spec B e k X2
  change (k : ℤ) * routingM B e +
      physicalAlpha B e (X2 - (k * routingM B e : ℕ)) -
      physicalAlpha B e X2 =
        (routingA B e : ℤ) * rawCandidate B e k X2 at hspecX
  have hspecC := rawCandidate_spec B e Q Cc
  change (Q : ℤ) * routingM B e +
      physicalAlpha B e (Cc - (Q * routingM B e : ℕ)) -
      physicalAlpha B e Cc =
        (routingA B e : ℤ) * rawCandidate B e Q Cc at hspecC
  rw [hprincipal] at hspecC
  have ha : (0 : ℤ) < routingA B e := by
    exact_mod_cast routingA_pos B e
  have hQcast : (Q : ℤ) = k + S.ell := by exact_mod_cast hQsplit
  rw [htranslatedAlpha, halphaXC] at hspecX
  nlinarith

/-- The complementary active-pure cell is already zero in both the strict
prefix envelope and the final routing ideal. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_U_X2_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let X2 := gridResidue B e (c1 R - 1) 0
    branchBPrefixHeight R x hsx X2 = 0 ∧
      eta B e (c1 R - 1) 0 = 0 := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let Q := actualPrincipalIndex B
  let k := Q - S.ell
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let X2 := gridResidue B e (c1 R - 1) 0
  change S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R at haxis
  have hcomp :=
    branchB_actualZeroEdgeBirth_high_seam_target_U_complement_X2
      R hB x hsx hbirth haxis hU
  change 1 ≤ k ∧ k < Q ∧
      rawCandidate B e k X2 = (r23 R : ℤ) - S.coordinate.j at hcomp
  have hfinal :=
    branchB_actualZeroEdgeBirth_high_seam_target_U_final_height_packet
      R hB x hsx hbirth haxis hU
  change eta B e (r31 R - S.depth - 1) (c2 R - 1) = 0 ∧
      eta B e (r31 R - S.depth) (c2 R - 1) = 0 ∧
      eta B e (c1 R - S.depth - 1) 0 = r23 R ∧
      r23 R ≤ S.coordinate.j.toNat at hfinal
  have hj0 : (0 : ℤ) ≤ S.coordinate.j := by
    have hq0 : (0 : ℤ) ≤ qH R := by positivity
    omega
  have hj : S.coordinate.j = (S.coordinate.j.toNat : ℤ) :=
    (Int.toNat_of_nonneg hj0).symm
  have hcandNonpos : rawCandidate B e k X2 ≤ 0 := by
    rw [hcomp.2.2, hj]
    have hcast : (r23 R : ℤ) ≤ S.coordinate.j.toNat := by
      exact_mod_cast (show r23 R ≤ S.coordinate.j.toNat from hfinal.2.2.2)
    omega
  have hprefix : branchBPrefixHeight R x hsx X2 = 0 := by
    by_contra hne
    have hpos : 0 < branchBPrefixHeight R x hsx X2 := Nat.pos_of_ne_zero hne
    have hcandPos := branchB_prefix_candidate_pos_of_prefixHeight_pos
      R x hsx X2 hpos hcomp.1 hcomp.2.1
    exact (not_lt_of_ge hcandNonpos) hcandPos
  refine ⟨hprefix, ?_⟩
  have hheightLe := branchB_finalHeight_le_prefixHeight R x hsx X2
  change physicalHeight B e X2 ≤ branchBPrefixHeight R x hsx X2 at hheightLe
  have hheight : physicalHeight B e X2 = 0 := by
    rw [hprefix] at hheightLe
    omega
  have hcanon := branchB_high_seam_target_U_X2_canonical R
  have hetaPhysical :=
    eta_eq_physicalHeight_of_isCanonical B e (c1 R - 1) 0 hcanon
  change eta B e (c1 R - 1) 0 = physicalHeight B e X2 at hetaPhysical
  rw [hetaPhysical, hheight]

/-- B56 mandatory endpoint: the actual high-axis U target is impossible.
Its complementary cell is forced to final height zero, contradicting the
genuine first-critical pure predecessor. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_U_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hU :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base (branchBInactiveReindex R)
          (c1 R - S.depth) 0) : False := by
  have hzero := branchB_actualZeroEdgeBirth_high_seam_target_U_X2_zero
    R hB x hsx hbirth haxis hU
  have hlive := branchB_inactive_first_pure_height_pos R hB
  exact (Nat.ne_of_gt hlive) hzero.2

/-! ### B58: individual-return threshold kernel -/

/-- The Apéry representative of `J_n = H ∩ (n + H)` is the larger of the
two ambient Apéry representatives in the relevant residue classes.  The
modulus is assumed to lie in `H`, as it does for the inactive routing
generator. -/
theorem returnIdeal_aperyRepresentative_eq_max
    (H : NumericalSemigroup) (n a : ℕ) [NeZero a] (ha : a ∈ H)
    (r : ZMod a) :
    (returnIdeal H n).aperyRepresentative a r =
      max (H.asRelativeIdeal.aperyRepresentative a r)
        ((n : ℤ) + H.asRelativeIdeal.aperyRepresentative a
          (r - (n : ZMod a))) := by
  let I := returnIdeal H n
  let alpha := H.asRelativeIdeal.aperyRepresentative a r
  let gamma := H.asRelativeIdeal.aperyRepresentative a (r - (n : ZMod a))
  let beta : ℤ := n + gamma
  have halpha : alpha ∈ H.asRelativeIdeal :=
    H.asRelativeIdeal.aperyRepresentative_mem a r
  have hgamma : gamma ∈ H.asRelativeIdeal :=
    H.asRelativeIdeal.aperyRepresentative_mem a (r - (n : ZMod a))
  have hmodAlpha : (alpha : ZMod a) = r := by
    simpa [alpha] using H.asRelativeIdeal.aperyRepresentative_mod a r
  have hmodGamma : (gamma : ZMod a) = r - (n : ZMod a) := by
    simpa [gamma] using
      H.asRelativeIdeal.aperyRepresentative_mod a (r - (n : ZMod a))
  have hmodBeta : (beta : ZMod a) = r := by
    dsimp [beta]
    push_cast
    rw [hmodGamma]
    abel
  have hcandidate : max alpha beta ∈ I := by
    rw [mem_returnIdeal_iff]
    rcases le_total alpha beta with hab | hba
    · rw [max_eq_right hab]
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
          a hab (hmodBeta.trans hmodAlpha.symm)
        have hak : a * k ∈ H := by
          have := H.toAddSubmonoid.nsmul_mem ha k
          simpa [nsmul_eq_mul, Nat.mul_comm] using this
        rw [hk]
        exact H.asRelativeIdeal.add_mem halpha hak
      · simpa [beta] using hgamma
    · rw [max_eq_left hba]
      refine ⟨halpha, ?_⟩
      obtain ⟨k, hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
        a hba (hmodAlpha.trans hmodBeta.symm)
      have hak : a * k ∈ H := by
        have := H.toAddSubmonoid.nsmul_mem ha k
        simpa [nsmul_eq_mul, Nat.mul_comm] using this
      have hsum : alpha - n = gamma + (a * k : ℕ) := by
        dsimp [beta] at hk
        push_cast at hk ⊢
        omega
      rw [hsum]
      exact H.asRelativeIdeal.add_mem hgamma hak
  apply le_antisymm
  · apply I.aperyRepresentative_le a r hcandidate
    rcases le_total alpha beta with hab | hba
    · rw [max_eq_right hab]
      exact hmodBeta
    · rw [max_eq_left hba]
      exact hmodAlpha
  · have hlambda := I.aperyRepresentative_mem a r
    have halpha_le : alpha ≤ I.aperyRepresentative a r :=
      H.asRelativeIdeal.aperyRepresentative_le a r hlambda.1
        (I.aperyRepresentative_mod a r)
    have hgamma_le : gamma ≤ I.aperyRepresentative a r - n := by
      apply H.asRelativeIdeal.aperyRepresentative_le a (r - (n : ZMod a))
        hlambda.2
      have hmodI := I.aperyRepresentative_mod a r
      push_cast
      rw [hmodI]
    change max alpha beta ≤ I.aperyRepresentative a r
    apply max_le halpha_le
    dsimp [beta]
    omega

/-- The four-row height table for the selected high-axis-`c` individual
return, written in the frozen inactive chart. -/
def branchBHighSeamIndividualHeight
    (R : SectorBCriticalRoleBranchB P) (j d i t : ℕ) : ℕ :=
  if t < r32 R then
    if i < c1 R - d then j else j - r13 R
  else if i < r31 R - d then j else 0

private theorem branchB_high_seam_lower_wrap_residue
    (R : SectorBCriticalRoleBranchB P) (i d t : ℕ)
    (hge : c1 R ≤ i + d) :
    gridResidue P.M.base (branchBInactiveReindex R) (i + d) t =
      gridResidue P.M.base (branchBInactiveReindex R)
        (i + d - c1 R) (t + r12 R) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  have hA : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hB : routingB B e = normalizedA R := by
    simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hC : routingC B e = normalizedB R := by
    simpa [B, e] using branchB_inactive_routingC_eq_normalizedB R
  have hrel : c1 R * normalizedA R =
      r13 R * normalizedC R + r12 R * normalizedB R := by
    simpa [Nat.add_comm] using
      (branchB_actual_herzog_coordinates R).normalized_relations.1
  have hrelmod := congrArg (fun n : ℕ => (n : ZMod a)) hrel
  push_cast at hrelmod
  rw [← hA, ← hB, ← hC] at hrelmod
  simp at hrelmod
  have hsplit : i + d = c1 R + (i + d - c1 R) := by omega
  simp only [B, e, gridResidue]
  rw [hsplit]
  simp only [Nat.add_sub_cancel_left]
  push_cast
  linear_combination hrelmod

private theorem branchB_high_seam_lower_wrap_physicalAlpha
    (R : SectorBCriticalRoleBranchB P) (i d t : ℕ)
    (hge : c1 R ≤ i + d)
    (hdom : L5A2C4OR5.HerzogLShapeDomain
      (branchB_inactive_coherentHerzogData R)
        (i + d - c1 R) (t + r12 R)) :
    physicalAlpha P.M.base (branchBInactiveReindex R)
        (gridResidue P.M.base (branchBInactiveReindex R) (i + d) t) =
      normalizedGrid P.M.base (branchBInactiveReindex R) 0
        (i + d - c1 R) (t + r12 R) := by
  rw [branchB_high_seam_lower_wrap_residue R i d t hge]
  exact (herzogLShapeCanonicality P.M.base (branchBInactiveReindex R)
    (branchB_inactive_coherentHerzogData R) _ _ hdom).symm

private theorem branchB_high_seam_upper_wrap_residue
    (R : SectorBCriticalRoleBranchB P) (i d t : ℕ)
    (hige : r31 R ≤ i + d) (htge : r32 R ≤ t) :
    gridResidue P.M.base (branchBInactiveReindex R) (i + d) t =
      gridResidue P.M.base (branchBInactiveReindex R)
        (i + d - r31 R) (t - r32 R) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  have hA : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hB : routingB B e = normalizedA R := by
    simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hC : routingC B e = normalizedB R := by
    simpa [B, e] using branchB_inactive_routingC_eq_normalizedB R
  have hrel : c3 R * normalizedC R =
      r31 R * normalizedA R + r32 R * normalizedB R := by
    simpa using
      (branchB_actual_herzog_coordinates R).normalized_relations.2.2
  have hrelmod := congrArg (fun n : ℕ => (n : ZMod a)) hrel
  push_cast at hrelmod
  rw [← hA, ← hB, ← hC] at hrelmod
  simp at hrelmod
  have hisplit : i + d = r31 R + (i + d - r31 R) := by omega
  have htsplit : t = r32 R + (t - r32 R) := by omega
  simp only [B, e, gridResidue]
  rw [hisplit, htsplit]
  simp only [Nat.add_sub_cancel_left]
  push_cast
  linear_combination -hrelmod

private theorem branchB_high_seam_upper_wrap_physicalAlpha
    (R : SectorBCriticalRoleBranchB P) (i d t : ℕ)
    (hige : r31 R ≤ i + d) (htge : r32 R ≤ t)
    (hdom : L5A2C4OR5.HerzogLShapeDomain
      (branchB_inactive_coherentHerzogData R)
        (i + d - r31 R) (t - r32 R)) :
    physicalAlpha P.M.base (branchBInactiveReindex R)
        (gridResidue P.M.base (branchBInactiveReindex R) (i + d) t) =
      normalizedGrid P.M.base (branchBInactiveReindex R) 0
        (i + d - r31 R) (t - r32 R) := by
  rw [branchB_high_seam_upper_wrap_residue R i d t hige htge]
  exact (herzogLShapeCanonicality P.M.base (branchBInactiveReindex R)
    (branchB_inactive_coherentHerzogData R) _ _ hdom).symm

/-! ### B59: exact high-seam individual height formula -/

set_option maxHeartbeats 1200000 in
/-- Exact individual-return threshold table on every canonical cell of the
inactive Herzog L-shape.  The actual routing source does not occur in the
conclusion. -/
theorem branchB_high_seam_individual_height_formula
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (i t : ℕ)
    (hdom : L5A2C4OR5.HerzogLShapeDomain
      (branchB_inactive_coherentHerzogData R) i t) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let j := S.coordinate.j.toNat
    letI : NeZero (routingA B e) :=
      ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (returnIdeal (routingH B e) S.n).aperyRepresentative
        (routingA B e) (gridResidue B e i t) =
      physicalAlpha B e (gridResidue B e i t) +
        routingA B e * branchBHighSeamIndividualHeight R j S.depth i t := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let j := S.coordinate.j.toNat
  let H := routingH B e
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let r := gridResidue B e i t
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change (returnIdeal H S.n).aperyRepresentative a r =
    physicalAlpha B e r +
      a * branchBHighSeamIndividualHeight R j S.depth i t
  change S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R at haxis
  have hj0 : (0 : ℤ) ≤ S.coordinate.j := by omega
  have hj : S.coordinate.j = (j : ℤ) :=
    (Int.toNat_of_nonneg hj0).symm
  have hju : r13 R < j := by
    rw [hj] at haxis
    exact_mod_cast (show (r13 R : ℤ) < j by
      simpa using haxis.2.1)
  have hjc : j < c3 R := by
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    rw [hj] at haxis
    exact_mod_cast (show (j : ℤ) < c3 R by omega)
  have hdpos : 0 < S.depth := S.depth_pos
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hAeq : a = normalizedC R := by
    simpa [a, B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hBeq : b = normalizedA R := by
    simpa [b, B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hCeq : c = normalizedB R := by
    simpa [c, B, e] using branchB_inactive_routingC_eq_normalizedB R
  have hAraw : routingN1 B e / routingD B e = normalizedC R := hAeq
  have hBraw : routingN2 B e / routingD B e = normalizedA R := hBeq
  have hCraw : routingN3 B e / routingD B e = normalizedB R := hCeq
  have hAZ : (a : ℤ) = normalizedC R := by exact_mod_cast hAeq
  have hBrawZ : ((routingN2 B e / routingD B e : ℕ) : ℤ) =
      normalizedA R := by exact_mod_cast hBraw
  have hCrawZ : ((routingN3 B e / routingD B e : ℕ) : ℤ) =
      normalizedB R := by exact_mod_cast hCraw
  have hrA : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hrB : routingB B e = normalizedA R := by
    simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hrC : routingC B e = normalizedB R := by
    simpa [B, e] using branchB_inactive_routingC_eq_normalizedB R
  have hmaps := branchB_inactive_coherent_coefficients R
  dsimp only [D, B, e] at hmaps
  obtain ⟨h12, h13, _h21, _h23, _h31, _h32⟩ := hmaps
  have hc2map : L5A2C4A.c2 B e = c1 R := by
    simpa [B, e] using branchB_inactive_coherent_c2 R
  have hc3map : L5A2C4A.c3 B e = c2 R := by
    simpa [B, e] using branchB_inactive_coherent_c3 R
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hsum3 : c3 R = r13 R + r23 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
  have hdomBounds := hdom
  simp only [L5A2C4OR5.HerzogLShapeDomain] at hdomBounds
  rw [hc2map, hc3map, h12, h13] at hdomBounds
  have hrel1 : c1 R * normalizedA R =
      r13 R * normalizedC R + r12 R * normalizedB R := by
    simpa [Nat.add_comm] using
      (branchB_actual_herzog_coordinates R).normalized_relations.1
  have hrel3 : c3 R * normalizedC R =
      r31 R * normalizedA R + r32 R * normalizedB R := by
    simpa using (branchB_actual_herzog_coordinates R).normalized_relations.2.2
  have hn : S.n + normalizedA R * S.depth = j * normalizedC R := by
    exact_mod_cast (show (S.n : ℤ) + normalizedA R * S.depth =
      (j : ℤ) * normalizedC R by simpa [hj] using haxis.2.2.2.2)
  have hnZ : (S.n : ℤ) + (normalizedA R : ℤ) * S.depth =
      (j : ℤ) * normalizedC R := by exact_mod_cast hn
  have hnRoutingZ : (S.n : ℤ) + (b : ℤ) * S.depth =
      (j : ℤ) * a := by
    rw [hBeq, hAeq]
    exact hnZ
  have hrel1RoutingZ : (c1 R : ℤ) * b =
      (r13 R : ℤ) * a + (r12 R : ℤ) * c := by
    rw [hBeq, hAeq, hCeq]
    exact_mod_cast hrel1
  have hrel3RoutingZ : (c3 R : ℤ) * a =
      (r31 R : ℤ) * b + (r32 R : ℤ) * c := by
    rw [hAeq, hBeq, hCeq]
    exact_mod_cast hrel3
  have hsum3Z : (c3 R : ℤ) = (r13 R : ℤ) + r23 R := by
    exact_mod_cast hsum3
  have hrel3ExpandedZ : ((r13 R : ℤ) + r23 R) * a =
      (r31 R : ℤ) * b + (r32 R : ℤ) * c := by
    rw [← hsum3Z]
    exact hrel3RoutingZ
  have hnmod : (S.n : ZMod a) = -(S.depth * b : ℕ) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← Nat.cast_add]
    rw [hBeq, Nat.mul_comm S.depth (normalizedA R), hn, hAeq]
    simp
  have hrshift : r - (S.n : ZMod a) =
      gridResidue B e (i + S.depth) t := by
    simp only [r, gridResidue]
    rw [hnmod]
    push_cast
    ring
  have haH : a ∈ routingH B e := by
    exact (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
        (AddSubmonoid.subset_closure (by simp [a]))
  have hapos : 0 < a := routingA_pos B e
  rw [returnIdeal_aperyRepresentative_eq_max (routingH B e) S.n a haH r]
  have hcanon := herzogLShapeCanonicality B e D i t hdom
  have halpha : physicalAlpha B e r = normalizedGrid B e 0 i t := by
    exact hcanon.symm
  rw [← physicalAlpha]
  change max (physicalAlpha B e r)
      ((S.n : ℤ) + physicalAlpha B e (r - (S.n : ZMod a))) = _
  rw [hrshift, halpha]
  by_cases ht : t < r32 R
  · by_cases hi : i < c1 R - S.depth
    · have hid : L5A2C4OR5.HerzogLShapeDomain D (i + S.depth) t := by
        simp only [L5A2C4OR5.HerzogLShapeDomain]
        rw [hc2map, hc3map, h12, h13]
        exact ⟨by omega, by omega, Or.inr ht⟩
      have hshift := herzogLShapeCanonicality B e D _ _ hid
      rw [show physicalAlpha B e (gridResidue B e (i + S.depth) t) =
          normalizedGrid B e 0 (i + S.depth) t from hshift.symm]
      have hcandidate :
          (S.n : ℤ) + (normalizedGrid B e 0 (i + S.depth) t : ℤ) =
            (normalizedGrid B e 0 i t : ℤ) + (a : ℤ) * j := by
        simp only [normalizedGrid, zero_mul, zero_add]
        change (S.n : ℤ) + (((i + S.depth) * b + t * c : ℕ) : ℤ) =
          ((i * b + t * c : ℕ) : ℤ) + (a : ℤ) * j
        push_cast
        linear_combination hnRoutingZ
      rw [hcandidate]
      simp only [branchBHighSeamIndividualHeight, ht, hi, if_pos]
      have hnonneg : (0 : ℤ) ≤ (a : ℤ) * j := by positivity
      exact max_eq_right (le_add_of_nonneg_right hnonneg)
    · have hiGe : c1 R ≤ i + S.depth := by omega
      let ii := i + S.depth - c1 R
      let tt := t + r12 R
      have hid : L5A2C4OR5.HerzogLShapeDomain D ii tt := by
        simp only [L5A2C4OR5.HerzogLShapeDomain]
        rw [hc2map, hc3map, h12, h13]
        exact ⟨by dsimp [ii]; omega, by dsimp [tt]; omega,
          Or.inl (by dsimp [ii]; omega)⟩
      have hshift := branchB_high_seam_lower_wrap_physicalAlpha
        R i S.depth t hiGe (by simpa [D, B, e, ii, tt] using hid)
      rw [show physicalAlpha B e (gridResidue B e (i + S.depth) t) =
          normalizedGrid B e 0 ii tt by simpa [B, e, ii, tt] using hshift]
      have hcandidate :
          (S.n : ℤ) + (normalizedGrid B e 0 ii tt : ℤ) =
            (normalizedGrid B e 0 i t : ℤ) +
              (a : ℤ) * (j - r13 R) := by
        simp only [normalizedGrid, zero_mul, zero_add]
        change (S.n : ℤ) + ((ii * b + tt * c : ℕ) : ℤ) =
          ((i * b + t * c : ℕ) : ℤ) + (a : ℤ) * (j - r13 R)
        dsimp [ii, tt]
        push_cast
        have hiiCast : ((i + S.depth - c1 R : ℕ) : ℤ) =
            (i : ℤ) + S.depth - c1 R := by omega
        rw [hiiCast]
        linear_combination hnRoutingZ - hrel1RoutingZ
      rw [hcandidate]
      simp only [branchBHighSeamIndividualHeight, ht, hi, if_pos, if_false]
      rw [Nat.cast_sub (Nat.le_of_lt hju)]
      have hnonneg : (0 : ℤ) ≤ (a : ℤ) * ((j : ℤ) - r13 R) := by
        exact mul_nonneg (by positivity) (by omega)
      exact max_eq_right (le_add_of_nonneg_right hnonneg)
  · have htGe : r32 R ≤ t := le_of_not_gt ht
    by_cases hi : i < r31 R - S.depth
    · have hid : L5A2C4OR5.HerzogLShapeDomain D (i + S.depth) t := by
        simp only [L5A2C4OR5.HerzogLShapeDomain]
        rw [hc2map, hc3map, h12, h13]
        exact ⟨by omega, by omega, Or.inl (by omega)⟩
      have hshift := herzogLShapeCanonicality B e D _ _ hid
      rw [show physicalAlpha B e (gridResidue B e (i + S.depth) t) =
          normalizedGrid B e 0 (i + S.depth) t from hshift.symm]
      have hcandidate :
          (S.n : ℤ) + (normalizedGrid B e 0 (i + S.depth) t : ℤ) =
            (normalizedGrid B e 0 i t : ℤ) + (a : ℤ) * j := by
        simp only [normalizedGrid, zero_mul, zero_add]
        change (S.n : ℤ) + (((i + S.depth) * b + t * c : ℕ) : ℤ) =
          ((i * b + t * c : ℕ) : ℤ) + (a : ℤ) * j
        push_cast
        linear_combination hnRoutingZ
      rw [hcandidate]
      simp only [branchBHighSeamIndividualHeight, ht, hi, if_pos, if_false]
      have hnonneg : (0 : ℤ) ≤ (a : ℤ) * j := by positivity
      exact max_eq_right (le_add_of_nonneg_right hnonneg)
    · have hiGe : r31 R ≤ i + S.depth := by omega
      let ii := i + S.depth - r31 R
      let tt := t - r32 R
      have hid : L5A2C4OR5.HerzogLShapeDomain D ii tt := by
        simp only [L5A2C4OR5.HerzogLShapeDomain]
        rw [hc2map, hc3map, h12, h13]
        exact ⟨by dsimp [ii]; omega, by dsimp [tt]; omega,
          Or.inl (by dsimp [ii]; omega)⟩
      have hshift := branchB_high_seam_upper_wrap_physicalAlpha
        R i S.depth t hiGe htGe (by simpa [D, B, e, ii, tt] using hid)
      rw [show physicalAlpha B e (gridResidue B e (i + S.depth) t) =
          normalizedGrid B e 0 ii tt by simpa [B, e, ii, tt] using hshift]
      have hcandidate :
          (S.n : ℤ) + (normalizedGrid B e 0 ii tt : ℤ) +
              (a : ℤ) * (c3 R - j) =
            (normalizedGrid B e 0 i t : ℤ) := by
        simp only [normalizedGrid, zero_mul, zero_add]
        change (S.n : ℤ) + ((ii * b + tt * c : ℕ) : ℤ) +
            (a : ℤ) * (c3 R - j) = ((i * b + t * c : ℕ) : ℤ)
        dsimp [ii, tt]
        push_cast
        have hiiCast : ((i + S.depth - r31 R : ℕ) : ℤ) =
            (i : ℤ) + S.depth - r31 R := by omega
        have httCast : ((t - r32 R : ℕ) : ℤ) = (t : ℤ) - r32 R := by omega
        rw [hiiCast, httCast]
        linear_combination hnRoutingZ + hrel3ExpandedZ
      have hle :
          (S.n : ℤ) + (normalizedGrid B e 0 ii tt : ℤ) ≤
            (normalizedGrid B e 0 i t : ℤ) := by
        have hnonneg : (0 : ℤ) ≤ (a : ℤ) * (c3 R - j) := by
          exact mul_nonneg (by positivity) (by omega)
        linarith
      simp only [branchBHighSeamIndividualHeight, ht, hi, if_pos, if_false,
        Nat.cast_zero, mul_zero, add_zero]
      exact max_eq_left hle

/- B60 source classification promoted from the frozen downstream draft.
The public B59 checkpoint supplying its exact height table is
`branchB_high_seam_individual_height_formula` above. -/

set_option maxHeartbeats 1200000 in
/-- Every minimal source of the selected high-seam individual return lies at
one of the three exact source coordinates `O`, `U`, or `F`. -/
theorem branchB_high_seam_individual_source_trichotomy
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (i t : ℕ)
    (hdom : L5A2C4OR5.HerzogLShapeDomain
      (branchB_inactive_coherentHerzogData R) i t)
    (hmin :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let B := P.M.base
      let e := branchBInactiveReindex R
      letI : NeZero (routingA B e) :=
        ⟨Nat.ne_of_gt (routingA_pos B e)⟩
      (returnIdeal (routingH B e) S.n).IsMinimalGenerator
        ((returnIdeal (routingH B e) S.n).aperyRepresentative
          (routingA B e) (gridResidue B e i t))) :
    (i = 0 ∧ t = 0) ∨
      (i = c1 R -
          (branchB_actual_selected_return_anchor_v2 R hB hsx).depth ∧ t = 0) ∨
      (i = r31 R -
          (branchB_actual_selected_return_anchor_v2 R hB hsx).depth ∧
        t = r32 R) := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let H := routingH B e
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let I := returnIdeal H S.n
  let j := S.coordinate.j.toNat
  let height := branchBHighSeamIndividualHeight R j S.depth
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have haxis' : S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
    S.coordinate.j < qH R + vH R ∧
    S.beta = S.coordinate.j * normalizedC R ∧
    (S.n : ℤ) + normalizedA R * S.depth =
      S.coordinate.j * normalizedC R := by
    simpa [S] using haxis
  change (i = 0 ∧ t = 0) ∨
    (i = c1 R - S.depth ∧ t = 0) ∨
    (i = r31 R - S.depth ∧ t = r32 R)
  have hmaps := branchB_inactive_coherent_coefficients R
  dsimp only [D, B, e] at hmaps
  obtain ⟨h12, h13, _h21, _h23, _h31, _h32⟩ := hmaps
  have hc2map : L5A2C4A.c2 B e = c1 R := by
    simpa [B, e] using branchB_inactive_coherent_c2 R
  have hc3map : L5A2C4A.c3 B e = c2 R := by
    simpa [B, e] using branchB_inactive_coherent_c3 R
  have hAeq : a = normalizedC R := by
    simpa [a, B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hBeq : b = normalizedA R := by
    simpa [b, B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hCeq : c = normalizedB R := by
    simpa [c, B, e] using branchB_inactive_routingC_eq_normalizedB R
  have haH : a ∈ H := by
    exact (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
        (AddSubmonoid.subset_closure (by simp [a]))
  have hbH : b ∈ H := by simpa [H, b] using routingHB B e
  have hcH : c ∈ H := by simpa [H, c] using routingHC B e
  have hgen : H.IsGeneratedByThree a b c := by
    simpa [H, a, b, c] using
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1
  have hb0 : b ≠ 0 := by
    intro hb
    apply (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).2.2.1
    simpa [b, hb] using (AddSubmonoid.zero_mem (routingH B e))
  have hc0 : c ≠ 0 := by
    intro hc
    apply (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).2.2.2
    simpa [c, hc] using (AddSubmonoid.zero_mem (routingH B e))
  have hsub := (I.isMinimalGenerator_iff_sub_generators
    hgen (NeZero.ne a) hb0 hc0
      (I.aperyRepresentative a (gridResidue B e i t))).1 hmin
  have hformula (ii tt : ℕ)
      (hd : L5A2C4OR5.HerzogLShapeDomain D ii tt) :
      I.aperyRepresentative a (gridResidue B e ii tt) =
        physicalAlpha B e (gridResidue B e ii tt) + a * height ii tt := by
    simpa [I, H, a, height, S, B, e, j, D] using
      branchB_high_seam_individual_height_formula
        R hB x hsx hbirth haxis ii tt hd
  have hwest (hi : 0 < i) : height i t < height (i - 1) t := by
    by_contra hnlt
    have hle : height (i - 1) t ≤ height i t := le_of_not_gt hnlt
    have hdomW : L5A2C4OR5.HerzogLShapeDomain D (i - 1) t := by
      simp only [L5A2C4OR5.HerzogLShapeDomain] at hdom ⊢
      rw [show L5A2C4D.cr12 D = r31 R by simpa [D] using h12,
        show L5A2C4D.cr13 D = r32 R by simpa [D] using h13] at hdom ⊢
      omega
    have hfw := hformula (i - 1) t hdomW
    have hfc := hformula i t hdom
    have hcanon := herzogLShapeCanonicality B e D i t hdom
    have hcanonW := herzogLShapeCanonicality B e D (i - 1) t hdomW
    have hcoord : gridResidue B e (i - 1) t + b = gridResidue B e i t := by
      simpa [b, show i - 1 + 1 = i by omega] using
        (gridResidue_add_b B e (i - 1) t).symm
    have hgridW : normalizedGrid B e 0 i t =
        normalizedGrid B e 0 (i - 1) t + b := by
      simp only [normalizedGrid, zero_mul, zero_add]
      change i * b + t * c = (i - 1) * b + t * c + b
      have hiEq : i - 1 + 1 = i := by omega
      calc
        i * b + t * c = ((i - 1) + 1) * b + t * c := by rw [hiEq]
        _ = (i - 1) * b + t * c + b := by
          simp only [Nat.add_mul, one_mul]
          omega
    have halphaW :
        physicalAlpha B e (gridResidue B e i t) - b =
          physicalAlpha B e (gridResidue B e (i - 1) t) := by
      rw [← hcanon, ← hcanonW]
      have hgridWZ := congrArg (fun n : ℕ => (n : ℤ)) hgridW
      push_cast at hgridWZ
      omega
    have hdiffW :
        (a : ℤ) * height i t =
          (a : ℤ) * height (i - 1) t +
            (a * (height i t - height (i - 1) t) : ℕ) := by
      push_cast
      rw [Nat.cast_sub hle]
      ring
    have hdelta :
        I.aperyRepresentative a (gridResidue B e i t) - b =
          I.aperyRepresentative a (gridResidue B e (i - 1) t) +
            (a * (height i t - height (i - 1) t) : ℕ) := by
      rw [hfc, hfw]
      linarith [halphaW, hdiffW]
    have hak : a * (height i t - height (i - 1) t) ∈ H := by
      have := H.toAddSubmonoid.nsmul_mem haH
        (height i t - height (i - 1) t)
      simpa [nsmul_eq_mul, Nat.mul_comm] using this
    apply hsub.2.2.1
    rw [hdelta]
    exact I.add_mem (I.aperyRepresentative_mem a _) hak
  have hsouth (ht : 0 < t) : height i t < height i (t - 1) := by
    by_contra hnlt
    have hle : height i (t - 1) ≤ height i t := le_of_not_gt hnlt
    have hdomS : L5A2C4OR5.HerzogLShapeDomain D i (t - 1) := by
      simp only [L5A2C4OR5.HerzogLShapeDomain] at hdom ⊢
      rw [show L5A2C4D.cr12 D = r31 R by simpa [D] using h12,
        show L5A2C4D.cr13 D = r32 R by simpa [D] using h13] at hdom ⊢
      omega
    have hfs := hformula i (t - 1) hdomS
    have hfc := hformula i t hdom
    have hcanon := herzogLShapeCanonicality B e D i t hdom
    have hcanonS := herzogLShapeCanonicality B e D i (t - 1) hdomS
    have hgridS : normalizedGrid B e 0 i t =
        normalizedGrid B e 0 i (t - 1) + c := by
      simp only [normalizedGrid, zero_mul, zero_add]
      change i * b + t * c = i * b + (t - 1) * c + c
      have htEq : t - 1 + 1 = t := by omega
      calc
        i * b + t * c = i * b + ((t - 1) + 1) * c := by rw [htEq]
        _ = i * b + (t - 1) * c + c := by
          simp only [Nat.add_mul, one_mul]
          omega
    have halphaS :
        physicalAlpha B e (gridResidue B e i t) - c =
          physicalAlpha B e (gridResidue B e i (t - 1)) := by
      rw [← hcanon, ← hcanonS]
      have hgridSZ := congrArg (fun n : ℕ => (n : ℤ)) hgridS
      push_cast at hgridSZ
      omega
    have hdiffS :
        (a : ℤ) * height i t =
          (a : ℤ) * height i (t - 1) +
            (a * (height i t - height i (t - 1)) : ℕ) := by
      push_cast
      rw [Nat.cast_sub hle]
      ring
    have hdelta :
        I.aperyRepresentative a (gridResidue B e i t) - c =
          I.aperyRepresentative a (gridResidue B e i (t - 1)) +
            (a * (height i t - height i (t - 1)) : ℕ) := by
      rw [hfc, hfs]
      linarith [halphaS, hdiffS]
    have hak : a * (height i t - height i (t - 1)) ∈ H := by
      have := H.toAddSubmonoid.nsmul_mem haH
        (height i t - height i (t - 1))
      simpa [nsmul_eq_mul, Nat.mul_comm] using this
    apply hsub.2.2.2
    rw [hdelta]
    exact I.add_mem (I.aperyRepresentative_mem a _) hak
  have hr32pos : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hr31pos : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr13pos : 0 < r13 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.1
  have hj0 : (0 : ℤ) ≤ S.coordinate.j := by omega
  have hj : S.coordinate.j = (j : ℤ) :=
    (Int.toNat_of_nonneg hj0).symm
  have hju : r13 R < j := by
    rw [hj] at haxis'
    exact_mod_cast (show (r13 R : ℤ) < j by
      simpa using haxis'.2.1)
  have hc1split : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hjpos : 0 < j := lt_trans hr13pos hju
  have hjsubpos : 0 < j - r13 R := by omega
  have hPpos : 0 < r31 R - S.depth := by omega
  have hApos : 0 < c1 R - S.depth := by omega
  by_cases hi0 : i = 0
  · by_cases ht0 : t = 0
    · exact Or.inl ⟨hi0, ht0⟩
    · have hs := hsouth (Nat.pos_of_ne_zero ht0)
      by_cases htLow : t < r32 R
      · have htpred : t - 1 < r32 R := by omega
        simp [height, branchBHighSeamIndividualHeight, hi0, htLow,
          htpred, hApos] at hs
      · by_cases htpred : t - 1 < r32 R
        · simp [height, branchBHighSeamIndividualHeight, hi0, htLow,
            htpred, hApos, hPpos] at hs
        · simp [height, branchBHighSeamIndividualHeight, hi0, htLow,
            htpred, hPpos] at hs
  · have hw := hwest (Nat.pos_of_ne_zero hi0)
    by_cases ht0 : t = 0
    · right; left
      by_cases hiA : i < c1 R - S.depth
      · have hipA : i - 1 < c1 R - S.depth := by omega
        simp [height, branchBHighSeamIndividualHeight, ht0, hr32pos,
          hiA, hipA] at hw
      · by_cases hipA : i - 1 < c1 R - S.depth
        · exact ⟨by omega, ht0⟩
        · simp [height, branchBHighSeamIndividualHeight, ht0, hr32pos,
            hiA, hipA] at hw
    · have hs := hsouth (Nat.pos_of_ne_zero ht0)
      by_cases htLow : t < r32 R
      · have htpred : t - 1 < r32 R := by omega
        simp [height, branchBHighSeamIndividualHeight, htLow, htpred] at hs
      · by_cases htpred : t - 1 < r32 R
        · right; right
          have htEq : t = r32 R := by omega
          by_cases hiP : i < r31 R - S.depth
          · have hipP : i - 1 < r31 R - S.depth := by omega
            simp [height, branchBHighSeamIndividualHeight, htLow,
              hiP, hipP] at hw
          · by_cases hipP : i - 1 < r31 R - S.depth
            · exact ⟨by omega, htEq⟩
            · simp [height, branchBHighSeamIndividualHeight, htLow,
                hiP, hipP] at hw
        · simp [height, branchBHighSeamIndividualHeight, htLow,
            htpred] at hs

/- Downstream target-trichotomy/F-support draft, retained non-load-bearing
until the B60 source classification above is kernel-green.
-/

set_option maxHeartbeats 1200000 in
/-- The actual B42 target is one of the three sources in the selected
individual-return table.  This uses equality of Apéry values and not an
identification of the selected anchor with the actual source. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_trichotomy
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let e := branchBInactiveReindex R
    let r := (branchBActualExceptionalRoutingSource P R x).val
    r = gridResidue P.M.base e 0 0 ∨
      r = gridResidue P.M.base e (c1 R - S.depth) 0 ∨
      r = gridResidue P.M.base e (r31 R - S.depth) (r32 R) := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let H := routingH B e
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let I := returnIdeal H S.n
  let r := (branchBActualExceptionalRoutingSource P R x).val
  let s := (branchBActualExceptionalNormalizedSource P R x).val
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hprov := branchB_actualZeroEdgeBirth_individual_return_source
    R hB x hsx hbirth
  have hmin : I.IsMinimalGenerator s := by
    dsimp [I, H, B, e]
    rw [branchBRoutingH_eq_normalizedH R]
    simpa [S, s] using hprov.2.2.2.1
  have hpacket := branchB_actualExceptional_source_packet P R x
  have hsfinal :
      (routingI B e).aperyRepresentative a r = s := by
    simpa [B, e, a, r, s] using hpacket.2.2.2.1.symm
  have hsr : (s : ZMod a) = r := by
    rw [← hsfinal]
    exact (routingI B e).aperyRepresentative_mod a r
  have hsH : s ∈ H.asRelativeIdeal := hmin.1.1
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hsH
  obtain ⟨sn, hsnH, hsneq⟩ := hsH
  obtain ⟨xa, yb, zc, hfac⟩ := routingH_factorization B e hsnH
  obtain ⟨i, t, k, hdom, hreduce⟩ := coherent_exists_reduction B e D yb zc
  have hsnfac :
      sn = i * b + t * c + (xa + k) * a := by
    dsimp [a, b, c, H] at hfac hreduce ⊢
    nlinarith only [hfac, hreduce]
  have hri : r = gridResidue B e i t := by
    rw [← hsr, hsneq]
    change ((sn : ℤ) : ZMod a) = gridResidue B e i t
    rw [hsnfac]
    simp only [gridResidue]
    push_cast
    simp only [ZMod.natCast_self, mul_zero, add_zero]
    rfl
  have hgen : H.IsGeneratedByThree a b c := by
    simpa [H, a, b, c] using
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1
  have hrep : I.aperyRepresentative a (gridResidue B e i t) = s := by
    rw [← hri, ← hsr]
    exact I.aperyRepresentative_eq_of_isMinimalGenerator a b c hgen hmin
  have hminRep :
      I.IsMinimalGenerator (I.aperyRepresentative a (gridResidue B e i t)) := by
    rw [hrep]
    exact hmin
  have htri := branchB_high_seam_individual_source_trichotomy
    R hB x hsx hbirth haxis i t hdom (by
      simpa [I, H, a, S, B, e] using hminRep)
  rcases htri with hO | hU | hF
  · left
    change r = gridResidue B e 0 0
    rw [hO.1, hO.2] at hri
    exact hri
  · right; left
    change r = gridResidue B e (c1 R - S.depth) 0
    rw [hU.1, hU.2] at hri
    exact hri
  · right; right
    change r = gridResidue B e (r31 R - S.depth) (r32 R)
    rw [hF.1, hF.2] at hri
    exact hri

/- The downstream F-support theorem remains non-load-bearing for B60.
set_option maxHeartbeats 1200000 in
/-- At the high-seam `F` target the actual source has support on the two
non-modulus generators.  In the historical inactive notation this is the
local `bc` support; under the frozen raw Branch-B coordinate API it is
`ActualSourceSupportRoute.ab`, since local `(a,b,c)` is raw `(C,A,B)`.

This theorem deliberately records that reindexing in its result rather than
silently identifying the two support enums. -/
theorem branchB_high_seam_target_F_forces_bc_support
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
    ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
      C.data.sourceX C.data.sourceY C.data.sourceZ := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let H := routingH B e
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let I := returnIdeal H S.n
  let r := (branchBActualExceptionalRoutingSource P R x).val
  let s := (branchBActualExceptionalNormalizedSource P R x).val
  let fi := r31 R - S.depth
  let ft := r32 R
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R at haxis
  change r = gridResidue B e fi ft at hF
  have hprov := branchB_actualZeroEdgeBirth_individual_return_source
    R hB x hsx hbirth
  have hmin : I.IsMinimalGenerator s := by
    dsimp [I, H, B, e]
    rw [branchBRoutingH_eq_normalizedH R]
    simpa [S, s] using hprov.2.2.2.1
  have hpacket := branchB_actualExceptional_source_packet P R x
  have hsfinal : (routingI B e).aperyRepresentative a r = s := by
    simpa [B, e, a, r, s] using hpacket.2.2.2.1.symm
  have hsr : (s : ZMod a) = r := by
    rw [← hsfinal]
    exact (routingI B e).aperyRepresentative_mod a r
  have hgen : H.IsGeneratedByThree a b c := by
    simpa [H, a, b, c] using
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1
  have hrep : I.aperyRepresentative a r = s := by
    rw [← hsr]
    exact I.aperyRepresentative_eq_of_isMinimalGenerator a b c hgen hmin
  have hmaps := branchB_inactive_coherent_coefficients R
  dsimp only [D, B, e] at hmaps
  obtain ⟨h12, h13, _h21, _h23, _h31, _h32⟩ := hmaps
  have hc2map : L5A2C4A.c2 B e = c1 R := by
    simpa [B, e] using branchB_inactive_coherent_c2 R
  have hc3map : L5A2C4A.c3 B e = c2 R := by
    simpa [B, e] using branchB_inactive_coherent_c3 R
  have hdomF : L5A2C4OR5.HerzogLShapeDomain D fi ft := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    rw [hc2map, hc3map, h12, h13]
    have hdlt := branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
    have hsum1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
    have hsum2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    refine ⟨?_, ?_, Or.inl ?_⟩ <;> dsimp [fi, ft] <;> omega
  have hformula := branchB_high_seam_individual_height_formula
    R hB x hsx hbirth haxis fi ft hdomF
  have hr32pos : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hdlt := branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
    R hB x hsx hbirth haxis
  have hheight :
      branchBHighSeamIndividualHeight R S.coordinate.j.toNat
        S.depth fi ft = 0 := by
    simp [branchBHighSeamIndividualHeight, fi, ft] <;> omega
  have hcanon := herzogLShapeCanonicality B e D fi ft hdomF
  have hrepValue : s = fi * b + ft * c := by
    have hrepF : I.aperyRepresentative a (gridResidue B e fi ft) = s := by
      rw [← hF]
      exact hrep
    have hformulaF : I.aperyRepresentative a (gridResidue B e fi ft) =
        physicalAlpha B e (gridResidue B e fi ft) := by
      simpa [S, B, e, hheight] using hformula
    calc
      s = I.aperyRepresentative a (gridResidue B e fi ft) := hrepF.symm
      _ = physicalAlpha B e (gridResidue B e fi ft) := hformulaF
      _ = (normalizedGrid B e 0 fi ft : ℤ) := hcanon.symm
      _ = fi * b + ft * c := by simp [normalizedGrid, b, c]
  have hsourceValue : C.data.sourceValue = fi * b + ft * c := by
    have hsC : (C.data.sourceValue : ℤ) = s := by
      simpa [C, s] using hprov.2.2.2.2.1
    have hcast : (C.data.sourceValue : ℤ) =
        ((fi * b + ft * c : ℕ) : ℤ) := by
      simpa using hsC.trans hrepValue
    exact_mod_cast hcast
  have hsourceFac := C.data.source_factorization
  have hAeq : normalizedA R = b := by
    simpa [b, B, e] using (branchB_inactive_routingB_eq_normalizedA R).symm
  have hBeq : normalizedB R = c := by
    simpa [c, B, e] using (branchB_inactive_routingC_eq_normalizedB R).symm
  have hCeq : normalizedC R = a := by
    simpa [a, B, e] using (branchB_inactive_routingA_eq_normalizedC R).symm
  rw [hsourceValue, hAeq, hBeq, hCeq] at hsourceFac
  have haH : a ∈ H := by
    exact (NumericalSemigroup.mem_generatedByThree_iff hgen).2
      (AddSubmonoid.subset_closure (by simp [a]))
  have hbH : b ∈ H := by simpa [H, b] using routingHB B e
  have hcH : c ∈ H := by simpa [H, c] using routingHC B e
  have hz0 : C.data.sourceZ = 0 := by
    by_contra hz
    have hzpos : 0 < C.data.sourceZ := Nat.pos_of_ne_zero hz
    let rest := C.data.sourceX * b + C.data.sourceY * c +
      (C.data.sourceZ - 1) * a
    have hrestH : rest ∈ H := by
      dsimp [rest]
      exact H.add_mem (H.add_mem
        (H.toAddSubmonoid.nsmul_mem hbH C.data.sourceX)
        (H.toAddSubmonoid.nsmul_mem hcH C.data.sourceY))
        (H.toAddSubmonoid.nsmul_mem haH (C.data.sourceZ - 1))
    have hrestI : (rest : ℤ) ∈ H.asRelativeIdeal :=
      (NumericalSemigroup.mem_asRelativeIdeal_iff H rest).2
        ⟨rest, hrestH, rfl⟩
    have hambient :
        H.asRelativeIdeal.aperyRepresentative a r = fi * b + ft * c := by
      change physicalAlpha B e r = _
      rw [hF]
      calc
        physicalAlpha B e (gridResidue B e fi ft) =
            (normalizedGrid B e 0 fi ft : ℤ) := hcanon.symm
        _ = fi * b + ft * c := by simp [normalizedGrid, b, c]
    have hnot := H.asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem a r
    apply hnot
    rw [hambient]
    convert hrestI using 1
    dsimp [rest]
    push_cast
    have hzsplit : C.data.sourceZ =
        (C.data.sourceZ - 1) + 1 := by omega
    rw [hzsplit, Nat.add_mul] at hsourceFac
    omega
  have hx0 : C.data.sourceX ≠ 0 := by
    intro hx
    have hrel : fi * normalizedA R =
        (C.data.sourceY - ft) * normalizedB R +
          0 * normalizedC R := by
      rw [hAeq, hBeq, hCeq]
      simp only [zero_mul, add_zero]
      rw [hx, hz0] at hsourceFac
      simp only [zero_mul, add_zero] at hsourceFac
      have htle : ft ≤ C.data.sourceY := by
        have hfipos : 0 < fi := by omega
        have hbpos : 0 < b := by
          rw [← hAeq]
          have hscale := L5A2B4AR3.normalizedWeight_scale
            P.M.base (R.reindex 0)
          have hweight := L2B.weights_positive P.M.base (R.reindex 0)
          change 0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex 0)
          nlinarith
        have hprod : 0 < fi * b := Nat.mul_pos hfipos hbpos
        omega
      rw [Nat.sub_mul]
      omega
    have hfi : 0 < fi := by omega
    have hminA := branchB_normalizedA_relation_min R fi
      (C.data.sourceY - ft) 0 hfi hrel
    have hsum1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
    omega
  have hy0 : C.data.sourceY ≠ 0 := by
    intro hy
    have hrel : ft * normalizedB R =
        (C.data.sourceX - fi) * normalizedA R +
          0 * normalizedC R := by
      rw [hAeq, hBeq, hCeq]
      simp only [zero_mul, add_zero]
      rw [hy, hz0] at hsourceFac
      simp only [zero_mul, add_zero] at hsourceFac
      have hile : fi ≤ C.data.sourceX := by
        have hftpos : 0 < ft := hr32pos
        have hcpos : 0 < c := by
          rw [← hBeq]
          have hscale := L5A2B4AR3.normalizedWeight_scale
            P.M.base (R.reindex 1)
          have hweight := L2B.weights_positive P.M.base (R.reindex 1)
          change 0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex 1)
          nlinarith
        have hprod : 0 < ft * c := Nat.mul_pos hftpos hcpos
        omega
      rw [Nat.sub_mul]
      omega
    have hminB := branchB_normalizedB_relation_min R ft
      (C.data.sourceX - fi) 0 hr32pos hrel
    have hsum2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    omega
  exact ⟨hx0, hy0, hz0⟩

-/

/-! ### B57: inverse-grid localization -/

/-- In the frozen inactive chart, the unique preimage of the origin under
the `b`/`c` diamond is the inner notch `(p-1,q-1)`.  This is cancellation in
the residue group only; it does not cancel membership in an ideal. -/
theorem branchB_grid_bc_preimage_origin_eq_inner_notch
    (R : SectorBCriticalRoleBranchB P)
    (A : ZMod (routingA P.M.base (branchBInactiveReindex R)))
    (h : (routingData P.M.base (branchBInactiveReindex R)).b
          ((routingData P.M.base (branchBInactiveReindex R)).c A) = 0) :
    A = gridResidue P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R - 1) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let G := routingData B e
  let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
  have hp : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hq : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hpi : r31 R - 1 + 1 = r31 R := by omega
  have hqi : r32 R - 1 + 1 = r32 R := by omega
  have hAeq : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hBeq : routingB B e = normalizedA R := by
    simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hCeq : routingC B e = normalizedB R := by
    simpa [B, e] using branchB_inactive_routingC_eq_normalizedB R
  have htarget0 : G.branchTarget A0 = 0 := by
    rw [routing_branchTarget_gridResidue, hpi, hqi]
    simp only [gridResidue]
    rw [hAeq, hBeq, hCeq]
    have hrel : c3 R * normalizedC R =
        r31 R * normalizedA R + r32 R * normalizedB R := by
      simpa using
        (branchB_actual_herzog_coordinates R).normalized_relations.2.2
    have hz : ((r31 R * normalizedA R + r32 R * normalizedB R : ℕ) :
        ZMod (normalizedC R)) = 0 := by
      rw [← hrel]
      simp
    exact_mod_cast hz
  change A = A0
  apply G.branchTarget_injective
  have htargetA : G.branchTarget A = 0 := by
    change G.c (G.b A) = 0
    rw [← G.commute A]
    exact h
  exact htargetA.trans htarget0.symm

/-! ### B61: the high-seam F diamond and its complementary inner notch -/

/-- Exact inverse diamond for the high-seam `F` alternative. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_F_inverse_diamond
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let G := routingData P.M.base e
    let A := gridResidue P.M.base e
      (r31 R - S.depth - 1) (r32 R - 1)
    let Bb := gridResidue P.M.base e
      (r31 R - S.depth) (r32 R - 1)
    let Cc := gridResidue P.M.base e
      (r31 R - S.depth - 1) (r32 R)
    let F := gridResidue P.M.base e
      (r31 R - S.depth) (r32 R)
    x.val.val.val = A ∧ G.branchTarget x.val.val.val = F ∧
      G.b A = Bb ∧ G.c A = Cc ∧ G.b (G.c A) = F := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let G := routingData B e
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  let Bb := gridResidue B e (r31 R - S.depth) (r32 R - 1)
  let Cc := gridResidue B e (r31 R - S.depth - 1) (r32 R)
  let F := gridResidue B e (r31 R - S.depth) (r32 R)
  change (branchBActualExceptionalRoutingSource P R x).val = F at hF
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hi : r31 R - S.depth - 1 + 1 = r31 R - S.depth := by omega
  have hj : r32 R - 1 + 1 = r32 R := by omega
  have htargetA : G.branchTarget A = F := by
    simpa [A, F, hi, hj] using
      (routing_branchTarget_gridResidue B e
        (r31 R - S.depth - 1) (r32 R - 1))
  have htargetX : G.branchTarget x.val.val.val = F :=
    hbirth.2.2.2.2.2.2.trans hF
  have hbase : x.val.val.val = A := by
    exact G.b.injective (G.c.injective (htargetX.trans htargetA.symm))
  have hb : G.b A = Bb := by
    simpa [A, Bb, hi] using
      (routing_b_gridResidue B e
        (r31 R - S.depth - 1) (r32 R - 1))
  have hc : G.c A = Cc := by
    simpa [A, Cc, hj] using
      (routing_c_gridResidue B e
        (r31 R - S.depth - 1) (r32 R - 1))
  have hbc : G.b (G.c A) = F := by
    rw [G.commute A]
    exact htargetA
  exact ⟨hbase, htargetX, hb, hc, hbc⟩

/-- Canonical geometry and zero ambient carries for the high-seam `F`
diamond, together with the translation to the inner notch. -/
private theorem branchB_high_seam_target_F_canonical_and_carries
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
    let Bb := gridResidue B e (r31 R - S.depth) (r32 R - 1)
    let Cc := gridResidue B e (r31 R - S.depth - 1) (r32 R)
    let F := gridResidue B e (r31 R - S.depth) (r32 R)
    let N := gridResidue B e (r31 R - 1) (r32 R - 1)
    IsCanonicalTailGridPoint B e (r31 R - S.depth - 1) (r32 R - 1) ∧
      IsCanonicalTailGridPoint B e (r31 R - S.depth) (r32 R - 1) ∧
      IsCanonicalTailGridPoint B e (r31 R - S.depth - 1) (r32 R) ∧
      IsCanonicalTailGridPoint B e (r31 R - S.depth) (r32 R) ∧
      IsCanonicalTailGridPoint B e (r31 R - 1) (r32 R - 1) ∧
      branchBPrefixAmbientU R A = 0 ∧ branchBPrefixAmbientV R A = 0 ∧
      A + routingB B e = Bb ∧ A + routingC B e = Cc ∧
      physicalAlpha B e N = physicalAlpha B e A +
        (S.depth : ℤ) * routingB B e := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  let Bb := gridResidue B e (r31 R - S.depth) (r32 R - 1)
  let Cc := gridResidue B e (r31 R - S.depth - 1) (r32 R)
  let F := gridResidue B e (r31 R - S.depth) (r32 R)
  let N := gridResidue B e (r31 R - 1) (r32 R - 1)
  let D := branchB_inactive_coherentHerzogData R
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hdpos : 0 < S.depth := S.depth_pos
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hr21 : 0 < r21 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hdomain (i j : ℕ) (hi : i < r31 R) (hj : j < c2 R) :
      L5A2C4OR5.HerzogLShapeDomain D i j := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change i < L5A2C4A.c2 B e ∧ j < L5A2C4A.c3 B e ∧
      (i < L5A2C4D.cr12 D ∨ j < L5A2C4D.cr13 D)
    dsimp only [B, e]
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
    have hmap := branchB_inactive_coherent_coefficients R
    dsimp only [D, B, e] at hmap
    obtain ⟨h12, _h13, _h21, _h23, _h31, _h32⟩ := hmap
    rw [h12]
    exact ⟨by omega, hj, Or.inl hi⟩
  have hAi : r31 R - S.depth - 1 < r31 R := by omega
  have hFi : r31 R - S.depth < r31 R := Nat.sub_lt hr31 hdpos
  have hAj : r32 R - 1 < c2 R := by omega
  have hFj : r32 R < c2 R := by omega
  have hNi : r31 R - 1 < r31 R := by omega
  have hAcanon := herzogLShapeCanonicality B e D _ _ (hdomain _ _ hAi hAj)
  have hBcanon := herzogLShapeCanonicality B e D _ _ (hdomain _ _ hFi hAj)
  have hCcanon := herzogLShapeCanonicality B e D _ _ (hdomain _ _ hAi hFj)
  have hFcanon := herzogLShapeCanonicality B e D _ _ (hdomain _ _ hFi hFj)
  have hNcanon := herzogLShapeCanonicality B e D _ _ (hdomain _ _ hNi hAj)
  have hi : r31 R - S.depth - 1 + 1 = r31 R - S.depth := by omega
  have hj : r32 R - 1 + 1 = r32 R := by omega
  have hAB : A + routingB B e = Bb := by
    simpa [A, Bb, hi] using
      (gridResidue_add_b B e (r31 R - S.depth - 1) (r32 R - 1)).symm
  have hAC : A + routingC B e = Cc := by
    simpa [A, Cc, hj] using
      (gridResidue_add_c B e (r31 R - S.depth - 1) (r32 R - 1)).symm
  have halpha (i j : ℕ) (hc : IsCanonicalTailGridPoint B e i j) :
      branchBPrefixAlpha R (gridResidue B e i j) = normalizedGrid B e 0 i j := by
    have hlift :=
      (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e i j).mp hc
    have hg := normalizedGrid_eq_physicalAlpha_add B e 0 i j
    rw [hlift] at hg
    simp only [zero_add, Nat.cast_zero, mul_zero] at hg
    simpa [branchBPrefixAlpha, physicalAlpha, B, e] using hg.symm
  have huStep := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e) A
  change branchBPrefixAlpha R A + routingB B e =
    branchBPrefixAlpha R (A + routingB B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientU R A at huStep
  rw [hAB, halpha _ _ hAcanon, halpha _ _ hBcanon] at huStep
  have hu : branchBPrefixAmbientU R A = 0 := by
    have huNat :
        normalizedGrid B e 0 (r31 R - S.depth - 1) (r32 R - 1) +
            routingB B e =
          normalizedGrid B e 0 (r31 R - S.depth) (r32 R - 1) +
            routingA B e * branchBPrefixAmbientU R A := by
      exact_mod_cast huStep
    dsimp [normalizedGrid] at huNat
    have hprod : routingA B e * branchBPrefixAmbientU R A = 0 := by
      have hbase :
          (r31 R - S.depth - 1) * routingB B e + routingB B e =
            (r31 R - S.depth) * routingB B e := by
        calc
          _ = (r31 R - S.depth - 1 + 1) * routingB B e := by ring
          _ = _ := by rw [hi]
      omega
    exact (Nat.mul_eq_zero.mp hprod).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  have hvStep := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) A
  change branchBPrefixAlpha R A + routingC B e =
    branchBPrefixAlpha R (A + routingC B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientV R A at hvStep
  rw [hAC, halpha _ _ hAcanon, halpha _ _ hCcanon] at hvStep
  have hv : branchBPrefixAmbientV R A = 0 := by
    have hvNat :
        normalizedGrid B e 0 (r31 R - S.depth - 1) (r32 R - 1) +
            routingC B e =
          normalizedGrid B e 0 (r31 R - S.depth - 1) (r32 R) +
            routingA B e * branchBPrefixAmbientV R A := by
      exact_mod_cast hvStep
    dsimp [normalizedGrid] at hvNat
    have hprod : routingA B e * branchBPrefixAmbientV R A = 0 := by
      have hbase :
          (r32 R - 1) * routingC B e + routingC B e =
            r32 R * routingC B e := by
        calc
          _ = (r32 R - 1 + 1) * routingC B e := by ring
          _ = _ := by rw [hj]
      omega
    exact (Nat.mul_eq_zero.mp hprod).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  have hAlphaA := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
    B e (r31 R - S.depth - 1) (r32 R - 1) hAcanon
  have hAlphaN := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
    B e (r31 R - 1) (r32 R - 1) hNcanon
  have hcoord : r31 R - S.depth - 1 + S.depth = r31 R - 1 := by omega
  have hAN : physicalAlpha B e N = physicalAlpha B e A +
      (S.depth : ℤ) * routingB B e := by
    change physicalAlpha B e (gridResidue B e (r31 R - 1) (r32 R - 1)) =
      physicalAlpha B e
          (gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)) +
        (S.depth : ℤ) * routingB B e
    rw [hAlphaN, hAlphaA]
    exact_mod_cast (show normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) =
        normalizedGrid B e 0 (r31 R - S.depth - 1) (r32 R - 1) +
          S.depth * routingB B e by
      simp only [normalizedGrid, zero_mul, zero_add]
      rw [← hcoord]
      ring)
  exact ⟨hAcanon, hBcanon, hCcanon, hFcanon, hNcanon,
    hu, hv, hAB, hAC, hAN⟩

/-- The selected nonprincipal return has heights `j,j,j,0` on the exact
high-seam `F` diamond. -/
theorem branchB_high_seam_target_F_selected_height_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let I := returnIdeal (routingH B e) S.n
    let j := S.coordinate.j.toNat
    letI : NeZero (routingA B e) :=
      ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    I.aperyRepresentative (routingA B e)
        (gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)) =
          physicalAlpha B e
            (gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)) +
              (routingA B e : ℤ) * j ∧
      I.aperyRepresentative (routingA B e)
        (gridResidue B e (r31 R - S.depth) (r32 R - 1)) =
          physicalAlpha B e
            (gridResidue B e (r31 R - S.depth) (r32 R - 1)) +
              (routingA B e : ℤ) * j ∧
      I.aperyRepresentative (routingA B e)
        (gridResidue B e (r31 R - S.depth - 1) (r32 R)) =
          physicalAlpha B e
            (gridResidue B e (r31 R - S.depth - 1) (r32 R)) +
              (routingA B e : ℤ) * j ∧
      I.aperyRepresentative (routingA B e)
        (gridResidue B e (r31 R - S.depth) (r32 R)) =
          physicalAlpha B e
            (gridResidue B e (r31 R - S.depth) (r32 R)) := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let I := returnIdeal (routingH B e) S.n
  let j := S.coordinate.j.toNat
  let D := branchB_inactive_coherentHerzogData R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R at haxis
  have hg := branchB_high_seam_target_F_canonical_and_carries
    R hB x hsx hbirth haxis hF
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hr21 : 0 < r21 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hdom (i t : ℕ) (hi : i < r31 R) (ht : t < c2 R) :
      L5A2C4OR5.HerzogLShapeDomain D i t := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change i < L5A2C4A.c2 B e ∧ t < L5A2C4A.c3 B e ∧
      (i < L5A2C4D.cr12 D ∨ t < L5A2C4D.cr13 D)
    dsimp only [B, e]
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
    have hmap := branchB_inactive_coherent_coefficients R
    dsimp only [D, B, e] at hmap
    obtain ⟨h12, _h13, _h21, _h23, _h31, _h32⟩ := hmap
    rw [h12]
    exact ⟨by omega, ht, Or.inl hi⟩
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hdpos : 0 < S.depth := S.depth_pos
  have hA := branchB_high_seam_individual_height_formula R hB x hsx hbirth haxis
    (r31 R - S.depth - 1) (r32 R - 1) (hdom _ _ (by omega) (by omega))
  have hBb := branchB_high_seam_individual_height_formula R hB x hsx hbirth haxis
    (r31 R - S.depth) (r32 R - 1) (hdom _ _ (by omega) (by omega))
  have hCc := branchB_high_seam_individual_height_formula R hB x hsx hbirth haxis
    (r31 R - S.depth - 1) (r32 R) (hdom _ _ (by omega) (by omega))
  have hFh := branchB_high_seam_individual_height_formula R hB x hsx hbirth haxis
    (r31 R - S.depth) (r32 R) (hdom _ _ (by omega) (by omega))
  have hj0 : (0 : ℤ) ≤ S.coordinate.j := by omega
  have hj : S.coordinate.j = (j : ℤ) := (Int.toNat_of_nonneg hj0).symm
  have htPred : r32 R - 1 < r32 R := by omega
  have hAlo : r31 R - S.depth - 1 < c1 R - S.depth := by omega
  have hBlo : r31 R - S.depth < c1 R - S.depth := by omega
  have hClo : r31 R - S.depth - 1 < r31 R - S.depth := by omega
  have hvals :
      branchBHighSeamIndividualHeight R j S.depth
          (r31 R - S.depth - 1) (r32 R - 1) = j ∧
      branchBHighSeamIndividualHeight R j S.depth
          (r31 R - S.depth) (r32 R - 1) = j ∧
      branchBHighSeamIndividualHeight R j S.depth
          (r31 R - S.depth - 1) (r32 R) = j ∧
      branchBHighSeamIndividualHeight R j S.depth
          (r31 R - S.depth) (r32 R) = 0 := by
    simp [branchBHighSeamIndividualHeight, htPred, hAlo, hBlo, hClo]
  change I.aperyRepresentative (routingA B e)
      (gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)) =
    physicalAlpha B e
        (gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)) +
      (routingA B e : ℤ) *
        branchBHighSeamIndividualHeight R j S.depth
          (r31 R - S.depth - 1) (r32 R - 1) at hA
  change I.aperyRepresentative (routingA B e)
      (gridResidue B e (r31 R - S.depth) (r32 R - 1)) =
    physicalAlpha B e
        (gridResidue B e (r31 R - S.depth) (r32 R - 1)) +
      (routingA B e : ℤ) *
        branchBHighSeamIndividualHeight R j S.depth
          (r31 R - S.depth) (r32 R - 1) at hBb
  change I.aperyRepresentative (routingA B e)
      (gridResidue B e (r31 R - S.depth - 1) (r32 R)) =
    physicalAlpha B e
        (gridResidue B e (r31 R - S.depth - 1) (r32 R)) +
      (routingA B e : ℤ) *
        branchBHighSeamIndividualHeight R j S.depth
          (r31 R - S.depth - 1) (r32 R) at hCc
  change I.aperyRepresentative (routingA B e)
      (gridResidue B e (r31 R - S.depth) (r32 R)) =
    physicalAlpha B e (gridResidue B e (r31 R - S.depth) (r32 R)) +
      (routingA B e : ℤ) *
        branchBHighSeamIndividualHeight R j S.depth
          (r31 R - S.depth) (r32 R) at hFh
  rw [hvals.1] at hA
  rw [hvals.2.1] at hBb
  rw [hvals.2.2.1] at hCc
  rw [hvals.2.2.2] at hFh
  norm_num at hFh
  exact ⟨hA, hBb, hCc, hFh⟩

/-- Final-height packet on the actual high-seam `F` diamond. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_F_final_height_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
    let K := physicalHeight B e A
    eta B e (r31 R - S.depth - 1) (r32 R - 1) = K ∧
      eta B e (r31 R - S.depth) (r32 R - 1) = K ∧
      eta B e (r31 R - S.depth - 1) (r32 R) = K ∧ 0 < K := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let G := routingData B e
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  let Bb := gridResidue B e (r31 R - S.depth) (r32 R - 1)
  let Cc := gridResidue B e (r31 R - S.depth - 1) (r32 R)
  let F := gridResidue B e (r31 R - S.depth) (r32 R)
  let K := physicalHeight B e A
  have hgeom := branchB_high_seam_target_F_canonical_and_carries
    R hB x hsx hbirth haxis hF
  have hdiamond := branchB_actualZeroEdgeBirth_high_seam_target_F_inverse_diamond
    R hB x hsx hbirth haxis hF
  have hbase : x.val.val.val = A := by
    simpa [S, B, e, A] using hdiamond.1
  have hbranch : G.IsBranch A := by
    rw [← hbase]
    exact hbirth.2.2.2.2.2.1
  have hAB : A + routingB B e = Bb := hgeom.2.2.2.2.2.2.2.1
  have hAC : A + routingC B e = Cc := hgeom.2.2.2.2.2.2.2.2.1
  have hbStep := branchB_final_height_step_b_with_ambient_carry R A
  change physicalHeight B e A + branchBPrefixAmbientU R A =
    physicalHeight B e (A + routingB B e) + G.u A at hbStep
  rw [hgeom.2.2.2.2.2.1, hAB, hbranch.1] at hbStep
  have hBbHeight : physicalHeight B e Bb = K := by simpa [K] using hbStep.symm
  have hcStep := branchB_final_height_step_c_with_ambient_carry R A
  change physicalHeight B e A + branchBPrefixAmbientV R A =
    physicalHeight B e (A + routingC B e) + G.v A at hcStep
  rw [hgeom.2.2.2.2.2.2.1, hAC, hbranch.2] at hcStep
  have hCcHeight : physicalHeight B e Cc = K := by simpa [K] using hcStep.symm
  have hselected := branchB_high_seam_target_F_selected_height_packet
    R hB x hsx hbirth haxis hF
  let I := returnIdeal (routingH B e) S.n
  have hselectedF : I.aperyRepresentative (routingA B e) F =
      physicalAlpha B e F := by
    simpa [S, B, e, I, F] using hselected.2.2.2
  let s := (branchBActualExceptionalNormalizedSource P R x).val
  let r := (branchBActualExceptionalRoutingSource P R x).val
  have hprov := branchB_actualZeroEdgeBirth_individual_return_source
    R hB x hsx hbirth
  have hmin : I.IsMinimalGenerator s := by
    dsimp [I, B, e]
    rw [branchBRoutingH_eq_normalizedH R]
    simpa [S, s] using hprov.2.2.2.1
  have hpacket := branchB_actualExceptional_source_packet P R x
  have hsr : (s : ZMod (routingA B e)) = r := by
    have hfinalRep : s = (routingI B e).aperyRepresentative
        (routingA B e) r := by simpa [B, e, r, s] using hpacket.2.2.2.1
    rw [hfinalRep]
    exact (routingI B e).aperyRepresentative_mod (routingA B e) r
  have hgen : (routingH B e).IsGeneratedByThree
      (routingA B e) (routingB B e) (routingC B e) := by
    simpa using (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1
  have hselectedRep : I.aperyRepresentative (routingA B e) r = s := by
    rw [← hsr]
    exact I.aperyRepresentative_eq_of_isMinimalGenerator
      (routingA B e) (routingB B e) (routingC B e) hgen hmin
  have hfinalRep : (routingI B e).aperyRepresentative (routingA B e) r = s := by
    simpa [B, e, r, s] using hpacket.2.2.2.1.symm
  have hFzero : physicalHeight B e F = 0 := by
    have hspec := physicalHeight_spec B e F
    change (routingI B e).aperyRepresentative (routingA B e) F =
      physicalAlpha B e F + (routingA B e : ℤ) * physicalHeight B e F at hspec
    have hrF : r = F := by simpa [r, F, S, B, e] using hF
    rw [← hrF, hfinalRep, ← hselectedRep, hrF, hselectedF] at hspec
    have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
    have hz : (routingA B e : ℤ) * physicalHeight B e F = 0 := by linarith
    exact_mod_cast (mul_eq_zero.mp hz |>.resolve_left (ne_of_gt ha))
  have hsourceF : G.IsSource F := by
    have hs := (branchBActualExceptionalRoutingSource P R x).property
    change G.IsSource r at hs
    have hrF : r = F := by simpa [r, F, S, B, e] using hF
    simpa [hrF] using hs
  have hcross : 0 < G.u (G.c A) := by
    have hst : L5A2C4I.ResidueData.SourceTargetBranch G A := by
      refine ⟨hbranch, ?_⟩
      have ht : G.branchTarget A = F := by
        rw [← hbase]
        simpa [S, B, e, F] using hdiamond.2.1
      simpa [ht] using hsourceF
    exact (L5A2C4I.ResidueData.sourceTargetBranch_iff_positive_cross G).1 hst |>.2.2
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hCF : Cc + routingB B e = F := by
    have hi : r31 R - S.depth - 1 + 1 = r31 R - S.depth := by omega
    simpa [Cc, F, hi] using
      (gridResidue_add_b B e (r31 R - S.depth - 1) (r32 R)).symm
  have hAmbientC : branchBPrefixAmbientU R Cc = 0 := by
    have hstep := (routingH B e).asRelativeIdeal.apery_step_eq
      (routingA B e) (routingB B e) (routingHB B e) Cc
    change branchBPrefixAlpha R Cc + routingB B e =
      branchBPrefixAlpha R (Cc + routingB B e) +
        (routingA B e : ℤ) * branchBPrefixAmbientU R Cc at hstep
    have hAlphaC := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e (r31 R - S.depth - 1) (r32 R) hgeom.2.2.1
    have hAlphaF := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e (r31 R - S.depth) (r32 R) hgeom.2.2.2.1
    have hprefix (i t : ℕ)
        (hc : IsCanonicalTailGridPoint B e i t) :
        branchBPrefixAlpha R (gridResidue B e i t) =
          normalizedGrid B e 0 i t := by
      simpa [branchBPrefixAlpha, physicalAlpha, B, e] using
        (branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical B e i t hc)
    rw [hCF, hprefix _ _ hgeom.2.2.1, hprefix _ _ hgeom.2.2.2.1] at hstep
    have hnat :
        normalizedGrid B e 0 (r31 R - S.depth - 1) (r32 R) + routingB B e =
          normalizedGrid B e 0 (r31 R - S.depth) (r32 R) +
            routingA B e * branchBPrefixAmbientU R Cc := by exact_mod_cast hstep
    dsimp [normalizedGrid] at hnat
    have hprod : routingA B e * branchBPrefixAmbientU R Cc = 0 := by
      have hi : r31 R - S.depth - 1 + 1 = r31 R - S.depth := by omega
      have hb :
          (r31 R - S.depth - 1) * routingB B e + routingB B e =
            (r31 R - S.depth) * routingB B e := by
        calc
          _ = (r31 R - S.depth - 1 + 1) * routingB B e := by ring
          _ = _ := by rw [hi]
      omega
    exact (Nat.mul_eq_zero.mp hprod).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  have hcrossStep := branchB_final_height_step_b_with_ambient_carry R Cc
  change physicalHeight B e Cc + branchBPrefixAmbientU R Cc =
    physicalHeight B e (Cc + routingB B e) + G.u Cc at hcrossStep
  rw [hAmbientC, hCF, hFzero] at hcrossStep
  have hcA : G.c A = Cc := by
    change A + routingC B e = Cc
    exact hgeom.2.2.2.2.2.2.2.2.1
  rw [hcA] at hcross
  have hCcPos : 0 < physicalHeight B e Cc := by omega
  have hKpos : 0 < K := by
    rw [← hCcHeight]
    exact hCcPos
  have hAeta := eta_eq_physicalHeight_of_isCanonical B e _ _ hgeom.1
  have hBeta := eta_eq_physicalHeight_of_isCanonical B e _ _ hgeom.2.1
  have hCeta := eta_eq_physicalHeight_of_isCanonical B e _ _ hgeom.2.2.1
  change eta B e (r31 R - S.depth - 1) (r32 R - 1) =
    physicalHeight B e A at hAeta
  change eta B e (r31 R - S.depth) (r32 R - 1) =
    physicalHeight B e Bb at hBeta
  change eta B e (r31 R - S.depth - 1) (r32 R) =
    physicalHeight B e Cc at hCeta
  exact ⟨by simpa [K] using hAeta,
    hBeta.trans hBbHeight, hCeta.trans hCcHeight, hKpos⟩

/-- At the F-diamond base the prefix envelope is strictly above the final
positive height. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_F_prefix_A_gt_final
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
    physicalHeight B e A < branchBPrefixHeight R x hsx A := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  let Bb := gridResidue B e (r31 R - S.depth) (r32 R - 1)
  let Cc := gridResidue B e (r31 R - S.depth - 1) (r32 R)
  let Gminus := branchBActualPrefixRoutingData R x hsx
  have hgeom := branchB_high_seam_target_F_canonical_and_carries
    R hB x hsx hbirth haxis hF
  have hfinal := branchB_actualZeroEdgeBirth_high_seam_target_F_final_height_packet
    R hB x hsx hbirth haxis hF
  let K := physicalHeight B e A
  have hBbHeight : physicalHeight B e Bb = K := by
    have h := eta_eq_physicalHeight_of_isCanonical B e _ _ hgeom.2.1
    change eta B e (r31 R - S.depth) (r32 R - 1) =
      physicalHeight B e Bb at h
    exact h.symm.trans hfinal.2.1
  have hCcHeight : physicalHeight B e Cc = K := by
    have h := eta_eq_physicalHeight_of_isCanonical B e _ _ hgeom.2.2.1
    change eta B e (r31 R - S.depth - 1) (r32 R) =
      physicalHeight B e Cc at h
    exact h.symm.trans hfinal.2.2.1
  have hAle := branchB_finalHeight_le_prefixHeight R x hsx A
  change K ≤ branchBPrefixHeight R x hsx A at hAle
  by_contra hnot
  have hPAle : branchBPrefixHeight R x hsx A ≤ K := le_of_not_gt hnot
  have hPA : branchBPrefixHeight R x hsx A = K := le_antisymm hPAle hAle
  have hBle := branchB_finalHeight_le_prefixHeight R x hsx Bb
  have hCle := branchB_finalHeight_le_prefixHeight R x hsx Cc
  have hPB : K ≤ branchBPrefixHeight R x hsx Bb := by rw [← hBbHeight]; exact hBle
  have hPC : K ≤ branchBPrefixHeight R x hsx Cc := by rw [← hCcHeight]; exact hCle
  have hb := branchB_prefix_height_step_b_with_ambient_carry R x hsx A
  change branchBPrefixHeight R x hsx A + branchBPrefixAmbientU R A =
    branchBPrefixHeight R x hsx (A + routingB B e) + Gminus.u A at hb
  rw [hPA, hgeom.2.2.2.2.2.1, hgeom.2.2.2.2.2.2.2.1] at hb
  change K = branchBPrefixHeight R x hsx Bb + Gminus.u A at hb
  have hu : Gminus.u A = 0 := by omega
  have hc := branchB_prefix_height_step_c_with_ambient_carry R x hsx A
  change branchBPrefixHeight R x hsx A + branchBPrefixAmbientV R A =
    branchBPrefixHeight R x hsx (A + routingC B e) + Gminus.v A at hc
  rw [hPA, hgeom.2.2.2.2.2.2.1, hgeom.2.2.2.2.2.2.2.2.1] at hc
  change K = branchBPrefixHeight R x hsx Cc + Gminus.v A at hc
  have hv : Gminus.v A = 0 := by omega
  have hdiamond := branchB_actualZeroEdgeBirth_high_seam_target_F_inverse_diamond
    R hB x hsx hbirth haxis hF
  have hbase : x.val.val.val = A := by
    simpa [S, B, e, A] using hdiamond.1
  apply hbirth.2.2.2.1
  rw [hbase]
  exact ⟨hu, hv⟩

/-- The principal candidate realizes the positive final height at the exact
F-diamond base; the equality comes from the strict prefix drop. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_F_principal_base_eq_final
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
    rawCandidate B e (actualPrincipalIndex B) A = physicalHeight B e A := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  let K := physicalHeight B e A
  let Q := actualPrincipalIndex B
  have hgeom := branchB_high_seam_target_F_canonical_and_carries
    R hB x hsx hbirth haxis hF
  have hfinal := branchB_actualZeroEdgeBirth_high_seam_target_F_final_height_packet
    R hB x hsx hbirth haxis hF
  have hKpos : 0 < K := hfinal.2.2.2
  have hheightMin := physicalHeight_eq_max_rawMinimum B e A
  have hmin : rawMinimum B e A = K := by
    change K = max 0 (rawMinimum B e A) at hheightMin
    omega
  let selector := currentSelector B e A
  have hspos : 0 < selector := currentSelector_pos B e A
  have hsvalue : rawCandidate B e selector A = K := by
    rw [rawCandidate_currentSelector B e A, hmin]
  obtain ⟨t, htpos, htle, htvalue⟩ :=
    branchB_candidate_reduce_to_first_principal_block R A hspos
  have htK : rawCandidate B e t A ≤ K := by rw [← hsvalue]; exact htvalue
  have htQ : t = Q := by
    by_contra hne
    have htlt : t < Q := Nat.lt_of_le_of_ne htle hne
    have hsub := (rawCandidate_threshold B e A htpos K).2 htK
    let z := normalizedGrid B e K
      (r31 R - S.depth - 1) (r32 R - 1)
    have hgrid := normalizedGrid_eq_physicalAlpha_add B e K
      (r31 R - S.depth - 1) (r32 R - 1)
    have hlift := (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e _ _).mp
      hgeom.1
    rw [hlift] at hgrid
    simp only [Nat.cast_zero, zero_add] at hgrid
    have hzH : (z : ℤ) ∈ (routingH B e).asRelativeIdeal := by
      rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨z, ?_, rfl⟩
      have haH : routingA B e ∈ routingH B e :=
        (NumericalSemigroup.mem_generatedByThree_iff
          (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
            (AddSubmonoid.subset_closure (by simp))
      have ha := (routingH B e).toAddSubmonoid.nsmul_mem
        haH K
      have hb := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e)
        (r31 R - S.depth - 1)
      have hc := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e)
        (r32 R - 1)
      simpa [z, normalizedGrid, nsmul_eq_mul, Nat.add_assoc] using
        (routingH B e).add_mem ((routingH B e).add_mem ha hb) hc
    have hret : (z : ℤ) ∈ returnIdeal (routingH B e) (t * routingM B e) := by
      rw [mem_returnIdeal_iff]
      refine ⟨hzH, ?_⟩
      have hzEq : (z : ℤ) = physicalAlpha B e A + routingA B e * K := by
        simpa [z, A] using hgrid
      rw [hzEq]
      exact hsub
    have hpref : (z : ℤ) ∈ branchBActualPrefixIdeal R x hsx := by
      change ∃ ell : ℕ, 0 < ell ∧ ell < actualPrincipalIndex B ∧
        (z : ℤ) ∈ returnIdeal (routingH B e) (ell * normalizedM B)
      refine ⟨t, htpos, htlt, ?_⟩
      simpa [routingM, normalizedM, B, e] using hret
    have hPrefixLe := branchB_prefixHeight_le_of_canonical_mem R x hsx
      (r31 R - S.depth - 1) (r32 R - 1) K hgeom.1 hpref
    have hstrict := branchB_actualZeroEdgeBirth_high_seam_target_F_prefix_A_gt_final
      R hB x hsx hbirth haxis hF
    change K < branchBPrefixHeight R x hsx A at hstrict
    exact (not_lt_of_ge hPrefixLe) hstrict
  have hQle : rawCandidate B e Q A ≤ K := by simpa [htQ] using htK
  have hQpos : 0 < Q := (actualPrincipalIndex_spec B).1
  have hKle : (K : ℤ) ≤ rawCandidate B e Q A := by
    rw [← hmin]
    exact rawMinimum_le B e A hQpos
  exact le_antisymm hQle hKle

/-- The selected individual return bounds the prefix height at the F base,
and hence also bounds its smaller final height. -/
theorem branchB_high_seam_target_F_prefix_A_le_selected
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
    branchBPrefixHeight R x hsx A ≤ S.coordinate.j.toNat ∧
      physicalHeight B e A ≤ S.coordinate.j.toNat := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  let j := S.coordinate.j.toNat
  let I := returnIdeal (routingH B e) S.n
  let z := normalizedGrid B e j (r31 R - S.depth - 1) (r32 R - 1)
  have hgeom := branchB_high_seam_target_F_canonical_and_carries
    R hB x hsx hbirth haxis hF
  have hselected := branchB_high_seam_target_F_selected_height_packet
    R hB x hsx hbirth haxis hF
  have hgrid := normalizedGrid_eq_physicalAlpha_add B e j
    (r31 R - S.depth - 1) (r32 R - 1)
  have hlift := (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e _ _).mp
    hgeom.1
  rw [hlift] at hgrid
  simp only [Nat.cast_zero, zero_add] at hgrid
  have hrep : I.aperyRepresentative (routingA B e) A = (z : ℤ) := by
    have hs : I.aperyRepresentative (routingA B e) A =
        physicalAlpha B e A + (routingA B e : ℤ) * j := by
      simpa [S, B, e, I, A, j] using hselected.1
    rw [hs]
    simpa [z, A] using hgrid.symm
  have hzI : (z : ℤ) ∈ I := by
    rw [← hrep]
    exact I.aperyRepresentative_mem (routingA B e) A
  have hpref : (z : ℤ) ∈ branchBActualPrefixIdeal R x hsx := by
    change ∃ ell : ℕ, 0 < ell ∧ ell < actualPrincipalIndex B ∧
      (z : ℤ) ∈ returnIdeal (routingH B e) (ell * normalizedM B)
    refine ⟨S.ell, S.ell_pos, S.ell_lt_principal, ?_⟩
    have hn : S.n = S.ell * normalizedM B := S.n_eq
    simpa [I, hn] using hzI
  have hPrefix := branchB_prefixHeight_le_of_canonical_mem R x hsx
    (r31 R - S.depth - 1) (r32 R - 1) j hgeom.1 hpref
  have hstrict := branchB_actualZeroEdgeBirth_high_seam_target_F_prefix_A_gt_final
    R hB x hsx hbirth haxis hF
  change physicalHeight B e A < branchBPrefixHeight R x hsx A at hstrict
  exact ⟨hPrefix, le_trans (Nat.le_of_lt hstrict) hPrefix⟩

/-- Exact Apéry and residue translation from the F base to the fixed inner
notch, at the complementary return index. -/
theorem branchB_high_seam_target_F_A_to_inner_notch_apery_translation
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let Q := actualPrincipalIndex B
    let k := Q - S.ell
    let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
    let N := gridResidue B e (r31 R - 1) (r32 R - 1)
    physicalAlpha B e N + (S.ell : ℤ) * routingM B e =
        physicalAlpha B e A +
          (S.coordinate.j.toNat : ℤ) * routingA B e ∧
      N - (k * routingM B e : ℕ) = A - (Q * routingM B e : ℕ) ∧
      physicalAlpha B e (N - (k * routingM B e : ℕ)) =
        physicalAlpha B e (A - (Q * routingM B e : ℕ)) := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Q := actualPrincipalIndex B
  let k := Q - S.ell
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  let N := gridResidue B e (r31 R - 1) (r32 R - 1)
  let j := S.coordinate.j.toNat
  change S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R at haxis
  have hj0 : (0 : ℤ) ≤ S.coordinate.j := by omega
  have hj : S.coordinate.j = (j : ℤ) := (Int.toNat_of_nonneg hj0).symm
  have hgeom := branchB_high_seam_target_F_canonical_and_carries
    R hB x hsx hbirth haxis hF
  have hAeq : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hBeq : routingB B e = normalizedA R := by
    simpa [B, e] using branchB_inactive_routingB_eq_normalizedA R
  have hMeq : routingM B e = normalizedM B := by simp [B, e, routingM]
  have hn : S.n = S.ell * routingM B e := by rw [S.n_eq, hMeq]
  have hbalance : (S.ell : ℤ) * routingM B e +
      (S.depth : ℤ) * routingB B e = (j : ℤ) * routingA B e := by
    have hnZ : (S.n : ℤ) = (S.ell : ℤ) * routingM B e := by exact_mod_cast hn
    rw [hnZ, hj] at haxis
    rw [hAeq, hBeq]
    simpa [mul_comm, mul_left_comm, mul_assoc] using haxis.2.2.2.2
  have hAlpha : physicalAlpha B e N + (S.ell : ℤ) * routingM B e =
      physicalAlpha B e A + (j : ℤ) * routingA B e := by
    have hAN := hgeom.2.2.2.2.2.2.2.2.2
    change physicalAlpha B e N = physicalAlpha B e A +
      (S.depth : ℤ) * routingB B e at hAN
    rw [hAN]
    linarith
  have hQsplit : Q = k + S.ell := by
    dsimp only [k]
    exact Nat.eq_add_of_sub_eq (Nat.le_of_lt S.ell_lt_principal) rfl
  have hNres : N = A + S.depth * (routingB B e : ZMod (routingA B e)) := by
    dsimp only [N, A, gridResidue]
    have hc : r31 R - S.depth - 1 + S.depth = r31 R - 1 := by
      have hdlt := branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
        R hB x hsx hbirth haxis
      have hone : 1 ≤ r31 R - S.depth :=
        Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (Nat.sub_pos_iff_lt.mpr hdlt))
      calc
        r31 R - S.depth - 1 + S.depth =
            (r31 R - S.depth) + S.depth - 1 :=
          (Nat.sub_add_comm hone).symm
        _ = r31 R - 1 := by
          rw [Nat.sub_add_cancel (Nat.le_of_lt hdlt)]
    rw [← hc]
    push_cast
    ring
  have hselected : (S.depth : ZMod (routingA B e)) * routingB B e +
      S.ell * routingM B e = 0 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod (routingA B e))) hbalance
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at hcast
    rw [show (routingA B e : ZMod (routingA B e)) = 0 by simp, mul_zero] at hcast
    simpa only [add_comm] using hcast
  have hres : N - (k * routingM B e : ℕ) =
      A - (Q * routingM B e : ℕ) := by
    rw [hNres, hQsplit]
    push_cast
    linear_combination hselected
  exact ⟨hAlpha, hres, by rw [hres]⟩

set_option maxHeartbeats 800000 in
/-- Complementary-index candidate identity at the inner notch. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_F_complement_inner_notch
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let Q := actualPrincipalIndex B
    let k := Q - S.ell
    let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
    let N := gridResidue B e (r31 R - 1) (r32 R - 1)
    1 ≤ k ∧ k < Q ∧
      rawCandidate B e k N = rawCandidate B e Q A - S.coordinate.j.toNat ∧
      rawCandidate B e k N =
        (physicalHeight B e A : ℤ) - S.coordinate.j.toNat ∧
      rawCandidate B e k N ≤ 0 := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Q := actualPrincipalIndex B
  let k := Q - S.ell
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  let N := gridResidue B e (r31 R - 1) (r32 R - 1)
  let j := S.coordinate.j.toNat
  have hkpos : 1 ≤ k := by
    have hp := S.ell_pos
    have hl : S.ell < Q := by simpa [Q, B] using S.ell_lt_principal
    dsimp only [k, Q]
    omega
  have hklt : k < Q := by
    have hp := S.ell_pos
    have hl := S.ell_lt_principal
    dsimp only [k, Q]
    omega
  have htrans := branchB_high_seam_target_F_A_to_inner_notch_apery_translation
    R hB x hsx hbirth haxis hF
  change physicalAlpha B e N + (S.ell : ℤ) * routingM B e =
      physicalAlpha B e A + (j : ℤ) * routingA B e ∧
    N - (k * routingM B e : ℕ) = A - (Q * routingM B e : ℕ) ∧
    physicalAlpha B e (N - (k * routingM B e : ℕ)) =
      physicalAlpha B e (A - (Q * routingM B e : ℕ)) at htrans
  have hQsplit : (Q : ℤ) = k + S.ell := by
    exact_mod_cast (show Q = k + S.ell by dsimp only [k]; omega)
  have hspecN := rawCandidate_spec B e k N
  change (k : ℤ) * routingM B e +
      physicalAlpha B e (N - (k * routingM B e : ℕ)) - physicalAlpha B e N =
        (routingA B e : ℤ) * rawCandidate B e k N at hspecN
  have hspecA := rawCandidate_spec B e Q A
  change (Q : ℤ) * routingM B e +
      physicalAlpha B e (A - (Q * routingM B e : ℕ)) - physicalAlpha B e A =
        (routingA B e : ℤ) * rawCandidate B e Q A at hspecA
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hcand : rawCandidate B e k N = rawCandidate B e Q A - j := by
    rw [htrans.2.2] at hspecN
    nlinarith
  have hprincipal :=
    branchB_actualZeroEdgeBirth_high_seam_target_F_principal_base_eq_final
      R hB x hsx hbirth haxis hF
  change rawCandidate B e Q A = physicalHeight B e A at hprincipal
  have hbound := branchB_high_seam_target_F_prefix_A_le_selected
    R hB x hsx hbirth haxis hF
  change branchBPrefixHeight R x hsx A ≤ j ∧ physicalHeight B e A ≤ j at hbound
  have hcandK : rawCandidate B e k N =
      (physicalHeight B e A : ℤ) - j := by rw [hcand, hprincipal]
  have hboundZ : (physicalHeight B e A : ℤ) ≤ (j : ℤ) := by
    exact_mod_cast hbound.2
  have hnonpos : rawCandidate B e k N ≤ 0 := by
    rw [hcandK]
    omega
  exact ⟨hkpos, hklt, hcand, hcandK, hnonpos⟩

/-- B61 endpoint: the complementary inner notch has final height zero. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_F_inner_notch_final_height_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    eta P.M.base (branchBInactiveReindex R) (r31 R - 1) (r32 R - 1) = 0 := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Q := actualPrincipalIndex B
  let k := Q - S.ell
  let N := gridResidue B e (r31 R - 1) (r32 R - 1)
  have hcomp :=
    branchB_actualZeroEdgeBirth_high_seam_target_F_complement_inner_notch
      R hB x hsx hbirth haxis hF
  change 1 ≤ k ∧ k < Q ∧ _ ∧ _ ∧ rawCandidate B e k N ≤ 0 at hcomp
  have hmin : rawMinimum B e N ≤ 0 :=
    (rawMinimum_le B e N hcomp.1).trans hcomp.2.2.2.2
  have hheight := physicalHeight_eq_max_rawMinimum B e N
  have hzero : physicalHeight B e N = 0 := by omega
  have hgeom := branchB_high_seam_target_F_canonical_and_carries
    R hB x hsx hbirth haxis hF
  have heta := eta_eq_physicalHeight_of_isCanonical B e
    (r31 R - 1) (r32 R - 1) hgeom.2.2.2.2.1
  change eta B e (r31 R - 1) (r32 R - 1) = physicalHeight B e N at heta
  exact heta.trans hzero

/-! ### B62: the F corridor and first-stage exclusion -/

/-- Every canonical upper-arm translate of the actual F source, strictly
before the inner-notch boundary, is already on the final ambient floor. -/
private theorem branchB_high_seam_target_F_translate_height_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R))
    (t : ℕ)
    (ht : t < (branchB_actual_selected_return_anchor_v2 R hB hsx).depth) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    physicalHeight B e
      (gridResidue B e (r31 R - S.depth + t) (r32 R)) = 0 := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let F := gridResidue B e (r31 R - S.depth) (r32 R)
  let T := gridResidue B e (r31 R - S.depth + t) (r32 R)
  let s := (branchBActualExceptionalNormalizedSource P R x).val
  let r := (branchBActualExceptionalRoutingSource P R x).val
  let I := returnIdeal (routingH B e) S.n
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hr21 : 0 < r21 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hdomain (i : ℕ) (hi : i < r31 R) :
      L5A2C4OR5.HerzogLShapeDomain D i (r32 R) := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change i < L5A2C4A.c2 B e ∧ r32 R < L5A2C4A.c3 B e ∧
      (i < L5A2C4D.cr12 D ∨ r32 R < L5A2C4D.cr13 D)
    dsimp only [D, B, e]
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12]
    exact ⟨by omega, by omega, Or.inl hi⟩
  change t < S.depth at ht
  have hFi : r31 R - S.depth < r31 R := by omega
  have hTi : r31 R - S.depth + t < r31 R := by omega
  have hFcanon := herzogLShapeCanonicality B e D _ _ (hdomain _ hFi)
  have hTcanon := herzogLShapeCanonicality B e D _ _ (hdomain _ hTi)
  have hselected := branchB_high_seam_target_F_selected_height_packet
    R hB x hsx hbirth haxis hF
  have hselectedF : I.aperyRepresentative (routingA B e) F =
      physicalAlpha B e F := by
    simpa [S, B, e, I, F] using hselected.2.2.2
  have hprov := branchB_actualZeroEdgeBirth_individual_return_source
    R hB x hsx hbirth
  have hmin : I.IsMinimalGenerator s := by
    dsimp [I, B, e]
    rw [branchBRoutingH_eq_normalizedH R]
    simpa [S, s] using hprov.2.2.2.1
  have hpacket := branchB_actualExceptional_source_packet P R x
  have hfinalRep : (routingI B e).aperyRepresentative
      (routingA B e) r = s := by
    simpa [B, e, r, s] using hpacket.2.2.2.1.symm
  have hsr : (s : ZMod (routingA B e)) = r := by
    rw [← hfinalRep]
    exact (routingI B e).aperyRepresentative_mod (routingA B e) r
  have hgen : (routingH B e).IsGeneratedByThree
      (routingA B e) (routingB B e) (routingC B e) := by
    simpa using (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1
  have hselectedRep : I.aperyRepresentative (routingA B e) r = s := by
    rw [← hsr]
    exact I.aperyRepresentative_eq_of_isMinimalGenerator
      (routingA B e) (routingB B e) (routingC B e) hgen hmin
  have hrF : r = F := by simpa [r, F, S, B, e] using hF
  have hsAlpha : (s : ℤ) = physicalAlpha B e F := by
    calc
      (s : ℤ) = I.aperyRepresentative (routingA B e) r := hselectedRep.symm
      _ = I.aperyRepresentative (routingA B e) F := by rw [hrF]
      _ = physicalAlpha B e F := hselectedF
  have hsI : (s : ℤ) ∈ routingI B e := by
    rw [← hfinalRep]
    exact (routingI B e).aperyRepresentative_mem (routingA B e) r
  have hAlphaF := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
    B e (r31 R - S.depth) (r32 R) hFcanon
  have hAlphaT := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
    B e (r31 R - S.depth + t) (r32 R) hTcanon
  have hshift : physicalAlpha B e T =
      physicalAlpha B e F + (t : ℤ) * routingB B e := by
    change physicalAlpha B e
        (gridResidue B e (r31 R - S.depth + t) (r32 R)) =
      physicalAlpha B e (gridResidue B e (r31 R - S.depth) (r32 R)) +
        (t : ℤ) * routingB B e
    rw [hAlphaT, hAlphaF]
    exact_mod_cast (show normalizedGrid B e 0 (r31 R - S.depth + t) (r32 R) =
        normalizedGrid B e 0 (r31 R - S.depth) (r32 R) +
          t * routingB B e by
      simp only [normalizedGrid, zero_mul, zero_add]
      ring)
  have htb : t * routingB B e ∈ routingH B e := by
    simpa [nsmul_eq_mul] using
      (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e) t
  have hAlphaTI : physicalAlpha B e T ∈ routingI B e := by
    rw [hshift, ← hsAlpha]
    exact (routingI B e).add_mem_nat hsI htb
  have hminT : rawMinimum B e T ≤ 0 := by
    have hm := (rawMinimum_threshold B e T 0).mp (by simpa using hAlphaTI)
    simpa using hm
  have hh := physicalHeight_eq_max_rawMinimum B e T
  change (physicalHeight B e T : ℤ) = max 0 (rawMinimum B e T) at hh
  change physicalHeight B e T = 0
  omega

/-- Every positive point strictly before the F depth boundary has zero
transverse final carry. -/
theorem branchB_high_seam_target_F_corridor_transverse_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R))
    (h : ℕ) (hhpos : 1 ≤ h)
    (hhlt : h < (branchB_actual_selected_return_anchor_v2 R hB hsx).depth) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let G := routingData B e
    let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
    G.u (G.c ((G.b ^ h) A)) = 0 := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let G := routingData B e
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  change h < S.depth at hhlt
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hpow (n : ℕ) : (G.b ^ n) A =
      gridResidue B e (r31 R - S.depth - 1 + n) (r32 R - 1) := by
    induction n with
    | zero => simp [A]
    | succ n ih =>
        rw [pow_succ']
        change G.b ((G.b ^ n) A) = _
        rw [ih]
        simpa [Nat.add_assoc] using
          (routing_b_gridResidue B e
            (r31 R - S.depth - 1 + n) (r32 R - 1))
  have hcoordH : r31 R - S.depth - 1 + h =
      r31 R - S.depth + (h - 1) := by omega
  have hcoordJ : r32 R - 1 + 1 = r32 R := by
    have hr32 : 0 < r32 R := by
      simpa using
        (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
    omega
  have hcE : G.c ((G.b ^ h) A) =
      gridResidue B e (r31 R - S.depth + (h - 1)) (r32 R) := by
    rw [hpow, routing_c_gridResidue]
    rw [hcoordH, hcoordJ]
  have hbE : G.b (G.c ((G.b ^ h) A)) =
      gridResidue B e (r31 R - S.depth + h) (r32 R) := by
    rw [hcE, routing_b_gridResidue]
    congr 1
    rw [Nat.add_assoc, Nat.sub_add_cancel hhpos]
  have hz0 := branchB_high_seam_target_F_translate_height_zero
    R hB x hsx hbirth haxis hF (h - 1)
      ((Nat.sub_le h 1).trans_lt hhlt)
  have hz1 := branchB_high_seam_target_F_translate_height_zero
    R hB x hsx hbirth haxis hF h hhlt
  change physicalHeight B e
      (gridResidue B e (r31 R - S.depth + (h - 1)) (r32 R)) = 0 at hz0
  change physicalHeight B e
      (gridResidue B e (r31 R - S.depth + h) (r32 R)) = 0 at hz1
  have hstep := branchB_final_height_step_b_with_ambient_carry R
    (G.c ((G.b ^ h) A))
  change physicalHeight B e (G.c ((G.b ^ h) A)) +
      branchBPrefixAmbientU R (G.c ((G.b ^ h) A)) =
    physicalHeight B e (G.b (G.c ((G.b ^ h) A))) +
      G.u (G.c ((G.b ^ h) A)) at hstep
  rw [hcE, routing_b_gridResidue,
    show r31 R - S.depth + (h - 1) + 1 =
      r31 R - S.depth + h by
        rw [Nat.add_assoc, Nat.sub_add_cancel hhpos], hz0, hz1] at hstep
  have hambient : branchBPrefixAmbientU R
      (gridResidue B e (r31 R - S.depth + (h - 1)) (r32 R)) = 0 := by
    have hcanon0 := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e (r31 R - S.depth + (h - 1)) (r32 R)
    have hcanon1 := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e (r31 R - S.depth + h) (r32 R)
    let D := branchB_inactive_coherentHerzogData R
    have hsum1 : c1 R = r21 R + r31 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
    have hsum2 : c2 R = r12 R + r32 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    have hr21 : 0 < r21 R := by
      simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
    have hr12 : 0 < r12 R := by
      simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
    have hdom (i : ℕ) (hi : i < r31 R) :
        L5A2C4OR5.HerzogLShapeDomain D i (r32 R) := by
      simp only [L5A2C4OR5.HerzogLShapeDomain]
      change i < L5A2C4A.c2 B e ∧ r32 R < L5A2C4A.c3 B e ∧
        (i < L5A2C4D.cr12 D ∨ r32 R < L5A2C4D.cr13 D)
      dsimp only [D, B, e]
      rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
        branchB_inactive_coherent_cr12]
      exact ⟨by omega, by omega, Or.inl hi⟩
    have hsplit : r31 R - S.depth + S.depth = r31 R :=
      Nat.sub_add_cancel (Nat.le_of_lt hdlt)
    have hi1base : r31 R - S.depth + h <
        r31 R - S.depth + S.depth := Nat.add_lt_add_left hhlt _
    have hi1 : r31 R - S.depth + h < r31 R := by
      simpa [hsplit] using hi1base
    have hhpred : h - 1 < h := Nat.sub_lt (by omega) Nat.zero_lt_one
    have hi0 : r31 R - S.depth + (h - 1) < r31 R :=
      (Nat.add_lt_add_left hhpred _).trans hi1
    have hc0 := herzogLShapeCanonicality B e D _ _
      (hdom (r31 R - S.depth + (h - 1)) hi0)
    have hc1 := herzogLShapeCanonicality B e D _ _
      (hdom (r31 R - S.depth + h) hi1)
    have ha0 := hcanon0 hc0
    have ha1 := hcanon1 hc1
    have hs := (routingH B e).asRelativeIdeal.apery_step_eq
      (routingA B e) (routingB B e) (routingHB B e)
      (gridResidue B e (r31 R - S.depth + (h - 1)) (r32 R))
    change physicalAlpha B e
        (gridResidue B e (r31 R - S.depth + (h - 1)) (r32 R)) + routingB B e =
      physicalAlpha B e
        (gridResidue B e (r31 R - S.depth + (h - 1)) (r32 R) + routingB B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientU R
        (gridResidue B e (r31 R - S.depth + (h - 1)) (r32 R)) at hs
    have hadd := gridResidue_add_b B e
      (r31 R - S.depth + (h - 1)) (r32 R)
    rw [← hadd, show r31 R - S.depth + (h - 1) + 1 =
        r31 R - S.depth + h by
          rw [Nat.add_assoc, Nat.sub_add_cancel hhpos], ha0, ha1] at hs
    have hbase :
        normalizedGrid B e 0 (r31 R - S.depth + (h - 1)) (r32 R) +
            routingB B e =
          normalizedGrid B e 0 (r31 R - S.depth + h) (r32 R) := by
      simp only [normalizedGrid, zero_mul, zero_add]
      rw [show r31 R - S.depth + h =
          r31 R - S.depth + (h - 1) + 1 by
            rw [Nat.add_assoc, Nat.sub_add_cancel hhpos]]
      ring
    have hbaseZ :
        (normalizedGrid B e 0 (r31 R - S.depth + (h - 1)) (r32 R) : ℤ) +
            routingB B e =
          normalizedGrid B e 0 (r31 R - S.depth + h) (r32 R) := by
      exact_mod_cast hbase
    have hp : (routingA B e : ℤ) * branchBPrefixAmbientU R
        (gridResidue B e (r31 R - S.depth + (h - 1)) (r32 R)) = 0 := by
      rw [hbaseZ] at hs
      omega
    exact (Nat.mul_eq_zero.mp (by exact_mod_cast hp)).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  rw [hambient] at hstep
  change G.u (G.c ((G.b ^ h) A)) = 0
  rw [hcE]
  omega

/-- At the inner-notch step, the transverse final carry has vanished. -/
private theorem branchB_actualZeroEdgeBirth_high_seam_target_F_terminal_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let G := routingData B e
    let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
    G.v ((G.b ^ S.depth) A) = 0 := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let G := routingData B e
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  let N := gridResidue B e (r31 R - 1) (r32 R - 1)
  let Cn := gridResidue B e (r31 R - 1) (r32 R)
  have hdlt : S.depth < r31 R :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
  have hdpos : 0 < S.depth := S.depth_pos
  have hpow (n : ℕ) : (G.b ^ n) A =
      gridResidue B e (r31 R - S.depth - 1 + n) (r32 R - 1) := by
    induction n with
    | zero => simp [A]
    | succ n ih =>
        rw [pow_succ']
        change G.b ((G.b ^ n) A) = _
        rw [ih]
        simpa [Nat.add_assoc] using
          (routing_b_gridResidue B e
            (r31 R - S.depth - 1 + n) (r32 R - 1))
  have hpowN : (G.b ^ S.depth) A = N := by
    rw [hpow]
    congr 1
    omega
  have hNzero : physicalHeight B e N = 0 := by
    have heta :=
      branchB_actualZeroEdgeBirth_high_seam_target_F_inner_notch_final_height_zero
        R hB x hsx hbirth haxis hF
    have hgeom := branchB_high_seam_target_F_canonical_and_carries
      R hB x hsx hbirth haxis hF
    have heq := eta_eq_physicalHeight_of_isCanonical B e
      (r31 R - 1) (r32 R - 1) hgeom.2.2.2.2.1
    change eta B e (r31 R - 1) (r32 R - 1) = physicalHeight B e N at heq
    rw [← heq]
    simpa [B, e] using heta
  have hCnzero : physicalHeight B e Cn = 0 := by
    have hz := branchB_high_seam_target_F_translate_height_zero
      R hB x hsx hbirth haxis hF (S.depth - 1)
        (Nat.sub_lt hdpos Nat.zero_lt_one)
    change physicalHeight B e
      (gridResidue B e (r31 R - S.depth + (S.depth - 1)) (r32 R)) = 0 at hz
    simpa [Cn, show r31 R - S.depth + (S.depth - 1) = r31 R - 1 by omega]
      using hz
  have hambient : branchBPrefixAmbientV R N = 0 := by
    let D := branchB_inactive_coherentHerzogData R
    have hsum1 : c1 R = r21 R + r31 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
    have hsum2 : c2 R = r12 R + r32 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    have hr21 : 0 < r21 R := by
      simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
    have hr12 : 0 < r12 R := by
      simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
    have hr31 : 0 < r31 R := by
      simpa using
        (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
    have hdom (j : ℕ) (hj : j ≤ r32 R) :
        L5A2C4OR5.HerzogLShapeDomain D (r31 R - 1) j := by
      simp only [L5A2C4OR5.HerzogLShapeDomain]
      change r31 R - 1 < L5A2C4A.c2 B e ∧ j < L5A2C4A.c3 B e ∧
        (r31 R - 1 < L5A2C4D.cr12 D ∨ j < L5A2C4D.cr13 D)
      dsimp only [D, B, e]
      rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
        branchB_inactive_coherent_cr12]
      exact ⟨by omega, by omega, Or.inl (by omega)⟩
    have hcN := herzogLShapeCanonicality B e D _ _
      (hdom (r32 R - 1) (Nat.sub_le _ _))
    have hcC := herzogLShapeCanonicality B e D _ _ (hdom (r32 R) le_rfl)
    have haN := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e (r31 R - 1) (r32 R - 1) hcN
    have haC := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e (r31 R - 1) (r32 R) hcC
    have hs := (routingH B e).asRelativeIdeal.apery_step_eq
      (routingA B e) (routingC B e) (routingHC B e) N
    change physicalAlpha B e N + routingC B e =
      physicalAlpha B e (N + routingC B e) +
        (routingA B e : ℤ) * branchBPrefixAmbientV R N at hs
    have hadd : N + routingC B e = Cn := by
      have hr32 : 0 < r32 R := by
        simpa using
          (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
      change gridResidue B e (r31 R - 1) (r32 R - 1) + routingC B e =
        gridResidue B e (r31 R - 1) (r32 R)
      rw [show r32 R = r32 R - 1 + 1 by omega]
      exact (gridResidue_add_c B e (r31 R - 1) (r32 R - 1)).symm
    rw [hadd, haN, haC] at hs
    have hbase :
        normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) + routingC B e =
          normalizedGrid B e 0 (r31 R - 1) (r32 R) := by
      simp only [normalizedGrid, zero_mul, zero_add]
      have hr32 : 0 < r32 R := by
        simpa using
          (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
      calc
        (r31 R - 1) * routingB B e + (r32 R - 1) * routingC B e +
              routingC B e =
            (r31 R - 1) * routingB B e +
              (r32 R - 1 + 1) * routingC B e := by ring
        _ = (r31 R - 1) * routingB B e + r32 R * routingC B e := by
          rw [show r32 R - 1 + 1 = r32 R by omega]
    have hbaseZ :
        (normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) : ℤ) + routingC B e =
          normalizedGrid B e 0 (r31 R - 1) (r32 R) := by
      exact_mod_cast hbase
    rw [hbaseZ] at hs
    have hp : (routingA B e : ℤ) * branchBPrefixAmbientV R N = 0 := by
      omega
    exact (Nat.mul_eq_zero.mp (by exact_mod_cast hp)).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  have hstep := branchB_final_height_step_c_with_ambient_carry R N
  change physicalHeight B e N + branchBPrefixAmbientV R N =
    physicalHeight B e (N + routingC B e) + G.v N at hstep
  have hadd : N + routingC B e = Cn := by
    have hr32 : 0 < r32 R := by
      simpa using
        (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
    change gridResidue B e (r31 R - 1) (r32 R - 1) + routingC B e =
      gridResidue B e (r31 R - 1) (r32 R)
    rw [show r32 R = r32 R - 1 + 1 by omega]
    exact (gridResidue_add_c B e (r31 R - 1) (r32 R - 1)).symm
  rw [hNzero, hambient, hadd, hCnzero] at hstep
  change G.v ((G.b ^ S.depth) A) = 0
  rw [hpowN]
  omega

/-- The B-run reaches a transverse zero no later than the selected depth. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_F_firstZeroIndex_le_depth
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let G := routingData P.M.base e
    L5A2C4I.ResidueData.bFirstZeroIndex G x.val.val ≤ S.depth := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let G := routingData B e
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  have hz := branchB_actualZeroEdgeBirth_high_seam_target_F_terminal_zero
    R hB x hsx hbirth haxis hF
  have hdiamond := branchB_actualZeroEdgeBirth_high_seam_target_F_inverse_diamond
    R hB x hsx hbirth haxis hF
  have hbase : x.val.val.val = A := by
    simpa [S, B, e, A] using hdiamond.1
  change G.v ((G.b ^ S.depth) A) = 0 at hz
  let n0 := L5A2C4I.ResidueData.bFirstZeroIndex G x.val.val
  by_contra hnle
  have hdlt : S.depth < n0 := Nat.lt_of_not_ge hnle
  have hp' := L5A2C4I.ResidueData.firstZeroIndex_positive_before G.b G.v
    x.val.val.val x.val.val.property.1.2 S.depth_pos hdlt
  rw [hbase] at hp'
  exact (Nat.ne_of_gt hp') hz

/-- An actual high-seam F target is first-stage nonexceptional. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_F_firstStage_nonexceptional
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let G := routingData P.M.base e
    L5A2C4I.ResidueData.BFirstStageNonexceptional G x.val.val := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let G := routingData B e
  let A := gridResidue B e (r31 R - S.depth - 1) (r32 R - 1)
  have hdiamond := branchB_actualZeroEdgeBirth_high_seam_target_F_inverse_diamond
    R hB x hsx hbirth haxis hF
  have hbase : x.val.val.val = A := by
    simpa [S, B, e, A] using hdiamond.1
  have hterminal := branchB_actualZeroEdgeBirth_high_seam_target_F_terminal_zero
    R hB x hsx hbirth haxis hF
  change G.v ((G.b ^ S.depth) A) = 0 at hterminal
  have hcross :=
    (L5A2C4I.ResidueData.sourceTargetBranch_iff_positive_cross G).1
      x.val.val.property
  have hseed : 0 < G.v (G.b x.val.val.val) := by
    rw [← hcross.2.1]
    exact hcross.2.2
  by_cases hd1 : S.depth = 1
  · have hzseed : G.v (G.b x.val.val.val) = 0 := by
      rw [hbase]
      simpa [hd1] using hterminal
    exact (Nat.ne_of_gt hseed hzseed).elim
  · have hbound :=
      branchB_actualZeroEdgeBirth_high_seam_target_F_firstZeroIndex_le_depth
        R hB x hsx hbirth haxis hF
    let n0 := L5A2C4I.ResidueData.bFirstZeroIndex G x.val.val
    change n0 ≤ S.depth at hbound
    have hn0gt : 1 < n0 := by
      have hzfirst := L5A2C4I.ResidueData.firstZeroIndex_zero G.b G.v
        x.val.val.val x.val.val.property.1.2
      have hn0pos := L5A2C4I.ResidueData.firstZeroIndex_pos G.b G.v
        x.val.val.val x.val.val.property.1.2
      change G.v ((G.b ^ n0) x.val.val.val) = 0 at hzfirst
      change 0 < n0 at hn0pos
      by_contra hngt
      have hn0 : n0 = 1 := by omega
      rw [hn0] at hzfirst
      have : G.v (G.b x.val.val.val) = 0 := by simpa using hzfirst
      exact (Nat.ne_of_gt hseed) this
    have hhpos : 1 ≤ n0 - 1 := by omega
    have hhlt : n0 - 1 < S.depth := by omega
    have hcorr := branchB_high_seam_target_F_corridor_transverse_zero
      R hB x hsx hbirth haxis hF (n0 - 1) hhpos hhlt
    change G.u (G.c ((G.b ^ (n0 - 1)) A)) = 0 at hcorr
    change G.u (G.c (L5A2C4I.ResidueData.canonicalBEndpoint G x.val.val)) = 0
    simp only [L5A2C4I.ResidueData.canonicalBEndpoint]
    change G.u (G.c ((G.b ^ (n0 - 1)) x.val.val.val)) = 0
    rw [hbase]
    exact hcorr

/-- The actual exceptional fibre cannot carry the high-seam F target. -/
theorem branchB_actualZeroEdgeBirth_high_seam_target_F_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (hF :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      let e := branchBInactiveReindex R
      (branchBActualExceptionalRoutingSource P R x).val =
        gridResidue P.M.base e (r31 R - S.depth) (r32 R)) : False := by
  exact x.val.property
    (branchB_actualZeroEdgeBirth_high_seam_target_F_firstStage_nonexceptional
      R hB x hsx hbirth haxis hF)

/-- With U and F excluded, the actual high-axis target is the origin. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_target_eq_origin
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    (branchBActualExceptionalRoutingSource P R x).val =
      gridResidue P.M.base (branchBInactiveReindex R) 0 0 := by
  rcases branchB_actualZeroEdgeBirth_high_seam_target_trichotomy
      R hB x hsx hbirth haxis with hO | hU | hF
  · exact hO
  · exact (branchB_actualZeroEdgeBirth_high_seam_target_U_impossible
      R hB x hsx hbirth haxis hU).elim
  · exact (branchB_actualZeroEdgeBirth_high_seam_target_F_impossible
      R hB x hsx hbirth haxis hF).elim

/-- The same-diamond base of the actual event is the inactive inner notch. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_base_eq_inner_notch
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    x.val.val.val = gridResidue P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R - 1) := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let G := routingData P.M.base e
  have hpacket := branchB_actualZeroEdgeBirth_same_diamond_source_packet
    R x hsx hbirth
  rcases hpacket with ⟨_, _, _, _, _, _, _, _, hdiamond, _⟩
  have htarget := branchB_actualZeroEdgeBirth_axisC_high_seam_target_eq_origin
    R hB x hsx hbirth haxis
  have htarget0 : (branchBActualExceptionalRoutingSource P R x).val = 0 := by
    simpa [gridResidue] using htarget
  have hbc : G.b (G.c x.val.val.val) = 0 := hdiamond.trans htarget0
  exact branchB_grid_bc_preimage_origin_eq_inner_notch R x.val.val.val hbc

/-! ### B63: the actual zero floor and the corrected local-`a` return window -/

/-- On the actual high-axis event the final envelope is zero on the whole
inner-notch diamond, while its origin has the selected individual height.
The selected anchor and the actual source are compared only through their
common individual-return ideal. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_origin_inner_notch_final_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    eta B e (r31 R - 1) (r32 R - 1) = 0 ∧
      eta B e (r31 R) (r32 R - 1) = 0 ∧
      eta B e (r31 R - 1) (r32 R) = 0 ∧
      eta B e 0 0 = S.coordinate.j.toNat := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let G := routingData B e
  let D := branchB_inactive_coherentHerzogData R
  let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
  let B0 := gridResidue B e (r31 R) (r32 R - 1)
  let C0 := gridResidue B e (r31 R - 1) (r32 R)
  let D0 := gridResidue B e 0 0
  let I := returnIdeal (routingH B e) S.n
  let s := (branchBActualExceptionalNormalizedSource P R x).val
  let r := (branchBActualExceptionalRoutingSource P R x).val
  change S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R at haxis
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hr21 : 0 < r21 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hdom (i t : ℕ) (hi : i ≤ r31 R) (ht : t ≤ r32 R)
      (hor : i < r31 R ∨ t < r32 R) :
      L5A2C4OR5.HerzogLShapeDomain D i t := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change i < L5A2C4A.c2 B e ∧ t < L5A2C4A.c3 B e ∧
      (i < L5A2C4D.cr12 D ∨ t < L5A2C4D.cr13 D)
    dsimp only [D, B, e]
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12]
    exact ⟨by omega, by omega, by simpa using hor⟩
  have hAcanon := herzogLShapeCanonicality B e D _ _
    (hdom (r31 R - 1) (r32 R - 1) (Nat.sub_le _ _) (Nat.sub_le _ _)
      (Or.inl (by omega)))
  have hBcanon := herzogLShapeCanonicality B e D _ _
    (hdom (r31 R) (r32 R - 1) le_rfl (Nat.sub_le _ _)
      (Or.inr (by omega)))
  have hCcanon := herzogLShapeCanonicality B e D _ _
    (hdom (r31 R - 1) (r32 R) (Nat.sub_le _ _) le_rfl
      (Or.inl (by omega)))
  have hDcanon := herzogLShapeCanonicality B e D 0 0
    (hdom 0 0 (Nat.zero_le _) (Nat.zero_le _) (Or.inl hr31))
  have hAB : A0 + routingB B e = B0 := by
    change gridResidue B e (r31 R - 1) (r32 R - 1) + routingB B e =
      gridResidue B e (r31 R) (r32 R - 1)
    rw [show r31 R = r31 R - 1 + 1 by omega]
    exact (gridResidue_add_b B e (r31 R - 1) (r32 R - 1)).symm
  have hAC : A0 + routingC B e = C0 := by
    change gridResidue B e (r31 R - 1) (r32 R - 1) + routingC B e =
      gridResidue B e (r31 R - 1) (r32 R)
    rw [show r32 R = r32 R - 1 + 1 by omega]
    exact (gridResidue_add_c B e (r31 R - 1) (r32 R - 1)).symm
  have halpha (i t : ℕ) (hc : IsCanonicalTailGridPoint B e i t) :
      physicalAlpha B e (gridResidue B e i t) = normalizedGrid B e 0 i t :=
    branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical B e i t hc
  have huAmbient : branchBPrefixAmbientU R A0 = 0 := by
    have hs := (routingH B e).asRelativeIdeal.apery_step_eq
      (routingA B e) (routingB B e) (routingHB B e) A0
    change physicalAlpha B e A0 + routingB B e =
      physicalAlpha B e (A0 + routingB B e) +
        (routingA B e : ℤ) * branchBPrefixAmbientU R A0 at hs
    rw [hAB, halpha _ _ hAcanon, halpha _ _ hBcanon] at hs
    have hbase : normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) +
        routingB B e = normalizedGrid B e 0 (r31 R) (r32 R - 1) := by
      simp only [normalizedGrid, zero_mul, zero_add]
      calc
        (r31 R - 1) * routingB B e + (r32 R - 1) * routingC B e +
              routingB B e =
            (r31 R - 1 + 1) * routingB B e +
              (r32 R - 1) * routingC B e := by ring
        _ = r31 R * routingB B e +
              (r32 R - 1) * routingC B e := by
          rw [show r31 R - 1 + 1 = r31 R by omega]
    have hbaseZ : (normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) : ℤ) +
        routingB B e = normalizedGrid B e 0 (r31 R) (r32 R - 1) :=
      by exact_mod_cast hbase
    rw [hbaseZ] at hs
    have hp : (routingA B e : ℤ) * branchBPrefixAmbientU R A0 = 0 := by omega
    exact (Nat.mul_eq_zero.mp (by exact_mod_cast hp)).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  have hvAmbient : branchBPrefixAmbientV R A0 = 0 := by
    have hs := (routingH B e).asRelativeIdeal.apery_step_eq
      (routingA B e) (routingC B e) (routingHC B e) A0
    change physicalAlpha B e A0 + routingC B e =
      physicalAlpha B e (A0 + routingC B e) +
        (routingA B e : ℤ) * branchBPrefixAmbientV R A0 at hs
    rw [hAC, halpha _ _ hAcanon, halpha _ _ hCcanon] at hs
    have hbase : normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) +
        routingC B e = normalizedGrid B e 0 (r31 R - 1) (r32 R) := by
      simp only [normalizedGrid, zero_mul, zero_add]
      calc
        (r31 R - 1) * routingB B e + (r32 R - 1) * routingC B e +
              routingC B e =
            (r31 R - 1) * routingB B e +
              (r32 R - 1 + 1) * routingC B e := by ring
        _ = (r31 R - 1) * routingB B e +
              r32 R * routingC B e := by
          rw [show r32 R - 1 + 1 = r32 R by omega]
    have hbaseZ : (normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) : ℤ) +
        routingC B e = normalizedGrid B e 0 (r31 R - 1) (r32 R) :=
      by exact_mod_cast hbase
    rw [hbaseZ] at hs
    have hp : (routingA B e : ℤ) * branchBPrefixAmbientV R A0 = 0 := by omega
    exact (Nat.mul_eq_zero.mp (by exact_mod_cast hp)).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  have hprov := branchB_actualZeroEdgeBirth_individual_return_source
    R hB x hsx hbirth
  have hmin : I.IsMinimalGenerator s := by
    dsimp [I, B, e]
    rw [branchBRoutingH_eq_normalizedH R]
    simpa [S, s] using hprov.2.2.2.1
  have hsourcePacket := branchB_actualExceptional_source_packet P R x
  have hfinalRep : (routingI B e).aperyRepresentative (routingA B e) r = s := by
    simpa [B, e, r, s] using hsourcePacket.2.2.2.1.symm
  have hsr : (s : ZMod (routingA B e)) = r := by
    rw [← hfinalRep]
    exact (routingI B e).aperyRepresentative_mod (routingA B e) r
  have hgen : (routingH B e).IsGeneratedByThree
      (routingA B e) (routingB B e) (routingC B e) := by
    simpa using (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1
  have hindividualRep : I.aperyRepresentative (routingA B e) r = s := by
    rw [← hsr]
    exact I.aperyRepresentative_eq_of_isMinimalGenerator
      (routingA B e) (routingB B e) (routingC B e) hgen hmin
  have htarget := branchB_actualZeroEdgeBirth_axisC_high_seam_target_eq_origin
    R hB x hsx hbirth haxis
  have hrD : r = D0 := by simpa [r, D0, B, e] using htarget
  have hformulaD := branchB_high_seam_individual_height_formula
    R hB x hsx hbirth haxis 0 0
      (hdom 0 0 (Nat.zero_le _) (Nat.zero_le _) (Or.inl hr31))
  have hj0 : (0 : ℤ) ≤ S.coordinate.j := by omega
  let j := S.coordinate.j.toNat
  have hj : S.coordinate.j = (j : ℤ) := (Int.toNat_of_nonneg hj0).symm
  have hheightD : branchBHighSeamIndividualHeight R j S.depth 0 0 = j := by
    have hdlt := branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
      R hB x hsx hbirth haxis
    change S.depth < c1 R - r21 R at hdlt
    have hc1 : S.depth < c1 R := by omega
    simp [branchBHighSeamIndividualHeight, hr32, hc1]
  have hindividualD : I.aperyRepresentative (routingA B e) D0 =
      physicalAlpha B e D0 + (routingA B e : ℤ) * j := by
    simpa [S, B, e, I, D0, j, hheightD] using hformulaD
  have hphysicalD := physicalHeight_spec B e D0
  change (routingI B e).aperyRepresentative (routingA B e) D0 =
    physicalAlpha B e D0 + (routingA B e : ℤ) * physicalHeight B e D0 at hphysicalD
  have hDheight : physicalHeight B e D0 = j := by
    rw [← hrD, hfinalRep, ← hindividualRep, hrD, hindividualD] at hphysicalD
    have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
    nlinarith
  have hetaD := eta_eq_physicalHeight_of_isCanonical B e 0 0 hDcanon
  change eta B e 0 0 = physicalHeight B e D0 at hetaD
  have hetaD' : eta B e 0 0 = S.coordinate.j.toNat := by
    simpa [j] using hetaD.trans hDheight
  have hformulaC := branchB_high_seam_individual_height_formula
    R hB x hsx hbirth haxis (r31 R - 1) (r32 R)
      (hdom _ _ (Nat.sub_le _ _) le_rfl (Or.inl (by omega)))
  have hdlt := branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
    R hB x hsx hbirth haxis
  have hheightC : branchBHighSeamIndividualHeight R j S.depth
      (r31 R - 1) (r32 R) = 0 := by
    have hdpos : 0 < S.depth := S.depth_pos
    have hnlt : ¬ r31 R - 1 < r31 R - S.depth := by omega
    simp [branchBHighSeamIndividualHeight, hnlt]
  have hindividualC : I.aperyRepresentative (routingA B e) C0 =
      physicalAlpha B e C0 := by
    simpa [S, B, e, I, C0, j, hheightC] using hformulaC
  have hCmemI : physicalAlpha B e C0 ∈ I := by
    rw [← hindividualC]
    exact I.aperyRepresentative_mem (routingA B e) C0
  have hCmemPrefix : physicalAlpha B e C0 ∈ branchBActualPrefixIdeal R x hsx := by
    change ∃ ell : ℕ, 0 < ell ∧ ell < actualPrincipalIndex B ∧
      physicalAlpha B e C0 ∈ returnIdeal (routingH B e) (ell * normalizedM B)
    refine ⟨S.ell, S.ell_pos, S.ell_lt_principal, ?_⟩
    simpa [I, S.n_eq] using hCmemI
  have hprefixC : branchBPrefixHeight R x hsx C0 = 0 := by
    have hle := branchB_prefixHeight_le_of_canonical_mem R x hsx
      (r31 R - 1) (r32 R) 0 hCcanon
    have hgrid := halpha (r31 R - 1) (r32 R) hCcanon
    apply Nat.eq_zero_of_le_zero
    apply hle
    simpa [C0, hgrid] using hCmemPrefix
  have hfinalC : physicalHeight B e C0 = 0 := by
    have hle := branchB_finalHeight_le_prefixHeight R x hsx C0
    change physicalHeight B e C0 ≤ branchBPrefixHeight R x hsx C0 at hle
    omega
  have hbase := branchB_actualZeroEdgeBirth_axisC_high_seam_base_eq_inner_notch
    R hB x hsx hbirth haxis
  have hbranch : G.IsBranch A0 := by
    have hb : G.IsBranch x.val.val.val := by
      simpa [G, B, e] using hbirth.2.2.2.2.2.1
    rw [hbase] at hb
    simpa [A0, B, e] using hb
  have hcstep := branchB_final_height_step_c_with_ambient_carry R A0
  change physicalHeight B e A0 + branchBPrefixAmbientV R A0 =
    physicalHeight B e (A0 + routingC B e) + G.v A0 at hcstep
  rw [hvAmbient, hAC, hfinalC, hbranch.2] at hcstep
  have hfinalA : physicalHeight B e A0 = 0 := by omega
  have hbstep := branchB_final_height_step_b_with_ambient_carry R A0
  change physicalHeight B e A0 + branchBPrefixAmbientU R A0 =
    physicalHeight B e (A0 + routingB B e) + G.u A0 at hbstep
  rw [hfinalA, huAmbient, hAB, hbranch.1] at hbstep
  have hfinalB : physicalHeight B e B0 = 0 := by omega
  have hetaA := eta_eq_physicalHeight_of_isCanonical B e _ _ hAcanon
  have hetaB := eta_eq_physicalHeight_of_isCanonical B e _ _ hBcanon
  have hetaC := eta_eq_physicalHeight_of_isCanonical B e _ _ hCcanon
  change eta B e (r31 R - 1) (r32 R - 1) = physicalHeight B e A0 at hetaA
  change eta B e (r31 R) (r32 R - 1) = physicalHeight B e B0 at hetaB
  change eta B e (r31 R - 1) (r32 R) = physicalHeight B e C0 at hetaC
  exact ⟨hetaA.trans hfinalA, hetaB.trans hfinalB,
    hetaC.trans hfinalC, hetaD'⟩

/-- The fixed inner-notch diamond is canonical and has no ambient carry on
either outgoing edge. -/
private theorem branchB_inner_notch_canonical_and_carries
    (R : SectorBCriticalRoleBranchB P) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
    let B0 := gridResidue B e (r31 R) (r32 R - 1)
    let C0 := gridResidue B e (r31 R - 1) (r32 R)
    IsCanonicalTailGridPoint B e (r31 R - 1) (r32 R - 1) ∧
      IsCanonicalTailGridPoint B e (r31 R) (r32 R - 1) ∧
      IsCanonicalTailGridPoint B e (r31 R - 1) (r32 R) ∧
      branchBPrefixAmbientU R A0 = 0 ∧
      branchBPrefixAmbientV R A0 = 0 ∧
      A0 + routingB B e = B0 ∧ A0 + routingC B e = C0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let D := branchB_inactive_coherentHerzogData R
  let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
  let B0 := gridResidue B e (r31 R) (r32 R - 1)
  let C0 := gridResidue B e (r31 R - 1) (r32 R)
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hr21 : 0 < r21 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hdom (i t : ℕ) (hi : i ≤ r31 R) (ht : t ≤ r32 R)
      (hor : i < r31 R ∨ t < r32 R) :
      L5A2C4OR5.HerzogLShapeDomain D i t := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change i < L5A2C4A.c2 B e ∧ t < L5A2C4A.c3 B e ∧
      (i < L5A2C4D.cr12 D ∨ t < L5A2C4D.cr13 D)
    dsimp only [D, B, e]
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12]
    exact ⟨by omega, by omega, by simpa using hor⟩
  have hA := herzogLShapeCanonicality B e D _ _
    (hdom (r31 R - 1) (r32 R - 1) (Nat.sub_le _ _) (Nat.sub_le _ _)
      (Or.inl (by omega)))
  have hB0 := herzogLShapeCanonicality B e D _ _
    (hdom (r31 R) (r32 R - 1) le_rfl (Nat.sub_le _ _)
      (Or.inr (by omega)))
  have hC := herzogLShapeCanonicality B e D _ _
    (hdom (r31 R - 1) (r32 R) (Nat.sub_le _ _) le_rfl
      (Or.inl (by omega)))
  have hAB : A0 + routingB B e = B0 := by
    change gridResidue B e (r31 R - 1) (r32 R - 1) + routingB B e =
      gridResidue B e (r31 R) (r32 R - 1)
    rw [show r31 R = r31 R - 1 + 1 by omega]
    exact (gridResidue_add_b B e (r31 R - 1) (r32 R - 1)).symm
  have hAC : A0 + routingC B e = C0 := by
    change gridResidue B e (r31 R - 1) (r32 R - 1) + routingC B e =
      gridResidue B e (r31 R - 1) (r32 R)
    rw [show r32 R = r32 R - 1 + 1 by omega]
    exact (gridResidue_add_c B e (r31 R - 1) (r32 R - 1)).symm
  have halpha (i t : ℕ) (hc : IsCanonicalTailGridPoint B e i t) :
      physicalAlpha B e (gridResidue B e i t) = normalizedGrid B e 0 i t :=
    branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical B e i t hc
  have hu : branchBPrefixAmbientU R A0 = 0 := by
    have hs := (routingH B e).asRelativeIdeal.apery_step_eq
      (routingA B e) (routingB B e) (routingHB B e) A0
    change physicalAlpha B e A0 + routingB B e =
      physicalAlpha B e (A0 + routingB B e) +
        (routingA B e : ℤ) * branchBPrefixAmbientU R A0 at hs
    rw [hAB, halpha _ _ hA, halpha _ _ hB0] at hs
    have heq : (normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) : ℤ) +
        routingB B e = normalizedGrid B e 0 (r31 R) (r32 R - 1) := by
      exact_mod_cast (show normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) +
          routingB B e = normalizedGrid B e 0 (r31 R) (r32 R - 1) by
        simp only [normalizedGrid, zero_mul, zero_add]
        calc
          (r31 R - 1) * routingB B e + (r32 R - 1) * routingC B e +
                routingB B e =
              (r31 R - 1 + 1) * routingB B e +
                (r32 R - 1) * routingC B e := by ring
          _ = _ := by rw [show r31 R - 1 + 1 = r31 R by omega])
    rw [heq] at hs
    have hp : (routingA B e : ℤ) * branchBPrefixAmbientU R A0 = 0 := by omega
    exact (Nat.mul_eq_zero.mp (by exact_mod_cast hp)).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  have hv : branchBPrefixAmbientV R A0 = 0 := by
    have hs := (routingH B e).asRelativeIdeal.apery_step_eq
      (routingA B e) (routingC B e) (routingHC B e) A0
    change physicalAlpha B e A0 + routingC B e =
      physicalAlpha B e (A0 + routingC B e) +
        (routingA B e : ℤ) * branchBPrefixAmbientV R A0 at hs
    rw [hAC, halpha _ _ hA, halpha _ _ hC] at hs
    have heq : (normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) : ℤ) +
        routingC B e = normalizedGrid B e 0 (r31 R - 1) (r32 R) := by
      exact_mod_cast (show normalizedGrid B e 0 (r31 R - 1) (r32 R - 1) +
          routingC B e = normalizedGrid B e 0 (r31 R - 1) (r32 R) by
        simp only [normalizedGrid, zero_mul, zero_add]
        calc
          (r31 R - 1) * routingB B e + (r32 R - 1) * routingC B e +
                routingC B e =
              (r31 R - 1) * routingB B e +
                (r32 R - 1 + 1) * routingC B e := by ring
          _ = _ := by rw [show r32 R - 1 + 1 = r32 R by omega])
    rw [heq] at hs
    have hp : (routingA B e : ℤ) * branchBPrefixAmbientV R A0 = 0 := by omega
    exact (Nat.mul_eq_zero.mp (by exact_mod_cast hp)).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  exact ⟨hA, hB0, hC, hu, hv, hAB, hAC⟩

/-- The pre-principal envelope is strictly above the final zero floor at the
actual inner-notch base. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_inner_notch_prefix_pos
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
    0 < branchBPrefixHeight R x hsx A0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
  let B0 := gridResidue B e (r31 R) (r32 R - 1)
  let C0 := gridResidue B e (r31 R - 1) (r32 R)
  have hg := branchB_inner_notch_canonical_and_carries R
  change _ ∧ _ ∧ _ ∧ branchBPrefixAmbientU R A0 = 0 ∧
      branchBPrefixAmbientV R A0 = 0 ∧
      A0 + routingB B e = B0 ∧ A0 + routingC B e = C0 at hg
  by_contra hn
  have hzero : branchBPrefixHeight R x hsx A0 = 0 :=
    Nat.eq_zero_of_not_pos hn
  have hb := branchB_prefix_height_step_b_with_ambient_carry R x hsx A0
  change branchBPrefixHeight R x hsx A0 + branchBPrefixAmbientU R A0 =
    branchBPrefixHeight R x hsx (A0 + routingB B e) + Gminus.u A0 at hb
  rw [hzero, hg.2.2.2.1, hg.2.2.2.2.2.1] at hb
  have hu0 : Gminus.u A0 = 0 := by omega
  have hc := branchB_prefix_height_step_c_with_ambient_carry R x hsx A0
  change branchBPrefixHeight R x hsx A0 + branchBPrefixAmbientV R A0 =
    branchBPrefixHeight R x hsx (A0 + routingC B e) + Gminus.v A0 at hc
  rw [hzero, hg.2.2.2.2.1, hg.2.2.2.2.2.2] at hc
  have hv0 : Gminus.v A0 = 0 := by omega
  have hbase := branchB_actualZeroEdgeBirth_axisC_high_seam_base_eq_inner_notch
    R hB x hsx hbirth haxis
  have hedge := branchB_actualZeroEdgeBirth_edge_nonzero R x hsx hbirth
  rw [hbase] at hedge
  change Gminus.u A0 ≠ 0 ∨ Gminus.v A0 ≠ 0 at hedge
  exact hedge.elim (fun h ↦ h hu0) (fun h ↦ h hv0)

/-- The first principal candidate is exactly the final zero floor at the
actual inner notch. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_principal_inner_notch_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
    rawCandidate B e (actualPrincipalIndex B) A0 = 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
  have hprefix : 0 < branchBPrefixHeight R x hsx A0 :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_inner_notch_prefix_pos
      R hB x hsx hbirth haxis
  have hpacket :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_origin_inner_notch_final_packet
      R hB x hsx hbirth haxis
  change eta B e (r31 R - 1) (r32 R - 1) = 0 ∧ _ at hpacket
  have hg := branchB_inner_notch_canonical_and_carries R
  have hAphysical := eta_eq_physicalHeight_of_isCanonical B e _ _ hg.1
  change eta B e (r31 R - 1) (r32 R - 1) = physicalHeight B e A0 at hAphysical
  have hheight0 : physicalHeight B e A0 = 0 := by omega
  have hheightMin := physicalHeight_eq_max_rawMinimum B e A0
  have hmin : rawMinimum B e A0 ≤ 0 := by
    rw [hheight0] at hheightMin
    omega
  let k := currentSelector B e A0
  have hkpos : 0 < k := currentSelector_pos B e A0
  have hkvalue : rawCandidate B e k A0 ≤ 0 := by
    rw [rawCandidate_currentSelector B e A0]
    exact hmin
  obtain ⟨j, hjpos, hjle, hjvalue⟩ :=
    branchB_candidate_reduce_to_first_principal_block R A0 hkpos
  have hjnonpos : rawCandidate B e j A0 ≤ 0 := hjvalue.trans hkvalue
  have hjeq : j = actualPrincipalIndex B := by
    by_contra hne
    have hjlt : j < actualPrincipalIndex B := Nat.lt_of_le_of_ne hjle hne
    have hjstrict := branchB_prefix_candidate_pos_of_prefixHeight_pos
      R x hsx A0 hprefix hjpos hjlt
    exact (not_lt_of_ge hjnonpos) hjstrict
  have hle : rawCandidate B e (actualPrincipalIndex B) A0 ≤ 0 := by
    simpa [hjeq] using hjnonpos
  have hge := branchB_principal_rawCandidate_nonnegative R A0
  exact le_antisymm hle hge

/-- Expanded principal-candidate equality at the actual inner notch. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_principal_inner_notch_apery_eq
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let Q := actualPrincipalIndex B
    let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
    (Q : ℤ) * routingM B e +
        physicalAlpha B e (A0 - (Q * routingM B e : ℕ)) =
      physicalAlpha B e A0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let Q := actualPrincipalIndex B
  let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
  have hz :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_principal_inner_notch_zero
      R hB x hsx hbirth haxis
  change rawCandidate B e Q A0 = 0 at hz
  have hs := rawCandidate_spec B e Q A0
  change (Q : ℤ) * routingM B e +
      physicalAlpha B e (A0 - (Q * routingM B e : ℕ)) -
        physicalAlpha B e A0 =
      (routingA B e : ℤ) * rawCandidate B e Q A0 at hs
  rw [hz, mul_zero] at hs
  linarith

/-- The principal return itself is an ambient local-`a` Apéry point. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_principal_routingA_predecessor_excluded
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let Q := actualPrincipalIndex B
    (((Q * routingM B e : ℕ) : ℤ) - routingA B e) ∉
      (routingH B e).asRelativeIdeal := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let Q := actualPrincipalIndex B
  let A0 := gridResidue B e (r31 R - 1) (r32 R - 1)
  change (((Q * routingM B e : ℕ) : ℤ) - routingA B e) ∉
    (routingH B e).asRelativeIdeal
  intro hpred
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hpred
  obtain ⟨t, htH, htEq⟩ := hpred
  have heq :=
    branchB_actualZeroEdgeBirth_axisC_high_seam_principal_inner_notch_apery_eq
      R hB x hsx hbirth haxis
  change (Q : ℤ) * routingM B e +
      physicalAlpha B e (A0 - (Q * routingM B e : ℕ)) =
        physicalAlpha B e A0 at heq
  have hshift : physicalAlpha B e (A0 - (Q * routingM B e : ℕ)) ∈
      (routingH B e).asRelativeIdeal :=
    (routingH B e).asRelativeIdeal.aperyRepresentative_mem
      (routingA B e) (A0 - (Q * routingM B e : ℕ))
  have hsum := (routingH B e).asRelativeIdeal.add_mem_nat hshift htH
  have hbad : physicalAlpha B e A0 - routingA B e ∈
      (routingH B e).asRelativeIdeal := by
    rw [← htEq] at hsum
    convert hsum using 1 <;> omega
  exact ((routingH B e).asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem
    (routingA B e) A0) hbad

/-- Corrected strict-prefix barrier for ASTRA's local `a = routingA`.
Unlike the historical B52 lemma, this theorem subtracts `normalizedC`, not
`normalizedA`. -/
theorem branchB_preprincipal_return_window_routingA_predecessor_excluded
    (R : SectorBCriticalRoleBranchB P) (k : ℕ)
    (hkpos : 0 < k) (hklt : k < actualPrincipalIndex P.M.base) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    (((k * routingM B e : ℕ) : ℤ) - routingA B e) ∉
      (routingH B e).asRelativeIdeal := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  change (((k * routingM B e : ℕ) : ℤ) - routingA B e) ∉
    (routingH B e).asRelativeIdeal
  intro hpred
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hpred
  obtain ⟨t, htH, htEq⟩ := hpred
  have haEq : routingA B e = normalizedC R := by
    simpa [B, e] using branchB_inactive_routingA_eq_normalizedC R
  have hHEq : routingH B e = normalizedH B := by
    simpa [B, e] using branchBRoutingH_eq_normalizedH R
  have haH : routingA B e ∈ routingH B e := by
    rw [haEq, hHEq]
    exact branchB_actual_normalizedC_mem R
  have hsum : t + routingA B e ∈ routingH B e :=
    (routingH B e).add_mem htH haH
  have hkm : k * routingM B e = t + routingA B e := by
    exact_mod_cast (show ((k * routingM B e : ℕ) : ℤ) =
      (t + routingA B e : ℕ) by omega)
  have hmem : k * routingM B e ∈ routingH B e := by
    rw [hkm]
    exact hsum
  have hmemNorm : k * normalizedM B ∈ normalizedH B := by
    rw [← hHEq]
    simpa [routingM, normalizedM] using hmem
  have hqle := principalIndex_min (normalizedH B) (normalizedM B)
    B.q_positive hkpos hmemNorm
  exact (Nat.not_le_of_gt hklt) hqle

/-- Complete corrected ASTRA WINDOW-A, including the principal endpoint. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_return_window_routingA
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    ∀ k : ℕ, 0 < k → k ≤ actualPrincipalIndex B →
      (((k * routingM B e : ℕ) : ℤ) - routingA B e) ∉
        (routingH B e).asRelativeIdeal := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  change ∀ k : ℕ, 0 < k → k ≤ actualPrincipalIndex B →
    (((k * routingM B e : ℕ) : ℤ) - routingA B e) ∉
      (routingH B e).asRelativeIdeal
  intro k hkpos hkle
  rcases lt_or_eq_of_le hkle with hklt | rfl
  · exact branchB_preprincipal_return_window_routingA_predecessor_excluded
      R k hkpos hklt
  · exact
      branchB_actualZeroEdgeBirth_axisC_high_seam_principal_routingA_predecessor_excluded
        R hB x hsx hbirth haxis

/-! ### B64: actual x2 minimizer and interior transport -/

/-- The three live gates used by the repaired ASTRA transport, derived from
the actual mixed critical components rather than added to the event packet. -/
theorem branchB_inactive_active_gate_liveness
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :
    0 < eta P.M.base (branchBInactiveReindex R) (c1 R - 1) 0 ∧
      r13 R ≤ eta P.M.base (branchBInactiveReindex R) 0 (r12 R) ∧
      r23 R ≤ eta P.M.base (branchBInactiveReindex R) (r21 R) 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  have hfirst := branchB_first_mixed_boundary_exclusions R hB
  have hsecond :
      R.secondDegree - weights B (R.reindex 2) ∉ B.K := by
    classical
    obtain ⟨h, g, _hne, hdegrees, _hhcount, _hgcount, _hhzero, _hgzero,
      hhgenuine, hggenuine⟩ := L5A2B3.sectorB_actualFiberData P hB
    have hgenuine (d : ℕ) (hd : d ∈ positiveDegrees P.M)
        (C : FiberComponent B d) : ¬BoundaryKilled P.M d C := by
      rw [hdegrees] at hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl
      · exact hhgenuine C
      · exact hggenuine C
    have hd : R.secondDegree ∈ positiveDegrees P.M := by
      rw [R.positiveDegrees_eq]
      simp
    intro hmem
    apply hgenuine R.secondDegree hd R.second.mixedComponent
    exact ⟨R.second.witness, R.second.witness_component, R.reindex 2,
      R.second_witness_two_pos, hmem⟩
  have hr13 : 0 < r13 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.1
  have hr23 : 0 < r23 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.1
  have hfirstDegree :
      R.firstDegree = c1 R * weights B (R.reindex 0) := by
    simpa [B, c1, R.reindex_zero] using R.first.degree_eq_critical
  have hsecondDegree :
      R.secondDegree = c2 R * weights B (R.reindex 1) := by
    simpa [B, c2, R.reindex_one] using R.second.degree_eq_critical
  have hrel1 : c1 R * weights B (R.reindex 0) =
      r12 R * weights B (R.reindex 1) +
        r13 R * weights B (R.reindex 2) := by
    simpa [B, rawA, rawB, rawC, pH, qH] using
      (branchB_actual_herzog_coordinates R).raw_relations.1
  have hrel2 : c2 R * weights B (R.reindex 1) =
      r21 R * weights B (R.reindex 0) +
        r23 R * weights B (R.reindex 2) := by
    simpa [B, rawA, rawB, rawC, uH, vH] using
      (branchB_actual_herzog_coordinates R).raw_relations.2.1
  refine ⟨branchB_inactive_first_pure_height_pos R hB, ?_, ?_⟩
  · by_contra hn
    have hetaLt : eta B e 0 (r12 R) < r13 R := Nat.lt_of_not_ge hn
    have heta : eta B e 0 (r12 R) ≤ r13 R - 1 := Nat.le_pred_of_lt hetaLt
    have hK : gridDegree B e (r13 R - 1) 0 (r12 R) ∈ B.K :=
      (gridDegree_mem_K_iff_eta_le B e 0 (r12 R) (r13 R - 1)).2 heta
    apply hfirst.2
    have heq : gridDegree B e (r13 R - 1) 0 (r12 R) =
        R.firstDegree - weights B (R.reindex 2) := by
      apply Nat.eq_sub_of_add_eq
      calc
        gridDegree B e (r13 R - 1) 0 (r12 R) +
              weights B (R.reindex 2) =
            (r13 R - 1) * weights B (R.reindex 2) +
              r12 R * weights B (R.reindex 1) +
                weights B (R.reindex 2) := by
              simp [B, e, gridDegree]
        _ = r12 R * weights B (R.reindex 1) +
              ((r13 R - 1) + 1) * weights B (R.reindex 2) := by
              simp only [Nat.add_mul, one_mul]
              ac_rfl
        _ = r12 R * weights B (R.reindex 1) +
              r13 R * weights B (R.reindex 2) := by
              rw [show r13 R - 1 + 1 = r13 R by omega]
        _ = c1 R * weights B (R.reindex 0) := hrel1.symm
        _ = R.firstDegree := hfirstDegree.symm
    rw [← heq]
    exact hK
  · by_contra hn
    have hetaLt : eta B e (r21 R) 0 < r23 R := Nat.lt_of_not_ge hn
    have heta : eta B e (r21 R) 0 ≤ r23 R - 1 := Nat.le_pred_of_lt hetaLt
    have hK : gridDegree B e (r23 R - 1) (r21 R) 0 ∈ B.K :=
      (gridDegree_mem_K_iff_eta_le B e (r21 R) 0 (r23 R - 1)).2 heta
    apply hsecond
    have heq : gridDegree B e (r23 R - 1) (r21 R) 0 =
        R.secondDegree - weights B (R.reindex 2) := by
      apply Nat.eq_sub_of_add_eq
      calc
        gridDegree B e (r23 R - 1) (r21 R) 0 +
              weights B (R.reindex 2) =
            (r23 R - 1) * weights B (R.reindex 2) +
              r21 R * weights B (R.reindex 0) +
                weights B (R.reindex 2) := by
              simp [B, e, gridDegree]
        _ = r21 R * weights B (R.reindex 0) +
              ((r23 R - 1) + 1) * weights B (R.reindex 2) := by
              simp only [Nat.add_mul, one_mul]
              ac_rfl
        _ = r21 R * weights B (R.reindex 0) +
              r23 R * weights B (R.reindex 2) := by
              rw [show r23 R - 1 + 1 = r23 R by omega]
        _ = c2 R * weights B (R.reindex 1) := hrel2.symm
        _ = R.secondDegree := hsecondDegree.symm
    rw [← heq]
    exact hK

private theorem branchB_high_seam_rawCandidate_eq_individualHeight
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (i t : ℕ)
    (hdom : L5A2C4OR5.HerzogLShapeDomain
      (branchB_inactive_coherentHerzogData R) i t)
    (hpos : 0 < branchBHighSeamIndividualHeight R
      (branchB_actual_selected_return_anchor_v2 R hB hsx).coordinate.j.toNat
      (branchB_actual_selected_return_anchor_v2 R hB hsx).depth i t) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    rawCandidate B e S.ell (gridResidue B e i t) =
      branchBHighSeamIndividualHeight R S.coordinate.j.toNat S.depth i t := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let H := routingH B e
  let a := routingA B e
  let r := gridResidue B e i t
  let height := branchBHighSeamIndividualHeight R S.coordinate.j.toNat S.depth i t
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have haH : a ∈ H := by
    exact (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
        (AddSubmonoid.subset_closure (by simp [H, a]))
  have hf := branchB_high_seam_individual_height_formula
    R hB x hsx hbirth haxis i t hdom
  change (returnIdeal H S.n).aperyRepresentative a r =
    physicalAlpha B e r + a * height at hf
  rw [returnIdeal_aperyRepresentative_eq_max H S.n a haH r] at hf
  change max (physicalAlpha B e r)
      ((S.n : ℤ) + physicalAlpha B e (r - (S.n : ZMod a))) =
        physicalAlpha B e r + (a : ℤ) * height at hf
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  have hh : (0 : ℤ) < height := by exact_mod_cast hpos
  have hle : physicalAlpha B e r ≤
      (S.n : ℤ) + physicalAlpha B e (r - (S.n : ZMod a)) := by
    by_contra hn
    have hright : (S.n : ℤ) + physicalAlpha B e (r - (S.n : ZMod a)) ≤
        physicalAlpha B e r := le_of_not_ge hn
    rw [max_eq_left hright] at hf
    nlinarith
  have hshift :
      (S.n : ℤ) + physicalAlpha B e (r - (S.n : ZMod a)) =
        physicalAlpha B e r + (a : ℤ) * height := by
    calc
      _ = max (physicalAlpha B e r)
          ((S.n : ℤ) + physicalAlpha B e (r - (S.n : ZMod a))) :=
        (max_eq_right hle).symm
      _ = _ := hf
  have hs := rawCandidate_spec B e S.ell r
  have hn : S.n = S.ell * routingM B e := by
    simpa [routingM] using S.n_eq
  change (S.ell : ℤ) * routingM B e +
      physicalAlpha B e (r - (S.ell * routingM B e : ℕ)) -
        physicalAlpha B e r =
      (a : ℤ) * rawCandidate B e S.ell r at hs
  rw [← hn] at hs
  have hane : (a : ℤ) ≠ 0 := ne_of_gt ha
  apply (mul_left_cancel₀ hane)
  nlinarith

/-- Strict ASTRA cap at `x2`, with the selected-return candidate exposed
source-exactly. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_x2_cap
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let S := branchB_actual_selected_return_anchor_v2 R hB hsx
    let B := P.M.base
    let e := branchBInactiveReindex R
    let X := eta B e (c1 R - 1) 0
    S.depth < r31 R ∧
      rawCandidate B e S.ell (gridResidue B e (c1 R - 1) 0) =
        (S.coordinate.j.toNat : ℤ) - r13 R ∧
      1 ≤ X ∧ X ≤ S.coordinate.j.toNat - r13 R ∧ X < r23 R := by
  let S := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let j := S.coordinate.j.toNat
  let X := eta B e (c1 R - 1) 0
  have hdlt := branchB_actualZeroEdgeBirth_axisC_high_seam_depth_lt_r31
    R hB x hsx hbirth haxis
  have hlive := (branchB_inactive_active_gate_liveness R hB).1
  have hr13 : 0 < r13 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.1
  have hr23 : 0 < r23 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hc2pos : 0 < c2 R := by
    have hr12 : 0 < r12 R := by
      simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
    have hs : c2 R = r12 R + r32 R := by
      simpa [pH, zH] using
        (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    omega
  have hsum3 : c3 R = r13 R + r23 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
  have hj0 : (0 : ℤ) ≤ S.coordinate.j := by
    have hh : (r13 R : ℤ) < S.coordinate.j := by
      simpa [qH] using haxis.2.1
    have hr13z : (0 : ℤ) < r13 R := by exact_mod_cast hr13
    omega
  have hj : S.coordinate.j = (j : ℤ) := (Int.toNat_of_nonneg hj0).symm
  have hju : r13 R < j := by
    have hh := haxis.2.1
    rw [hj] at hh
    exact_mod_cast (show (r13 R : ℤ) < j by simpa [qH] using hh)
  have hjc : j < c3 R := by
    have hh := haxis.2.2.1
    rw [hj] at hh
    have hh' : (j : ℤ) < r13 R + r23 R := by simpa [qH, vH] using hh
    exact_mod_cast (show (j : ℤ) < c3 R by omega)
  have hmaps := branchB_inactive_coherent_coefficients R
  dsimp only [D, B, e] at hmaps
  obtain ⟨_h12, h13, _h21, _h23, _h31, _h32⟩ := hmaps
  have hdom : L5A2C4OR5.HerzogLShapeDomain D (c1 R - 1) 0 := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change c1 R - 1 < L5A2C4A.c2 B e ∧
      0 < L5A2C4A.c3 B e ∧
      (c1 R - 1 < L5A2C4D.cr12 D ∨ 0 < L5A2C4D.cr13 D)
    rw [show L5A2C4A.c2 B e = c1 R by
        simpa [B, e] using branchB_inactive_coherent_c2 R,
      show L5A2C4A.c3 B e = c2 R by
        simpa [B, e] using branchB_inactive_coherent_c3 R,
      show L5A2C4D.cr13 D = r32 R by simpa [D, B, e] using h13]
    exact ⟨by omega, hc2pos, Or.inr hr32⟩
  have hheight : branchBHighSeamIndividualHeight R j S.depth
      (c1 R - 1) 0 = j - r13 R := by
    have hdpos := S.depth_pos
    have hnlt : ¬c1 R - 1 < c1 R - S.depth := by omega
    simp [branchBHighSeamIndividualHeight, hr32, hnlt]
  have hheightPos : 0 < branchBHighSeamIndividualHeight R j S.depth
      (c1 R - 1) 0 := by rw [hheight]; omega
  have hcand := branchB_high_seam_rawCandidate_eq_individualHeight
    R hB x hsx hbirth haxis (c1 R - 1) 0 hdom hheightPos
  change rawCandidate B e S.ell (gridResidue B e (c1 R - 1) 0) =
    branchBHighSeamIndividualHeight R j S.depth (c1 R - 1) 0 at hcand
  rw [hheight] at hcand
  have hcandZ : rawCandidate B e S.ell (gridResidue B e (c1 R - 1) 0) =
      (j : ℤ) - r13 R := by
    rw [hcand]
    exact_mod_cast (Nat.cast_sub (Nat.le_of_lt hju) :
      ((j - r13 R : ℕ) : ℤ) = (j : ℤ) - r13 R)
  have hcanon := herzogLShapeCanonicality B e D _ _ hdom
  have hetaPhys := eta_eq_physicalHeight_of_isCanonical B e _ _ hcanon
  have hrawMin := physicalHeight_eq_max_rawMinimum B e
    (gridResidue B e (c1 R - 1) 0)
  change X = physicalHeight B e (gridResidue B e (c1 R - 1) 0) at hetaPhys
  have hminEq : rawMinimum B e (gridResidue B e (c1 R - 1) 0) = X := by
    rw [← hetaPhys] at hrawMin
    change (X : ℤ) = max 0 (rawMinimum B e
      (gridResidue B e (c1 R - 1) 0)) at hrawMin
    have hxpos : (0 : ℤ) < X := by exact_mod_cast hlive
    omega
  have hleRaw := rawMinimum_le B e (gridResidue B e (c1 R - 1) 0) S.ell_pos
  rw [hminEq, hcand] at hleRaw
  have hleX : X ≤ j - r13 R := by exact_mod_cast hleRaw
  have hltX : X < r23 R := by omega
  change S.depth < r31 R ∧
    rawCandidate B e S.ell (gridResidue B e (c1 R - 1) 0) =
      (j : ℤ) - r13 R ∧
    1 ≤ X ∧ X ≤ j - r13 R ∧ X < r23 R
  exact ⟨hdlt, hcandZ, by dsimp [X, B, e]; omega, hleX, hltX⟩

/-- A genuine minimizer at `x2` can be chosen in the first principal return
window.  This does not identify it with the selected high-seam return. -/
theorem branchB_high_axisC_x2_finite_window_minimizer
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let X2 := gridResidue B e (c1 R - 1) 0
    ∃ k : ℕ, 0 < k ∧ k ≤ actualPrincipalIndex B ∧
      rawCandidate B e k X2 = eta B e (c1 R - 1) 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let X2 := gridResidue B e (c1 R - 1) 0
  let X := eta B e (c1 R - 1) 0
  have hxpos := (branchB_inactive_active_gate_liveness R hB).1
  have hcanon := branchB_high_seam_target_U_X2_canonical R
  have hetaPhys := eta_eq_physicalHeight_of_isCanonical B e _ _ hcanon
  change X = physicalHeight B e X2 at hetaPhys
  have hheightMin := physicalHeight_eq_max_rawMinimum B e X2
  have hmin : rawMinimum B e X2 = X := by
    rw [← hetaPhys] at hheightMin
    change (X : ℤ) = max 0 (rawMinimum B e X2) at hheightMin
    have hxposZ : (0 : ℤ) < X := by exact_mod_cast hxpos
    omega
  let q := currentSelector B e X2
  have hqpos : 0 < q := currentSelector_pos B e X2
  have hqval : rawCandidate B e q X2 = X := by
    rw [rawCandidate_currentSelector B e X2, hmin]
  obtain ⟨k, hkpos, hkle, hkq⟩ :=
    branchB_candidate_reduce_to_first_principal_block R X2 hqpos
  have hlower := rawMinimum_le B e X2 hkpos
  have hkeq : rawCandidate B e k X2 = X := by
    rw [hmin] at hlower
    have hu := hkq.trans_eq hqval
    exact le_antisymm hu hlower
  exact ⟨k, hkpos, hkle, hkeq⟩

private theorem branchB_inactive_physicalAlpha_canonical_coordinates
    (R : SectorBCriticalRoleBranchB P)
    (s : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    ∃ I J : ℕ,
      L5A2C4OR5.HerzogLShapeDomain
          (branchB_inactive_coherentHerzogData R) I J ∧
        gridResidue P.M.base (branchBInactiveReindex R) I J = s ∧
        physicalAlpha P.M.base (branchBInactiveReindex R) s =
          normalizedGrid P.M.base (branchBInactiveReindex R) 0 I J := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let alpha := physicalAlpha B e s
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have halphaMem : alpha ∈ (routingH B e).asRelativeIdeal := by
    dsimp [alpha, physicalAlpha]
    exact (routingH B e).asRelativeIdeal.aperyRepresentative_mem a s
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at halphaMem
  obtain ⟨n, hnH, hnalpha⟩ := halphaMem
  obtain ⟨x, y, z, hnfac⟩ := routingH_factorization B e hnH
  obtain ⟨I, J, q, hdom, hreduce⟩ := coherent_exists_reduction B e D y z
  have hnterminal : n = I * b + J * c + (x + q) * a := by
    calc
      n = x * a + y * b + z * c := hnfac
      _ = x * a + (y * b + z * c) := by ring
      _ = x * a + (I * b + J * c + q * a) := by rw [hreduce]
      _ = I * b + J * c + (x + q) * a := by ring
  have hnResidue : (n : ZMod a) = s := by
    have hm := (routingH B e).asRelativeIdeal.aperyRepresentative_mod a s
    change (alpha : ZMod a) = s at hm
    rw [hnalpha] at hm
    exact_mod_cast hm
  have hres : gridResidue B e I J = s := by
    simp only [gridResidue]
    calc
      (I : ZMod a) * routingB B e + (J : ZMod a) * routingC B e =
          ((I * b + J * c : ℕ) : ZMod a) := by
        push_cast
        rfl
      _ = (n : ZMod a) := by
        rw [hnterminal]
        push_cast
        simp
      _ = s := hnResidue
  have hcanon := herzogLShapeCanonicality B e D I J hdom
  have halpha : physicalAlpha B e s = normalizedGrid B e 0 I J := by
    rw [← hres]
    exact hcanon.symm
  exact ⟨I, J, hdom, hres, halpha⟩

set_option maxHeartbeats 1200000 in
/-- Every first-window minimizer at `x2` has an interior shifted Apéry point,
and that same return transports without a hidden carry to `y2` and
`y2minus`. -/
theorem branchB_high_axisC_x2_minimizer_interior_transport
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R)
    (k : ℕ) (hkpos : 0 < k) (hkle : k ≤ actualPrincipalIndex P.M.base)
    (hkmin :
      let B := P.M.base
      let e := branchBInactiveReindex R
      rawCandidate B e k (gridResidue B e (c1 R - 1) 0) =
        eta B e (c1 R - 1) 0) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let X := eta B e (c1 R - 1) 0
    let X2 := gridResidue B e (c1 R - 1) 0
    let Y2 := gridResidue B e 0 (r12 R)
    let Ym := gridResidue B e 0 (r12 R - 1)
    ∃ I J : ℕ,
      L5A2C4OR5.HerzogLShapeDomain
          (branchB_inactive_coherentHerzogData R) I J ∧
        physicalAlpha B e (X2 - (k * routingM B e : ℕ)) =
          normalizedGrid B e 0 I J ∧
        I + 1 < r31 R ∧ 1 ≤ J ∧
        rawCandidate B e k Y2 = X + r13 R ∧
        rawCandidate B e k Ym = X + r13 R := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let X := eta B e (c1 R - 1) 0
  let X2 := gridResidue B e (c1 R - 1) 0
  let Y2 := gridResidue B e 0 (r12 R)
  let Ym := gridResidue B e 0 (r12 R - 1)
  let T := X2 - (k * routingM B e : ℕ)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change rawCandidate B e k X2 = X at hkmin
  have hcap := branchB_actualZeroEdgeBirth_axisC_high_seam_x2_cap
    R hB x hsx hbirth haxis
  change _ ∧ _ ∧ 1 ≤ X ∧ _ ∧ X < r23 R at hcap
  have hxpos : 0 < X := by omega
  have hxlt : X < r23 R := hcap.2.2.2.2
  obtain ⟨I, J, hdom, hres, halphaT⟩ :=
    branchB_inactive_physicalAlpha_canonical_coordinates R T
  have hmaps := branchB_inactive_coherent_coefficients R
  dsimp only [D, B, e] at hmaps
  obtain ⟨h12, h13, _h21, _h23, _h31, _h32⟩ := hmaps
  have hbounds := hdom
  simp only [L5A2C4OR5.HerzogLShapeDomain] at hbounds
  change I < L5A2C4A.c2 B e ∧ J < L5A2C4A.c3 B e ∧ _ at hbounds
  rw [show L5A2C4A.c2 B e = c1 R by
      simpa [B, e] using branchB_inactive_coherent_c2 R,
    show L5A2C4A.c3 B e = c2 R by
      simpa [B, e] using branchB_inactive_coherent_c3 R,
    show L5A2C4D.cr12 D = r31 R by simpa [D, B, e] using h12,
    show L5A2C4D.cr13 D = r32 R by simpa [D, B, e] using h13] at hbounds
  have hIc1 : I < c1 R := hbounds.1
  have hJc2 : J < c2 R := hbounds.2.1
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hr31 : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hrel : c1 R * b = r13 R * a + r12 R * c := by
    dsimp [a, b, c, B, e]
    simpa [Nat.add_comm] using
      (branchB_actual_herzog_coordinates R).normalized_relations.1
  have haH : a ∈ routingH B e := by
    exact (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
        (AddSubmonoid.subset_closure (by simp [a]))
  have hXcanon := branchB_high_seam_target_U_X2_canonical R
  have halphaX : physicalAlpha B e X2 = normalizedGrid B e 0 (c1 R - 1) 0 := by
    exact hXcanon.symm
  have hspecX := rawCandidate_spec B e k X2
  change (k : ℤ) * routingM B e + physicalAlpha B e T -
      physicalAlpha B e X2 = (a : ℤ) * rawCandidate B e k X2 at hspecX
  rw [hkmin, halphaT, halphaX] at hspecX
  simp only [normalizedGrid, zero_mul, zero_add, add_zero] at hspecX
  change (k : ℤ) * routingM B e +
      ((I * b + J * c : ℕ) : ℤ) -
        (((c1 R - 1) * b : ℕ) : ℤ) =
      (a : ℤ) * X at hspecX
  have hI : I + 1 < r31 R := by
    by_contra hn
    have hIp : r31 R - 1 ≤ I := by omega
    let tail := (r23 R - 1 - X) * a + (I - (r31 R - 1)) * b + J * c
    have htailH : tail ∈ routingH B e := by
      have haH' := (routingH B e).toAddSubmonoid.nsmul_mem haH
        (r23 R - 1 - X)
      have hbH := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e)
        (I - (r31 R - 1))
      have hcH := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e) J
      have hab := (routingH B e).add_mem haH' hbH
      have habc := (routingH B e).add_mem hab hcH
      simpa [tail, nsmul_eq_mul, Nat.add_assoc] using habc
    have htailZ : (normalizedGrid B e (r23 R - 1) (r21 R) 0 : ℤ) -
        (k : ℤ) * routingM B e = tail := by
      simp only [normalizedGrid, zero_mul, add_zero]
      change (((r23 R - 1) * a + r21 R * b : ℕ) : ℤ) -
        (k : ℤ) * routingM B e = tail
      dsimp [tail]
      push_cast
      have hxle : X ≤ r23 R - 1 := by omega
      have hIle : r31 R - 1 ≤ I := hIp
      rw [Nat.cast_sub hxle, Nat.cast_sub hIle]
      rw [Nat.cast_sub (by omega : 1 ≤ r31 R)]
      push_cast at hspecX
      rw [Nat.cast_sub (by omega : 1 ≤ c1 R)] at hspecX
      rw [hsum1] at hspecX
      push_cast at hspecX
      linear_combination -hspecX
    have hGmem : (normalizedGrid B e (r23 R - 1) (r21 R) 0 : ℤ) ∈
        routingI B e := by
      apply (mem_routingI_iff_positive_return B e _).2
      refine ⟨k, hkpos, ?_, ?_⟩
      · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
        let g := normalizedGrid B e (r23 R - 1) (r21 R) 0
        refine ⟨g, ?_, rfl⟩
        have haH' := (routingH B e).toAddSubmonoid.nsmul_mem haH (r23 R - 1)
        have hbH := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e)
          (r21 R)
        have hcH := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e) 0
        have habc := (routingH B e).add_mem ((routingH B e).add_mem haH' hbH) hcH
        simpa [g, normalizedGrid, nsmul_eq_mul, Nat.add_assoc] using habc
      · rw [htailZ]
        exact (NumericalSemigroup.mem_asRelativeIdeal_iff (routingH B e) tail).2
          ⟨tail, htailH, rfl⟩
    have hetaLe := (normalizedGrid_mem_iff_eta_le B e
      (r23 R - 1) (r21 R) 0).1 hGmem
    have hlive := (branchB_inactive_active_gate_liveness R hB).2.2
    change r23 R ≤ eta B e (r21 R) 0 at hlive
    omega
  have hJ : 1 ≤ J := by
    by_contra hn
    have hJ0 : J = 0 := Nat.eq_zero_of_not_pos hn
    let tail := (X - 1) * a + (c1 R - 1 - I) * b
    have htailH : tail ∈ routingH B e := by
      have haH' := (routingH B e).toAddSubmonoid.nsmul_mem haH (X - 1)
      have hbH := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e)
        (c1 R - 1 - I)
      have hab := (routingH B e).add_mem haH' hbH
      simpa [tail, nsmul_eq_mul, Nat.add_assoc] using hab
    have htailZ : (((k * routingM B e : ℕ) : ℤ) - a) = tail := by
      dsimp [tail]
      push_cast
      have hxle : 1 ≤ X := by omega
      have hIle : I ≤ c1 R - 1 := by omega
      rw [Nat.cast_sub hxle, Nat.cast_sub hIle]
      rw [Nat.cast_sub (by omega : 1 ≤ c1 R)]
      rw [hJ0] at hspecX
      simp only [Nat.cast_zero, zero_mul, add_zero] at hspecX
      push_cast at hspecX
      rw [Nat.cast_sub (by omega : 1 ≤ c1 R)] at hspecX
      linear_combination hspecX
    have hwindow :=
      branchB_actualZeroEdgeBirth_axisC_high_seam_return_window_routingA
        R hB x hsx hbirth haxis k hkpos hkle
    apply hwindow
    rw [htailZ]
    exact (NumericalSemigroup.mem_asRelativeIdeal_iff (routingH B e) tail).2
      ⟨tail, htailH, rfl⟩
  have hdomY : L5A2C4OR5.HerzogLShapeDomain D (I + 1) J := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change I + 1 < L5A2C4A.c2 B e ∧ J < L5A2C4A.c3 B e ∧
      (I + 1 < L5A2C4D.cr12 D ∨ J < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨by omega, hJc2, Or.inl hI⟩
  have hdomYm : L5A2C4OR5.HerzogLShapeDomain D (I + 1) (J - 1) := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change I + 1 < L5A2C4A.c2 B e ∧ J - 1 < L5A2C4A.c3 B e ∧
      (I + 1 < L5A2C4D.cr12 D ∨ J - 1 < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨by omega, by omega, Or.inl hI⟩
  have hcanonY := herzogLShapeCanonicality B e D _ _ hdomY
  have hcanonYm := herzogLShapeCanonicality B e D _ _ hdomYm
  have hresY : gridResidue B e (I + 1) J = Y2 - (k * routingM B e : ℕ) := by
    have hxy : gridResidue B e (c1 R - 1) 0 + b = gridResidue B e 0 (r12 R) := by
      simp only [gridResidue]
      have hm := congrArg (fun n : ℕ => (n : ZMod a)) hrel
      push_cast at hm
      simp at hm
      push_cast
      have hc1step : c1 R - 1 + 1 = c1 R := by omega
      rw [← hc1step] at hm
      push_cast at hm
      linear_combination hm
    have hstep := gridResidue_add_b B e I J
    rw [hres] at hstep
    calc
      gridResidue B e (I + 1) J = T + b := hstep
      _ = Y2 - (k * routingM B e : ℕ) := by
        dsimp [T, X2, Y2]
        rw [← hxy]
        abel
  have hresYm : gridResidue B e (I + 1) (J - 1) =
      Ym - (k * routingM B e : ℕ) := by
    have hstepL := gridResidue_add_c B e (I + 1) (J - 1)
    have hstepR := gridResidue_add_c B e 0 (r12 R - 1)
    rw [show J - 1 + 1 = J by omega] at hstepL
    rw [show r12 R - 1 + 1 = r12 R by omega] at hstepR
    have hstepL' : gridResidue B e (I + 1) (J - 1) =
        gridResidue B e (I + 1) J - routingC B e := by
      calc
        gridResidue B e (I + 1) (J - 1) =
            (gridResidue B e (I + 1) (J - 1) + routingC B e) -
              routingC B e := by abel
        _ = gridResidue B e (I + 1) J - routingC B e := by rw [hstepL]
    have hstepR' : Ym = Y2 - routingC B e := by
      dsimp [Ym, Y2]
      calc
        gridResidue B e 0 (r12 R - 1) =
            (gridResidue B e 0 (r12 R - 1) + routingC B e) -
              routingC B e := by abel
        _ = gridResidue B e 0 (r12 R) - routingC B e := by rw [hstepR]
    calc
      gridResidue B e (I + 1) (J - 1) =
          gridResidue B e (I + 1) J - routingC B e := hstepL'
      _ = (Y2 - (k * routingM B e : ℕ)) - routingC B e := by rw [hresY]
      _ = Ym - (k * routingM B e : ℕ) := by rw [hstepR']; abel
  have halphaYshift : physicalAlpha B e (Y2 - (k * routingM B e : ℕ)) =
      normalizedGrid B e 0 (I + 1) J := by
    rw [← hresY]
    exact hcanonY.symm
  have halphaYmshift : physicalAlpha B e (Ym - (k * routingM B e : ℕ)) =
      normalizedGrid B e 0 (I + 1) (J - 1) := by
    rw [← hresYm]
    exact hcanonYm.symm
  have hYcanon : IsCanonicalTailGridPoint B e 0 (r12 R) := by
    apply herzogLShapeCanonicality B e D
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change 0 < L5A2C4A.c2 B e ∧ r12 R < L5A2C4A.c3 B e ∧
      (0 < L5A2C4D.cr12 D ∨ r12 R < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨by omega, by omega, Or.inl hr31⟩
  have hYmcanon : IsCanonicalTailGridPoint B e 0 (r12 R - 1) := by
    apply herzogLShapeCanonicality B e D
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change 0 < L5A2C4A.c2 B e ∧ r12 R - 1 < L5A2C4A.c3 B e ∧
      (0 < L5A2C4D.cr12 D ∨ r12 R - 1 < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨by omega, by omega, Or.inl hr31⟩
  have hcandY : rawCandidate B e k Y2 = X + r13 R := by
    have hs := rawCandidate_spec B e k Y2
    change (k : ℤ) * routingM B e +
      physicalAlpha B e (Y2 - (k * routingM B e : ℕ)) -
        physicalAlpha B e Y2 = (a : ℤ) * rawCandidate B e k Y2 at hs
    rw [halphaYshift, hYcanon.symm] at hs
    simp only [normalizedGrid, zero_mul, zero_add] at hs
    change (k : ℤ) * routingM B e +
        (((I + 1) * b + J * c : ℕ) : ℤ) -
          ((r12 R * c : ℕ) : ℤ) =
        (a : ℤ) * rawCandidate B e k Y2 at hs
    push_cast at hspecX hs
    rw [Nat.cast_sub (by omega : 1 ≤ c1 R)] at hspecX
    have hrelZ : (c1 R : ℤ) * b = (r13 R : ℤ) * a + (r12 R : ℤ) * c := by
      exact_mod_cast hrel
    have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
    have hmul : (a : ℤ) * rawCandidate B e k Y2 =
        (a : ℤ) * ((X : ℤ) + r13 R) := by
      ring_nf at hs hspecX hrelZ ⊢
      linarith
    exact mul_left_cancel₀ (ne_of_gt ha) hmul
  have hcandYm : rawCandidate B e k Ym = X + r13 R := by
    have hs := rawCandidate_spec B e k Ym
    change (k : ℤ) * routingM B e +
      physicalAlpha B e (Ym - (k * routingM B e : ℕ)) -
        physicalAlpha B e Ym = (a : ℤ) * rawCandidate B e k Ym at hs
    rw [halphaYmshift, hYmcanon.symm] at hs
    simp only [normalizedGrid, zero_mul, zero_add] at hs
    change (k : ℤ) * routingM B e +
        (((I + 1) * b + (J - 1) * c : ℕ) : ℤ) -
          (((r12 R - 1) * c : ℕ) : ℤ) =
        (a : ℤ) * rawCandidate B e k Ym at hs
    push_cast at hspecX hs
    rw [Nat.cast_sub (by omega : 1 ≤ c1 R)] at hspecX
    have hrelZ : (c1 R : ℤ) * b = (r13 R : ℤ) * a + (r12 R : ℤ) * c := by
      exact_mod_cast hrel
    have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
    have hJcast : ((J - 1 : ℕ) : ℤ) = (J : ℤ) - 1 := by omega
    have hr12cast : ((r12 R - 1 : ℕ) : ℤ) = (r12 R : ℤ) - 1 := by omega
    rw [hJcast, hr12cast] at hs
    have hmul : (a : ℤ) * rawCandidate B e k Ym =
        (a : ℤ) * ((X : ℤ) + r13 R) := by
      ring_nf at hs hspecX hrelZ ⊢
      linarith
    exact mul_left_cancel₀ (ne_of_gt ha) hmul
  exact ⟨I, J, hdom, halphaT, hI, hJ, hcandY, hcandYm⟩

/-- The transported first-window minimizer gives the two active-gate upper
bounds.  This is the forward half of the B64 clamp; no reverse-envelope
identification is used. -/
theorem branchB_high_axisC_active_gate_upper_bounds
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let X := eta B e (c1 R - 1) 0
    eta B e 0 (r12 R) ≤ X + r13 R ∧
      eta B e 0 (r12 R - 1) ≤ X + r13 R := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let X := eta B e (c1 R - 1) 0
  let Y2 := gridResidue B e 0 (r12 R)
  let Ym := gridResidue B e 0 (r12 R - 1)
  obtain ⟨k, hkpos, hkle, hkmin⟩ :=
    branchB_high_axisC_x2_finite_window_minimizer R hB x hsx hbirth haxis
  obtain ⟨I, J, hdom, halpha, hI, hJ, hcandY, hcandYm⟩ :=
    branchB_high_axisC_x2_minimizer_interior_transport
      R hB x hsx hbirth haxis k hkpos hkle hkmin
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hr21 : 0 < r21 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.1
  have hr31 : 0 < r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hc1pos : 0 < c1 R := by omega
  have hr12lt : r12 R < c2 R := by omega
  have hYcanon : IsCanonicalTailGridPoint B e 0 (r12 R) := by
    apply herzogLShapeCanonicality B e D
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change 0 < L5A2C4A.c2 B e ∧ r12 R < L5A2C4A.c3 B e ∧
      (0 < L5A2C4D.cr12 D ∨ r12 R < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨hc1pos, hr12lt, Or.inl hr31⟩
  have hYmcanon : IsCanonicalTailGridPoint B e 0 (r12 R - 1) := by
    apply herzogLShapeCanonicality B e D
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change 0 < L5A2C4A.c2 B e ∧ r12 R - 1 < L5A2C4A.c3 B e ∧
      (0 < L5A2C4D.cr12 D ∨ r12 R - 1 < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨hc1pos, by omega, Or.inl hr31⟩
  have hY : eta B e 0 (r12 R) ≤ X + r13 R := by
    have heta := eta_eq_physicalHeight_of_isCanonical B e 0 (r12 R) hYcanon
    change eta B e 0 (r12 R) = physicalHeight B e Y2 at heta
    have hheight := physicalHeight_eq_max_rawMinimum B e Y2
    rw [← heta] at hheight
    change (eta B e 0 (r12 R) : ℤ) = max 0 (rawMinimum B e Y2) at hheight
    have hraw := rawMinimum_le B e Y2 hkpos
    rw [hcandY] at hraw
    have hz : (eta B e 0 (r12 R) : ℤ) ≤ (X : ℤ) + r13 R := by
      rw [hheight]
      exact max_le (by positivity) hraw
    exact_mod_cast hz
  have hYm : eta B e 0 (r12 R - 1) ≤ X + r13 R := by
    have heta := eta_eq_physicalHeight_of_isCanonical B e 0 (r12 R - 1) hYmcanon
    change eta B e 0 (r12 R - 1) = physicalHeight B e Ym at heta
    have hheight := physicalHeight_eq_max_rawMinimum B e Ym
    rw [← heta] at hheight
    change (eta B e 0 (r12 R - 1) : ℤ) = max 0 (rawMinimum B e Ym) at hheight
    have hraw := rawMinimum_le B e Ym hkpos
    rw [hcandYm] at hraw
    have hz : (eta B e 0 (r12 R - 1) : ℤ) ≤ (X : ℤ) + r13 R := by
      rw [hheight]
      exact max_le (by positivity) hraw
    exact_mod_cast hz
  exact ⟨hY, hYm⟩

/-! ### B65: reverse envelope and active-gate clamp -/

/-- At the second active gate, a genuine minimizing return can be chosen in
the first principal window.  This is independent of the minimizer chosen at
the first gate. -/
theorem branchB_high_axisC_y2_finite_window_minimizer
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let Y2 := gridResidue B e 0 (r12 R)
    ∃ h : ℕ, 0 < h ∧ h ≤ actualPrincipalIndex B ∧
      rawCandidate B e h Y2 = eta B e 0 (r12 R) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let Y2 := gridResidue B e 0 (r12 R)
  let Y := eta B e 0 (r12 R)
  let D := branchB_inactive_coherentHerzogData R
  have hr13 : 0 < r13 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.1
  have hYpos : 0 < Y := by
    have hgate := (branchB_inactive_active_gate_liveness R hB).2.1
    dsimp only [Y, B, e]
    omega
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hsum1 : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hcanon : IsCanonicalTailGridPoint B e 0 (r12 R) := by
    apply herzogLShapeCanonicality B e D
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change 0 < L5A2C4A.c2 B e ∧ r12 R < L5A2C4A.c3 B e ∧
      (0 < L5A2C4D.cr12 D ∨ r12 R < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨by omega, by omega, Or.inl hr31⟩
  have hetaPhys := eta_eq_physicalHeight_of_isCanonical B e 0 (r12 R) hcanon
  change Y = physicalHeight B e Y2 at hetaPhys
  have hheightMin := physicalHeight_eq_max_rawMinimum B e Y2
  have hmin : rawMinimum B e Y2 = Y := by
    rw [← hetaPhys] at hheightMin
    change (Y : ℤ) = max 0 (rawMinimum B e Y2) at hheightMin
    have hYposZ : (0 : ℤ) < Y := by exact_mod_cast hYpos
    omega
  let q := currentSelector B e Y2
  have hqpos : 0 < q := currentSelector_pos B e Y2
  have hqval : rawCandidate B e q Y2 = Y := by
    rw [rawCandidate_currentSelector B e Y2, hmin]
  obtain ⟨h, hhpos, hhle, hhq⟩ :=
    branchB_candidate_reduce_to_first_principal_block R Y2 hqpos
  have hlower := rawMinimum_le B e Y2 hhpos
  have hheq : rawCandidate B e h Y2 = Y := by
    rw [hmin] at hlower
    exact le_antisymm (hhq.trans_eq hqval) hlower
  exact ⟨h, hhpos, hhle, hheq⟩

/-- Exact ambient Apéry `b`-carry specification in the inactive chart. -/
theorem branchB_inactive_b_carry_spec
    (R : SectorBCriticalRoleBranchB P)
    (T : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    physicalAlpha B e T + routingB B e =
      physicalAlpha B e (T + routingB B e) +
        (routingA B e : ℤ) * branchBPrefixAmbientU R T := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hs := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e) T
  change branchBPrefixAlpha R T + routingB B e =
    branchBPrefixAlpha R (T + routingB B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientU R T at hs
  simpa [branchBPrefixAlpha, physicalAlpha, B, e] using hs

/-- The inactive Herzog L-shape has exactly the ordinary, lower-wrap, and
upper-wrap ambient `b`-carry classes. -/
theorem branchB_inactive_b_carry_trichotomy
    (R : SectorBCriticalRoleBranchB P)
    (T : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let S := T + routingB B e
    let sigma := branchBPrefixAmbientU R T
    sigma = 0 ∨
      (∃ t : ℕ, T = gridResidue B e (c1 R - 1) t ∧
        t < r32 R ∧ sigma = r13 R ∧
        S = gridResidue B e 0 (r12 R + t)) ∨
      (∃ t : ℕ, T = gridResidue B e (r31 R - 1) t ∧
        r32 R ≤ t ∧ t < c2 R ∧ sigma = c3 R ∧
        S = gridResidue B e 0 (t - r32 R)) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let S := T + b
  let sigma := branchBPrefixAmbientU R T
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  obtain ⟨I, J, hdom, hres, halphaT⟩ :=
    branchB_inactive_physicalAlpha_canonical_coordinates R T
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hc1sum : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hc2sum : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hc3sum : c3 R = r13 R + r23 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
  have hbounds := hdom
  simp only [L5A2C4OR5.HerzogLShapeDomain] at hbounds
  change I < L5A2C4A.c2 B e ∧ J < L5A2C4A.c3 B e ∧
    (I < L5A2C4D.cr12 D ∨ J < L5A2C4D.cr13 D) at hbounds
  rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
    branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13] at hbounds
  have hspec := branchB_inactive_b_carry_spec R T
  change physicalAlpha B e T + b = physicalAlpha B e S +
    (a : ℤ) * sigma at hspec
  by_cases hord : I + 1 < c1 R ∧ (I + 1 < r31 R ∨ J < r32 R)
  · left
    have hdomS : L5A2C4OR5.HerzogLShapeDomain D (I + 1) J := by
      simp only [L5A2C4OR5.HerzogLShapeDomain]
      change I + 1 < L5A2C4A.c2 B e ∧ J < L5A2C4A.c3 B e ∧
        (I + 1 < L5A2C4D.cr12 D ∨ J < L5A2C4D.cr13 D)
      rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
        branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
      exact ⟨hord.1, hbounds.2.1, hord.2⟩
    have hcanonS := herzogLShapeCanonicality B e D _ _ hdomS
    have halphaS := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e (I + 1) J hcanonS
    have hstep := gridResidue_add_b B e I J
    have hS : S = gridResidue B e (I + 1) J := by
      dsimp only [S, b]
      rw [← hres]
      exact hstep.symm
    rw [hS, halphaT, halphaS] at hspec
    simp only [normalizedGrid, zero_mul, zero_add] at hspec
    have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
    have hp : (a : ℤ) * sigma = 0 := by
      change (((I * b + J * c : ℕ) : ℤ) + b) =
        (((I + 1) * b + J * c : ℕ) : ℤ) + (a : ℤ) * sigma at hspec
      push_cast at hspec
      ring_nf at hspec
      linarith
    exact (Nat.mul_eq_zero.mp (by exact_mod_cast hp)).resolve_left
      (Nat.ne_of_gt (routingA_pos B e))
  · by_cases hJ : J < r32 R
    · right; left
      have hI : I = c1 R - 1 := by omega
      have hsuccRes : S = gridResidue B e 0 (r12 R + J) := by
        have hstep := gridResidue_add_b B e I J
        have hwrap := branchB_high_seam_lower_wrap_residue R (c1 R) 0 J
          (by omega)
        calc
          S = gridResidue B e (I + 1) J := by
            dsimp only [S, b]
            rw [← hres]
            exact hstep.symm
          _ = gridResidue B e (c1 R) J := by rw [hI]; congr 2 <;> omega
          _ = gridResidue B e 0 (r12 R + J) := by
            simpa [Nat.add_comm] using hwrap
      have hdomS : L5A2C4OR5.HerzogLShapeDomain D 0 (r12 R + J) := by
        simp only [L5A2C4OR5.HerzogLShapeDomain]
        change 0 < L5A2C4A.c2 B e ∧ r12 R + J < L5A2C4A.c3 B e ∧
          (0 < L5A2C4D.cr12 D ∨ r12 R + J < L5A2C4D.cr13 D)
        rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
          branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
        exact ⟨by omega, by omega, Or.inl hr31⟩
      have hcanonS := herzogLShapeCanonicality B e D _ _ hdomS
      have halphaS := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
        B e 0 (r12 R + J) hcanonS
      rw [hsuccRes, halphaT, halphaS, hI] at hspec
      simp only [normalizedGrid, zero_mul, zero_add] at hspec
      have hA : a = normalizedC R := by
        simpa [a, B, e] using branchB_inactive_routingA_eq_normalizedC R
      have hB : b = normalizedA R := by
        simpa [b, B, e] using branchB_inactive_routingB_eq_normalizedA R
      have hC : c = normalizedB R := by
        simpa [c, B, e] using branchB_inactive_routingC_eq_normalizedB R
      have hrel : c1 R * b = r13 R * a + r12 R * c := by
        rw [hA, hB, hC]
        simpa [Nat.add_comm] using
          (branchB_actual_herzog_coordinates R).normalized_relations.1
      have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
      have hp : (a : ℤ) * sigma = (a : ℤ) * r13 R := by
        change ((((c1 R - 1) * b + J * c : ℕ) : ℤ) + b) =
          (((r12 R + J) * c : ℕ) : ℤ) + (a : ℤ) * sigma at hspec
        have hrelZ : (c1 R : ℤ) * b =
            (r13 R : ℤ) * a + (r12 R : ℤ) * c := by
          exact_mod_cast hrel
        push_cast at hspec
        rw [Nat.cast_sub (by omega : 1 ≤ c1 R)] at hspec
        ring_nf at hspec hrelZ ⊢
        linarith
      have hsigmaZ : (sigma : ℤ) = r13 R :=
        mul_left_cancel₀ (ne_of_gt ha) hp
      exact ⟨J, by simpa [hI] using hres.symm, hJ,
        by exact_mod_cast hsigmaZ, hsuccRes⟩
    · right; right
      have hJge : r32 R ≤ J := le_of_not_gt hJ
      have hI : I = r31 R - 1 := by omega
      have hsuccRes : S = gridResidue B e 0 (J - r32 R) := by
        have hstep := gridResidue_add_b B e I J
        have hwrap := branchB_high_seam_upper_wrap_residue R (r31 R) 0 J
          (by omega) hJge
        calc
          S = gridResidue B e (I + 1) J := by
            dsimp only [S, b]
            rw [← hres]
            exact hstep.symm
          _ = gridResidue B e (r31 R) J := by rw [hI]; congr 2 <;> omega
          _ = gridResidue B e 0 (J - r32 R) := by simpa using hwrap
      have hdomS : L5A2C4OR5.HerzogLShapeDomain D 0 (J - r32 R) := by
        simp only [L5A2C4OR5.HerzogLShapeDomain]
        change 0 < L5A2C4A.c2 B e ∧ J - r32 R < L5A2C4A.c3 B e ∧
          (0 < L5A2C4D.cr12 D ∨ J - r32 R < L5A2C4D.cr13 D)
        rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
          branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
        exact ⟨by omega, by omega, Or.inl hr31⟩
      have hcanonS := herzogLShapeCanonicality B e D _ _ hdomS
      have halphaS := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
        B e 0 (J - r32 R) hcanonS
      rw [hsuccRes, halphaT, halphaS, hI] at hspec
      simp only [normalizedGrid, zero_mul, zero_add] at hspec
      have hA : a = normalizedC R := by
        simpa [a, B, e] using branchB_inactive_routingA_eq_normalizedC R
      have hB : b = normalizedA R := by
        simpa [b, B, e] using branchB_inactive_routingB_eq_normalizedA R
      have hC : c = normalizedB R := by
        simpa [c, B, e] using branchB_inactive_routingC_eq_normalizedB R
      have hrel : c3 R * a = r31 R * b + r32 R * c := by
        rw [hA, hB, hC]
        simpa using
          (branchB_actual_herzog_coordinates R).normalized_relations.2.2
      have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
      have hp : (a : ℤ) * sigma = (a : ℤ) * c3 R := by
        change ((((r31 R - 1) * b + J * c : ℕ) : ℤ) + b) =
          (((J - r32 R) * c : ℕ) : ℤ) + (a : ℤ) * sigma at hspec
        have hrelZ : (c3 R : ℤ) * a =
            (r31 R : ℤ) * b + (r32 R : ℤ) * c := by
          exact_mod_cast hrel
        push_cast at hspec
        rw [Nat.cast_sub (by omega : 1 ≤ r31 R),
          Nat.cast_sub hJge] at hspec
        ring_nf at hspec hrelZ ⊢
        linarith
      have hsigmaZ : (sigma : ℤ) = c3 R :=
        mul_left_cancel₀ (ne_of_gt ha) hp
      exact ⟨J, by simpa [hI] using hres.symm, hJge, hbounds.2.1,
        by exact_mod_cast hsigmaZ, hsuccRes⟩

/-- Candidate cocycle across the first active `b`-edge.  The return index is
arbitrary; no owner is transported between the two gates. -/
theorem branchB_high_axisC_y2_minimizer_cocycle
    (R : SectorBCriticalRoleBranchB P) (h : ℕ)
    (hhmin :
      let B := P.M.base
      let e := branchBInactiveReindex R
      rawCandidate B e h (gridResidue B e 0 (r12 R)) =
        eta B e 0 (r12 R)) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let X2 := gridResidue B e (c1 R - 1) 0
    let T := X2 - (h * routingM B e : ℕ)
    rawCandidate B e h X2 =
      (eta B e 0 (r12 R) : ℤ) - r13 R + branchBPrefixAmbientU R T := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let X2 := gridResidue B e (c1 R - 1) 0
  let Y2 := gridResidue B e 0 (r12 R)
  let T := X2 - (h * routingM B e : ℕ)
  let S := Y2 - (h * routingM B e : ℕ)
  let sigma := branchBPrefixAmbientU R T
  let Y := eta B e 0 (r12 R)
  let D := branchB_inactive_coherentHerzogData R
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change rawCandidate B e h Y2 = Y at hhmin
  have hc1pos : 0 < c1 R := by
    have hsum : c1 R = r21 R + r31 R := by
      simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
    have hr31 : 0 < r31 R := by
      simpa using
        (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
    omega
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hsum2 : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hrel : c1 R * b = r13 R * a + r12 R * c := by
    have hA : a = normalizedC R := by
      simpa [a, B, e] using branchB_inactive_routingA_eq_normalizedC R
    have hB : b = normalizedA R := by
      simpa [b, B, e] using branchB_inactive_routingB_eq_normalizedA R
    have hC : c = normalizedB R := by
      simpa [c, B, e] using branchB_inactive_routingC_eq_normalizedB R
    rw [hA, hB, hC]
    simpa [Nat.add_comm] using
      (branchB_actual_herzog_coordinates R).normalized_relations.1
  have hXY : X2 + b = Y2 := by
    have hstep := gridResidue_add_b B e (c1 R - 1) 0
    have hwrap := branchB_high_seam_lower_wrap_residue R (c1 R) 0 0
      (by omega)
    calc
      X2 + b = gridResidue B e (c1 R) 0 := by
        dsimp only [X2, b]
        rw [show c1 R = c1 R - 1 + 1 by omega]
        exact hstep.symm
      _ = Y2 := by simpa [Y2] using hwrap
  have hST : S = T + b := by
    dsimp only [S, T]
    rw [← hXY]
    abel
  have hXcanon := branchB_high_seam_target_U_X2_canonical R
  have hYcanon : IsCanonicalTailGridPoint B e 0 (r12 R) := by
    apply herzogLShapeCanonicality B e D
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change 0 < L5A2C4A.c2 B e ∧ r12 R < L5A2C4A.c3 B e ∧
      (0 < L5A2C4D.cr12 D ∨ r12 R < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨hc1pos, by omega, Or.inl hr31⟩
  have halphaX := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
    B e (c1 R - 1) 0 hXcanon
  have halphaY := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
    B e 0 (r12 R) hYcanon
  have hcarry := branchB_inactive_b_carry_spec R T
  change physicalAlpha B e T + b = physicalAlpha B e (T + b) +
    (a : ℤ) * sigma at hcarry
  rw [← hST] at hcarry
  have hxspec := rawCandidate_spec B e h X2
  have hyspec := rawCandidate_spec B e h Y2
  change (h : ℤ) * routingM B e + physicalAlpha B e T -
    physicalAlpha B e X2 = (a : ℤ) * rawCandidate B e h X2 at hxspec
  change (h : ℤ) * routingM B e + physicalAlpha B e S -
    physicalAlpha B e Y2 = (a : ℤ) * rawCandidate B e h Y2 at hyspec
  rw [halphaX] at hxspec
  rw [halphaY, hhmin] at hyspec
  simp only [normalizedGrid, zero_mul, zero_add, mul_zero, add_zero] at hxspec hyspec
  have hrelZ : (c1 R : ℤ) * b =
      (r13 R : ℤ) * a + (r12 R : ℤ) * c := by exact_mod_cast hrel
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  have hmul : (a : ℤ) * rawCandidate B e h X2 =
      (a : ℤ) * ((Y : ℤ) - r13 R + sigma) := by
    change (h : ℤ) * routingM B e + physicalAlpha B e T -
      (((c1 R - 1) * b : ℕ) : ℤ) =
        (a : ℤ) * rawCandidate B e h X2 at hxspec
    change (h : ℤ) * routingM B e + physicalAlpha B e S -
      ((r12 R * c : ℕ) : ℤ) = (a : ℤ) * Y at hyspec
    push_cast at hxspec hyspec hcarry
    rw [Nat.cast_sub (by omega : 1 ≤ c1 R)] at hxspec
    ring_nf at hxspec hyspec hcarry hrelZ ⊢
    linarith
  exact mul_left_cancel₀ (ne_of_gt ha) hmul

/-- Reverse active-gate envelope.  All three ambient carry classes are
handled explicitly; in particular no minimizer is identified across
residues. -/
theorem branchB_high_axisC_active_gate_reverse_bound
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let X := eta B e (c1 R - 1) 0
    let Y := eta B e 0 (r12 R)
    X + r13 R ≤ Y := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hsx
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let b := routingB B e
  let c := routingC B e
  let X := eta B e (c1 R - 1) 0
  let Y := eta B e 0 (r12 R)
  let X2 := gridResidue B e (c1 R - 1) 0
  let Y2 := gridResidue B e 0 (r12 R)
  let O := gridResidue B e 0 0
  let D := branchB_inactive_coherentHerzogData R
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  obtain ⟨h, hhpos, hhle, hhmin⟩ :=
    branchB_high_axisC_y2_finite_window_minimizer R hB
  let T := X2 - (h * routingM B e : ℕ)
  let S := Y2 - (h * routingM B e : ℕ)
  let sigma := branchBPrefixAmbientU R T
  have hcocycle := branchB_high_axisC_y2_minimizer_cocycle R h hhmin
  change rawCandidate B e h X2 = (Y : ℤ) - r13 R + sigma at hcocycle
  have htri := branchB_inactive_b_carry_trichotomy R T
  change sigma = 0 ∨
      (∃ t : ℕ, T = gridResidue B e (c1 R - 1) t ∧
        t < r32 R ∧ sigma = r13 R ∧
        T + b = gridResidue B e 0 (r12 R + t)) ∨
      (∃ t : ℕ, T = gridResidue B e (r31 R - 1) t ∧
        r32 R ≤ t ∧ t < c2 R ∧ sigma = c3 R ∧
        T + b = gridResidue B e 0 (t - r32 R)) at htri
  have hr13 : 0 < r13 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.2.1
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hc1sum : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hc2sum : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hXpos : 0 < X := (branchB_inactive_active_gate_liveness R hB).1
  have hYpos : 0 < Y := by
    have hgate := (branchB_inactive_active_gate_liveness R hB).2.1
    change r13 R ≤ Y at hgate
    omega
  have hXcanon := branchB_high_seam_target_U_X2_canonical R
  have hXphys := eta_eq_physicalHeight_of_isCanonical
    B e (c1 R - 1) 0 hXcanon
  change X = physicalHeight B e X2 at hXphys
  have hXheight := physicalHeight_eq_max_rawMinimum B e X2
  have hXmin : rawMinimum B e X2 = X := by
    rw [← hXphys] at hXheight
    change (X : ℤ) = max 0 (rawMinimum B e X2) at hXheight
    have hxz : (0 : ℤ) < X := by exact_mod_cast hXpos
    omega
  rcases htri with hzero | hlower | hupper
  · have hraw := rawMinimum_le B e X2 hhpos
    rw [hXmin, hcocycle, hzero] at hraw
    have hz : (X : ℤ) + r13 R ≤ Y := by omega
    exact_mod_cast hz
  · obtain ⟨t, hT, htlt, hsigma, hS⟩ := hlower
    have hSt : S = gridResidue B e 0 (r12 R + t) := by
      have hXY : Y2 = X2 + b := by
        have hstep := gridResidue_add_b B e (c1 R - 1) 0
        have hwrap := branchB_high_seam_lower_wrap_residue R (c1 R) 0 0
          (by omega)
        calc
          Y2 = gridResidue B e (c1 R) 0 := by simpa [Y2] using hwrap.symm
          _ = X2 + b := by
            dsimp only [X2, b]
            rw [show c1 R = c1 R - 1 + 1 by omega]
            exact hstep
      dsimp only [S, T] at hS ⊢
      rw [hXY]
      abel_nf at hS ⊢
      exact hS
    have hshiftO : O - (h * routingM B e : ℕ) = gridResidue B e 0 t := by
      have hadd : gridResidue B e 0 (r12 R + t) =
          Y2 + gridResidue B e 0 t := by
        simp only [Y2, gridResidue, Nat.cast_add, add_mul, zero_mul, zero_add]
        ring
      have hSdef : Y2 - (h * routingM B e : ℕ) =
          gridResidue B e 0 (r12 R + t) := hSt
      rw [hadd] at hSdef
      calc
        O - (h * routingM B e : ℕ) =
            (Y2 - (h * routingM B e : ℕ)) - Y2 := by
              dsimp only [O]
              simp only [gridResidue, Nat.cast_zero, zero_mul, zero_add]
              abel
        _ = (Y2 + gridResidue B e 0 t) - Y2 := by rw [hSdef]
        _ = gridResidue B e 0 t := by abel
    have hdomt : L5A2C4OR5.HerzogLShapeDomain D 0 t := by
      simp only [L5A2C4OR5.HerzogLShapeDomain]
      change 0 < L5A2C4A.c2 B e ∧ t < L5A2C4A.c3 B e ∧
        (0 < L5A2C4D.cr12 D ∨ t < L5A2C4D.cr13 D)
      rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
        branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
      exact ⟨by omega, by omega, Or.inl hr31⟩
    have hdomS : L5A2C4OR5.HerzogLShapeDomain D 0 (r12 R + t) := by
      simp only [L5A2C4OR5.HerzogLShapeDomain]
      change 0 < L5A2C4A.c2 B e ∧ r12 R + t < L5A2C4A.c3 B e ∧
        (0 < L5A2C4D.cr12 D ∨ r12 R + t < L5A2C4D.cr13 D)
      rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
        branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
      exact ⟨by omega, by omega, Or.inl hr31⟩
    have hdomO : L5A2C4OR5.HerzogLShapeDomain D 0 0 := by
      simp only [L5A2C4OR5.HerzogLShapeDomain]
      change 0 < L5A2C4A.c2 B e ∧ 0 < L5A2C4A.c3 B e ∧
        (0 < L5A2C4D.cr12 D ∨ 0 < L5A2C4D.cr13 D)
      rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
        branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
      exact ⟨by omega, by omega, Or.inl hr31⟩
    have hct := herzogLShapeCanonicality B e D 0 t hdomt
    have hcS := herzogLShapeCanonicality B e D 0 (r12 R + t) hdomS
    have hcO := herzogLShapeCanonicality B e D 0 0 hdomO
    have hat := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical B e 0 t hct
    have haS := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e 0 (r12 R + t) hcS
    have haY := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e 0 (r12 R) (by
        apply herzogLShapeCanonicality B e D
        simp only [L5A2C4OR5.HerzogLShapeDomain]
        change 0 < L5A2C4A.c2 B e ∧ r12 R < L5A2C4A.c3 B e ∧
          (0 < L5A2C4D.cr12 D ∨ r12 R < L5A2C4D.cr13 D)
        rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
          branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
        exact ⟨by omega, by omega, Or.inl hr31⟩)
    have haO := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical B e 0 0 hcO
    have hyspec := rawCandidate_spec B e h Y2
    have hospec := rawCandidate_spec B e h O
    change (h : ℤ) * routingM B e + physicalAlpha B e S -
      physicalAlpha B e Y2 = (a : ℤ) * rawCandidate B e h Y2 at hyspec
    change (h : ℤ) * routingM B e +
      physicalAlpha B e (O - (h * routingM B e : ℕ)) -
      physicalAlpha B e O = (a : ℤ) * rawCandidate B e h O at hospec
    rw [hSt, haS, haY, hhmin] at hyspec
    rw [hshiftO, hat, haO] at hospec
    simp only [normalizedGrid, zero_mul, zero_add] at hyspec hospec
    have haPos : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
    have hmulO : (a : ℤ) * rawCandidate B e h O = (a : ℤ) * Y := by
      push_cast at hyspec hospec
      ring_nf at hyspec hospec ⊢
      linarith
    have hcandO : rawCandidate B e h O = Y :=
      mul_left_cancel₀ (ne_of_gt haPos) hmulO
    have horigin :=
      branchB_actualZeroEdgeBirth_axisC_high_seam_origin_inner_notch_final_packet
        R hB x hsx hbirth haxis
    have hetaO : eta B e 0 0 = A.coordinate.j.toNat := horigin.2.2.2
    have hjpos : 0 < A.coordinate.j.toNat := by
      have hqpos : (0 : ℤ) < qH R := by
        exact_mod_cast (show 0 < qH R by simpa [qH] using hr13)
      have hj : (qH R : ℤ) < A.coordinate.j := haxis.2.1
      have hj0 : (0 : ℤ) < A.coordinate.j := lt_trans hqpos hj
      have hjEq : A.coordinate.j = (A.coordinate.j.toNat : ℤ) :=
        (Int.toNat_of_nonneg (le_of_lt hj0)).symm
      rw [hjEq] at hj0
      exact_mod_cast hj0
    have hetaPhys := eta_eq_physicalHeight_of_isCanonical B e 0 0 hcO
    change eta B e 0 0 = physicalHeight B e O at hetaPhys
    have hheight := physicalHeight_eq_max_rawMinimum B e O
    have hminO : rawMinimum B e O = A.coordinate.j.toNat := by
      rw [← hetaPhys, hetaO] at hheight
      change (A.coordinate.j.toNat : ℤ) = max 0 (rawMinimum B e O) at hheight
      have hjz : (0 : ℤ) < A.coordinate.j.toNat := by exact_mod_cast hjpos
      omega
    have hrawO := rawMinimum_le B e O hhpos
    rw [hminO, hcandO] at hrawO
    have hcap := branchB_actualZeroEdgeBirth_axisC_high_seam_x2_cap
      R hB x hsx hbirth haxis
    have hXj : X + r13 R ≤ A.coordinate.j.toNat := by
      change A.depth < r31 R ∧
        rawCandidate B e A.ell X2 = (A.coordinate.j.toNat : ℤ) - r13 R ∧
        1 ≤ X ∧ X ≤ A.coordinate.j.toNat - r13 R ∧ X < r23 R at hcap
      omega
    have hjY : (A.coordinate.j.toNat : ℤ) ≤ Y := hrawO
    exact_mod_cast (show (X : ℤ) + r13 R ≤ Y by omega)
  · obtain ⟨t, hT, htge, htlt, hsigma, hS⟩ := hupper
    have hSt : S = gridResidue B e 0 (t - r32 R) := by
      have hXY : Y2 = X2 + b := by
        have hstep := gridResidue_add_b B e (c1 R - 1) 0
        have hwrap := branchB_high_seam_lower_wrap_residue R (c1 R) 0 0
          (by omega)
        calc
          Y2 = gridResidue B e (c1 R) 0 := by simpa [Y2] using hwrap.symm
          _ = X2 + b := by
            dsimp only [X2, b]
            rw [show c1 R = c1 R - 1 + 1 by omega]
            exact hstep
      dsimp only [S, T] at hS ⊢
      rw [hXY]
      abel_nf at hS ⊢
      exact hS
    have hdomS : L5A2C4OR5.HerzogLShapeDomain D 0 (t - r32 R) := by
      simp only [L5A2C4OR5.HerzogLShapeDomain]
      change 0 < L5A2C4A.c2 B e ∧ t - r32 R < L5A2C4A.c3 B e ∧
        (0 < L5A2C4D.cr12 D ∨ t - r32 R < L5A2C4D.cr13 D)
      rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
        branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
      exact ⟨by omega, by omega, Or.inl hr31⟩
    have hcS := herzogLShapeCanonicality B e D 0 (t - r32 R) hdomS
    have haS := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e 0 (t - r32 R) hcS
    have hdomY : L5A2C4OR5.HerzogLShapeDomain D 0 (r12 R) := by
      simp only [L5A2C4OR5.HerzogLShapeDomain]
      change 0 < L5A2C4A.c2 B e ∧ r12 R < L5A2C4A.c3 B e ∧
        (0 < L5A2C4D.cr12 D ∨ r12 R < L5A2C4D.cr13 D)
      rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
        branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
      exact ⟨by omega, by omega, Or.inl hr31⟩
    have hcY := herzogLShapeCanonicality B e D 0 (r12 R) hdomY
    have haY := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
      B e 0 (r12 R) hcY
    have hyspec := rawCandidate_spec B e h Y2
    change (h : ℤ) * routingM B e + physicalAlpha B e S -
      physicalAlpha B e Y2 = (a : ℤ) * rawCandidate B e h Y2 at hyspec
    rw [hSt, haS, haY, hhmin] at hyspec
    simp only [normalizedGrid, zero_mul, zero_add] at hyspec
    have hEq : (((h * routingM B e : ℕ) : ℤ) - a) =
        (((Y - 1) * a + (c2 R - t) * c : ℕ) : ℤ) := by
      change (h : ℤ) * routingM B e +
        (((t - r32 R) * c : ℕ) : ℤ) - ((r12 R * c : ℕ) : ℤ) =
          (a : ℤ) * Y at hyspec
      push_cast at hyspec ⊢
      rw [Nat.cast_sub htge] at hyspec
      rw [Nat.cast_sub (by omega : 1 ≤ Y),
        Nat.cast_sub (Nat.le_of_lt htlt)]
      have hc2sumZ : (c2 R : ℤ) = r12 R + r32 R := by
        exact_mod_cast hc2sum
      have hc2mul : (c2 R : ℤ) * c =
          (r12 R : ℤ) * c + (r32 R : ℤ) * c := by
        rw [hc2sumZ]
        ring
      ring_nf at hyspec hc2mul ⊢
      linarith
    have haH : routingA B e ∈ routingH B e :=
      (NumericalSemigroup.mem_generatedByThree_iff
        (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
          (AddSubmonoid.subset_closure (by simp))
    have hpartA := (routingH B e).toAddSubmonoid.nsmul_mem haH (Y - 1)
    have hpartC := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e) (c2 R - t)
    have hnH : (Y - 1) * a + (c2 R - t) * c ∈ routingH B e := by
      simpa [nsmul_eq_mul, Nat.add_comm, Nat.mul_comm] using
        (routingH B e).add_mem hpartA hpartC
    have hbad : (((h * routingM B e : ℕ) : ℤ) - a) ∈
        (routingH B e).asRelativeIdeal := by
      rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨(Y - 1) * a + (c2 R - t) * c, hnH, ?_⟩
      exact hEq
    exact False.elim
      ((branchB_actualZeroEdgeBirth_axisC_high_seam_return_window_routingA
        R hB x hsx hbirth haxis h hhpos hhle) hbad)

/-- The second active gate is exactly clamped by the first gate and the
lower-wrap Herzog coefficient. -/
theorem branchB_high_axisC_y2_gate_equality
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    eta B e 0 (r12 R) = eta B e (c1 R - 1) 0 + r13 R := by
  have hu := branchB_high_axisC_active_gate_upper_bounds
    R hB x hsx hbirth haxis
  have hl := branchB_high_axisC_active_gate_reverse_bound
    R hB x hsx hbirth haxis
  omega

/-- The ambient `c`-edge immediately before the second gate is ordinary. -/
theorem branchB_high_axisC_yminus_ambient_c_carry_zero
    (R : SectorBCriticalRoleBranchB P) :
    branchBPrefixAmbientV R
      (gridResidue P.M.base (branchBInactiveReindex R) 0 (r12 R - 1)) = 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let Ym := gridResidue B e 0 (r12 R - 1)
  let Y2 := gridResidue B e 0 (r12 R)
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hc1sum : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hc2sum : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hdom (j : ℕ) (hj : j < c2 R) :
      L5A2C4OR5.HerzogLShapeDomain D 0 j := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change 0 < L5A2C4A.c2 B e ∧ j < L5A2C4A.c3 B e ∧
      (0 < L5A2C4D.cr12 D ∨ j < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨by omega, hj, Or.inl hr31⟩
  have hYmCanon := herzogLShapeCanonicality B e D 0 (r12 R - 1)
    (hdom _ (by omega))
  have hYCanon := herzogLShapeCanonicality B e D 0 (r12 R)
    (hdom _ (by omega))
  have hstep : Ym + routingC B e = Y2 := by
    calc
      Ym + routingC B e = gridResidue B e 0 (r12 R - 1 + 1) :=
        (gridResidue_add_c B e 0 (r12 R - 1)).symm
      _ = Y2 := by congr 2 <;> omega
  have halphaYm := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
    B e 0 (r12 R - 1) hYmCanon
  have halphaY := branchB_physicalAlpha_eq_normalizedGrid_zero_of_canonical
    B e 0 (r12 R) hYCanon
  have hs := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) Ym
  change physicalAlpha B e Ym + routingC B e =
    physicalAlpha B e (Ym + routingC B e) +
      (routingA B e : ℤ) * branchBPrefixAmbientV R Ym at hs
  rw [hstep, halphaYm, halphaY] at hs
  simp only [normalizedGrid, zero_mul, zero_add] at hs
  have hgrid : (r12 R - 1) * routingC B e + routingC B e =
      r12 R * routingC B e := by
    calc
      (r12 R - 1) * routingC B e + routingC B e =
          (r12 R - 1 + 1) * routingC B e := by ring
      _ = r12 R * routingC B e := by rw [Nat.sub_add_cancel (by omega)]
  have hgridZ : (((r12 R - 1) * routingC B e : ℕ) : ℤ) + routingC B e =
      ((r12 R * routingC B e : ℕ) : ℤ) := by exact_mod_cast hgrid
  rw [hgridZ] at hs
  have hp : routingA B e * branchBPrefixAmbientV R Ym = 0 := by
    exact_mod_cast (show (routingA B e : ℤ) * branchBPrefixAmbientV R Ym = 0 by omega)
  exact (Nat.mul_eq_zero.mp hp).resolve_left
    (Nat.ne_of_gt (routingA_pos B e))

/-- The ordinary final `c`-edge makes the predecessor gate no lower than the
second gate. -/
theorem branchB_high_axisC_yminus_ge_y
    (R : SectorBCriticalRoleBranchB P) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    eta B e 0 (r12 R) ≤ eta B e 0 (r12 R - 1) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let Ym := gridResidue B e 0 (r12 R - 1)
  let Y2 := gridResidue B e 0 (r12 R)
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hr12 : 0 < r12 R := by
    simpa using (branchB_actual_herzog_coordinates R).cross_positive.1
  have hr31 : 0 < r31 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.1
  have hr32 : 0 < r32 R := by
    simpa using
      (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
  have hc1sum : c1 R = r21 R + r31 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have hc2sum : c2 R = r12 R + r32 R := by
    simpa using (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hdom (j : ℕ) (hj : j < c2 R) :
      L5A2C4OR5.HerzogLShapeDomain D 0 j := by
    simp only [L5A2C4OR5.HerzogLShapeDomain]
    change 0 < L5A2C4A.c2 B e ∧ j < L5A2C4A.c3 B e ∧
      (0 < L5A2C4D.cr12 D ∨ j < L5A2C4D.cr13 D)
    rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3,
      branchB_inactive_coherent_cr12, branchB_inactive_coherent_cr13]
    exact ⟨by omega, hj, Or.inl hr31⟩
  have hYmDom := hdom (r12 R - 1) (by omega)
  have hYDom := hdom (r12 R) (by omega)
  have hYmLift := gridLift_eq_zero_on_herzogDomain B e D hYmDom
  have hYLift := gridLift_eq_zero_on_herzogDomain B e D hYDom
  have hsEta := eta_c_carry_transition B e 0 (r12 R - 1)
  rw [show r12 R - 1 + 1 = r12 R by omega, hYmLift, hYLift] at hsEta
  change eta B e 0 (r12 R) ≤ eta B e 0 (r12 R - 1)
  omega

/-- Full B65 active-gate clamp. -/
theorem branchB_high_axisC_gate_clamp
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = 0 ∧ qH R < S.coordinate.j ∧
      S.coordinate.j < qH R + vH R ∧
      S.beta = S.coordinate.j * normalizedC R ∧
      (S.n : ℤ) + normalizedA R * S.depth =
        S.coordinate.j * normalizedC R) :
    let B := P.M.base
    let e := branchBInactiveReindex R
    let X := eta B e (c1 R - 1) 0
    let Y := eta B e 0 (r12 R)
    let Ym := eta B e 0 (r12 R - 1)
    Ym = Y ∧ Y = X + r13 R := by
  have hupper := branchB_high_axisC_active_gate_upper_bounds
    R hB x hsx hbirth haxis
  have heq := branchB_high_axisC_y2_gate_equality R hB x hsx hbirth haxis
  have hmono := branchB_high_axisC_yminus_ge_y R
  omega


end NS25Lean.L5A2B4AR5B
