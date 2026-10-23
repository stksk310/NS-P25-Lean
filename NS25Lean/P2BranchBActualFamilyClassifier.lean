import NS25Lean.P2BranchBActualEventFamily
import NS25Lean.P2SectorCPhysicalHeightBridge

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2C4C L5A2C4H L5A2C4OR3

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The two inward predecessors of the first actual mixed critical component
are excluded from the chosen tail ideal.  This is the active internal-gate
statement in the coherent Branch-B indexing. -/
theorem branchB_first_mixed_boundary_exclusions
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :
    R.firstDegree - weights P.M.base (R.reindex 1) ∉ P.M.base.K ∧
      R.firstDegree - weights P.M.base (R.reindex 2) ∉ P.M.base.K := by
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
  constructor
  · intro hmem
    apply hgenuine R.firstDegree hfirst R.first.mixedComponent
    exact ⟨R.first.witness, R.first.witness_component, R.reindex 1,
      R.first_witness_one_pos, hmem⟩
  · intro hmem
    apply hgenuine R.firstDegree hfirst R.first.mixedComponent
    exact ⟨R.first.witness, R.first.witness_component, R.reindex 2,
      R.first_witness_two_pos, hmem⟩

/-- A positive selected anchor cannot lie in the closed CENTER rectangle.
The proof uses the selected positive return to put one of the two inward
predecessors of the first mixed critical relation into the normalized tail
ideal, contradicting the actual internal gate above. -/
theorem branchB_positive_center_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R)) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let B := P.M.base
  let e := R.reindex
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, hi, hj] at hbeta
  have hanchor := A.anchor_eq
  rw [hbeta] at hanchor
  have hanchorNat : i * normalizedB R + j * normalizedC R =
      A.n + normalizedA R * A.depth := by
    exact_mod_cast hanchor
  have hdeq := routingD_eq_chosenTailGcd B e
  have hAeq : routingA B e = normalizedA R := by
    simp only [routingA, routingN1, tailValue, normalizedA,
      L5A2B4AR3.normalizedWeight]
    rw [hdeq]
    rfl
  have hBeq : routingB B e = normalizedB R := by
    simp only [routingB, routingN2, tailValue, normalizedB,
      L5A2B4AR3.normalizedWeight]
    rw [hdeq]
    rfl
  have hCeq : routingC B e = normalizedC R := by
    simp only [routingC, routingN3, tailValue, normalizedC,
      L5A2B4AR3.normalizedWeight]
    rw [hdeq]
    rfl
  have haH : routingA B e ∈ routingH B e :=
    (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
        (AddSubmonoid.subset_closure (by simp))
  have hgen (x y z : ℕ) :
      x * routingA B e + y * routingB B e + z * routingC B e ∈ routingH B e := by
    have hx := (routingH B e).toAddSubmonoid.nsmul_mem haH x
    have hy := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e) y
    have hz := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using
      (routingH B e).add_mem ((routingH B e).add_mem hx hy) hz
  have hfirstDegree : R.firstDegree =
      L5A2B4AR4R2B.c1 R * weights B (e 0) := by
    simpa [e, L5A2B4AR4R2B.c1, R.reindex_zero] using
      R.first.degree_eq_critical
  have hrawRelation := L5A2B4AR4R2B.branchB_first_relation R
  by_cases hip : i < pH R
  · let x : ℕ := (pH R - 1) * normalizedB R + qH R * normalizedC R
    have hxm : (x : ℤ) ∈ routingI B e := by
      apply (mem_routingI_iff_positive_return B e (x : ℤ)).2
      refine ⟨A.ell, A.ell_pos, ?_, ?_⟩
      · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
        refine ⟨x, ?_, rfl⟩
        simpa [x, hAeq, hBeq, hCeq, Nat.zero_mul, Nat.zero_add] using
          hgen 0 (pH R - 1) (qH R)
      · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
        let y : ℕ := A.depth * normalizedA R +
          (pH R - 1 - i) * normalizedB R + (qH R - j) * normalizedC R
        refine ⟨y, ?_, ?_⟩
        · simpa [y, hAeq, hBeq, hCeq, Nat.add_assoc] using
            hgen A.depth (pH R - 1 - i) (qH R - j)
        · have hn : A.n = A.ell * normalizedM B := A.n_eq
          have hip' : i ≤ pH R - 1 := by omega
          have hpSplit : pH R - 1 = i + (pH R - 1 - i) := by omega
          have hqSplit : qH R = j + (qH R - j) := by omega
          have hpMul : (pH R - 1) * normalizedB R =
              i * normalizedB R + (pH R - 1 - i) * normalizedB R := by
            rw [← Nat.add_mul]
            exact congrArg (fun t => t * normalizedB R) hpSplit
          have hqMul : qH R * normalizedC R =
              j * normalizedC R + (qH R - j) * normalizedC R := by
            rw [← Nat.add_mul]
            exact congrArg (fun t => t * normalizedC R) hqSplit
          have hcalc : x = A.n + y := by
            calc
              x = (i * normalizedB R + j * normalizedC R) +
                  ((pH R - 1 - i) * normalizedB R +
                    (qH R - j) * normalizedC R) := by
                dsimp [x]
                rw [hpMul, hqMul]
                ring
              _ = (A.n + normalizedA R * A.depth) +
                  ((pH R - 1 - i) * normalizedB R +
                    (qH R - j) * normalizedC R) := by rw [hanchorNat]
              _ = A.n + y := by dsimp [y]; ring
          rw [hcalc, hn]
          push_cast
          ring
    have heta : eta B e (pH R - 1) (qH R) = 0 := by
      have hle := (normalizedGrid_mem_iff_eta_le B e 0 (pH R - 1) (qH R)).1
        (by simpa [x, normalizedGrid, hAeq, hBeq, hCeq] using hxm)
      omega
    have hK := (eta_eq_zero_iff B e (pH R - 1) (qH R)).1 heta
    exact (branchB_first_mixed_boundary_exclusions R hB).1 (by
      have hp := (branchB_actual_herzog_coordinates R).cross_positive.1
      have hpSplit : pH R = 1 + (pH R - 1) := by omega
      rw [hfirstDegree, hrawRelation]
      change (pH R * weights B (e 1) + qH R * weights B (e 2)) -
          weights B (e 1) ∈ B.K
      rw [hpSplit, Nat.add_mul]
      simpa [gridDegree, e, Nat.add_assoc] using hK)
  · have hipEq : i = pH R := by omega
    have hjq : j < qH R := by
      by_contra hnot
      have : j = qH R := by omega
      exact hcorner (by simp [hipEq, this])
    let x : ℕ := pH R * normalizedB R + (qH R - 1) * normalizedC R
    have hxm : (x : ℤ) ∈ routingI B e := by
      apply (mem_routingI_iff_positive_return B e (x : ℤ)).2
      refine ⟨A.ell, A.ell_pos, ?_, ?_⟩
      · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
        refine ⟨x, ?_, rfl⟩
        simpa [x, hAeq, hBeq, hCeq, Nat.zero_mul, Nat.zero_add] using
          hgen 0 (pH R) (qH R - 1)
      · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
        let y : ℕ := A.depth * normalizedA R +
          (qH R - 1 - j) * normalizedC R
        refine ⟨y, ?_, ?_⟩
        · simpa [y, hAeq, hBeq, hCeq, Nat.add_assoc] using
            hgen A.depth 0 (qH R - 1 - j)
        · have hn : A.n = A.ell * normalizedM B := A.n_eq
          have hjq' : j ≤ qH R - 1 := by omega
          have hqSplit : qH R - 1 = j + (qH R - 1 - j) := by omega
          have hqMul : (qH R - 1) * normalizedC R =
              j * normalizedC R + (qH R - 1 - j) * normalizedC R := by
            rw [← Nat.add_mul]
            exact congrArg (fun t => t * normalizedC R) hqSplit
          have hcalc : x = A.n + y := by
            calc
              x = i * normalizedB R + j * normalizedC R +
                  (qH R - 1 - j) * normalizedC R := by
                dsimp [x]
                rw [← hipEq, hqMul]
                ring
              _ = (A.n + normalizedA R * A.depth) +
                  (qH R - 1 - j) * normalizedC R := by rw [hanchorNat]
              _ = A.n + y := by dsimp [y]; ring
          rw [hcalc, hn]
          push_cast
          ring
    have heta : eta B e (pH R) (qH R - 1) = 0 := by
      have hle := (normalizedGrid_mem_iff_eta_le B e 0 (pH R) (qH R - 1)).1
        (by simpa [x, normalizedGrid, hAeq, hBeq, hCeq] using hxm)
      omega
    have hK := (eta_eq_zero_iff B e (pH R) (qH R - 1)).1 heta
    exact (branchB_first_mixed_boundary_exclusions R hB).2 (by
      have hq := (branchB_actual_herzog_coordinates R).cross_positive.2.1
      have hqSplit : qH R = 1 + (qH R - 1) := by omega
      rw [hfirstDegree, hrawRelation]
      change (pH R * weights B (e 1) + qH R * weights B (e 2)) -
          weights B (e 2) ∈ B.K
      rw [hqSplit, Nat.add_mul]
      have hcraw : 0 < weights B (e 2) := weights_positive B (e 2)
      have hsub :
          (pH R * weights B (e 1) +
              (weights B (e 2) + (qH R - 1) * weights B (e 2))) -
            weights B (e 2) =
          pH R * weights B (e 1) + (qH R - 1) * weights B (e 2) := by
        omega
      simp only [one_mul]
      rw [hsub]
      simpa [gridDegree, e] using hK)

/-- Repaired CENTER depth package.  On actual Branch-B data the closed
CENTER alternative is eliminated by the active internal gate, so both sharp
depth inequalities follow without adding a chart-depth premise. -/
theorem branchB_positive_center_depth_lt_uH_wH
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R)) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    A.depth < uH R ∧ A.depth < wH R := by
  exact (branchB_positive_center_impossible R hB hs i j hcenter).elim

theorem branchB_positive_center_pureB_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  have hlt := (branchB_positive_center_depth_lt_uH_wH
    R hB hs i j hcenter).2
  have hge := branchB_positive_center_pureB_depth_ge_wH
    R hB hs i j hcenter hroute
  omega

theorem branchB_positive_center_pureC_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  have hlt := (branchB_positive_center_depth_lt_uH_wH
    R hB hs i j hcenter).1
  have hge := branchB_positive_center_pureC_depth_ge_uH
    R hB hs i j hcenter hroute
  omega

theorem branchB_positive_center_outer_ab_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (_hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (_hi : i = pH R) : False :=
  branchB_positive_center_impossible R hB hs i j hcenter

theorem branchB_positive_center_outer_ac_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (_hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (_hj : j = qH R) : False :=
  branchB_positive_center_impossible R hB hs i j hcenter

/-- The B43 CENTER packet with all four residual alternatives discharged.
Every surviving conclusion is one of the already-defined F/O/X/Y canonical
packets; no boundary family is introduced. -/
theorem branchB_positive_center_actual_family_exhaustive
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R)) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (C.data.sourceValue : ℤ) = s ∧
    ((C.source_coordinate.i = A.coordinate.i ∧
        C.source_coordinate.j = A.coordinate.j ∧
        C.source_coordinate.level = A.coordinate.level ∧
        C.source_chart = A.chart ∧
        C.returned_coordinate.i = 0 ∧ C.returned_coordinate.j = 0 ∧
        C.returned_coordinate.level = A.depth) ∨
      (C.source_coordinate.i = 0 ∧ C.source_coordinate.j = 0 ∧
        C.source_coordinate.level =
          ((L5A2B4AR4R2B.c1 R - A.depth : ℕ) : ℤ) ∧
        C.returned_coordinate.i = ((pH R - i : ℕ) : ℤ) ∧
        C.returned_coordinate.j = ((qH R - j : ℕ) : ℤ) ∧
        C.returned_coordinate.level = 0) ∨
      (i < pH R ∧
        C.source_coordinate.i = i + zH R ∧ C.source_coordinate.j = 0 ∧
        C.source_coordinate.level = ((wH R - A.depth : ℕ) : ℤ) ∧
        C.returned_coordinate.i = 0 ∧
        C.returned_coordinate.j =
          ((L5A2B4AR4R2B.c3 R - j : ℕ) : ℤ) ∧
        C.returned_coordinate.level = 0) ∨
      (j < qH R ∧
        C.source_coordinate.i = 0 ∧ C.source_coordinate.j = j + vH R ∧
        C.source_coordinate.level = ((uH R - A.depth : ℕ) : ℤ) ∧
        C.returned_coordinate.i =
          ((L5A2B4AR4R2B.c2 R - i : ℕ) : ℤ) ∧
        C.returned_coordinate.j = 0 ∧ C.returned_coordinate.level = 0)) := by
  exact (branchB_positive_center_impossible R hB hs i j hcenter).elim

/-- B44 name for the repaired boundary-CENTER statement: the boundary
residuals do not form a fifth family. -/
theorem branchB_positive_center_boundary_axis_family_identification
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R)) :
    ¬(let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
          C.data.sourceX C.data.sourceY C.data.sourceZ ∨
        ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
          C.data.sourceX C.data.sourceY C.data.sourceZ ∨
        (i = pH R ∧ ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
          C.data.sourceX C.data.sourceY C.data.sourceZ) ∨
        (j = qH R ∧ ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
          C.data.sourceX C.data.sourceY C.data.sourceZ)) := by
  exact fun _ => branchB_positive_center_impossible R hB hs i j hcenter

/-- Event-local B44 checkpoint after closing CENTER: every actual B42 birth
is now forced into strict RB, strict LT, or one of the two selected-anchor
axis obstructions.  The actual individual-return source and its support route
remain in the packet. -/
theorem branchB_actualZeroEdgeBirth_strict_arm_or_axis_frontier
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hsx
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
    (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
        (branchBActualExceptionalNormalizedSource P R x).val ∧
      ∃ route, ActualSourceSupportRoute.Matches route
          C.data.sourceX C.data.sourceY C.data.sourceZ ∧
        ((∃ sigma tau : ℕ,
            A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
            1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R) ∨
          (∃ sigma tau : ℕ,
            A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
            1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R) ∨
          A.coordinate.i = 0 ∨ A.coordinate.j = 0) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hsx
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  have hfront := branchB_actualZeroEdgeBirth_source_complete_frontier
    R hB x hsx hbirth
  refine ⟨hfront.1, ?_⟩
  rcases hfront.2 with hcenter | hrest
  · obtain ⟨i, j, hi, hj, hi0, hip, hj0, hjq, hcorner, _hsource⟩ := hcenter
    exact (branchB_positive_center_impossible R hB hsx i j
      ⟨hi, hj, hi0, hip, hj0, hjq, hcorner⟩).elim
  · exact hrest

end NS25Lean.L5A2B4AR5B
