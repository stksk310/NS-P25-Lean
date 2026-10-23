import NS25Lean.P2BranchBStrictLTClassifier

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2C4C L5A2C4H L5A2C4OR3

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- A selected return whose canonical anchor is weakly southwest of the
`b`-inward predecessor of the first mixed critical relation puts that
predecessor in the chosen tail ideal.  No positivity of the anchor coordinates
is assumed. -/
theorem branchB_selected_anchor_first_b_predecessor_mem
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hi : (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.i = i)
    (hj : (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.j = j)
    (hip : i < pH R) (hjq : j ≤ qH R) :
    R.firstDegree - weights P.M.base (R.reindex 1) ∈ P.M.base.K := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let B := P.M.base
  let e := R.reindex
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
  let x : ℕ := (pH R - 1) * normalizedB R + qH R * normalizedC R
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
  have hfirstDegree : R.firstDegree =
      L5A2B4AR4R2B.c1 R * weights B (e 0) := by
    simpa [e, L5A2B4AR4R2B.c1, R.reindex_zero] using
      R.first.degree_eq_critical
  have hrawRelation := L5A2B4AR4R2B.branchB_first_relation R
  have hp := (branchB_actual_herzog_coordinates R).cross_positive.1
  have hpSplit : pH R = 1 + (pH R - 1) := by omega
  rw [hfirstDegree, hrawRelation]
  change (pH R * weights B (e 1) + qH R * weights B (e 2)) -
      weights B (e 1) ∈ B.K
  rw [hpSplit, Nat.add_mul]
  simpa [gridDegree, e, Nat.add_assoc] using hK

/-- Exact dual of `branchB_selected_anchor_first_b_predecessor_mem`. -/
theorem branchB_selected_anchor_first_c_predecessor_mem
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hi : (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.i = i)
    (hj : (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.j = j)
    (hip : i ≤ pH R) (hjq : j < qH R) :
    R.firstDegree - weights P.M.base (R.reindex 2) ∈ P.M.base.K := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let B := P.M.base
  let e := R.reindex
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
        (pH R - i) * normalizedB R + (qH R - 1 - j) * normalizedC R
      refine ⟨y, ?_, ?_⟩
      · simpa [y, hAeq, hBeq, hCeq, Nat.add_assoc] using
          hgen A.depth (pH R - i) (qH R - 1 - j)
      · have hn : A.n = A.ell * normalizedM B := A.n_eq
        have hjq' : j ≤ qH R - 1 := by omega
        have hpSplit : pH R = i + (pH R - i) := by omega
        have hqSplit : qH R - 1 = j + (qH R - 1 - j) := by omega
        have hpMul : pH R * normalizedB R =
            i * normalizedB R + (pH R - i) * normalizedB R := by
          rw [← Nat.add_mul]
          exact congrArg (fun t => t * normalizedB R) hpSplit
        have hqMul : (qH R - 1) * normalizedC R =
            j * normalizedC R + (qH R - 1 - j) * normalizedC R := by
          rw [← Nat.add_mul]
          exact congrArg (fun t => t * normalizedC R) hqSplit
        have hcalc : x = A.n + y := by
          calc
            x = (i * normalizedB R + j * normalizedC R) +
                ((pH R - i) * normalizedB R +
                  (qH R - 1 - j) * normalizedC R) := by
              dsimp [x]
              rw [hpMul, hqMul]
              ring
            _ = (A.n + normalizedA R * A.depth) +
                ((pH R - i) * normalizedB R +
                  (qH R - 1 - j) * normalizedC R) := by rw [hanchorNat]
            _ = A.n + y := by dsimp [y]; ring
        rw [hcalc, hn]
        push_cast
        ring
  have heta : eta B e (pH R) (qH R - 1) = 0 := by
    have hle := (normalizedGrid_mem_iff_eta_le B e 0 (pH R) (qH R - 1)).1
      (by simpa [x, normalizedGrid, hAeq, hBeq, hCeq] using hxm)
    omega
  have hK := (eta_eq_zero_iff B e (pH R) (qH R - 1)).1 heta
  have hfirstDegree : R.firstDegree =
      L5A2B4AR4R2B.c1 R * weights B (e 0) := by
    simpa [e, L5A2B4AR4R2B.c1, R.reindex_zero] using
      R.first.degree_eq_critical
  have hrawRelation := L5A2B4AR4R2B.branchB_first_relation R
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
  simpa [gridDegree, e] using hK

/-- The lower part of the pure-`c` selected-anchor axis is excluded by the
active first mixed critical gate. -/
theorem branchB_selected_return_axisC_low_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (haxis :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = 0 ∧ 1 ≤ A.coordinate.j ∧
        A.coordinate.j ≤ qH R) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = 0 ∧ 1 ≤ A.coordinate.j ∧
      A.coordinate.j ≤ qH R at haxis
  let j := A.coordinate.j.toNat
  have hj0 : (0 : ℤ) ≤ A.coordinate.j := by omega
  have hj : A.coordinate.j = j := (Int.toNat_of_nonneg hj0).symm
  apply (branchB_first_mixed_boundary_exclusions R hB).1
  exact branchB_selected_anchor_first_b_predecessor_mem R hB hs 0 j
    haxis.1 hj (by exact (branchB_actual_herzog_coordinates R).cross_positive.1)
    (by omega)

/-- The lower part of the pure-`b` selected-anchor axis is excluded by the
active first mixed critical gate. -/
theorem branchB_selected_return_axisB_low_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (haxis :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.j = 0 ∧ 1 ≤ A.coordinate.i ∧
        A.coordinate.i ≤ pH R) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.j = 0 ∧ 1 ≤ A.coordinate.i ∧
      A.coordinate.i ≤ pH R at haxis
  let i := A.coordinate.i.toNat
  have hi0 : (0 : ℤ) ≤ A.coordinate.i := by omega
  have hi : A.coordinate.i = i := (Int.toNat_of_nonneg hi0).symm
  apply (branchB_first_mixed_boundary_exclusions R hB).2
  exact branchB_selected_anchor_first_c_predecessor_mem R hB hs i 0
    hi haxis.1 (by omega)
    (by exact (branchB_actual_herzog_coordinates R).cross_positive.2.1)

/-- The pure inward predecessor of the second actual critical relation is
excluded from the chosen tail ideal.  Unlike the third (inactive) critical
degree, the second degree is one of the two genuine positive degrees. -/
theorem branchB_second_pure_boundary_exclusion
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) :
    R.secondDegree - weights P.M.base (R.reindex 1) ∉ P.M.base.K := by
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
  have hsecond : R.secondDegree ∈ positiveDegrees P.M := by
    rw [R.positiveDegrees_eq]
    simp
  intro hmem
  apply hgenuine R.secondDegree hsecond R.second.pureComponent
  obtain ⟨pureWitness, hpureComponent, hpurePos⟩ :=
    (mem_componentSupport P.M.base R.secondDegree R.second.pureComponent
      (R.reindex 1)).mp (by rw [R.reindex_one, R.second.pureSupport]; simp)
  exact ⟨pureWitness, hpureComponent, R.reindex 1, hpurePos, hmem⟩

/-- A pure-`b` selected anchor always puts the pure predecessor of the second
actual critical relation into the chosen tail ideal. -/
theorem branchB_selected_anchor_second_pure_predecessor_mem
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i : ℕ)
    (hi : (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.i = i)
    (hj : (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.j = 0)
    (hiLt : i < L5A2B4AR4R2B.c2 R) :
    R.secondDegree - weights P.M.base (R.reindex 1) ∈ P.M.base.K := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let B := P.M.base
  let e := R.reindex
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, hi, hj]
    at hbeta
  simp only [zero_mul, add_zero] at hbeta
  have hanchor := A.anchor_eq
  rw [hbeta] at hanchor
  have hanchorNat : i * normalizedB R = A.n + normalizedA R * A.depth := by
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
  let x : ℕ := (L5A2B4AR4R2B.c2 R - 1) * normalizedB R
  have hxm : (x : ℤ) ∈ routingI B e := by
    apply (mem_routingI_iff_positive_return B e (x : ℤ)).2
    refine ⟨A.ell, A.ell_pos, ?_, ?_⟩
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      refine ⟨x, ?_, rfl⟩
      simpa [x, hAeq, hBeq, hCeq, Nat.zero_mul, Nat.zero_add] using
        hgen 0 (L5A2B4AR4R2B.c2 R - 1) 0
    · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
      let y : ℕ := A.depth * normalizedA R +
        (L5A2B4AR4R2B.c2 R - 1 - i) * normalizedB R
      refine ⟨y, ?_, ?_⟩
      · simpa [y, hAeq, hBeq, hCeq, Nat.add_assoc] using
          hgen A.depth (L5A2B4AR4R2B.c2 R - 1 - i) 0
      · have hn : A.n = A.ell * normalizedM B := A.n_eq
        have hiLe : i ≤ L5A2B4AR4R2B.c2 R - 1 := by omega
        have hiSplit : L5A2B4AR4R2B.c2 R - 1 =
            i + (L5A2B4AR4R2B.c2 R - 1 - i) := by omega
        have hiMul : (L5A2B4AR4R2B.c2 R - 1) * normalizedB R =
            i * normalizedB R +
              (L5A2B4AR4R2B.c2 R - 1 - i) * normalizedB R := by
          rw [← Nat.add_mul]
          exact congrArg (fun t => t * normalizedB R) hiSplit
        have hcalc : x = A.n + y := by
          calc
            x = i * normalizedB R +
                (L5A2B4AR4R2B.c2 R - 1 - i) * normalizedB R := by
              dsimp [x]
              rw [hiMul]
            _ = (A.n + normalizedA R * A.depth) +
                (L5A2B4AR4R2B.c2 R - 1 - i) * normalizedB R := by
              rw [hanchorNat]
            _ = A.n + y := by dsimp [y]; ring
        rw [hcalc, hn]
        push_cast
        ring
  have heta : eta B e (L5A2B4AR4R2B.c2 R - 1) 0 = 0 := by
    have hle := (normalizedGrid_mem_iff_eta_le B e 0
      (L5A2B4AR4R2B.c2 R - 1) 0).1
      (by simpa [x, normalizedGrid, hAeq, hBeq, hCeq] using hxm)
    omega
  have hK := (eta_eq_zero_iff B e (L5A2B4AR4R2B.c2 R - 1) 0).1 heta
  have hsecondDegree : R.secondDegree =
      L5A2B4AR4R2B.c2 R * weights B (e 1) := by
    simpa [e, L5A2B4AR4R2B.c2, R.reindex_one] using
      R.second.degree_eq_critical
  have hc2pos : 0 < L5A2B4AR4R2B.c2 R := by
    have hp := (branchB_actual_herzog_coordinates R).cross_positive.1
    have hz := (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.2.2
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    omega
  have hc2Split : L5A2B4AR4R2B.c2 R =
      1 + (L5A2B4AR4R2B.c2 R - 1) := by omega
  rw [hsecondDegree]
  change (L5A2B4AR4R2B.c2 R * weights B (e 1)) - weights B (e 1) ∈ B.K
  rw [hc2Split, Nat.add_mul]
  simpa [gridDegree, e, Nat.add_assoc] using hK

/-- The pure-`b` selected-anchor axis is excluded on its entire L-shape range.
This is the asymmetric B49 SILVER checkpoint. -/
theorem branchB_selected_return_axisB_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (haxis :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.j = 0 ∧ 1 ≤ A.coordinate.i ∧
        A.coordinate.i < pH R + zH R) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.j = 0 ∧ 1 ≤ A.coordinate.i ∧
      A.coordinate.i < pH R + zH R at haxis
  let i := A.coordinate.i.toNat
  have hi0 : (0 : ℤ) ≤ A.coordinate.i := by omega
  have hi : A.coordinate.i = i := (Int.toNat_of_nonneg hi0).symm
  have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  apply branchB_second_pure_boundary_exclusion R hB
  exact branchB_selected_anchor_second_pure_predecessor_mem R hB hs i
    hi haxis.1 (by rw [hsum]; omega)

/-- Kernel-closed axis frontier.  The complete pure-`b` axis is eliminated;
the sole remaining obstruction is the pure-`c` seam beyond `qH`, whose natural
critical predecessor belongs to the inactive third critical component. -/
theorem branchB_selected_return_positive_or_seam_axis
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    (1 ≤ A.coordinate.i ∧ 1 ≤ A.coordinate.j) ∨
      (A.coordinate.i = 0 ∧ qH R < A.coordinate.j ∧
        A.coordinate.j < qH R + vH R) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  have h := branchB_selected_return_anchor_positive_or_axis_obstruction R hB hs
  change (1 ≤ A.coordinate.i ∧ 1 ≤ A.coordinate.j) ∨ _ ∨ _ at h
  rcases h with hpos | haxisC | haxisB
  · exact Or.inl hpos
  · right
    refine ⟨haxisC.1, ?_, haxisC.2.2.1⟩
    by_contra hnot
    exact branchB_selected_return_axisC_low_impossible R hB hs
      ⟨haxisC.1, haxisC.2.1, by omega⟩
  · exact (branchB_selected_return_axisB_impossible R hB hs
      ⟨haxisB.1, haxisB.2.1, haxisB.2.2.1⟩).elim

/-- Event-local B49 SILVER frontier.  Positive CENTER and the entire pure-`b`
axis have been discharged; the packet retains the actual individual source,
its support route, and exactly one of strict RB, strict LT, or the sole
remaining pure-`c` seam obstruction. -/
theorem branchB_actualZeroEdgeBirth_strict_arm_or_axisC_seam
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
          (A.coordinate.i = 0 ∧ qH R < A.coordinate.j ∧
            A.coordinate.j < qH R + vH R)) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hsx
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  have hprov := branchB_actualZeroEdgeBirth_individual_return_source
    R hB x hsx hbirth
  obtain ⟨route, hroute⟩ := branchB_selected_return_source_support_route R hB hsx
  refine ⟨hprov.2.2.2.1, route, hroute, ?_⟩
  have hclass := branchB_selected_return_positive_or_seam_axis R hB hsx
  change (1 ≤ A.coordinate.i ∧ 1 ≤ A.coordinate.j) ∨ _ at hclass
  rcases hclass with hpos | haxisC
  · have hpositive := branchB_selected_return_exact_positive_class_v2 R hB hsx hpos
    change InActualPositiveReturnClass R A.coordinate.i A.coordinate.j at hpositive
    rcases hpositive with hcenter | hRB | hLT
    · obtain ⟨i, j, hi, hj, hi0, hip, hj0, hjq, hcorner⟩ := hcenter
      exact (branchB_positive_center_impossible R hB hsx i j
        ⟨hi, hj, hi0, hip, hj0, hjq, hcorner⟩).elim
    · exact Or.inl hRB
    · exact Or.inr (Or.inl hLT)
  · exact Or.inr (Or.inr haxisC)

end NS25Lean.L5A2B4AR5B
