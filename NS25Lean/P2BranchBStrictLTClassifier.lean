import NS25Lean.P2BranchBStrictRBPureAxisElimination

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Concrete strict-LT F packet. -/
def StrictLTActualFPacket
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (sigma tau : ℕ) : Prop :=
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  C.data.sourceValue =
      sigma * normalizedB R + (qH R + tau) * normalizedC R ∧
    C.data.returnedValue = A.depth * normalizedA R ∧
    C.source_coordinate.i = sigma ∧
    C.source_coordinate.j = qH R + tau ∧
    C.source_coordinate.level = 0 ∧
    C.returned_coordinate.i = 0 ∧
    C.returned_coordinate.j = 0 ∧
    C.returned_coordinate.level = A.depth

/-- On the actual `bc` support route, a strict-LT return has the complete F
value and canonical-coordinate packet. -/
theorem branchB_strictLT_bc_F_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.bc
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    StrictLTActualFPacket R hB hs sigma tau := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau at hLT
  have hvalues := branchB_individual_return_F_value_pair R hB hs hroute
  have hcanonical := branchB_individual_return_F_canonical_packet R hB hs hroute
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, hLT.1, hLT.2] at hbeta
  have hsourceZ : (C.data.sourceValue : ℤ) =
      sigma * normalizedB R + (qH R + tau) * normalizedC R :=
    hvalues.1.trans hbeta
  refine ⟨by exact_mod_cast hsourceZ, hvalues.2, ?_⟩
  exact ⟨hcanonical.1.trans hLT.1, hcanonical.2.1.trans hLT.2,
    hcanonical.2.2.1.trans hlevel, hcanonical.2.2.2.2.1,
    hcanonical.2.2.2.2.2.1, hcanonical.2.2.2.2.2.2⟩

private theorem strictLT_normalizedWeight_pos
    (R : SectorBCriticalRoleBranchB P) (k : Fin 3) :
    0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex k) := by
  have hs := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex k)
  have hw := L2B.weights_positive P.M.base (R.reindex k)
  nlinarith

private theorem strictLT_relation_of_signed_below
    (a b c A B C i : ℕ) (hBi : B ≤ i)
    (h : (A : ℤ) * a + ((B : ℤ) - i) * b = (C : ℤ) * c) :
    A * a = (i - B) * b + C * c := by
  have hcast : ((i - B : ℕ) : ℤ) = i - B := Nat.cast_sub hBi
  exact_mod_cast (show (A : ℤ) * a =
      ((i - B : ℕ) : ℤ) * b + C * c by
    rw [hcast]
    nlinarith only [h])

private theorem strictLT_relation_of_signed_above
    (a b c A B C i : ℕ) (hiB : i ≤ B)
    (h : (A : ℤ) * a + ((B : ℤ) - i) * b = (C : ℤ) * c) :
    C * c = A * a + (B - i) * b := by
  have hcast : ((B - i : ℕ) : ℤ) = B - i := Nat.cast_sub hiB
  exact_mod_cast (show (C : ℤ) * c =
      (A : ℤ) * a + ((B - i : ℕ) : ℤ) * b by
    rw [hcast]
    nlinarith only [h])

/-- On an actual strict-LT `ab` route, the returned `c` coefficient reaches
the LT-X floor. -/
theorem branchB_strictLT_ab_returnedZ_floor
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    vH R - tau ≤ C.data.returnedZ := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change vH R - tau ≤ C.data.returnedZ
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  rcases hLT with ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hcorner := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hcorner.1.resolve_left hroute'.1
  have hry : C.data.returnedY = 0 := hcorner.2.1.resolve_left hroute'.2.1
  have hreturned : C.data.returnedValue =
      C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hrx, hry]
    omega
  have hrz : C.data.returnedZ ≠ 0 := by
    intro hz
    apply (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.1
    rw [hreturned, hz]
    simp
  have hbalance := (branchB_selected_return_source_balance_packet R hB hs).2.1
  have hrelationZ :
      (((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R) +
          (((C.data.sourceY : ℤ) - sigma) * normalizedB R) =
        ((qH R + tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
    rw [hroute'.2.2, hrx, hry, hi, hj] at hbalance
    push_cast at hbalance ⊢
    nlinarith only [hbalance]
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  by_cases hmu : sigma ≤ C.data.sourceY
  · have hrelC : (qH R + tau + C.data.returnedZ) * normalizedC R =
        (C.data.sourceX + A.depth) * normalizedA R +
          (C.data.sourceY - sigma) * normalizedB R := by
      exact strictLT_relation_of_signed_above
        (normalizedA R) (normalizedB R) (normalizedC R)
        (C.data.sourceX + A.depth) C.data.sourceY
        (qH R + tau + C.data.returnedZ) sigma hmu hrelationZ
    have hc3Le := branchB_normalizedC_relation_min R _ _ _ (by omega) hrelC
    rw [hs3] at hc3Le
    omega
  · have hmuLt : C.data.sourceY < sigma := Nat.lt_of_not_ge hmu
    have hmuLe : C.data.sourceY ≤ sigma := Nat.le_of_lt hmuLt
    have hrelA : (C.data.sourceX + A.depth) * normalizedA R =
        (sigma - C.data.sourceY) * normalizedB R +
          (qH R + tau + C.data.returnedZ) * normalizedC R := by
      exact strictLT_relation_of_signed_below
        (normalizedA R) (normalizedB R) (normalizedC R)
        (C.data.sourceX + A.depth) C.data.sourceY
        (qH R + tau + C.data.returnedZ) sigma hmuLe hrelationZ
    have hc1Le := branchB_normalizedA_relation_min R _ _ _ (by omega) hrelA
    by_contra hfloor
    have hrzLt : C.data.returnedZ < vH R - tau := Nat.lt_of_not_ge hfloor
    have hsumLt : tau + C.data.returnedZ < vH R := by omega
    have hcoeff : sigma ≤ pH R + C.data.sourceY := by omega
    have hrelAZ : ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R =
        ((sigma - C.data.sourceY : ℕ) : ℤ) * normalizedB R +
          ((qH R + tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
      exact_mod_cast hrelA
    have hrel1Z : (L5A2B4AR4R2B.c1 R : ℤ) * normalizedA R =
        (pH R : ℤ) * normalizedB R + (qH R : ℤ) * normalizedC R := by
      exact_mod_cast hrel1
    have hdiffZ :
        (((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
            normalizedA R) +
          (((pH R + C.data.sourceY - sigma : ℕ) : ℤ) * normalizedB R) =
          ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
      rw [Nat.cast_sub hmuLe] at hrelAZ
      rw [Nat.cast_sub hc1Le, Nat.cast_sub hcoeff]
      push_cast only [Nat.cast_add, Nat.cast_mul] at hrelAZ hrel1Z ⊢
      linear_combination hrelAZ - hrel1Z
    have hdiff :
        (C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R) * normalizedA R +
          (pH R + C.data.sourceY - sigma) * normalizedB R =
          (tau + C.data.returnedZ) * normalizedC R := by
      exact_mod_cast hdiffZ
    have hcoefPos : 0 < tau + C.data.returnedZ := by omega
    have hc3Le := branchB_normalizedC_relation_min R _ _ _ hcoefPos hdiff.symm
    omega

/-- The strict-LT X value is an actual member of the same individual return
ideal. -/
theorem branchB_strictLT_X_value_mem_returnIdeal
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    ((((wH R - A.depth) * normalizedA R +
      (sigma + zH R) * normalizedB R : ℕ) : ℤ) ∈
        returnIdeal (normalizedH P.M.base) A.n) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  let Xval := (wH R - A.depth) * normalizedA R +
    (sigma + zH R) * normalizedB R
  have hX := branchB_strictLT_X_value_identity R hB hs sigma tau hLT
  have hX' : A.n + (vH R - tau) * normalizedC R = Xval := by
    simpa only [Xval] using hX
  have hsourceH : Xval ∈ normalizedH P.M.base := by
    have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedA_mem R) (wH R - A.depth)
    have hb := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedB_mem R) (sigma + zH R)
    simpa [Xval, nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).add_mem ha hb
  have hreturnedH : (vH R - tau) * normalizedC R ∈ normalizedH P.M.base := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) (vH R - tau)
  change (Xval : ℤ) ∈ (normalizedH P.M.base).asRelativeIdeal ∧
    (Xval : ℤ) - (A.n : ℕ) ∈ (normalizedH P.M.base).asRelativeIdeal
  constructor
  · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨Xval, hsourceH, rfl⟩
  · have hdiff : (Xval : ℤ) - (A.n : ℕ) =
        ((vH R - tau) * normalizedC R : ℕ) := by
      have hXZ : (Xval : ℤ) =
          (A.n : ℤ) + ((vH R - tau) * normalizedC R : ℕ) := by
        exact_mod_cast hX'.symm
      rw [hXZ]
      ring
    rw [hdiff, NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨(vH R - tau) * normalizedC R, hreturnedH, rfl⟩

/-- Minimality collapses the actual strict-LT `ab` source onto X. -/
theorem branchB_strictLT_ab_source_value_eq_X
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceValue = (wH R - A.depth) * normalizedA R +
      (sigma + zH R) * normalizedB R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  let Xval := (wH R - A.depth) * normalizedA R +
    (sigma + zH R) * normalizedB R
  have hfloor := branchB_strictLT_ab_returnedZ_floor R hB hs sigma tau hLT hroute
  change vH R - tau ≤ C.data.returnedZ at hfloor
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hcorner := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hcorner.1.resolve_left hroute'.1
  have hry : C.data.returnedY = 0 := hcorner.2.1.resolve_left hroute'.2.1
  have hreturned : C.data.returnedValue =
      C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hrx, hry]
    omega
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hX := branchB_strictLT_X_value_identity R hB hs sigma tau hLT
  have hX' : A.n + (vH R - tau) * normalizedC R = Xval := by
    simpa only [Xval] using hX
  let k := C.data.returnedZ - (vH R - tau)
  have hkadd : vH R - tau + k = C.data.returnedZ := Nat.add_sub_of_le hfloor
  have hsplit : C.data.sourceValue = Xval + k * normalizedC R := by
    rw [hactual, hreturned, ← hkadd, Nat.add_mul, ← Nat.add_assoc, hX']
  have hmin : (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) := by
    rw [C.data.source_eq]
    exact A.source_minimal
  have hXmem := branchB_strictLT_X_value_mem_returnIdeal R hB hs sigma tau hLT
  change (Xval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hXmem
  have hgapH : k * normalizedC R ∈ normalizedH P.M.base := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) k
  have hsplitZ : (C.data.sourceValue : ℤ) =
      (Xval : ℤ) + (k * normalizedC R : ℕ) := by
    exact_mod_cast hsplit
  have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
    (returnIdeal (normalizedH P.M.base) A.n) hmin hXmem hgapH hsplitZ).1
  have hk0 : k = 0 := (Nat.mul_eq_zero.mp hgap0).resolve_right
    (strictLT_normalizedWeight_pos R 2).ne'
  change C.data.sourceValue = Xval
  simpa [hk0] using hsplit

private theorem strictLT_lShape_coordinate_eq_of_exact
    (R : SectorBCriticalRoleBranchB P) {n : ℤ}
    (D : ActualLShapeCoordinate R n) (ii jj level : ℤ)
    (hshape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) ii jj)
    (hexact : n = level * normalizedA R +
      ii * normalizedB R + jj * normalizedC R) :
    D.i = ii ∧ D.j = jj ∧ D.level = level := by
  have hmod : Int.ModEq (normalizedA R)
      (ii * normalizedB R + jj * normalizedC R) n := by
    rw [Int.modEq_iff_dvd]
    refine ⟨level, ?_⟩
    nlinarith only [hexact]
  obtain ⟨hi, hj⟩ := D.pair_unique ii jj hshape hmod
  have hl : D.level = level := by
    symm
    apply D.level_unique level
    simpa [hi, hj] using hexact
  exact ⟨hi.symm, hj.symm, hl⟩

/-- Concrete strict-LT X packet. -/
def StrictLTActualXPacket
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (sigma tau : ℕ) : Prop :=
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  C.data.sourceValue = (wH R - A.depth) * normalizedA R +
      (sigma + zH R) * normalizedB R ∧
    C.data.returnedValue = (vH R - tau) * normalizedC R ∧
    C.source_coordinate.i = sigma + zH R ∧
    C.source_coordinate.j = 0 ∧
    C.source_coordinate.level = ((wH R - A.depth : ℕ) : ℤ) ∧
    C.returned_coordinate.i = 0 ∧
    C.returned_coordinate.j = ((vH R - tau : ℕ) : ℤ) ∧
    C.returned_coordinate.level = 0

/-- Full numeric and canonical X packet for an actual strict-LT `ab` route. -/
theorem branchB_strictLT_ab_X_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    StrictLTActualXPacket R hB hs sigma tau := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  rcases hLT with ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hLT' : A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R := ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hsource := branchB_strictLT_ab_source_value_eq_X
    R hB hs sigma tau hLT' hroute
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hX := branchB_strictLT_X_value_identity R hB hs sigma tau hLT'
  have hreturned : C.data.returnedValue = (vH R - tau) * normalizedC R := by
    have heq : A.n + C.data.returnedValue =
        A.n + (vH R - tau) * normalizedC R := by
      rw [← hactual, hsource]
      exact hX.symm
    exact Nat.add_left_cancel heq
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  have hsShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      ((sigma + zH R : ℕ) : ℤ) 0 := by
    unfold L5A2B.InLShape
    refine ⟨by positivity, by norm_num, ?_, ?_, Or.inr ?_⟩
    · exact_mod_cast Nat.add_lt_add_right hsigmaLt (zH R)
    · exact_mod_cast Nat.add_pos_left hq (vH R)
    · exact_mod_cast hq
  have hrShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      0 ((vH R - tau : ℕ) : ℤ) := by
    unfold L5A2B.InLShape
    refine ⟨by norm_num, by exact_mod_cast Nat.zero_le (vH R - tau), ?_, ?_, Or.inl ?_⟩
    · exact_mod_cast Nat.add_pos_left hp (zH R)
    · exact_mod_cast (show vH R - tau < qH R + vH R by omega)
    · exact_mod_cast hp
  have hsExact : (C.data.sourceValue : ℤ) =
      ((wH R - A.depth : ℕ) : ℤ) * normalizedA R +
        ((sigma + zH R : ℕ) : ℤ) * normalizedB R + 0 * normalizedC R := by
    have hcast : (C.data.sourceValue : ℤ) =
        (((wH R - A.depth) * normalizedA R +
          (sigma + zH R) * normalizedB R : ℕ) : ℤ) := by
      exact_mod_cast hsource
    push_cast at hcast
    simpa using hcast
  have hrExact : (C.data.returnedValue : ℤ) =
      0 * normalizedA R + 0 * normalizedB R +
        ((vH R - tau : ℕ) : ℤ) * normalizedC R := by
    have hcast : (C.data.returnedValue : ℤ) =
        (((vH R - tau) * normalizedC R : ℕ) : ℤ) := by
      exact_mod_cast hreturned
    push_cast at hcast
    simpa using hcast
  obtain ⟨hsi, hsj, hsl⟩ := strictLT_lShape_coordinate_eq_of_exact R
    C.source_coordinate ((sigma + zH R : ℕ) : ℤ) 0
      ((wH R - A.depth : ℕ) : ℤ) hsShape hsExact
  obtain ⟨hri, hrj, hrl⟩ := strictLT_lShape_coordinate_eq_of_exact R
    C.returned_coordinate 0 ((vH R - tau : ℕ) : ℤ) 0 hrShape hrExact
  exact ⟨hsource, hreturned, hsi, hsj, hsl, hri, hrj, hrl⟩

private theorem strictLT_ac_relation_above
    (a b c A B mu base : ℕ) (hbase : base ≤ mu)
    (h : (A : ℤ) * a + ((mu : ℤ) - base) * c = (B : ℤ) * b) :
    B * b = A * a + (mu - base) * c := by
  have hcast : ((mu - base : ℕ) : ℤ) = mu - base := Nat.cast_sub hbase
  exact_mod_cast (show (B : ℤ) * b =
      (A : ℤ) * a + ((mu - base : ℕ) : ℤ) * c by
    rw [hcast]
    nlinarith only [h])

private theorem strictLT_ac_relation_below
    (a b c A B mu base : ℕ) (hmu : mu ≤ base)
    (h : (A : ℤ) * a + ((mu : ℤ) - base) * c = (B : ℤ) * b) :
    A * a = B * b + (base - mu) * c := by
  have hcast : ((base - mu : ℕ) : ℤ) = base - mu := Nat.cast_sub hmu
  exact_mod_cast (show (A : ℤ) * a =
      (B : ℤ) * b + ((base - mu : ℕ) : ℤ) * c by
    rw [hcast]
    nlinarith only [h])

/-- On an actual strict-LT `ac` route, the returned `b` coefficient reaches
the LT-Y floor. -/
theorem branchB_strictLT_ac_returnedY_floor
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    pH R - sigma ≤ C.data.returnedY := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change pH R - sigma ≤ C.data.returnedY
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  rcases hLT with ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hcorner := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hcorner.1.resolve_left hroute'.1
  have hrz : C.data.returnedZ = 0 := hcorner.2.2.resolve_left hroute'.2.2
  have hreturned : C.data.returnedValue =
      C.data.returnedY * normalizedB R := by
    rw [C.data.returned_factorization, hrx, hrz]
    omega
  have hry : C.data.returnedY ≠ 0 := by
    intro hy
    apply (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.1
    rw [hreturned, hy]
    simp
  have hbalance := (branchB_selected_return_source_balance_packet R hB hs).2.1
  have hrelationZ :
      (((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R) +
          (((C.data.sourceZ : ℤ) - (qH R + tau)) * normalizedC R) =
        ((sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R := by
    rw [hroute'.2.1, hrx, hrz, hi, hj] at hbalance
    push_cast at hbalance ⊢
    nlinarith only [hbalance]
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  by_cases hmu : qH R + tau ≤ C.data.sourceZ
  · have hrelB : (sigma + C.data.returnedY) * normalizedB R =
        (C.data.sourceX + A.depth) * normalizedA R +
          (C.data.sourceZ - (qH R + tau)) * normalizedC R := by
      exact strictLT_ac_relation_above
        (normalizedA R) (normalizedB R) (normalizedC R)
        (C.data.sourceX + A.depth) (sigma + C.data.returnedY)
        C.data.sourceZ (qH R + tau) hmu hrelationZ
    have hc2Le := branchB_normalizedB_relation_min R _ _ _ (by omega) hrelB
    rw [hs2] at hc2Le
    omega
  · have hmuLt : C.data.sourceZ < qH R + tau := Nat.lt_of_not_ge hmu
    have hmuLe : C.data.sourceZ ≤ qH R + tau := Nat.le_of_lt hmuLt
    have hrelA : (C.data.sourceX + A.depth) * normalizedA R =
        (sigma + C.data.returnedY) * normalizedB R +
          (qH R + tau - C.data.sourceZ) * normalizedC R := by
      exact strictLT_ac_relation_below
        (normalizedA R) (normalizedB R) (normalizedC R)
        (C.data.sourceX + A.depth) (sigma + C.data.returnedY)
        C.data.sourceZ (qH R + tau) hmuLe hrelationZ
    have hc1Le := branchB_normalizedA_relation_min R _ _ _ (by omega) hrelA
    by_contra hfloor
    have hryLt : C.data.returnedY < pH R - sigma := Nat.lt_of_not_ge hfloor
    have hsumLt : sigma + C.data.returnedY < pH R := by omega
    have hrelAZ : ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R =
        ((sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R +
          ((qH R + tau - C.data.sourceZ : ℕ) : ℤ) * normalizedC R := by
      exact_mod_cast hrelA
    have hrel1Z : (L5A2B4AR4R2B.c1 R : ℤ) * normalizedA R =
        (pH R : ℤ) * normalizedB R + (qH R : ℤ) * normalizedC R := by
      exact_mod_cast hrel1
    have hdiffZ :
        (((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
            normalizedA R) +
          (((pH R - (sigma + C.data.returnedY) : ℕ) : ℤ) * normalizedB R) =
          ((tau : ℤ) - C.data.sourceZ) * normalizedC R := by
      rw [Nat.cast_sub hc1Le, Nat.cast_sub (Nat.le_of_lt hsumLt)]
      rw [Nat.cast_sub hmuLe] at hrelAZ
      push_cast only [Nat.cast_add, Nat.cast_mul] at hrelAZ hrel1Z ⊢
      linear_combination hrelAZ - hrel1Z
    by_cases hmutau : C.data.sourceZ ≤ tau
    · have hdiff :
          (C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R) * normalizedA R +
            (pH R - (sigma + C.data.returnedY)) * normalizedB R =
            (tau - C.data.sourceZ) * normalizedC R := by
        have hcast : ((tau - C.data.sourceZ : ℕ) : ℤ) =
            (tau : ℤ) - C.data.sourceZ := Nat.cast_sub hmutau
        exact_mod_cast (show
          (((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
              normalizedA R) +
            (((pH R - (sigma + C.data.returnedY) : ℕ) : ℤ) * normalizedB R) =
            ((tau - C.data.sourceZ : ℕ) : ℤ) * normalizedC R by
              rw [hcast]
              exact hdiffZ)
      have hbcoef : 0 < pH R - (sigma + C.data.returnedY) := by omega
      have hlhsPos : 0 <
          (C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R) * normalizedA R +
            (pH R - (sigma + C.data.returnedY)) * normalizedB R := by
        have hbpos := strictLT_normalizedWeight_pos R 1
        positivity
      have hctau : 0 < tau - C.data.sourceZ := by
        by_contra hn
        have hzcoef : tau - C.data.sourceZ = 0 := Nat.eq_zero_of_not_pos hn
        rw [hdiff, hzcoef, zero_mul] at hlhsPos
        exact (Nat.lt_irrefl 0 hlhsPos)
      have hc3Le := branchB_normalizedC_relation_min R _ _ _ hctau hdiff.symm
      omega
    · have htauMu : tau < C.data.sourceZ := Nat.lt_of_not_ge hmutau
      have hleftNonneg : 0 ≤
          (((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
            normalizedA R) := by positivity
      have hbcoef : 0 < pH R - (sigma + C.data.returnedY) := by omega
      have hbrightPos : 0 <
          (((pH R - (sigma + C.data.returnedY) : ℕ) : ℤ) * normalizedB R) := by
        have hbpos : (0 : ℤ) < normalizedB R := by
          exact_mod_cast strictLT_normalizedWeight_pos R 1
        positivity
      have hlhsPos : 0 <
          (((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
              normalizedA R) +
            (((pH R - (sigma + C.data.returnedY) : ℕ) : ℤ) * normalizedB R) :=
        add_pos_of_nonneg_of_pos hleftNonneg hbrightPos
      have hrightNeg : ((tau : ℤ) - C.data.sourceZ) * normalizedC R < 0 := by
        have htauZ : (tau : ℤ) < C.data.sourceZ := by exact_mod_cast htauMu
        have hdneg : (tau : ℤ) - C.data.sourceZ < 0 := sub_neg.mpr htauZ
        have hcpos : (0 : ℤ) < normalizedC R := by
          exact_mod_cast strictLT_normalizedWeight_pos R 2
        exact mul_neg_of_neg_of_pos hdneg hcpos
      rw [hdiffZ] at hlhsPos
      exact (not_lt_of_ge (le_of_lt hrightNeg)) hlhsPos

/-- The strict-LT Y value belongs to the same individual return ideal. -/
theorem branchB_strictLT_Y_value_mem_returnIdeal
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    ((((L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
      tau * normalizedC R : ℕ) : ℤ) ∈
        returnIdeal (normalizedH P.M.base) A.n) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  let Yval := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
    tau * normalizedC R
  have hY := branchB_strictLT_Y_value_identity R hB hs sigma tau hLT
  have hY' : A.n + (pH R - sigma) * normalizedB R = Yval := by
    simpa only [Yval] using hY
  have hsourceH : Yval ∈ normalizedH P.M.base := by
    have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedA_mem R) (L5A2B4AR4R2B.c1 R - A.depth)
    have hc := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedC_mem R) tau
    simpa [Yval, nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).add_mem ha hc
  have hreturnedH : (pH R - sigma) * normalizedB R ∈ normalizedH P.M.base := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) (pH R - sigma)
  change (Yval : ℤ) ∈ (normalizedH P.M.base).asRelativeIdeal ∧
    (Yval : ℤ) - (A.n : ℕ) ∈ (normalizedH P.M.base).asRelativeIdeal
  constructor
  · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨Yval, hsourceH, rfl⟩
  · have hdiff : (Yval : ℤ) - (A.n : ℕ) =
        ((pH R - sigma) * normalizedB R : ℕ) := by
      have hYZ : (Yval : ℤ) =
          (A.n : ℤ) + ((pH R - sigma) * normalizedB R : ℕ) := by
        exact_mod_cast hY'.symm
      rw [hYZ]
      ring
    rw [hdiff, NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨(pH R - sigma) * normalizedB R, hreturnedH, rfl⟩

/-- Minimality collapses the actual strict-LT `ac` source onto Y. -/
theorem branchB_strictLT_ac_source_value_eq_Y
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceValue =
      (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        tau * normalizedC R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  let Yval := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
    tau * normalizedC R
  have hfloor := branchB_strictLT_ac_returnedY_floor R hB hs sigma tau hLT hroute
  change pH R - sigma ≤ C.data.returnedY at hfloor
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hcorner := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hcorner.1.resolve_left hroute'.1
  have hrz : C.data.returnedZ = 0 := hcorner.2.2.resolve_left hroute'.2.2
  have hreturned : C.data.returnedValue =
      C.data.returnedY * normalizedB R := by
    rw [C.data.returned_factorization, hrx, hrz]
    omega
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hY := branchB_strictLT_Y_value_identity R hB hs sigma tau hLT
  have hY' : A.n + (pH R - sigma) * normalizedB R = Yval := by
    simpa only [Yval] using hY
  let k := C.data.returnedY - (pH R - sigma)
  have hkadd : pH R - sigma + k = C.data.returnedY := Nat.add_sub_of_le hfloor
  have hsplit : C.data.sourceValue = Yval + k * normalizedB R := by
    rw [hactual, hreturned, ← hkadd, Nat.add_mul, ← Nat.add_assoc, hY']
  have hmin : (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) := by
    rw [C.data.source_eq]
    exact A.source_minimal
  have hYmem := branchB_strictLT_Y_value_mem_returnIdeal R hB hs sigma tau hLT
  change (Yval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hYmem
  have hgapH : k * normalizedB R ∈ normalizedH P.M.base := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) k
  have hsplitZ : (C.data.sourceValue : ℤ) =
      (Yval : ℤ) + (k * normalizedB R : ℕ) := by exact_mod_cast hsplit
  have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
    (returnIdeal (normalizedH P.M.base) A.n) hmin hYmem hgapH hsplitZ).1
  have hk0 : k = 0 := (Nat.mul_eq_zero.mp hgap0).resolve_right
    (strictLT_normalizedWeight_pos R 1).ne'
  change C.data.sourceValue = Yval
  simpa [hk0] using hsplit

/-- Concrete strict-LT Y packet. -/
def StrictLTActualYPacket
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (sigma tau : ℕ) : Prop :=
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  C.data.sourceValue =
      (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        tau * normalizedC R ∧
    C.data.returnedValue = (pH R - sigma) * normalizedB R ∧
    C.source_coordinate.i = 0 ∧ C.source_coordinate.j = tau ∧
    C.source_coordinate.level =
      ((L5A2B4AR4R2B.c1 R - A.depth : ℕ) : ℤ) ∧
    C.returned_coordinate.i = ((pH R - sigma : ℕ) : ℤ) ∧
    C.returned_coordinate.j = 0 ∧ C.returned_coordinate.level = 0

/-- Full numeric and canonical Y packet for an actual strict-LT `ac` route. -/
theorem branchB_strictLT_ac_Y_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    StrictLTActualYPacket R hB hs sigma tau := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  rcases hLT with ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hLT' : A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R := ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hsource := branchB_strictLT_ac_source_value_eq_Y
    R hB hs sigma tau hLT' hroute
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hY := branchB_strictLT_Y_value_identity R hB hs sigma tau hLT'
  have hreturned : C.data.returnedValue = (pH R - sigma) * normalizedB R := by
    have heq : A.n + C.data.returnedValue =
        A.n + (pH R - sigma) * normalizedB R := by
      rw [← hactual, hsource]
      exact hY.symm
    exact Nat.add_left_cancel heq
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  have hsShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      0 (tau : ℤ) := by
    unfold L5A2B.InLShape
    refine ⟨by norm_num, by positivity, ?_, ?_, Or.inl ?_⟩
    · exact_mod_cast Nat.add_pos_left hp (zH R)
    · exact_mod_cast htauLt.trans_le (Nat.le_add_left _ _)
    · exact_mod_cast hp
  have hrShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      ((pH R - sigma : ℕ) : ℤ) 0 := by
    unfold L5A2B.InLShape
    refine ⟨by exact_mod_cast Nat.zero_le (pH R - sigma), by norm_num, ?_, ?_, Or.inr ?_⟩
    · exact_mod_cast (show pH R - sigma < pH R + zH R by omega)
    · exact_mod_cast Nat.add_pos_left hq (vH R)
    · exact_mod_cast hq
  have hsExact : (C.data.sourceValue : ℤ) =
      ((L5A2B4AR4R2B.c1 R - A.depth : ℕ) : ℤ) * normalizedA R +
        0 * normalizedB R + (tau : ℤ) * normalizedC R := by
    have hcast : (C.data.sourceValue : ℤ) =
        (((L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
          tau * normalizedC R : ℕ) : ℤ) := by exact_mod_cast hsource
    push_cast at hcast
    simpa using hcast
  have hrExact : (C.data.returnedValue : ℤ) =
      0 * normalizedA R + ((pH R - sigma : ℕ) : ℤ) * normalizedB R +
        0 * normalizedC R := by
    have hcast : (C.data.returnedValue : ℤ) =
        (((pH R - sigma) * normalizedB R : ℕ) : ℤ) := by
      exact_mod_cast hreturned
    push_cast at hcast
    simpa using hcast
  obtain ⟨hsi, hsj, hsl⟩ := strictLT_lShape_coordinate_eq_of_exact R
    C.source_coordinate 0 (tau : ℤ)
      ((L5A2B4AR4R2B.c1 R - A.depth : ℕ) : ℤ) hsShape hsExact
  obtain ⟨hri, hrj, hrl⟩ := strictLT_lShape_coordinate_eq_of_exact R
    C.returned_coordinate ((pH R - sigma : ℕ) : ℤ) 0 0 hrShape hrExact
  exact ⟨hsource, hreturned, hsi, hsj, hsl, hri, hrj, hrl⟩

/-- On the residual strict-LT `a` route, at least one repaired arm-return
floor is reached. -/
theorem branchB_strictLT_a_return_floor_disjunction
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    vH R - tau ≤ C.data.returnedZ ∨
      pH R - sigma ≤ C.data.returnedY := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change vH R - tau ≤ C.data.returnedZ ∨
    pH R - sigma ≤ C.data.returnedY
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hcorner := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hcorner.1.resolve_left hroute'.1
  have hbalance := (branchB_selected_return_source_balance_packet R hB hs).2.1
  have hcritZ : ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R =
      ((sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R +
        ((qH R + tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
    rw [hroute'.2.1, hroute'.2.2, hrx, hLT.1, hLT.2.1] at hbalance
    push_cast at hbalance ⊢
    linear_combination hbalance
  have hcrit : (C.data.sourceX + A.depth) * normalizedA R =
      (sigma + C.data.returnedY) * normalizedB R +
        (qH R + tau + C.data.returnedZ) * normalizedC R := by
    exact_mod_cast hcritZ
  have hc1Le := branchB_normalizedA_relation_min R _ _ _
    (show 0 < C.data.sourceX + A.depth by omega) hcrit
  by_contra hfloors
  push Not at hfloors
  have hzLt : C.data.returnedZ < vH R - tau := hfloors.1
  have hyLt : C.data.returnedY < pH R - sigma := hfloors.2
  have hsumZ : tau + C.data.returnedZ < vH R := by omega
  have hsumY : sigma + C.data.returnedY < pH R := by omega
  have hrel1 := (branchB_actual_herzog_coordinates R).normalized_relations.1
  have hrel1Z : (L5A2B4AR4R2B.c1 R : ℤ) * normalizedA R =
      (pH R : ℤ) * normalizedB R + (qH R : ℤ) * normalizedC R := by
    exact_mod_cast hrel1
  have hdiffZ :
      (((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
          normalizedA R) +
        (((pH R - (sigma + C.data.returnedY) : ℕ) : ℤ) * normalizedB R) =
        ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
    rw [Nat.cast_sub hc1Le, Nat.cast_sub (Nat.le_of_lt hsumY)]
    push_cast only [Nat.cast_add, Nat.cast_mul] at hcritZ hrel1Z ⊢
    linear_combination hcritZ - hrel1Z
  have hdiff :
      (C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R) * normalizedA R +
        (pH R - (sigma + C.data.returnedY)) * normalizedB R =
        (tau + C.data.returnedZ) * normalizedC R := by
    exact_mod_cast hdiffZ
  have hc3Le := branchB_normalizedC_relation_min R _ _ _ (by omega) hdiff.symm
  have hs3 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
  omega

/-- The pure-`a` chosen factorization cannot survive for an actual strict-LT
individual-return source. -/
theorem branchB_strictLT_a_route_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hcorner := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hcorner.1.resolve_left hroute'.1
  have hsource : C.data.sourceValue = C.data.sourceX * normalizedA R := by
    rw [C.data.source_factorization, hroute'.2.1, hroute'.2.2]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedY * normalizedB R + C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hrx]
    omega
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hmin : (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) := by
    rw [C.data.source_eq]
    exact A.source_minimal
  rcases branchB_strictLT_a_return_floor_disjunction
      R hB hs sigma tau hLT hroute with hzfloor | hyfloor
  · let Xval := (wH R - A.depth) * normalizedA R +
        (sigma + zH R) * normalizedB R
    let kZ := C.data.returnedZ - (vH R - tau)
    let gap := C.data.returnedY * normalizedB R + kZ * normalizedC R
    have hk : vH R - tau + kZ = C.data.returnedZ := Nat.add_sub_of_le hzfloor
    have hX := branchB_strictLT_X_value_identity R hB hs sigma tau hLT
    have hX' : A.n + (vH R - tau) * normalizedC R = Xval := by
      simpa [Xval] using hX
    have hsplit : C.data.sourceValue = Xval + gap := by
      rw [hactual, hreturned, ← hk, Nat.add_mul]
      calc
        A.n + (C.data.returnedY * normalizedB R +
            ((vH R - tau) * normalizedC R + kZ * normalizedC R)) =
            (A.n + (vH R - tau) * normalizedC R) +
              (C.data.returnedY * normalizedB R + kZ * normalizedC R) := by omega
        _ = Xval + gap := by rw [hX']
    have hgapH : gap ∈ normalizedH P.M.base := by
      have hb := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) C.data.returnedY
      have hc := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) kZ
      simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).add_mem hb hc
    have hXmem := branchB_strictLT_X_value_mem_returnIdeal R hB hs sigma tau hLT
    change (Xval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hXmem
    have hsplitZ : (C.data.sourceValue : ℤ) = (Xval : ℤ) + gap := by
      exact_mod_cast hsplit
    have heq := (RelativeIdeal.minimalGenerator_eq_of_mem_add
      (returnIdeal (normalizedH P.M.base) A.n) hmin hXmem hgapH hsplitZ).2
    have heqNat : C.data.sourceValue = Xval := by exact_mod_cast heq
    rw [hsource] at heqNat
    have hbasePos : 0 < wH R - A.depth := by omega
    have hcoefGt : wH R - A.depth < C.data.sourceX := by
      dsimp [Xval] at heqNat
      have hb := strictLT_normalizedWeight_pos R 1
      by_contra hnot
      have hle := Nat.le_of_not_gt hnot
      have hprodLe := Nat.mul_le_mul_right (normalizedA R) hle
      have hpos : 0 < (sigma + zH R) * normalizedB R :=
        Nat.mul_pos (by omega) hb
      omega
    have hrelB : (sigma + zH R) * normalizedB R =
        (C.data.sourceX - (wH R - A.depth)) * normalizedA R +
          0 * normalizedC R := by
      dsimp [Xval] at heqNat
      have hsplitCoeff : (wH R - A.depth) +
          (C.data.sourceX - (wH R - A.depth)) = C.data.sourceX :=
        Nat.add_sub_of_le (Nat.le_of_lt hcoefGt)
      rw [← hsplitCoeff, Nat.add_mul] at heqNat
      omega
    have hc2Le := branchB_normalizedB_relation_min R _ _ _ (by omega) hrelB
    have hs2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    omega
  · let Yval := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        tau * normalizedC R
    let kY := C.data.returnedY - (pH R - sigma)
    let gap := kY * normalizedB R + C.data.returnedZ * normalizedC R
    have hk : pH R - sigma + kY = C.data.returnedY := Nat.add_sub_of_le hyfloor
    have hY := branchB_strictLT_Y_value_identity R hB hs sigma tau hLT
    have hY' : A.n + (pH R - sigma) * normalizedB R = Yval := by
      simpa [Yval] using hY
    have hsplit : C.data.sourceValue = Yval + gap := by
      rw [hactual, hreturned, ← hk, Nat.add_mul]
      calc
        A.n + ((pH R - sigma) * normalizedB R +
            kY * normalizedB R + C.data.returnedZ * normalizedC R) =
            (A.n + (pH R - sigma) * normalizedB R) +
              (kY * normalizedB R + C.data.returnedZ * normalizedC R) := by omega
        _ = Yval + gap := by rw [hY']
    have hgapH : gap ∈ normalizedH P.M.base := by
      have hb := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) kY
      have hc := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) C.data.returnedZ
      simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).add_mem hb hc
    have hYmem := branchB_strictLT_Y_value_mem_returnIdeal R hB hs sigma tau hLT
    change (Yval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hYmem
    have hsplitZ : (C.data.sourceValue : ℤ) = (Yval : ℤ) + gap := by
      exact_mod_cast hsplit
    have heq := (RelativeIdeal.minimalGenerator_eq_of_mem_add
      (returnIdeal (normalizedH P.M.base) A.n) hmin hYmem hgapH hsplitZ).2
    have heqNat : C.data.sourceValue = Yval := by exact_mod_cast heq
    rw [hsource] at heqNat
    have hbasePos : 0 < L5A2B4AR4R2B.c1 R - A.depth := by
      have hs1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
      obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
        (branchB_actual_herzog_coordinates R).cross_positive
      omega
    have hcoefGt : L5A2B4AR4R2B.c1 R - A.depth < C.data.sourceX := by
      dsimp [Yval] at heqNat
      have hc := strictLT_normalizedWeight_pos R 2
      by_contra hnot
      have hle := Nat.le_of_not_gt hnot
      have hprodLe := Nat.mul_le_mul_right (normalizedA R) hle
      have hpos : 0 < tau * normalizedC R := Nat.mul_pos (by omega) hc
      omega
    have hrelC : tau * normalizedC R =
        (C.data.sourceX - (L5A2B4AR4R2B.c1 R - A.depth)) * normalizedA R +
          0 * normalizedB R := by
      dsimp [Yval] at heqNat
      have hsplitCoeff : (L5A2B4AR4R2B.c1 R - A.depth) +
          (C.data.sourceX - (L5A2B4AR4R2B.c1 R - A.depth)) =
          C.data.sourceX := Nat.add_sub_of_le (Nat.le_of_lt hcoefGt)
      rw [← hsplitCoeff, Nat.add_mul] at heqNat
      omega
    have hc3Le := branchB_normalizedC_relation_min R _ _ _ (by omega) hrelC
    have hs3 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    omega

private theorem strictLT_F_value_mem_returnIdeal
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    (((sigma * normalizedB R + (qH R + tau) * normalizedC R : ℕ) : ℤ) ∈
      returnIdeal (normalizedH P.M.base) A.n) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau at hLT
  have hmem := branchB_selected_return_anchor_mem_returnIdeal R hB hs
  change A.beta ∈ returnIdeal (normalizedH P.M.base) A.n at hmem
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hcoord := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, hLT.1, hLT.2] at hcoord
  have hcoord' :
      (((sigma * normalizedB R + (qH R + tau) * normalizedC R : ℕ) : ℤ)) =
        A.beta := by
    rw [hcoord]
    push_cast
    ring
  rw [hcoord']
  exact hmem

private theorem strictLT_pureB_to_A
    (a b c d x mu sigma T : ℕ) (hx : x ≤ d) (hmu : mu ≤ sigma)
    (h : (((d : ℤ) - x) * a) + (((mu : ℤ) - sigma) * b) = (T : ℤ) * c) :
    (d - x) * a = (sigma - mu) * b + T * c := by
  have hxCast : ((d - x : ℕ) : ℤ) = d - x := Nat.cast_sub hx
  have hmuCast : ((sigma - mu : ℕ) : ℤ) = sigma - mu := Nat.cast_sub hmu
  exact_mod_cast (show ((d - x : ℕ) : ℤ) * a =
      ((sigma - mu : ℕ) : ℤ) * b + (T : ℤ) * c by
    rw [hxCast, hmuCast]
    nlinarith only [h])

private theorem strictLT_pureB_to_C
    (a b c d x mu sigma T : ℕ) (hx : x ≤ d) (hmu : sigma ≤ mu)
    (h : (((d : ℤ) - x) * a) + (((mu : ℤ) - sigma) * b) = (T : ℤ) * c) :
    T * c = (d - x) * a + (mu - sigma) * b := by
  have hxCast : ((d - x : ℕ) : ℤ) = d - x := Nat.cast_sub hx
  have hmuCast : ((mu - sigma : ℕ) : ℤ) = mu - sigma := Nat.cast_sub hmu
  exact_mod_cast (show (T : ℤ) * c =
      ((d - x : ℕ) : ℤ) * a + ((mu - sigma : ℕ) : ℤ) * b by
    rw [hxCast, hmuCast]
    nlinarith only [h])

private theorem strictLT_pureB_core_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hry := (branchB_positive_center_pureB_returned_support_split
    R hB hs hroute).1
  have hsource : C.data.sourceValue = C.data.sourceY * normalizedB R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.2]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedX * normalizedA R + C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hry]
    omega
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  let Fval := sigma * normalizedB R + (qH R + tau) * normalizedC R
  have hF := branchB_strictLT_F_value_identity R hB hs sigma tau
    ⟨hLT.1, hLT.2.1⟩
  have hF' : Fval = A.n + A.depth * normalizedA R := by
    simpa [Fval, Nat.mul_comm] using hF
  have hFmem := strictLT_F_value_mem_returnIdeal R hB hs sigma tau
    ⟨hLT.1, hLT.2.1⟩
  change (Fval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hFmem
  have hmin : (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) := by
    rw [C.data.source_eq]
    exact A.source_minimal
  by_cases hdx : A.depth ≤ C.data.returnedX
  · let kA := C.data.returnedX - A.depth
    let gap := kA * normalizedA R + C.data.returnedZ * normalizedC R
    have hk : A.depth + kA = C.data.returnedX := Nat.add_sub_of_le hdx
    have hsplit : C.data.sourceValue = Fval + gap := by
      rw [hactual, hreturned, ← hk, Nat.add_mul]
      calc
        A.n + (A.depth * normalizedA R + kA * normalizedA R +
            C.data.returnedZ * normalizedC R) =
            (A.n + A.depth * normalizedA R) + gap := by
              simp only [gap]
              omega
        _ = Fval + gap := by rw [← hF']
    have hgapH : gap ∈ normalizedH P.M.base := by
      have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedA_mem R) kA
      have hc := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) C.data.returnedZ
      simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).add_mem ha hc
    have hsplitZ : (C.data.sourceValue : ℤ) = (Fval : ℤ) + gap := by
      exact_mod_cast hsplit
    have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
      (returnIdeal (normalizedH P.M.base) A.n) hmin hFmem hgapH hsplitZ).1
    have hk0 : kA = 0 := by
      have hp := (Nat.add_eq_zero_iff.mp hgap0).1
      exact (Nat.mul_eq_zero.mp hp).resolve_right
        (strictLT_normalizedWeight_pos R 0).ne'
    have hrz0 : C.data.returnedZ = 0 := by
      have hp := (Nat.add_eq_zero_iff.mp hgap0).2
      exact (Nat.mul_eq_zero.mp hp).resolve_right
        (strictLT_normalizedWeight_pos R 2).ne'
    have hsourceF : C.data.sourceValue = Fval := by
      simpa [gap, hk0, hrz0] using hsplit
    rw [hsource] at hsourceF
    have hmuGt : sigma < C.data.sourceY := by
      dsimp [Fval] at hsourceF
      by_contra hnot
      have hle := Nat.mul_le_mul_right (normalizedB R) (Nat.le_of_not_gt hnot)
      have hcpos : 0 < (qH R + tau) * normalizedC R :=
        Nat.mul_pos (by omega) (strictLT_normalizedWeight_pos R 2)
      omega
    have hrelC : (qH R + tau) * normalizedC R =
        0 * normalizedA R + (C.data.sourceY - sigma) * normalizedB R := by
      dsimp [Fval] at hsourceF
      have hsplitMu : sigma + (C.data.sourceY - sigma) = C.data.sourceY :=
        Nat.add_sub_of_le (Nat.le_of_lt hmuGt)
      rw [← hsplitMu, Nat.add_mul] at hsourceF
      omega
    have hc3Le := branchB_normalizedC_relation_min R _ _ _ (by omega) hrelC
    have hs3 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    omega
  · have hxd : C.data.returnedX < A.depth := Nat.lt_of_not_ge hdx
    have hbal := branchB_positive_center_pureB_signed_balance R hB hs
      sigma (qH R + tau) ⟨hLT.1, hLT.2.1⟩ hroute
    change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceY : ℤ) - sigma) * normalizedB R) =
      ((C.data.returnedZ + (qH R + tau) : ℕ) : ℤ) * normalizedC R at hbal
    have hbal' : (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceY : ℤ) - sigma) * normalizedB R) =
      ((qH R + tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbal
    by_cases hmu : C.data.sourceY ≤ sigma
    · have hrelA := strictLT_pureB_to_A
        (normalizedA R) (normalizedB R) (normalizedC R)
        A.depth C.data.returnedX C.data.sourceY sigma
        (qH R + tau + C.data.returnedZ)
        (Nat.le_of_lt hxd) hmu hbal'
      have hc1Le := branchB_normalizedA_relation_min R _ _ _
        (Nat.sub_pos_of_lt hxd) hrelA
      have hs1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
      obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
        (branchB_actual_herzog_coordinates R).cross_positive
      omega
    · have hmuGt : sigma < C.data.sourceY := Nat.lt_of_not_ge hmu
      have hrelC := strictLT_pureB_to_C
        (normalizedA R) (normalizedB R) (normalizedC R)
        A.depth C.data.returnedX C.data.sourceY sigma
        (qH R + tau + C.data.returnedZ)
        (Nat.le_of_lt hxd) (Nat.le_of_lt hmuGt) hbal'
      have hc3Le := branchB_normalizedC_relation_min R _ _ _ (by omega) hrelC
      have hs3 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
      have hfloor : vH R - tau ≤ C.data.returnedZ := by omega
      let Xval := (wH R - A.depth) * normalizedA R +
        (sigma + zH R) * normalizedB R
      let kZ := C.data.returnedZ - (vH R - tau)
      let gap := C.data.returnedX * normalizedA R + kZ * normalizedC R
      have hk : vH R - tau + kZ = C.data.returnedZ := Nat.add_sub_of_le hfloor
      have hX := branchB_strictLT_X_value_identity R hB hs sigma tau hLT
      have hX' : A.n + (vH R - tau) * normalizedC R = Xval := by
        simpa [Xval] using hX
      have hsplit : C.data.sourceValue = Xval + gap := by
        rw [hactual, hreturned, ← hk, Nat.add_mul]
        calc
          A.n + (C.data.returnedX * normalizedA R +
              ((vH R - tau) * normalizedC R + kZ * normalizedC R)) =
              (A.n + (vH R - tau) * normalizedC R) + gap := by
                simp only [gap]
                omega
          _ = Xval + gap := by rw [hX']
      have hgapH : gap ∈ normalizedH P.M.base := by
        have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R) C.data.returnedX
        have hc := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedC_mem R) kZ
        simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
          (normalizedH P.M.base).add_mem ha hc
      have hXmem := branchB_strictLT_X_value_mem_returnIdeal R hB hs sigma tau hLT
      change (Xval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hXmem
      have hsplitZ : (C.data.sourceValue : ℤ) = (Xval : ℤ) + gap := by
        exact_mod_cast hsplit
      have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
        (returnIdeal (normalizedH P.M.base) A.n) hmin hXmem hgapH hsplitZ).1
      have hx0 : C.data.returnedX = 0 := by
        have hp := (Nat.add_eq_zero_iff.mp hgap0).1
        exact (Nat.mul_eq_zero.mp hp).resolve_right
          (strictLT_normalizedWeight_pos R 0).ne'
      have hsourceX : C.data.sourceValue = Xval := by
        have hk0 : kZ = 0 := by
          have hp := (Nat.add_eq_zero_iff.mp hgap0).2
          exact (Nat.mul_eq_zero.mp hp).resolve_right
            (strictLT_normalizedWeight_pos R 2).ne'
        simpa [gap, hx0, hk0] using hsplit
      rw [hsource] at hsourceX
      have hbasePos : 0 < wH R - A.depth := by omega
      have hcoefGt : sigma + zH R < C.data.sourceY := by
        dsimp [Xval] at hsourceX
        by_contra hnot
        have hle := Nat.mul_le_mul_right (normalizedB R) (Nat.le_of_not_gt hnot)
        have hapos : 0 < (wH R - A.depth) * normalizedA R :=
          Nat.mul_pos hbasePos (strictLT_normalizedWeight_pos R 0)
        omega
      have hrelA : (wH R - A.depth) * normalizedA R =
          (C.data.sourceY - (sigma + zH R)) * normalizedB R +
            0 * normalizedC R := by
        dsimp [Xval] at hsourceX
        have hsplitMu : sigma + zH R +
            (C.data.sourceY - (sigma + zH R)) = C.data.sourceY :=
          Nat.add_sub_of_le (Nat.le_of_lt hcoefGt)
        rw [← hsplitMu, Nat.add_mul] at hsourceX
        omega
      have hc1Le := branchB_normalizedA_relation_min R _ _ _ hbasePos hrelA
      have hs1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
      obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
        (branchB_actual_herzog_coordinates R).cross_positive
      omega

/-- Complete strict-LT elimination of the pure-B chosen support route. -/
theorem branchB_strictLT_pureB_route_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  obtain ⟨_, hsplit⟩ := branchB_positive_center_pureB_returned_support_split
    R hB hs hroute
  rcases hsplit with _ | _ | _ <;>
    exact strictLT_pureB_core_impossible R hB hs sigma tau hLT hroute

private theorem strictLT_pureC_to_A
    (a b c d x mu base B : ℕ) (hx : x ≤ d) (hmu : mu ≤ base)
    (h : (((d : ℤ) - x) * a) + (((mu : ℤ) - base) * c) = (B : ℤ) * b) :
    (d - x) * a = B * b + (base - mu) * c := by
  have hxCast : ((d - x : ℕ) : ℤ) = d - x := Nat.cast_sub hx
  have hmuCast : ((base - mu : ℕ) : ℤ) = base - mu := Nat.cast_sub hmu
  exact_mod_cast (show ((d - x : ℕ) : ℤ) * a =
      (B : ℤ) * b + ((base - mu : ℕ) : ℤ) * c by
    rw [hxCast, hmuCast]
    nlinarith only [h])

private theorem strictLT_pureC_to_B
    (a b c d x mu base B : ℕ) (hx : x ≤ d) (hmu : base ≤ mu)
    (h : (((d : ℤ) - x) * a) + (((mu : ℤ) - base) * c) = (B : ℤ) * b) :
    B * b = (d - x) * a + (mu - base) * c := by
  have hxCast : ((d - x : ℕ) : ℤ) = d - x := Nat.cast_sub hx
  have hmuCast : ((mu - base : ℕ) : ℤ) = mu - base := Nat.cast_sub hmu
  exact_mod_cast (show (B : ℤ) * b =
      ((d - x : ℕ) : ℤ) * a + ((mu - base : ℕ) : ℤ) * c by
    rw [hxCast, hmuCast]
    nlinarith only [h])

private theorem strictLT_pureC_core_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hrz := (branchB_positive_center_pureC_returned_support_split
    R hB hs hroute).1
  have hsource : C.data.sourceValue = C.data.sourceZ * normalizedC R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.1]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedX * normalizedA R + C.data.returnedY * normalizedB R := by
    rw [C.data.returned_factorization, hrz]
    omega
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  let Fval := sigma * normalizedB R + (qH R + tau) * normalizedC R
  have hF := branchB_strictLT_F_value_identity R hB hs sigma tau
    ⟨hLT.1, hLT.2.1⟩
  have hF' : Fval = A.n + A.depth * normalizedA R := by
    simpa [Fval, Nat.mul_comm] using hF
  have hFmem := strictLT_F_value_mem_returnIdeal R hB hs sigma tau
    ⟨hLT.1, hLT.2.1⟩
  change (Fval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hFmem
  have hmin : (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) := by
    rw [C.data.source_eq]
    exact A.source_minimal
  by_cases hdx : A.depth ≤ C.data.returnedX
  · let kA := C.data.returnedX - A.depth
    let gap := kA * normalizedA R + C.data.returnedY * normalizedB R
    have hk : A.depth + kA = C.data.returnedX := Nat.add_sub_of_le hdx
    have hsplit : C.data.sourceValue = Fval + gap := by
      rw [hactual, hreturned, ← hk, Nat.add_mul]
      calc
        A.n + (A.depth * normalizedA R + kA * normalizedA R +
            C.data.returnedY * normalizedB R) =
            (A.n + A.depth * normalizedA R) + gap := by
              simp only [gap]
              omega
        _ = Fval + gap := by rw [← hF']
    have hgapH : gap ∈ normalizedH P.M.base := by
      have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedA_mem R) kA
      have hb := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) C.data.returnedY
      simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).add_mem ha hb
    have hsplitZ : (C.data.sourceValue : ℤ) = (Fval : ℤ) + gap := by
      exact_mod_cast hsplit
    have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
      (returnIdeal (normalizedH P.M.base) A.n) hmin hFmem hgapH hsplitZ).1
    have hk0 : kA = 0 := by
      have hp := (Nat.add_eq_zero_iff.mp hgap0).1
      exact (Nat.mul_eq_zero.mp hp).resolve_right
        (strictLT_normalizedWeight_pos R 0).ne'
    have hry0 : C.data.returnedY = 0 := by
      have hp := (Nat.add_eq_zero_iff.mp hgap0).2
      exact (Nat.mul_eq_zero.mp hp).resolve_right
        (strictLT_normalizedWeight_pos R 1).ne'
    have hsourceF : C.data.sourceValue = Fval := by
      simpa [gap, hk0, hry0] using hsplit
    rw [hsource] at hsourceF
    have hmuGt : qH R + tau < C.data.sourceZ := by
      dsimp [Fval] at hsourceF
      by_contra hnot
      have hle := Nat.mul_le_mul_right (normalizedC R) (Nat.le_of_not_gt hnot)
      have hbpos : 0 < sigma * normalizedB R :=
        Nat.mul_pos (by omega) (strictLT_normalizedWeight_pos R 1)
      omega
    have hrelB : sigma * normalizedB R =
        0 * normalizedA R + (C.data.sourceZ - (qH R + tau)) * normalizedC R := by
      dsimp [Fval] at hsourceF
      have hsplitMu : qH R + tau +
          (C.data.sourceZ - (qH R + tau)) = C.data.sourceZ :=
        Nat.add_sub_of_le (Nat.le_of_lt hmuGt)
      rw [← hsplitMu, Nat.add_mul] at hsourceF
      omega
    have hc2Le := branchB_normalizedB_relation_min R _ _ _ (by omega) hrelB
    have hs2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    omega
  · have hxd : C.data.returnedX < A.depth := Nat.lt_of_not_ge hdx
    have hbal := branchB_positive_center_pureC_signed_balance R hB hs
      sigma (qH R + tau) ⟨hLT.1, hLT.2.1⟩ hroute
    change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceZ : ℤ) - (qH R + tau)) * normalizedC R) =
      ((C.data.returnedY + sigma : ℕ) : ℤ) * normalizedB R at hbal
    have hbal' : (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceZ : ℤ) - (qH R + tau)) * normalizedC R) =
      ((sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbal
    by_cases hmu : C.data.sourceZ ≤ qH R + tau
    · have hrelA := strictLT_pureC_to_A
        (normalizedA R) (normalizedB R) (normalizedC R)
        A.depth C.data.returnedX C.data.sourceZ (qH R + tau)
        (sigma + C.data.returnedY)
        (Nat.le_of_lt hxd) hmu hbal'
      have hc1Le := branchB_normalizedA_relation_min R _ _ _
        (Nat.sub_pos_of_lt hxd) hrelA
      have hs1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
      obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
        (branchB_actual_herzog_coordinates R).cross_positive
      omega
    · have hmuGt : qH R + tau < C.data.sourceZ := Nat.lt_of_not_ge hmu
      have hrelB := strictLT_pureC_to_B
        (normalizedA R) (normalizedB R) (normalizedC R)
        A.depth C.data.returnedX C.data.sourceZ (qH R + tau)
        (sigma + C.data.returnedY)
        (Nat.le_of_lt hxd) (Nat.le_of_lt hmuGt) hbal'
      have hc2Le := branchB_normalizedB_relation_min R _ _ _ (by omega) hrelB
      have hs2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
      have hfloor : pH R - sigma ≤ C.data.returnedY := by omega
      let Yval := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        tau * normalizedC R
      let kY := C.data.returnedY - (pH R - sigma)
      let gap := C.data.returnedX * normalizedA R + kY * normalizedB R
      have hk : pH R - sigma + kY = C.data.returnedY := Nat.add_sub_of_le hfloor
      have hY := branchB_strictLT_Y_value_identity R hB hs sigma tau hLT
      have hY' : A.n + (pH R - sigma) * normalizedB R = Yval := by
        simpa [Yval] using hY
      have hsplit : C.data.sourceValue = Yval + gap := by
        rw [hactual, hreturned, ← hk, Nat.add_mul]
        calc
          A.n + (C.data.returnedX * normalizedA R +
              ((pH R - sigma) * normalizedB R + kY * normalizedB R)) =
              (A.n + (pH R - sigma) * normalizedB R) + gap := by
                simp only [gap]
                omega
          _ = Yval + gap := by rw [hY']
      have hgapH : gap ∈ normalizedH P.M.base := by
        have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R) C.data.returnedX
        have hb := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedB_mem R) kY
        simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
          (normalizedH P.M.base).add_mem ha hb
      have hYmem := branchB_strictLT_Y_value_mem_returnIdeal R hB hs sigma tau hLT
      change (Yval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hYmem
      have hsplitZ : (C.data.sourceValue : ℤ) = (Yval : ℤ) + gap := by
        exact_mod_cast hsplit
      have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
        (returnIdeal (normalizedH P.M.base) A.n) hmin hYmem hgapH hsplitZ).1
      have hx0 : C.data.returnedX = 0 := by
        have hp := (Nat.add_eq_zero_iff.mp hgap0).1
        exact (Nat.mul_eq_zero.mp hp).resolve_right
          (strictLT_normalizedWeight_pos R 0).ne'
      have hsourceY : C.data.sourceValue = Yval := by
        have hk0 : kY = 0 := by
          have hp := (Nat.add_eq_zero_iff.mp hgap0).2
          exact (Nat.mul_eq_zero.mp hp).resolve_right
            (strictLT_normalizedWeight_pos R 1).ne'
        simpa [gap, hx0, hk0] using hsplit
      rw [hsource] at hsourceY
      have hbasePos : 0 < L5A2B4AR4R2B.c1 R - A.depth := by
        have hs1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
        obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
          (branchB_actual_herzog_coordinates R).cross_positive
        omega
      have hcoefGt : tau < C.data.sourceZ := by
        dsimp [Yval] at hsourceY
        by_contra hnot
        have hle := Nat.mul_le_mul_right (normalizedC R) (Nat.le_of_not_gt hnot)
        have hapos : 0 <
            (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R :=
          Nat.mul_pos hbasePos (strictLT_normalizedWeight_pos R 0)
        omega
      have hrelA : (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R =
          0 * normalizedB R + (C.data.sourceZ - tau) * normalizedC R := by
        dsimp [Yval] at hsourceY
        have hsplitMu : tau + (C.data.sourceZ - tau) = C.data.sourceZ :=
          Nat.add_sub_of_le (Nat.le_of_lt hcoefGt)
        rw [← hsplitMu, Nat.add_mul] at hsourceY
        omega
      have hc1Le := branchB_normalizedA_relation_min R _ _ _ hbasePos hrelA
      omega

/-- Complete strict-LT elimination of the pure-C chosen support route. -/
theorem branchB_strictLT_pureC_route_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  obtain ⟨_, hsplit⟩ := branchB_positive_center_pureC_returned_support_split
    R hB hs hroute
  rcases hsplit with _ | _ | _ <;>
    exact strictLT_pureC_core_impossible R hB hs sigma tau hLT hroute

/-- Every actual strict-LT source has one of the complete F/X/Y packets. -/
theorem branchB_strictLT_actual_family_exhaustive
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R) :
    StrictLTActualFPacket R hB hs sigma tau ∨
      StrictLTActualXPacket R hB hs sigma tau ∨
      StrictLTActualYPacket R hB hs sigma tau := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  obtain ⟨route, hroute⟩ := branchB_selected_return_source_support_route R hB hs
  change ActualSourceSupportRoute.Matches route
    C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  cases route with
  | bc =>
      exact Or.inl (branchB_strictLT_bc_F_packet R hB hs sigma tau
        ⟨hLT.1, hLT.2.1⟩ hroute)
  | a =>
      exact False.elim
        (branchB_strictLT_a_route_impossible R hB hs sigma tau hLT hroute)
  | ab =>
      exact Or.inr (Or.inl
        (branchB_strictLT_ab_X_packet R hB hs sigma tau hLT hroute))
  | ac =>
      exact Or.inr (Or.inr
        (branchB_strictLT_ac_Y_packet R hB hs sigma tau hLT hroute))
  | pureB =>
      exact False.elim
        (branchB_strictLT_pureB_route_impossible R hB hs sigma tau hLT hroute)
  | pureC =>
      exact False.elim
        (branchB_strictLT_pureC_route_impossible R hB hs sigma tau hLT hroute)

/-- Value-level F/X/Y trichotomy projected from the complete strict-LT packet
classifier. -/
theorem branchB_strictLT_actual_source_value_trichotomy
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
        1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
        A.depth < wH R) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceValue =
        sigma * normalizedB R + (qH R + tau) * normalizedC R ∨
      C.data.sourceValue =
        (wH R - A.depth) * normalizedA R +
          (sigma + zH R) * normalizedB R ∨
      C.data.sourceValue =
        (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
          tau * normalizedC R := by
  rcases branchB_strictLT_actual_family_exhaustive
      R hB hs sigma tau hLT with hF | hX | hY
  · exact Or.inl hF.1
  · exact Or.inr (Or.inl hX.1)
  · exact Or.inr (Or.inr hY.1)

end NS25Lean.L5A2B4AR5B
