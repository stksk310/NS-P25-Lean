import NS25Lean.P2BranchBStrictArmClassifier

set_option linter.style.header false

noncomputable section
namespace NS25Lean

namespace RelativeIdeal

/-- A minimal relative-ideal generator cannot differ from another ideal
member by a nonzero semigroup element. -/
theorem minimalGenerator_eq_of_mem_add {H : NumericalSemigroup}
    (I : RelativeIdeal H) {s x : ℤ} {h : ℕ}
    (hs : I.IsMinimalGenerator s) (hx : x ∈ I) (hh : h ∈ H)
    (heq : s = x + h) : h = 0 ∧ s = x := by
  have hh0 : h = 0 := by
    by_contra hne
    apply hs.2 h hh hne
    have : s - (h : ℤ) = x := by rw [heq]; ring
    simpa [this] using hx
  subst h
  simpa using heq

end RelativeIdeal

namespace L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

private theorem branchB_strictArm_normalizedWeight_pos
    (R : SectorBCriticalRoleBranchB P) (k : Fin 3) :
    0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex k) := by
  have hs := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex k)
  have hw := L2B.weights_positive P.M.base (R.reindex k)
  nlinarith

private theorem branchB_strictArm_relation_of_signed_below
    (a b c A B C i : ℕ) (hBi : B ≤ i)
    (h : (A : ℤ) * a + ((B : ℤ) - i) * b = (C : ℤ) * c) :
    A * a = (i - B) * b + C * c := by
  have hcast : ((i - B : ℕ) : ℤ) = i - B := Nat.cast_sub hBi
  exact_mod_cast (show (A : ℤ) * a = ((i - B : ℕ) : ℤ) * b + C * c by
    rw [hcast]
    nlinarith only [h])

private theorem branchB_strictArm_relation_of_signed_above
    (a b c A B C i : ℕ) (hiB : i ≤ B)
    (h : (A : ℤ) * a + ((B : ℤ) - i) * b = (C : ℤ) * c) :
    C * c = A * a + (B - i) * b := by
  have hcast : ((B - i : ℕ) : ℤ) = B - i := Nat.cast_sub hiB
  exact_mod_cast (show (C : ℤ) * c = (A : ℤ) * a + ((B - i : ℕ) : ℤ) * b by
    rw [hcast]
    nlinarith only [h])

/-- On an actual strict-RB `ab` route, the returned `c` coefficient reaches
the repaired X floor. -/
theorem branchB_strictRB_ab_returnedZ_floor
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    qH R ≤ tau + C.data.returnedZ := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change qH R ≤ tau + C.data.returnedZ
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  rcases hRB with ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
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
          (((C.data.sourceY : ℤ) - (pH R + sigma)) * normalizedB R) =
        ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
    rw [hroute'.2.2, hrx, hry, hi, hj] at hbalance
    push_cast at hbalance ⊢
    nlinarith only [hbalance]
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_strictArm_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_strictArm_normalizedWeight_pos R 2
  by_cases hmu : pH R + sigma < C.data.sourceY
  · have hmuLe : pH R + sigma ≤ C.data.sourceY := Nat.le_of_lt hmu
    have hrelC : (tau + C.data.returnedZ) * normalizedC R =
        (C.data.sourceX + A.depth) * normalizedA R +
          (C.data.sourceY - (pH R + sigma)) * normalizedB R := by
      exact branchB_strictArm_relation_of_signed_above
        (normalizedA R) (normalizedB R) (normalizedC R)
        (C.data.sourceX + A.depth) C.data.sourceY
        (tau + C.data.returnedZ) (pH R + sigma) hmuLe hrelationZ
    have hc3Le := branchB_normalizedC_relation_min R _ _ _ (by omega) hrelC
    have hqLeC3 : qH R ≤ L5A2B4AR4R2B.c3 R := by
      rw [hs3]
      exact Nat.le_add_right _ _
    exact hqLeC3.trans hc3Le
  · have hmuLe : C.data.sourceY ≤ pH R + sigma := Nat.le_of_not_gt hmu
    have hrelA : (C.data.sourceX + A.depth) * normalizedA R =
        (pH R + sigma - C.data.sourceY) * normalizedB R +
          (tau + C.data.returnedZ) * normalizedC R := by
      exact branchB_strictArm_relation_of_signed_below
        (normalizedA R) (normalizedB R) (normalizedC R)
        (C.data.sourceX + A.depth) C.data.sourceY
        (tau + C.data.returnedZ) (pH R + sigma) hmuLe hrelationZ
    have hc1Le := branchB_normalizedA_relation_min R _ _ _ (by omega) hrelA
    by_contra hfloor
    have hsumLt : tau + C.data.returnedZ < qH R := Nat.lt_of_not_ge hfloor
    have hleftA : L5A2B4AR4R2B.c1 R ≤ C.data.sourceX + A.depth := hc1Le
    have hrelAZ : ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R =
        ((pH R + sigma - C.data.sourceY : ℕ) : ℤ) * normalizedB R +
          ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
      exact_mod_cast hrelA
    have hdiffZ :
        (((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
            normalizedA R) +
          (((qH R - (tau + C.data.returnedZ) : ℕ) : ℤ) * normalizedC R) =
          ((sigma : ℤ) - C.data.sourceY) * normalizedB R := by
      rw [Nat.cast_sub hleftA, Nat.cast_sub (Nat.le_of_lt hsumLt)]
      push_cast only [Nat.cast_add, Nat.cast_mul]
      have hrel1Z : (L5A2B4AR4R2B.c1 R : ℤ) * normalizedA R =
          (pH R : ℤ) * normalizedB R + (qH R : ℤ) * normalizedC R := by
        exact_mod_cast hrel1
      have hmuCast : ((pH R + sigma - C.data.sourceY : ℕ) : ℤ) =
          (pH R : ℤ) + sigma - C.data.sourceY := by
        rw [Nat.cast_sub hmuLe]
        push_cast
        rfl
      rw [hmuCast] at hrelAZ
      push_cast only [Nat.cast_add, Nat.cast_mul] at hrelAZ hrel1Z ⊢
      linear_combination hrelAZ - hrel1Z
    have hpositive : 0 <
          (qH R - (tau + C.data.returnedZ)) * normalizedC R :=
      Nat.mul_pos (Nat.sub_pos_of_lt hsumLt) hc
    by_cases hmusigma : C.data.sourceY ≤ sigma
    · have hdiffNat :
          (C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R) * normalizedA R +
              (qH R - (tau + C.data.returnedZ)) * normalizedC R =
            (sigma - C.data.sourceY) * normalizedB R := by
        apply Int.ofNat_inj.mp
        push_cast only [Nat.cast_mul, Nat.cast_add]
        rw [Nat.cast_sub hmusigma]
        exact hdiffZ
      have hcoefPos : 0 < sigma - C.data.sourceY := by
        by_contra hn
        have hzcoef : sigma - C.data.sourceY = 0 := Nat.eq_zero_of_not_pos hn
        have hlhsPos : 0 <
            (C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R) * normalizedA R +
              (qH R - (tau + C.data.returnedZ)) * normalizedC R :=
          lt_of_lt_of_le hpositive (Nat.le_add_left _ _)
        rw [hdiffNat, hzcoef, zero_mul] at hlhsPos
        exact (Nat.lt_irrefl 0 hlhsPos)
      have hc2Le := branchB_normalizedB_relation_min R
        (sigma - C.data.sourceY)
        (C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R)
        (qH R - (tau + C.data.returnedZ)) hcoefPos hdiffNat.symm
      have hcoefLe : sigma - C.data.sourceY ≤ sigma := Nat.sub_le _ _
      have hc2LeSigma : L5A2B4AR4R2B.c2 R ≤ sigma := hc2Le.trans hcoefLe
      have hsigmaLtC2 : sigma < L5A2B4AR4R2B.c2 R := by
        rw [hs2]
        exact hsigmaLt.trans_le (Nat.le_add_left _ _)
      exact (not_lt_of_ge hc2LeSigma) hsigmaLtC2
    · have hsigmaMu : sigma < C.data.sourceY := Nat.lt_of_not_ge hmusigma
      have hleftNonneg : 0 ≤
          ((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
            normalizedA R := by positivity
      have hpositiveZ : 0 <
          ((qH R - (tau + C.data.returnedZ) : ℕ) : ℤ) * normalizedC R := by
        exact_mod_cast hpositive
      have hrightNeg : ((sigma : ℤ) - C.data.sourceY) * normalizedB R < 0 := by
        have hsigmaZ : (sigma : ℤ) < (C.data.sourceY : ℤ) := by
          exact_mod_cast hsigmaMu
        have : (sigma : ℤ) - (C.data.sourceY : ℤ) < 0 := sub_neg.mpr hsigmaZ
        have hbZ : (0 : ℤ) < normalizedB R := by exact_mod_cast hb
        exact mul_neg_of_neg_of_pos this hbZ
      have hlhsPos : 0 <
          (((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
              normalizedA R) +
            (((qH R - (tau + C.data.returnedZ) : ℕ) : ℤ) * normalizedC R) :=
        add_pos_of_nonneg_of_pos hleftNonneg hpositiveZ
      rw [hdiffZ] at hlhsPos
      exact (not_lt_of_ge (le_of_lt hrightNeg)) hlhsPos

/-- The repaired strict-RB X value is an actual member of the same individual
return ideal, rather than merely a symbolic candidate. -/
theorem branchB_strictRB_X_value_mem_returnIdeal
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    (((L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
      sigma * normalizedB R : ℕ) : ℤ) ∈
        returnIdeal (normalizedH P.M.base) A.n := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  let Xval := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
    sigma * normalizedB R
  have hX := branchB_strictRB_X_value_identity R hB hs sigma tau hRB
  have hX' : A.n + (qH R - tau) * normalizedC R = Xval := by
    simpa only [Xval, Nat.add_comm] using hX
  have hsourceH : Xval ∈ normalizedH P.M.base := by
    have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedA_mem R) (L5A2B4AR4R2B.c1 R - A.depth)
    have hb := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedB_mem R) sigma
    simpa [Xval, nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).add_mem ha hb
  have hreturnedH : (qH R - tau) * normalizedC R ∈ normalizedH P.M.base := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) (qH R - tau)
  change (Xval : ℤ) ∈ (normalizedH P.M.base).asRelativeIdeal ∧
    (Xval : ℤ) - (A.n : ℕ) ∈ (normalizedH P.M.base).asRelativeIdeal
  constructor
  · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨Xval, hsourceH, rfl⟩
  · have hdiff : (Xval : ℤ) - (A.n : ℕ) =
        ((qH R - tau) * normalizedC R : ℕ) := by
      have hXZ : (Xval : ℤ) =
          (A.n : ℤ) + ((qH R - tau) * normalizedC R : ℕ) := by
        exact_mod_cast hX'.symm
      rw [hXZ]
      ring
    rw [hdiff, NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨(qH R - tau) * normalizedC R, hreturnedH, rfl⟩

/-- Minimality collapses the actual strict-RB `ab` source onto the repaired X
candidate value. -/
theorem branchB_strictRB_ab_source_value_eq_X
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceValue =
      (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        sigma * normalizedB R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  let Xval := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
    sigma * normalizedB R
  have hfloor := branchB_strictRB_ab_returnedZ_floor R hB hs sigma tau hRB hroute
  change qH R ≤ tau + C.data.returnedZ at hfloor
  have hremLe : qH R - tau ≤ C.data.returnedZ := by omega
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
  have hX := branchB_strictRB_X_value_identity R hB hs sigma tau hRB
  have hX' : A.n + (qH R - tau) * normalizedC R = Xval := by
    simpa only [Xval, Nat.add_comm] using hX
  let k := C.data.returnedZ - (qH R - tau)
  have hkadd : qH R - tau + k = C.data.returnedZ := by
    exact Nat.add_sub_of_le hremLe
  have hsplit : C.data.sourceValue = Xval + k * normalizedC R := by
    rw [hactual, hreturned, ← hkadd, Nat.add_mul, ← Nat.add_assoc, hX']
  have hmin : (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) := by
    rw [C.data.source_eq]
    exact A.source_minimal
  have hXmem := branchB_strictRB_X_value_mem_returnIdeal R hB hs sigma tau hRB
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
  have hk0 : k = 0 := by
    exact (Nat.mul_eq_zero.mp hgap0).resolve_right
      (branchB_strictArm_normalizedWeight_pos R 2).ne'
  change C.data.sourceValue = Xval
  simpa [hk0] using hsplit

private theorem branchB_strictArm_lShape_coordinate_eq_of_exact
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

/-- Full numeric and canonical X packet for the actual strict-RB `ab` route. -/
theorem branchB_strictRB_ab_X_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceValue =
        (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
          sigma * normalizedB R ∧
      C.data.returnedValue = (qH R - tau) * normalizedC R ∧
      C.source_coordinate.i = sigma ∧ C.source_coordinate.j = 0 ∧
      C.source_coordinate.level =
        ((L5A2B4AR4R2B.c1 R - A.depth : ℕ) : ℤ) ∧
      C.returned_coordinate.i = 0 ∧
      C.returned_coordinate.j = ((qH R - tau : ℕ) : ℤ) ∧
      C.returned_coordinate.level = 0 := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  rcases hRB with ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hRB' : A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R := ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hsource := branchB_strictRB_ab_source_value_eq_X R hB hs sigma tau hRB' hroute
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hX := branchB_strictRB_X_value_identity R hB hs sigma tau hRB'
  have hX' : A.n + (qH R - tau) * normalizedC R =
      (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        sigma * normalizedB R := by
    simpa only [Nat.add_comm] using hX
  have hreturned : C.data.returnedValue = (qH R - tau) * normalizedC R := by
    have heq : A.n + C.data.returnedValue =
        A.n + (qH R - tau) * normalizedC R := by
      calc
        A.n + C.data.returnedValue = C.data.sourceValue := hactual.symm
        _ = (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
            sigma * normalizedB R := hsource
        _ = A.n + (qH R - tau) * normalizedC R := hX'.symm
    exact Nat.add_left_cancel heq
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  have hsShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      (sigma : ℤ) 0 := by
    unfold L5A2B.InLShape
    constructor
    · exact_mod_cast Nat.zero_le sigma
    constructor
    · norm_num
    constructor
    · exact_mod_cast hsigmaLt.trans_le (Nat.le_add_left _ _)
    constructor
    · exact_mod_cast Nat.add_pos_left hq (vH R)
    · exact Or.inr (by exact_mod_cast hq)
  have hrShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      0 ((qH R - tau : ℕ) : ℤ) := by
    unfold L5A2B.InLShape
    constructor
    · norm_num
    constructor
    · exact_mod_cast Nat.zero_le (qH R - tau)
    constructor
    · exact_mod_cast Nat.add_pos_left hp (zH R)
    constructor
    · exact_mod_cast (show qH R - tau < qH R + vH R by omega)
    · exact Or.inl (by exact_mod_cast hp)
  have hsExact : (C.data.sourceValue : ℤ) =
      ((L5A2B4AR4R2B.c1 R - A.depth : ℕ) : ℤ) * normalizedA R +
        (sigma : ℤ) * normalizedB R + 0 * normalizedC R := by
    have hcast : (C.data.sourceValue : ℤ) =
        (((L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
          sigma * normalizedB R : ℕ) : ℤ) := by exact_mod_cast hsource
    push_cast at hcast
    simpa using hcast
  have hrExact : (C.data.returnedValue : ℤ) =
      0 * normalizedA R + 0 * normalizedB R +
        ((qH R - tau : ℕ) : ℤ) * normalizedC R := by
    have hcast : (C.data.returnedValue : ℤ) =
        (((qH R - tau) * normalizedC R : ℕ) : ℤ) := by
      exact_mod_cast hreturned
    push_cast at hcast
    simpa using hcast
  obtain ⟨hsi, hsj, hsl⟩ := branchB_strictArm_lShape_coordinate_eq_of_exact R
    C.source_coordinate (sigma : ℤ) 0
      ((L5A2B4AR4R2B.c1 R - A.depth : ℕ) : ℤ) hsShape hsExact
  obtain ⟨hri, hrj, hrl⟩ := branchB_strictArm_lShape_coordinate_eq_of_exact R
    C.returned_coordinate 0 ((qH R - tau : ℕ) : ℤ) 0 hrShape hrExact
  exact ⟨hsource, hreturned, hsi, hsj, hsl, hri, hrj, hrl⟩

/-- On an actual strict-RB `ac` route, the returned `b` coefficient reaches
the repaired Y floor. -/
theorem branchB_strictRB_ac_returnedY_floor
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    zH R ≤ sigma + C.data.returnedY := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change zH R ≤ sigma + C.data.returnedY
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  rcases hRB with ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
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
      (((pH R + sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R) =
        (((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R) +
          (((C.data.sourceZ : ℤ) - tau) * normalizedC R) := by
    rw [hroute'.2.1, hrx, hrz, hi, hj] at hbalance
    push_cast at hbalance ⊢
    nlinarith only [hbalance]
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_strictArm_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_strictArm_normalizedWeight_pos R 2
  by_cases htauSource : tau ≤ C.data.sourceZ
  · have hrelB : (pH R + sigma + C.data.returnedY) * normalizedB R =
        (C.data.sourceX + A.depth) * normalizedA R +
          (C.data.sourceZ - tau) * normalizedC R := by
      have hcast : ((C.data.sourceZ - tau : ℕ) : ℤ) =
          C.data.sourceZ - tau := Nat.cast_sub htauSource
      exact_mod_cast (show ((pH R + sigma + C.data.returnedY : ℕ) : ℤ) *
          normalizedB R =
          ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R +
            ((C.data.sourceZ - tau : ℕ) : ℤ) * normalizedC R by
        rw [hcast]
        exact hrelationZ)
    have hc2Le := branchB_normalizedB_relation_min R _ _ _ (by omega) hrelB
    rw [hs2] at hc2Le
    omega
  · have hsourceLt : C.data.sourceZ < tau := Nat.lt_of_not_ge htauSource
    have hrelA : (C.data.sourceX + A.depth) * normalizedA R =
        (pH R + sigma + C.data.returnedY) * normalizedB R +
          (tau - C.data.sourceZ) * normalizedC R := by
      have hcast : ((tau - C.data.sourceZ : ℕ) : ℤ) =
          tau - C.data.sourceZ := Nat.cast_sub (Nat.le_of_lt hsourceLt)
      exact_mod_cast (show ((C.data.sourceX + A.depth : ℕ) : ℤ) *
          normalizedA R =
          ((pH R + sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R +
            ((tau - C.data.sourceZ : ℕ) : ℤ) * normalizedC R by
        rw [hcast]
        nlinarith only [hrelationZ])
    have hc1Le := branchB_normalizedA_relation_min R _ _ _ (by omega) hrelA
    by_contra hfloor
    have hsumLt : sigma + C.data.returnedY < zH R := Nat.lt_of_not_ge hfloor
    have hKpos : 0 < tau - C.data.sourceZ := Nat.sub_pos_of_lt hsourceLt
    have hKlt : tau - C.data.sourceZ < qH R :=
      (Nat.sub_le tau C.data.sourceZ).trans_lt htauLt
    have hrelAZ : ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R =
        ((pH R + sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R +
          ((tau - C.data.sourceZ : ℕ) : ℤ) * normalizedC R := by
      exact_mod_cast hrelA
    have hrel1Z : (L5A2B4AR4R2B.c1 R : ℤ) * normalizedA R =
        (pH R : ℤ) * normalizedB R + (qH R : ℤ) * normalizedC R := by
      exact_mod_cast hrel1
    have hdiffZ :
        (((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) *
            normalizedA R) +
          (((qH R - (tau - C.data.sourceZ) : ℕ) : ℤ) * normalizedC R) =
          ((sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R := by
      rw [Nat.cast_sub hc1Le, Nat.cast_sub (Nat.le_of_lt hKlt)]
      push_cast only [Nat.cast_add, Nat.cast_mul] at hrelAZ hrel1Z ⊢
      linear_combination hrelAZ - hrel1Z
    have hdiffNat :
        (C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R) * normalizedA R +
          (qH R - (tau - C.data.sourceZ)) * normalizedC R =
          (sigma + C.data.returnedY) * normalizedB R := by
      exact_mod_cast hdiffZ
    have hcoefPos : 0 < sigma + C.data.returnedY := by omega
    have hc2Le := branchB_normalizedB_relation_min R _ _ _ hcoefPos hdiffNat.symm
    have hc2LeZ : L5A2B4AR4R2B.c2 R ≤ zH R := hc2Le.trans (Nat.le_of_lt hsumLt)
    have hzLtC2 : zH R < L5A2B4AR4R2B.c2 R := by
      rw [hs2]
      omega
    exact (not_lt_of_ge hc2LeZ) hzLtC2

/-- The repaired strict-RB Y value is an actual member of the same individual
return ideal. -/
theorem branchB_strictRB_Y_value_mem_returnIdeal
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    (((uH R - A.depth) * normalizedA R +
      (tau + vH R) * normalizedC R : ℕ) : ℤ) ∈
        returnIdeal (normalizedH P.M.base) A.n := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  let Yval := (uH R - A.depth) * normalizedA R +
    (tau + vH R) * normalizedC R
  have hY := branchB_strictRB_Y_value_identity R hB hs sigma tau hRB
  have hY' : A.n + (zH R - sigma) * normalizedB R = Yval := by
    simpa only [Yval, Nat.add_comm] using hY
  have hsourceH : Yval ∈ normalizedH P.M.base := by
    have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedA_mem R) (uH R - A.depth)
    have hc := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
      (branchB_actual_normalizedC_mem R) (tau + vH R)
    simpa [Yval, nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).add_mem ha hc
  have hreturnedH : (zH R - sigma) * normalizedB R ∈ normalizedH P.M.base := by
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) (zH R - sigma)
  change (Yval : ℤ) ∈ (normalizedH P.M.base).asRelativeIdeal ∧
    (Yval : ℤ) - (A.n : ℕ) ∈ (normalizedH P.M.base).asRelativeIdeal
  constructor
  · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨Yval, hsourceH, rfl⟩
  · have hdiff : (Yval : ℤ) - (A.n : ℕ) =
        ((zH R - sigma) * normalizedB R : ℕ) := by
      have hYZ : (Yval : ℤ) =
          (A.n : ℤ) + ((zH R - sigma) * normalizedB R : ℕ) := by
        exact_mod_cast hY'.symm
      rw [hYZ]
      ring
    rw [hdiff, NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨(zH R - sigma) * normalizedB R, hreturnedH, rfl⟩

/-- Minimality collapses the actual strict-RB `ac` source onto the repaired Y
candidate value. -/
theorem branchB_strictRB_ac_source_value_eq_Y
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceValue =
      (uH R - A.depth) * normalizedA R +
        (tau + vH R) * normalizedC R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  let Yval := (uH R - A.depth) * normalizedA R +
    (tau + vH R) * normalizedC R
  have hfloor := branchB_strictRB_ac_returnedY_floor R hB hs sigma tau hRB hroute
  change zH R ≤ sigma + C.data.returnedY at hfloor
  have hremLe : zH R - sigma ≤ C.data.returnedY := by omega
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
  have hY := branchB_strictRB_Y_value_identity R hB hs sigma tau hRB
  have hY' : A.n + (zH R - sigma) * normalizedB R = Yval := by
    simpa only [Yval, Nat.add_comm] using hY
  let k := C.data.returnedY - (zH R - sigma)
  have hkadd : zH R - sigma + k = C.data.returnedY := Nat.add_sub_of_le hremLe
  have hsplit : C.data.sourceValue = Yval + k * normalizedB R := by
    rw [hactual, hreturned, ← hkadd, Nat.add_mul, ← Nat.add_assoc, hY']
  have hmin : (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) := by
    rw [C.data.source_eq]
    exact A.source_minimal
  have hYmem := branchB_strictRB_Y_value_mem_returnIdeal R hB hs sigma tau hRB
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
    (branchB_strictArm_normalizedWeight_pos R 1).ne'
  change C.data.sourceValue = Yval
  simpa [hk0] using hsplit

/-- Full numeric and canonical Y packet for the actual strict-RB `ac` route. -/
theorem branchB_strictRB_ac_Y_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceValue =
        (uH R - A.depth) * normalizedA R +
          (tau + vH R) * normalizedC R ∧
      C.data.returnedValue = (zH R - sigma) * normalizedB R ∧
      C.source_coordinate.i = 0 ∧ C.source_coordinate.j = tau + vH R ∧
      C.source_coordinate.level = ((uH R - A.depth : ℕ) : ℤ) ∧
      C.returned_coordinate.i = ((zH R - sigma : ℕ) : ℤ) ∧
      C.returned_coordinate.j = 0 ∧ C.returned_coordinate.level = 0 := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  rcases hRB with ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hRB' : A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R := ⟨hi, hj, hsigma, hsigmaLt, htau, htauLt, hdepth⟩
  have hsource := branchB_strictRB_ac_source_value_eq_Y R hB hs sigma tau hRB' hroute
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hY := branchB_strictRB_Y_value_identity R hB hs sigma tau hRB'
  have hY' : A.n + (zH R - sigma) * normalizedB R =
      (uH R - A.depth) * normalizedA R +
        (tau + vH R) * normalizedC R := by simpa only [Nat.add_comm] using hY
  have hreturned : C.data.returnedValue = (zH R - sigma) * normalizedB R := by
    have heq : A.n + C.data.returnedValue =
        A.n + (zH R - sigma) * normalizedB R := by
      calc
        A.n + C.data.returnedValue = C.data.sourceValue := hactual.symm
        _ = (uH R - A.depth) * normalizedA R +
            (tau + vH R) * normalizedC R := hsource
        _ = A.n + (zH R - sigma) * normalizedB R := hY'.symm
    exact Nat.add_left_cancel heq
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  have hsShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      0 ((tau + vH R : ℕ) : ℤ) := by
    unfold L5A2B.InLShape
    refine ⟨by norm_num, by positivity, ?_, ?_, Or.inl ?_⟩
    · exact_mod_cast Nat.add_pos_left hp (zH R)
    · exact_mod_cast Nat.add_lt_add_right htauLt (vH R)
    · exact_mod_cast hp
  have hrShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      ((zH R - sigma : ℕ) : ℤ) 0 := by
    unfold L5A2B.InLShape
    refine ⟨by exact_mod_cast Nat.zero_le (zH R - sigma), by norm_num, ?_, ?_, Or.inr ?_⟩
    · exact_mod_cast (show zH R - sigma < pH R + zH R by omega)
    · exact_mod_cast Nat.add_pos_left hq (vH R)
    · exact_mod_cast hq
  have hsExact : (C.data.sourceValue : ℤ) =
      ((uH R - A.depth : ℕ) : ℤ) * normalizedA R +
        0 * normalizedB R + ((tau + vH R : ℕ) : ℤ) * normalizedC R := by
    have hcast : (C.data.sourceValue : ℤ) =
        (((uH R - A.depth) * normalizedA R +
          (tau + vH R) * normalizedC R : ℕ) : ℤ) := by exact_mod_cast hsource
    push_cast at hcast
    simpa using hcast
  have hrExact : (C.data.returnedValue : ℤ) =
      0 * normalizedA R + ((zH R - sigma : ℕ) : ℤ) * normalizedB R +
        0 * normalizedC R := by
    have hcast : (C.data.returnedValue : ℤ) =
        (((zH R - sigma) * normalizedB R : ℕ) : ℤ) := by exact_mod_cast hreturned
    push_cast at hcast
    simpa using hcast
  obtain ⟨hsi, hsj, hsl⟩ := branchB_strictArm_lShape_coordinate_eq_of_exact R
    C.source_coordinate 0 ((tau + vH R : ℕ) : ℤ)
      ((uH R - A.depth : ℕ) : ℤ) hsShape hsExact
  obtain ⟨hri, hrj, hrl⟩ := branchB_strictArm_lShape_coordinate_eq_of_exact R
    C.returned_coordinate ((zH R - sigma : ℕ) : ℤ) 0 0 hrShape hrExact
  exact ⟨hsource, hreturned, hsi, hsj, hsl, hri, hrj, hrl⟩

/-- On the residual strict-RB `a` route, one of the two genuine arm
candidate return coefficients has already been reached. -/
theorem branchB_strictRB_a_return_floor_disjunction
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    qH R - tau ≤ C.data.returnedZ ∨
      zH R - sigma ≤ C.data.returnedY := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hcorner := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hcorner.1.resolve_left hroute'.1
  have hbalance := (branchB_selected_return_source_balance_packet R hB hs).2.1
  have hcritZ : ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R =
      ((pH R + sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R +
        ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
    rw [hroute'.2.1, hroute'.2.2, hrx, hRB.1, hRB.2.1] at hbalance
    push_cast at hbalance ⊢
    linear_combination hbalance
  have hcrit : (C.data.sourceX + A.depth) * normalizedA R =
      (pH R + sigma + C.data.returnedY) * normalizedB R +
        (tau + C.data.returnedZ) * normalizedC R := by
    exact_mod_cast hcritZ
  have hc1Le := branchB_normalizedA_relation_min R _ _ _
    (show 0 < C.data.sourceX + A.depth by omega) hcrit
  by_cases hzfloor : qH R - tau ≤ C.data.returnedZ
  · exact Or.inl hzfloor
  · right
    change zH R - sigma ≤ C.data.returnedY
    have hsumLt : tau + C.data.returnedZ < qH R := by omega
    have hrel1 := (branchB_actual_herzog_coordinates R).normalized_relations.1
    have hrel1Z : (L5A2B4AR4R2B.c1 R : ℤ) * normalizedA R =
        (pH R : ℤ) * normalizedB R + (qH R : ℤ) * normalizedC R := by
      exact_mod_cast hrel1
    have hdiffZ :
        ((C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R : ℕ) : ℤ) * normalizedA R +
          ((qH R - (tau + C.data.returnedZ) : ℕ) : ℤ) * normalizedC R =
          ((sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R := by
      rw [Nat.cast_sub hc1Le, Nat.cast_sub (Nat.le_of_lt hsumLt)]
      push_cast only [Nat.cast_add, Nat.cast_mul] at hcritZ hrel1Z ⊢
      linear_combination hcritZ - hrel1Z
    have hdiff :
        (C.data.sourceX + A.depth - L5A2B4AR4R2B.c1 R) * normalizedA R +
          (qH R - (tau + C.data.returnedZ)) * normalizedC R =
          (sigma + C.data.returnedY) * normalizedB R := by
      exact_mod_cast hdiffZ
    have hcoef : 0 < sigma + C.data.returnedY := by omega
    have hc2Le := branchB_normalizedB_relation_min R _ _ _ hcoef hdiff.symm
    have hs2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    have hzsplit : zH R = sigma + (zH R - sigma) := by omega
    rw [hs2, hzsplit] at hc2Le
    omega

/-- The pure `a` chosen factorization cannot survive in a strict-RB actual
individual-return source.  The argument first reaches X or Y in the same
return ideal and only then uses source minimality and critical minimality. -/
theorem branchB_strictRB_a_route_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
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
  rcases branchB_strictRB_a_return_floor_disjunction R hB hs sigma tau hRB hroute with
      hzfloor | hyfloor
  · let Xval := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        sigma * normalizedB R
    let kZ := C.data.returnedZ - (qH R - tau)
    let gap := C.data.returnedY * normalizedB R + kZ * normalizedC R
    have hk : qH R - tau + kZ = C.data.returnedZ := Nat.add_sub_of_le hzfloor
    have hX := branchB_strictRB_X_value_identity R hB hs sigma tau hRB
    have hX' : A.n + (qH R - tau) * normalizedC R = Xval := by
      simpa [Xval, Nat.add_comm] using hX
    have hsplit : C.data.sourceValue = Xval + gap := by
      rw [hactual, hreturned, ← hk, Nat.add_mul]
      calc
        A.n + (C.data.returnedY * normalizedB R +
            ((qH R - tau) * normalizedC R + kZ * normalizedC R)) =
            (A.n + (qH R - tau) * normalizedC R) +
              (C.data.returnedY * normalizedB R + kZ * normalizedC R) := by omega
        _ = Xval + gap := by rw [hX']
    have hgapH : gap ∈ normalizedH P.M.base := by
      have hBmem := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) C.data.returnedY
      have hCmem := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) kZ
      simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).add_mem hBmem hCmem
    have hXmem := branchB_strictRB_X_value_mem_returnIdeal R hB hs sigma tau hRB
    change (Xval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hXmem
    have hsplitZ : (C.data.sourceValue : ℤ) = (Xval : ℤ) + gap := by
      exact_mod_cast hsplit
    have heq := (RelativeIdeal.minimalGenerator_eq_of_mem_add
      (returnIdeal (normalizedH P.M.base) A.n) hmin hXmem hgapH hsplitZ).2
    have heqNat : C.data.sourceValue = Xval := by exact_mod_cast heq
    rw [hsource] at heqNat
    have hbasePos : 0 < L5A2B4AR4R2B.c1 R - A.depth := by
      have huLtC1 : uH R < L5A2B4AR4R2B.c1 R := by
        have hs1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
        obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
          (branchB_actual_herzog_coordinates R).cross_positive
        omega
      omega
    have hcoefGt : L5A2B4AR4R2B.c1 R - A.depth < C.data.sourceX := by
      dsimp [Xval] at heqNat
      have hb := branchB_strictArm_normalizedWeight_pos R 1
      by_contra hnot
      have hle : C.data.sourceX ≤ L5A2B4AR4R2B.c1 R - A.depth :=
        Nat.le_of_not_gt hnot
      have hprodLe := Nat.mul_le_mul_right (normalizedA R) hle
      have hsigPos : 0 < sigma * normalizedB R := Nat.mul_pos (by omega) hb
      omega
    have hrelB : sigma * normalizedB R =
        (C.data.sourceX - (L5A2B4AR4R2B.c1 R - A.depth)) * normalizedA R +
          0 * normalizedC R := by
      dsimp [Xval] at heqNat
      have hsplitCoeff :
          (L5A2B4AR4R2B.c1 R - A.depth) +
            (C.data.sourceX - (L5A2B4AR4R2B.c1 R - A.depth)) =
              C.data.sourceX := Nat.add_sub_of_le (Nat.le_of_lt hcoefGt)
      rw [← hsplitCoeff, Nat.add_mul] at heqNat
      omega
    have hc2Le := branchB_normalizedB_relation_min R _ _ _
      (show 0 < sigma by omega) hrelB
    have hs2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
      (branchB_actual_herzog_coordinates R).cross_positive
    omega
  · let Yval := (uH R - A.depth) * normalizedA R +
        (tau + vH R) * normalizedC R
    let kY := C.data.returnedY - (zH R - sigma)
    let gap := kY * normalizedB R + C.data.returnedZ * normalizedC R
    have hk : zH R - sigma + kY = C.data.returnedY := Nat.add_sub_of_le hyfloor
    have hY := branchB_strictRB_Y_value_identity R hB hs sigma tau hRB
    have hY' : A.n + (zH R - sigma) * normalizedB R = Yval := by
      simpa [Yval, Nat.add_comm] using hY
    have hsplit : C.data.sourceValue = Yval + gap := by
      rw [hactual, hreturned, ← hk, Nat.add_mul]
      calc
        A.n + ((zH R - sigma) * normalizedB R +
            kY * normalizedB R + C.data.returnedZ * normalizedC R) =
            (A.n + (zH R - sigma) * normalizedB R) +
              (kY * normalizedB R + C.data.returnedZ * normalizedC R) := by omega
        _ = Yval + gap := by rw [hY']
    have hgapH : gap ∈ normalizedH P.M.base := by
      have hBmem := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) kY
      have hCmem := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) C.data.returnedZ
      simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).add_mem hBmem hCmem
    have hYmem := branchB_strictRB_Y_value_mem_returnIdeal R hB hs sigma tau hRB
    change (Yval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hYmem
    have hsplitZ : (C.data.sourceValue : ℤ) = (Yval : ℤ) + gap := by
      exact_mod_cast hsplit
    have heq := (RelativeIdeal.minimalGenerator_eq_of_mem_add
      (returnIdeal (normalizedH P.M.base) A.n) hmin hYmem hgapH hsplitZ).2
    have heqNat : C.data.sourceValue = Yval := by exact_mod_cast heq
    rw [hsource] at heqNat
    have hbasePos : 0 < uH R - A.depth := by omega
    have hcoefGt : uH R - A.depth < C.data.sourceX := by
      dsimp [Yval] at heqNat
      have hc := branchB_strictArm_normalizedWeight_pos R 2
      by_contra hnot
      have hle : C.data.sourceX ≤ uH R - A.depth := Nat.le_of_not_gt hnot
      have hprodLe := Nat.mul_le_mul_right (normalizedA R) hle
      have htcPos : 0 < (tau + vH R) * normalizedC R :=
        Nat.mul_pos (by omega) hc
      omega
    have hrelC : (tau + vH R) * normalizedC R =
        (C.data.sourceX - (uH R - A.depth)) * normalizedA R +
          0 * normalizedB R := by
      dsimp [Yval] at heqNat
      have hsplitCoeff : (uH R - A.depth) +
          (C.data.sourceX - (uH R - A.depth)) = C.data.sourceX :=
        Nat.add_sub_of_le (Nat.le_of_lt hcoefGt)
      rw [← hsplitCoeff, Nat.add_mul] at heqNat
      omega
    have hc3Le := branchB_normalizedC_relation_min R _ _ _
      (show 0 < tau + vH R by omega) hrelC
    have hs3 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    omega

end NS25Lean.L5A2B4AR5B
