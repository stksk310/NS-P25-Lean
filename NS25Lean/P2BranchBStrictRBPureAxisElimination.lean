import NS25Lean.P2BranchBStrictArmCoefficientRigidity

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

private theorem strictRB_normalizedWeight_pos
    (R : SectorBCriticalRoleBranchB P) (k : Fin 3) :
    0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex k) := by
  have hs := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex k)
  have hw := L2B.weights_positive P.M.base (R.reindex k)
  nlinarith

private theorem pureB_signed_to_A_relation
    (a b c d x mu base T : ℕ) (hx : x ≤ d) (hmu : mu ≤ base)
    (h : (((d : ℤ) - x) * a) + (((mu : ℤ) - base) * b) = (T : ℤ) * c) :
    (d - x) * a = (base - mu) * b + T * c := by
  have hxCast : ((d - x : ℕ) : ℤ) = d - x := Nat.cast_sub hx
  have hmuCast : ((base - mu : ℕ) : ℤ) = base - mu := Nat.cast_sub hmu
  exact_mod_cast (show ((d - x : ℕ) : ℤ) * a =
      ((base - mu : ℕ) : ℤ) * b + (T : ℤ) * c by
    rw [hxCast, hmuCast]
    nlinarith only [h])

private theorem pureB_signed_to_C_relation
    (a b c d x mu base T : ℕ) (hx : x ≤ d) (hmu : base ≤ mu)
    (h : (((d : ℤ) - x) * a) + (((mu : ℤ) - base) * b) = (T : ℤ) * c) :
    T * c = (d - x) * a + (mu - base) * b := by
  have hxCast : ((d - x : ℕ) : ℤ) = d - x := Nat.cast_sub hx
  have hmuCast : ((mu - base : ℕ) : ℤ) = mu - base := Nat.cast_sub hmu
  exact_mod_cast (show (T : ℤ) * c =
      ((d - x : ℕ) : ℤ) * a + ((mu - base : ℕ) : ℤ) * b by
    rw [hxCast, hmuCast]
    nlinarith only [h])

/-- The exact strict-RB signed balance on a chosen pure-B factorization. -/
theorem branchB_strictRB_pureB_signed_balance
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceY : ℤ) - (pH R + sigma)) * normalizedB R) =
      ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  have h := branchB_positive_center_pureB_signed_balance R hB hs
    (pH R + sigma) tau ⟨hRB.1, hRB.2.1⟩ hroute
  push_cast at h ⊢
  nlinarith only [h]

/-- The strict-RB F value is an actual member of the selected individual
return ideal; no source/anchor identification is made. -/
theorem branchB_strictRB_F_value_mem_returnIdeal
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    (((pH R + sigma) * normalizedB R + tau * normalizedC R : ℕ) : ℤ) ∈
      returnIdeal (normalizedH P.M.base) A.n := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau at hRB
  have hmem := branchB_selected_return_anchor_mem_returnIdeal R hB hs
  change A.beta ∈ returnIdeal (normalizedH P.M.base) A.n at hmem
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hcoord := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, hRB.1, hRB.2] at hcoord
  have hcoord' :
      (((pH R + sigma) * normalizedB R + tau * normalizedC R : ℕ) : ℤ) =
        A.beta := by
    rw [hcoord]
    push_cast
    ring
  change (((pH R + sigma) * normalizedB R + tau * normalizedC R : ℕ) : ℤ) ∈ _
  rw [hcoord']
  exact hmem

private theorem strictRB_c1_depth_bounds
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
    0 < A.depth ∧ A.depth < L5A2B4AR4R2B.c1 R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  have hs1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have huLtC1 : uH R < L5A2B4AR4R2B.c1 R := by
    rw [hs1]
    omega
  exact ⟨A.depth_pos, lt_trans hRB.2.2.2.2.2.2 huLtC1⟩

private theorem strictRB_actual_source_minimal
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
    (C.data.sourceValue : ℤ)
  rw [C.data.source_eq]
  exact A.source_minimal

/-- Strict-RB pure-B with returned support only on A is impossible. -/
theorem branchB_strictRB_pureB_aOnly_impossible
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ = 0) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX ≠ 0 at hrx
  change C.data.returnedZ = 0 at hrz
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hry := (branchB_positive_center_pureB_returned_support_split
    R hB hs hroute).1
  have hsource : C.data.sourceValue = C.data.sourceY * normalizedB R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.2]
    omega
  have hreturned : C.data.returnedValue = C.data.returnedX * normalizedA R := by
    rw [C.data.returned_factorization, hry, hrz]
    omega
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hF := branchB_strictRB_F_value_identity R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change (pH R + sigma) * normalizedB R + tau * normalizedC R =
      A.n + normalizedA R * A.depth at hF
  let Fval := (pH R + sigma) * normalizedB R + tau * normalizedC R
  have hF' : Fval = A.n + A.depth * normalizedA R := by
    simpa [Fval, Nat.mul_comm] using hF
  have hFmem := branchB_strictRB_F_value_mem_returnIdeal R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change (Fval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hFmem
  have hmin := strictRB_actual_source_minimal R hB hs
  change (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) at hmin
  have hdepth := strictRB_c1_depth_bounds R hB hs sigma tau hRB
  change 0 < A.depth ∧ A.depth < L5A2B4AR4R2B.c1 R at hdepth
  rcases lt_trichotomy C.data.returnedX A.depth with hxd | hxeq | hdx
  · have hbal := branchB_strictRB_pureB_signed_balance R hB hs sigma tau hRB hroute
    change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceY : ℤ) - (pH R + sigma)) * normalizedB R) =
      ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R at hbal
    rw [hrz, add_zero] at hbal
    by_cases hmu : pH R + sigma ≤ C.data.sourceY
    · have hrelC : tau * normalizedC R =
          (A.depth - C.data.returnedX) * normalizedA R +
            (C.data.sourceY - (pH R + sigma)) * normalizedB R := by
        have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
            A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxd)
        have hmuCast : ((C.data.sourceY - (pH R + sigma) : ℕ) : ℤ) =
            C.data.sourceY - (pH R + sigma) := Nat.cast_sub hmu
        exact_mod_cast (show (tau : ℤ) * normalizedC R =
            ((A.depth - C.data.returnedX : ℕ) : ℤ) * normalizedA R +
              ((C.data.sourceY - (pH R + sigma) : ℕ) : ℤ) * normalizedB R by
          rw [hxCast, hmuCast]
          nlinarith only [hbal])
      have hc3Le := branchB_normalizedC_relation_min R _ _ _
        (show 0 < tau by omega) hrelC
      have hs3 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
      obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
        (branchB_actual_herzog_coordinates R).cross_positive
      omega
    · have hmuLt : C.data.sourceY < pH R + sigma := Nat.lt_of_not_ge hmu
      have hrelA : (A.depth - C.data.returnedX) * normalizedA R =
          (pH R + sigma - C.data.sourceY) * normalizedB R +
            tau * normalizedC R := by
        have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
            A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxd)
        have hmuCast : ((pH R + sigma - C.data.sourceY : ℕ) : ℤ) =
            (pH R + sigma : ℤ) - C.data.sourceY :=
          Nat.cast_sub (Nat.le_of_lt hmuLt)
        exact_mod_cast (show ((A.depth - C.data.returnedX : ℕ) : ℤ) * normalizedA R =
            ((pH R + sigma - C.data.sourceY : ℕ) : ℤ) * normalizedB R +
              (tau : ℤ) * normalizedC R by
          rw [hxCast, hmuCast]
          nlinarith only [hbal])
      have hc1Le := branchB_normalizedA_relation_min R _ _ _
        (Nat.sub_pos_of_lt hxd) hrelA
      omega
  · have hsourceF : C.data.sourceValue = Fval := by
      rw [hactual, hreturned, hxeq, ← hF']
    have heq : C.data.sourceY * normalizedB R =
        (pH R + sigma) * normalizedB R + tau * normalizedC R := by
      rw [← hsource, hsourceF]
    have hmuGt : pH R + sigma < C.data.sourceY := by
      by_contra hnot
      have hle := Nat.mul_le_mul_right (normalizedB R) (Nat.le_of_not_gt hnot)
      have htc : 0 < tau * normalizedC R := Nat.mul_pos (by omega)
        (strictRB_normalizedWeight_pos R 2)
      omega
    have hrelC : tau * normalizedC R =
        0 * normalizedA R + (C.data.sourceY - (pH R + sigma)) * normalizedB R := by
      have hsplit := Nat.add_sub_of_le (Nat.le_of_lt hmuGt)
      rw [← hsplit, Nat.add_mul] at heq
      omega
    have hc3Le := branchB_normalizedC_relation_min R _ _ _
      (show 0 < tau by omega) hrelC
    have hs3 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
      (branchB_actual_herzog_coordinates R).cross_positive
    omega
  · let gap := (C.data.returnedX - A.depth) * normalizedA R
    have hk : A.depth + (C.data.returnedX - A.depth) = C.data.returnedX :=
      Nat.add_sub_of_le (Nat.le_of_lt hdx)
    have hsplit : C.data.sourceValue = Fval + gap := by
      rw [hactual, hreturned, ← hk, Nat.add_mul]
      calc
        A.n + (A.depth * normalizedA R +
            (C.data.returnedX - A.depth) * normalizedA R) =
            (A.n + A.depth * normalizedA R) + gap := by
              simp only [gap]
              omega
        _ = Fval + gap := by rw [← hF']
    have hgapH : gap ∈ normalizedH P.M.base := by
      simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R) (C.data.returnedX - A.depth)
    have hsplitZ : (C.data.sourceValue : ℤ) = (Fval : ℤ) + gap := by
      exact_mod_cast hsplit
    have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
      (returnIdeal (normalizedH P.M.base) A.n) hmin hFmem hgapH hsplitZ).1
    exact (Nat.mul_ne_zero (Nat.sub_ne_zero_of_lt hdx)
      (strictRB_normalizedWeight_pos R 0).ne') hgap0

/-- In the pure-B returned-C-only case, the returned C coefficient reaches
the strict-RB X floor. -/
theorem branchB_strictRB_pureB_cOnly_X_floor
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX = 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ ≠ 0) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    qH R - tau ≤ C.data.returnedZ := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change C.data.returnedX = 0 at hrx
  change C.data.returnedZ ≠ 0 at hrz
  have hbal := branchB_strictRB_pureB_signed_balance R hB hs sigma tau hRB hroute
  change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
      (((C.data.sourceY : ℤ) - (pH R + sigma)) * normalizedB R) =
    ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R at hbal
  rw [hrx] at hbal
  norm_num at hbal
  change qH R - tau ≤ C.data.returnedZ
  have hdepth := strictRB_c1_depth_bounds R hB hs sigma tau hRB
  change 0 < A.depth ∧ A.depth < L5A2B4AR4R2B.c1 R at hdepth
  have hmu : pH R + sigma ≤ C.data.sourceY := by
    by_contra hnot
    have hmuLt : C.data.sourceY < pH R + sigma := Nat.lt_of_not_ge hnot
    have hrelA : A.depth * normalizedA R =
        (pH R + sigma - C.data.sourceY) * normalizedB R +
          (tau + C.data.returnedZ) * normalizedC R := by
      simpa using pureB_signed_to_A_relation
        (normalizedA R) (normalizedB R) (normalizedC R)
        A.depth 0 C.data.sourceY (pH R + sigma) (tau + C.data.returnedZ)
        (Nat.zero_le _) (Nat.le_of_lt hmuLt) hbal
    have hc1Le := branchB_normalizedA_relation_min R _ _ _ hdepth.1 hrelA
    omega
  have hrelC : (tau + C.data.returnedZ) * normalizedC R =
      A.depth * normalizedA R +
        (C.data.sourceY - (pH R + sigma)) * normalizedB R := by
    simpa using pureB_signed_to_C_relation
      (normalizedA R) (normalizedB R) (normalizedC R)
      A.depth 0 C.data.sourceY (pH R + sigma) (tau + C.data.returnedZ)
      (Nat.zero_le _) hmu hbal
  have hc3Le := branchB_normalizedC_relation_min R _ _ _
    (show 0 < tau + C.data.returnedZ by omega) hrelC
  have hs3 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
  omega

/-- Strict-RB pure-B with returned support only on C collapses to X and is
then ruled out by A-critical minimality. -/
theorem branchB_strictRB_pureB_cOnly_impossible
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX = 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ ≠ 0) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX = 0 at hrx
  change C.data.returnedZ ≠ 0 at hrz
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hry := (branchB_positive_center_pureB_returned_support_split
    R hB hs hroute).1
  have hsource : C.data.sourceValue = C.data.sourceY * normalizedB R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.2]
    omega
  have hreturned : C.data.returnedValue = C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hrx, hry]
    omega
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hfloor := branchB_strictRB_pureB_cOnly_X_floor
    R hB hs sigma tau hRB hroute hrx hrz
  change qH R - tau ≤ C.data.returnedZ at hfloor
  let Xval := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
    sigma * normalizedB R
  let k := C.data.returnedZ - (qH R - tau)
  let gap := k * normalizedC R
  have hk : qH R - tau + k = C.data.returnedZ := Nat.add_sub_of_le hfloor
  have hX := branchB_strictRB_X_value_identity R hB hs sigma tau hRB
  have hX' : A.n + (qH R - tau) * normalizedC R = Xval := by
    simpa [Xval, Nat.add_comm] using hX
  have hsplit : C.data.sourceValue = Xval + gap := by
    rw [hactual, hreturned, ← hk, Nat.add_mul]
    calc
      A.n + ((qH R - tau) * normalizedC R + k * normalizedC R) =
          (A.n + (qH R - tau) * normalizedC R) + gap := by
            simp only [gap]
            omega
      _ = Xval + gap := by rw [hX']
  have hgapH : gap ∈ normalizedH P.M.base := by
    simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) k
  have hXmem := branchB_strictRB_X_value_mem_returnIdeal R hB hs sigma tau hRB
  change (Xval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hXmem
  have hmin := strictRB_actual_source_minimal R hB hs
  change (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) at hmin
  have hsplitZ : (C.data.sourceValue : ℤ) = (Xval : ℤ) + gap := by
    exact_mod_cast hsplit
  have heq := (RelativeIdeal.minimalGenerator_eq_of_mem_add
    (returnIdeal (normalizedH P.M.base) A.n) hmin hXmem hgapH hsplitZ).2
  have heqNat : C.data.sourceValue = Xval := by exact_mod_cast heq
  rw [hsource] at heqNat
  have hdepth := strictRB_c1_depth_bounds R hB hs sigma tau hRB
  change 0 < A.depth ∧ A.depth < L5A2B4AR4R2B.c1 R at hdepth
  have hbasePos : 0 < L5A2B4AR4R2B.c1 R - A.depth := by omega
  have hmuGt : sigma < C.data.sourceY := by
    dsimp [Xval] at heqNat
    by_contra hnot
    have hle := Nat.mul_le_mul_right (normalizedB R) (Nat.le_of_not_gt hnot)
    have hapos : 0 < (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R :=
      Nat.mul_pos hbasePos (strictRB_normalizedWeight_pos R 0)
    omega
  have hrelA : (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R =
      (C.data.sourceY - sigma) * normalizedB R + 0 * normalizedC R := by
    dsimp [Xval] at heqNat
    have hysplit : sigma + (C.data.sourceY - sigma) = C.data.sourceY :=
      Nat.add_sub_of_le (Nat.le_of_lt hmuGt)
    rw [← hysplit, Nat.add_mul] at heqNat
    omega
  have hc1Le := branchB_normalizedA_relation_min R _ _ _ hbasePos hrelA
  omega

/-- Strict-RB pure-B with mixed returned A+C support is impossible. -/
theorem branchB_strictRB_pureB_mixed_impossible
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ ≠ 0) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX ≠ 0 at hrx
  change C.data.returnedZ ≠ 0 at hrz
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
  have hF := branchB_strictRB_F_value_identity R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change (pH R + sigma) * normalizedB R + tau * normalizedC R =
      A.n + normalizedA R * A.depth at hF
  let Fval := (pH R + sigma) * normalizedB R + tau * normalizedC R
  have hF' : Fval = A.n + A.depth * normalizedA R := by
    simpa [Fval, Nat.mul_comm] using hF
  have hFmem := branchB_strictRB_F_value_mem_returnIdeal R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change (Fval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hFmem
  have hmin := strictRB_actual_source_minimal R hB hs
  change (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) at hmin
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
    have hgapPos : 0 < gap := by
      dsimp [gap]
      have hcpos := strictRB_normalizedWeight_pos R 2
      have hrzpos : 0 < C.data.returnedZ := Nat.pos_of_ne_zero hrz
      positivity
    exact hgapPos.ne' hgap0
  · have hxd : C.data.returnedX < A.depth := Nat.lt_of_not_ge hdx
    have hbal := branchB_strictRB_pureB_signed_balance R hB hs sigma tau hRB hroute
    change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceY : ℤ) - (pH R + sigma)) * normalizedB R) =
      ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R at hbal
    have hdepth := strictRB_c1_depth_bounds R hB hs sigma tau hRB
    change 0 < A.depth ∧ A.depth < L5A2B4AR4R2B.c1 R at hdepth
    by_cases hmu : pH R + sigma ≤ C.data.sourceY
    · have hrelC : (tau + C.data.returnedZ) * normalizedC R =
          (A.depth - C.data.returnedX) * normalizedA R +
            (C.data.sourceY - (pH R + sigma)) * normalizedB R := by
        have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
            A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxd)
        have hmuCast : ((C.data.sourceY - (pH R + sigma) : ℕ) : ℤ) =
            C.data.sourceY - (pH R + sigma) := Nat.cast_sub hmu
        exact_mod_cast (show ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R =
            ((A.depth - C.data.returnedX : ℕ) : ℤ) * normalizedA R +
              ((C.data.sourceY - (pH R + sigma) : ℕ) : ℤ) * normalizedB R by
          rw [hxCast, hmuCast]
          nlinarith only [hbal])
      have hc3Le := branchB_normalizedC_relation_min R _ _ _
        (show 0 < tau + C.data.returnedZ by omega) hrelC
      have hs3 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
      have hfloor : qH R - tau ≤ C.data.returnedZ := by omega
      let Xval := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        sigma * normalizedB R
      let kZ := C.data.returnedZ - (qH R - tau)
      let gap := C.data.returnedX * normalizedA R + kZ * normalizedC R
      have hk : qH R - tau + kZ = C.data.returnedZ := Nat.add_sub_of_le hfloor
      have hX := branchB_strictRB_X_value_identity R hB hs sigma tau hRB
      have hX' : A.n + (qH R - tau) * normalizedC R = Xval := by
        simpa [Xval, Nat.add_comm] using hX
      have hsplit : C.data.sourceValue = Xval + gap := by
        rw [hactual, hreturned, ← hk, Nat.add_mul]
        calc
          A.n + (C.data.returnedX * normalizedA R +
              ((qH R - tau) * normalizedC R + kZ * normalizedC R)) =
              (A.n + (qH R - tau) * normalizedC R) +
                (C.data.returnedX * normalizedA R + kZ * normalizedC R) := by omega
          _ = Xval + gap := by rw [hX']
      have hgapH : gap ∈ normalizedH P.M.base := by
        have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R) C.data.returnedX
        have hc := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedC_mem R) kZ
        simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
          (normalizedH P.M.base).add_mem ha hc
      have hXmem := branchB_strictRB_X_value_mem_returnIdeal R hB hs sigma tau hRB
      change (Xval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hXmem
      have hsplitZ : (C.data.sourceValue : ℤ) = (Xval : ℤ) + gap := by
        exact_mod_cast hsplit
      have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
        (returnIdeal (normalizedH P.M.base) A.n) hmin hXmem hgapH hsplitZ).1
      have hgapPos : 0 < gap := by
        dsimp [gap]
        have hapos := strictRB_normalizedWeight_pos R 0
        have hrxpos : 0 < C.data.returnedX := Nat.pos_of_ne_zero hrx
        positivity
      exact hgapPos.ne' hgap0
    · have hmuLt : C.data.sourceY < pH R + sigma := Nat.lt_of_not_ge hmu
      have hrelA : (A.depth - C.data.returnedX) * normalizedA R =
          (pH R + sigma - C.data.sourceY) * normalizedB R +
            (tau + C.data.returnedZ) * normalizedC R := by
        have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
            A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxd)
        have hmuCast : ((pH R + sigma - C.data.sourceY : ℕ) : ℤ) =
            (pH R + sigma : ℤ) - C.data.sourceY :=
          Nat.cast_sub (Nat.le_of_lt hmuLt)
        exact_mod_cast (show ((A.depth - C.data.returnedX : ℕ) : ℤ) * normalizedA R =
            ((pH R + sigma - C.data.sourceY : ℕ) : ℤ) * normalizedB R +
              ((tau + C.data.returnedZ : ℕ) : ℤ) * normalizedC R by
          rw [hxCast, hmuCast]
          nlinarith only [hbal])
      have hc1Le := branchB_normalizedA_relation_min R _ _ _
        (Nat.sub_pos_of_lt hxd) hrelA
      omega

/-- Complete strict-RB elimination of a chosen pure-B source route. -/
theorem branchB_strictRB_pureB_route_impossible
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  obtain ⟨hry, hsplit⟩ := branchB_positive_center_pureB_returned_support_split
    R hB hs hroute
  rcases hsplit with ha | hc | hm
  · exact branchB_strictRB_pureB_aOnly_impossible
      R hB hs sigma tau hRB hroute ha.1 ha.2
  · exact branchB_strictRB_pureB_cOnly_impossible
      R hB hs sigma tau hRB hroute hc.1 hc.2
  · exact branchB_strictRB_pureB_mixed_impossible
      R hB hs sigma tau hRB hroute hm.1 hm.2

private theorem pureC_signed_to_A_relation
    (a b c d x mu tau base rho : ℕ) (hx : x ≤ d) (hmu : mu ≤ tau)
    (h : (((d : ℤ) - x) * a) + (((mu : ℤ) - tau) * c) =
      ((base + rho : ℕ) : ℤ) * b) :
    (d - x) * a = (base + rho) * b + (tau - mu) * c := by
  have hxCast : ((d - x : ℕ) : ℤ) = d - x := Nat.cast_sub hx
  have hmuCast : ((tau - mu : ℕ) : ℤ) = tau - mu := Nat.cast_sub hmu
  exact_mod_cast (show ((d - x : ℕ) : ℤ) * a =
      ((base + rho : ℕ) : ℤ) * b + ((tau - mu : ℕ) : ℤ) * c by
    rw [hxCast, hmuCast]
    nlinarith only [h])

private theorem pureC_signed_to_B_relation
    (a b c d x mu tau base rho : ℕ) (hx : x ≤ d) (hmu : tau ≤ mu)
    (h : (((d : ℤ) - x) * a) + (((mu : ℤ) - tau) * c) =
      ((base + rho : ℕ) : ℤ) * b) :
    (base + rho) * b = (d - x) * a + (mu - tau) * c := by
  have hxCast : ((d - x : ℕ) : ℤ) = d - x := Nat.cast_sub hx
  have hmuCast : ((mu - tau : ℕ) : ℤ) = mu - tau := Nat.cast_sub hmu
  exact_mod_cast (show ((base + rho : ℕ) : ℤ) * b =
      ((d - x : ℕ) : ℤ) * a + ((mu - tau : ℕ) : ℤ) * c by
    rw [hxCast, hmuCast]
    nlinarith only [h])

/-- Exact strict-RB signed balance on a chosen pure-C factorization. -/
theorem branchB_strictRB_pureC_signed_balance
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceZ : ℤ) - tau) * normalizedC R) =
      ((pH R + sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  have h := branchB_positive_center_pureC_signed_balance R hB hs
    (pH R + sigma) tau ⟨hRB.1, hRB.2.1⟩ hroute
  push_cast at h ⊢
  nlinarith only [h]

/-- Strict-RB pure-C with returned support only on A is impossible. -/
theorem branchB_strictRB_pureC_aOnly_impossible
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hry :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedY = 0) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX ≠ 0 at hrx
  change C.data.returnedY = 0 at hry
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hrz := (branchB_positive_center_pureC_returned_support_split
    R hB hs hroute).1
  have hsource : C.data.sourceValue = C.data.sourceZ * normalizedC R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.1]
    omega
  have hreturned : C.data.returnedValue = C.data.returnedX * normalizedA R := by
    rw [C.data.returned_factorization, hry, hrz]
    omega
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  let Fval := (pH R + sigma) * normalizedB R + tau * normalizedC R
  have hF := branchB_strictRB_F_value_identity R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change Fval = A.n + normalizedA R * A.depth at hF
  have hF' : Fval = A.n + A.depth * normalizedA R := by
    simpa [Nat.mul_comm] using hF
  have hFmem := branchB_strictRB_F_value_mem_returnIdeal R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change (Fval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hFmem
  have hmin := strictRB_actual_source_minimal R hB hs
  change (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) at hmin
  have hdepth := strictRB_c1_depth_bounds R hB hs sigma tau hRB
  change 0 < A.depth ∧ A.depth < L5A2B4AR4R2B.c1 R at hdepth
  rcases lt_trichotomy C.data.returnedX A.depth with hxd | hxeq | hdx
  · have hbal := branchB_strictRB_pureC_signed_balance R hB hs sigma tau hRB hroute
    change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceZ : ℤ) - tau) * normalizedC R) =
      ((pH R + sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R at hbal
    rw [hry, add_zero] at hbal
    by_cases hmu : C.data.sourceZ ≤ tau
    · have hrelA := pureC_signed_to_A_relation
        (normalizedA R) (normalizedB R) (normalizedC R)
        A.depth C.data.returnedX C.data.sourceZ tau (pH R + sigma) 0
        (Nat.le_of_lt hxd) hmu hbal
      have hc1Le := branchB_normalizedA_relation_min R _ _ _
        (Nat.sub_pos_of_lt hxd) hrelA
      omega
    · have hmuGt : tau < C.data.sourceZ := Nat.lt_of_not_ge hmu
      have hrelB := pureC_signed_to_B_relation
        (normalizedA R) (normalizedB R) (normalizedC R)
        A.depth C.data.returnedX C.data.sourceZ tau (pH R + sigma) 0
        (Nat.le_of_lt hxd) (Nat.le_of_lt hmuGt) hbal
      have hc2Le := branchB_normalizedB_relation_min R _ _ _
        (show 0 < pH R + sigma + 0 by omega) hrelB
      have hs2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
      omega
  · have hsourceF : C.data.sourceValue = Fval := by
      rw [hactual, hreturned, hxeq, ← hF']
    have heq : C.data.sourceZ * normalizedC R =
        (pH R + sigma) * normalizedB R + tau * normalizedC R := by
      rw [← hsource, hsourceF]
    have hmuGt : tau < C.data.sourceZ := by
      by_contra hnot
      have hle := Nat.mul_le_mul_right (normalizedC R) (Nat.le_of_not_gt hnot)
      have hbb : 0 < (pH R + sigma) * normalizedB R :=
        Nat.mul_pos (by omega) (strictRB_normalizedWeight_pos R 1)
      omega
    have hrelB : (pH R + sigma) * normalizedB R =
        0 * normalizedA R + (C.data.sourceZ - tau) * normalizedC R := by
      have hsplit : tau + (C.data.sourceZ - tau) = C.data.sourceZ :=
        Nat.add_sub_of_le (Nat.le_of_lt hmuGt)
      rw [← hsplit, Nat.add_mul] at heq
      omega
    have hc2Le := branchB_normalizedB_relation_min R _ _ _
      (show 0 < pH R + sigma by omega) hrelB
    have hs2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
    omega
  · let gap := (C.data.returnedX - A.depth) * normalizedA R
    have hk : A.depth + (C.data.returnedX - A.depth) = C.data.returnedX :=
      Nat.add_sub_of_le (Nat.le_of_lt hdx)
    have hsplit : C.data.sourceValue = Fval + gap := by
      rw [hactual, hreturned, ← hk, Nat.add_mul]
      calc
        A.n + (A.depth * normalizedA R +
            (C.data.returnedX - A.depth) * normalizedA R) =
            (A.n + A.depth * normalizedA R) + gap := by
              simp only [gap]
              omega
        _ = Fval + gap := by rw [← hF']
    have hgapH : gap ∈ normalizedH P.M.base := by
      simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R) (C.data.returnedX - A.depth)
    have hsplitZ : (C.data.sourceValue : ℤ) = (Fval : ℤ) + gap := by
      exact_mod_cast hsplit
    have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
      (returnIdeal (normalizedH P.M.base) A.n) hmin hFmem hgapH hsplitZ).1
    exact (Nat.mul_ne_zero (Nat.sub_ne_zero_of_lt hdx)
      (strictRB_normalizedWeight_pos R 0).ne') hgap0

/-- In the pure-C returned-B-only case, the returned B coefficient reaches
the strict-RB Y floor. -/
theorem branchB_strictRB_pureC_bOnly_Y_floor
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX = 0)
    (hry :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedY ≠ 0) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    zH R - sigma ≤ C.data.returnedY := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change C.data.returnedX = 0 at hrx
  change C.data.returnedY ≠ 0 at hry
  have hbal := branchB_strictRB_pureC_signed_balance R hB hs sigma tau hRB hroute
  change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
      (((C.data.sourceZ : ℤ) - tau) * normalizedC R) =
    ((pH R + sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R at hbal
  rw [hrx] at hbal
  norm_num at hbal
  change zH R - sigma ≤ C.data.returnedY
  have hdepth := strictRB_c1_depth_bounds R hB hs sigma tau hRB
  change 0 < A.depth ∧ A.depth < L5A2B4AR4R2B.c1 R at hdepth
  have hmu : tau < C.data.sourceZ := by
    by_contra hnot
    have hmuLe : C.data.sourceZ ≤ tau := Nat.le_of_not_gt hnot
    have hrelA := pureC_signed_to_A_relation
      (normalizedA R) (normalizedB R) (normalizedC R)
      A.depth 0 C.data.sourceZ tau (pH R + sigma) C.data.returnedY
      (Nat.zero_le _) hmuLe hbal
    have hc1Le := branchB_normalizedA_relation_min R _ _ _ hdepth.1 hrelA
    omega
  have hrelB := pureC_signed_to_B_relation
    (normalizedA R) (normalizedB R) (normalizedC R)
    A.depth 0 C.data.sourceZ tau (pH R + sigma) C.data.returnedY
    (Nat.zero_le _) (Nat.le_of_lt hmu) hbal
  have hc2Le := branchB_normalizedB_relation_min R _ _ _
    (show 0 < pH R + sigma + C.data.returnedY by omega) hrelB
  have hs2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hzsplit : zH R = sigma + (zH R - sigma) := by omega
  rw [hs2, hzsplit] at hc2Le
  omega

/-- Strict-RB pure-C with returned support only on B collapses to Y and is
then ruled out by A-critical minimality. -/
theorem branchB_strictRB_pureC_bOnly_impossible
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX = 0)
    (hry :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedY ≠ 0) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX = 0 at hrx
  change C.data.returnedY ≠ 0 at hry
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hrz := (branchB_positive_center_pureC_returned_support_split
    R hB hs hroute).1
  have hsource : C.data.sourceValue = C.data.sourceZ * normalizedC R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.1]
    omega
  have hreturned : C.data.returnedValue = C.data.returnedY * normalizedB R := by
    rw [C.data.returned_factorization, hrx, hrz]
    omega
  have hactual := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
  change C.data.sourceValue = A.n + C.data.returnedValue at hactual
  have hfloor := branchB_strictRB_pureC_bOnly_Y_floor
    R hB hs sigma tau hRB hroute hrx hry
  change zH R - sigma ≤ C.data.returnedY at hfloor
  let Yval := (uH R - A.depth) * normalizedA R +
    (tau + vH R) * normalizedC R
  let k := C.data.returnedY - (zH R - sigma)
  let gap := k * normalizedB R
  have hk : zH R - sigma + k = C.data.returnedY := Nat.add_sub_of_le hfloor
  have hY := branchB_strictRB_Y_value_identity R hB hs sigma tau hRB
  have hY' : A.n + (zH R - sigma) * normalizedB R = Yval := by
    simpa [Yval, Nat.add_comm] using hY
  have hsplit : C.data.sourceValue = Yval + gap := by
    rw [hactual, hreturned, ← hk, Nat.add_mul]
    calc
      A.n + ((zH R - sigma) * normalizedB R + k * normalizedB R) =
          (A.n + (zH R - sigma) * normalizedB R) + gap := by
            simp only [gap]
            omega
      _ = Yval + gap := by rw [hY']
  have hgapH : gap ∈ normalizedH P.M.base := by
    simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) k
  have hYmem := branchB_strictRB_Y_value_mem_returnIdeal R hB hs sigma tau hRB
  change (Yval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hYmem
  have hmin := strictRB_actual_source_minimal R hB hs
  change (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) at hmin
  have hsplitZ : (C.data.sourceValue : ℤ) = (Yval : ℤ) + gap := by
    exact_mod_cast hsplit
  have heq := (RelativeIdeal.minimalGenerator_eq_of_mem_add
    (returnIdeal (normalizedH P.M.base) A.n) hmin hYmem hgapH hsplitZ).2
  have heqNat : C.data.sourceValue = Yval := by exact_mod_cast heq
  rw [hsource] at heqNat
  have hbasePos : 0 < uH R - A.depth := by omega
  have hmuGt : tau + vH R < C.data.sourceZ := by
    dsimp [Yval] at heqNat
    by_contra hnot
    have hle := Nat.mul_le_mul_right (normalizedC R) (Nat.le_of_not_gt hnot)
    have hapos : 0 < (uH R - A.depth) * normalizedA R :=
      Nat.mul_pos hbasePos (strictRB_normalizedWeight_pos R 0)
    omega
  have hrelA : (uH R - A.depth) * normalizedA R =
      0 * normalizedB R + (C.data.sourceZ - (tau + vH R)) * normalizedC R := by
    dsimp [Yval] at heqNat
    have hsplit : tau + vH R + (C.data.sourceZ - (tau + vH R)) =
        C.data.sourceZ := Nat.add_sub_of_le (Nat.le_of_lt hmuGt)
    rw [← hsplit, Nat.add_mul] at heqNat
    omega
  have hc1Le := branchB_normalizedA_relation_min R _ _ _ hbasePos hrelA
  have hs1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  omega

/-- Strict-RB pure-C with mixed returned A+B support is impossible. -/
theorem branchB_strictRB_pureC_mixed_impossible
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hry :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedY ≠ 0) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX ≠ 0 at hrx
  change C.data.returnedY ≠ 0 at hry
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
  let Fval := (pH R + sigma) * normalizedB R + tau * normalizedC R
  have hF := branchB_strictRB_F_value_identity R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change Fval = A.n + normalizedA R * A.depth at hF
  have hF' : Fval = A.n + A.depth * normalizedA R := by
    simpa [Nat.mul_comm] using hF
  have hFmem := branchB_strictRB_F_value_mem_returnIdeal R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change (Fval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hFmem
  have hmin := strictRB_actual_source_minimal R hB hs
  change (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
      (C.data.sourceValue : ℤ) at hmin
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
    have hgapPos : 0 < gap := by
      dsimp [gap]
      have hbpos := strictRB_normalizedWeight_pos R 1
      have hrypos : 0 < C.data.returnedY := Nat.pos_of_ne_zero hry
      positivity
    exact hgapPos.ne' hgap0
  · have hxd : C.data.returnedX < A.depth := Nat.lt_of_not_ge hdx
    have hbal := branchB_strictRB_pureC_signed_balance R hB hs sigma tau hRB hroute
    change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceZ : ℤ) - tau) * normalizedC R) =
      ((pH R + sigma + C.data.returnedY : ℕ) : ℤ) * normalizedB R at hbal
    have hdepth := strictRB_c1_depth_bounds R hB hs sigma tau hRB
    change 0 < A.depth ∧ A.depth < L5A2B4AR4R2B.c1 R at hdepth
    by_cases hmu : C.data.sourceZ ≤ tau
    · have hrelA := pureC_signed_to_A_relation
        (normalizedA R) (normalizedB R) (normalizedC R)
        A.depth C.data.returnedX C.data.sourceZ tau
          (pH R + sigma) C.data.returnedY
        (Nat.le_of_lt hxd) hmu hbal
      have hc1Le := branchB_normalizedA_relation_min R _ _ _
        (Nat.sub_pos_of_lt hxd) hrelA
      omega
    · have hmuGt : tau < C.data.sourceZ := Nat.lt_of_not_ge hmu
      have hrelB := pureC_signed_to_B_relation
        (normalizedA R) (normalizedB R) (normalizedC R)
        A.depth C.data.returnedX C.data.sourceZ tau
          (pH R + sigma) C.data.returnedY
        (Nat.le_of_lt hxd) (Nat.le_of_lt hmuGt) hbal
      have hc2Le := branchB_normalizedB_relation_min R _ _ _
        (show 0 < pH R + sigma + C.data.returnedY by omega) hrelB
      have hs2 := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
      have hfloor : zH R - sigma ≤ C.data.returnedY := by
        have hzsplit : zH R = sigma + (zH R - sigma) := by omega
        rw [hs2, hzsplit] at hc2Le
        omega
      let Yval := (uH R - A.depth) * normalizedA R +
        (tau + vH R) * normalizedC R
      let kY := C.data.returnedY - (zH R - sigma)
      let gap := C.data.returnedX * normalizedA R + kY * normalizedB R
      have hk : zH R - sigma + kY = C.data.returnedY := Nat.add_sub_of_le hfloor
      have hY := branchB_strictRB_Y_value_identity R hB hs sigma tau hRB
      have hY' : A.n + (zH R - sigma) * normalizedB R = Yval := by
        simpa [Yval, Nat.add_comm] using hY
      have hsplit : C.data.sourceValue = Yval + gap := by
        rw [hactual, hreturned, ← hk, Nat.add_mul]
        calc
          A.n + (C.data.returnedX * normalizedA R +
              ((zH R - sigma) * normalizedB R + kY * normalizedB R)) =
              (A.n + (zH R - sigma) * normalizedB R) +
                (C.data.returnedX * normalizedA R + kY * normalizedB R) := by omega
          _ = Yval + gap := by rw [hY']
      have hgapH : gap ∈ normalizedH P.M.base := by
        have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R) C.data.returnedX
        have hb := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedB_mem R) kY
        simpa [gap, nsmul_eq_mul, Nat.mul_comm] using
          (normalizedH P.M.base).add_mem ha hb
      have hYmem := branchB_strictRB_Y_value_mem_returnIdeal R hB hs sigma tau hRB
      change (Yval : ℤ) ∈ returnIdeal (normalizedH P.M.base) A.n at hYmem
      have hsplitZ : (C.data.sourceValue : ℤ) = (Yval : ℤ) + gap := by
        exact_mod_cast hsplit
      have hgap0 := (RelativeIdeal.minimalGenerator_eq_of_mem_add
        (returnIdeal (normalizedH P.M.base) A.n) hmin hYmem hgapH hsplitZ).1
      have hgapPos : 0 < gap := by
        dsimp [gap]
        have hapos := strictRB_normalizedWeight_pos R 0
        have hrxpos : 0 < C.data.returnedX := Nat.pos_of_ne_zero hrx
        positivity
      exact hgapPos.ne' hgap0

/-- Complete strict-RB elimination of a chosen pure-C source route. -/
theorem branchB_strictRB_pureC_route_impossible
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  obtain ⟨hrz, hsplit⟩ := branchB_positive_center_pureC_returned_support_split
    R hB hs hroute
  rcases hsplit with ha | hb | hm
  · exact branchB_strictRB_pureC_aOnly_impossible
      R hB hs sigma tau hRB hroute ha.1 ha.2
  · exact branchB_strictRB_pureC_bOnly_impossible
      R hB hs sigma tau hRB hroute hb.1 hb.2
  · exact branchB_strictRB_pureC_mixed_impossible
      R hB hs sigma tau hRB hroute hm.1 hm.2

/-- Concrete strict-RB F packet.  This is a transparent abbreviation for
the complete actual value and canonical-coordinate data, not a family label. -/
def StrictRBActualFPacket
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (sigma tau : ℕ) : Prop :=
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  C.data.sourceValue =
      (pH R + sigma) * normalizedB R + tau * normalizedC R ∧
    C.data.returnedValue = A.depth * normalizedA R ∧
    C.source_coordinate.i = pH R + sigma ∧
    C.source_coordinate.j = tau ∧
    C.source_coordinate.level = 0 ∧
    C.returned_coordinate.i = 0 ∧
    C.returned_coordinate.j = 0 ∧
    C.returned_coordinate.level = A.depth

/-- Concrete strict-RB X packet. -/
def StrictRBActualXPacket
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (sigma tau : ℕ) : Prop :=
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
    C.returned_coordinate.level = 0

/-- Concrete strict-RB Y packet. -/
def StrictRBActualYPacket
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (sigma tau : ℕ) : Prop :=
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  C.data.sourceValue =
      (uH R - A.depth) * normalizedA R +
        (tau + vH R) * normalizedC R ∧
    C.data.returnedValue = (zH R - sigma) * normalizedB R ∧
    C.source_coordinate.i = 0 ∧
    C.source_coordinate.j = tau + vH R ∧
    C.source_coordinate.level = ((uH R - A.depth : ℕ) : ℤ) ∧
    C.returned_coordinate.i = ((zH R - sigma : ℕ) : ℤ) ∧
    C.returned_coordinate.j = 0 ∧ C.returned_coordinate.level = 0

/-- Every actual strict-RB source has one of the three complete F/X/Y
packets.  The six chosen-support routes are used only for the proof split. -/
theorem branchB_strictRB_actual_family_exhaustive
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
        1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
        A.depth < uH R) :
    StrictRBActualFPacket R hB hs sigma tau ∨
      StrictRBActualXPacket R hB hs sigma tau ∨
      StrictRBActualYPacket R hB hs sigma tau := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  obtain ⟨route, hroute⟩ :=
    branchB_selected_return_source_support_route R hB hs
  change ActualSourceSupportRoute.Matches route
    C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  cases route with
  | bc =>
      left
      exact branchB_strictRB_bc_F_packet R hB hs sigma tau
        ⟨hRB.1, hRB.2.1⟩ hroute
  | a =>
      exact False.elim
        (branchB_strictRB_a_route_impossible R hB hs sigma tau hRB hroute)
  | ab =>
      exact Or.inr (Or.inl
        (branchB_strictRB_ab_X_packet R hB hs sigma tau hRB hroute))
  | ac =>
      exact Or.inr (Or.inr
        (branchB_strictRB_ac_Y_packet R hB hs sigma tau hRB hroute))
  | pureB =>
      exact False.elim
        (branchB_strictRB_pureB_route_impossible R hB hs sigma tau hRB hroute)
  | pureC =>
      exact False.elim
        (branchB_strictRB_pureC_route_impossible R hB hs sigma tau hRB hroute)

/-- Value-level strict-RB F/X/Y trichotomy, projected from the complete
packet classifier. -/
theorem branchB_strictRB_actual_source_value_trichotomy
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
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceValue =
        (pH R + sigma) * normalizedB R + tau * normalizedC R ∨
      C.data.sourceValue =
        (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
          sigma * normalizedB R ∨
      C.data.sourceValue =
        (uH R - A.depth) * normalizedA R +
          (tau + vH R) * normalizedC R := by
  rcases branchB_strictRB_actual_family_exhaustive
      R hB hs sigma tau hRB with hF | hX | hY
  · exact Or.inl hF.1
  · exact Or.inr (Or.inl hX.1)
  · exact Or.inr (Or.inr hY.1)

/-- The selected strict-LT anchor is the F candidate value. -/
theorem branchB_strictLT_F_value_identity
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hLT :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    sigma * normalizedB R + (qH R + tau) * normalizedC R =
      A.n + normalizedA R * A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau at hLT
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, hLT.1, hLT.2] at hbeta
  have hanchor := A.anchor_eq
  rw [hbeta] at hanchor
  exact_mod_cast hanchor

/-- Exact strict-LT X source equation. -/
theorem branchB_strictLT_X_value_identity
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
    A.n + (vH R - tau) * normalizedC R =
      (wH R - A.depth) * normalizedA R +
        (sigma + zH R) * normalizedB R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change A.n + (vH R - tau) * normalizedC R =
      (wH R - A.depth) * normalizedA R +
        (sigma + zH R) * normalizedB R
  have hF := branchB_strictLT_F_value_identity R hB hs sigma tau
    ⟨hLT.1, hLT.2.1⟩
  change sigma * normalizedB R + (qH R + tau) * normalizedC R =
      A.n + normalizedA R * A.depth at hF
  have hrel := (branchB_actual_herzog_coordinates R).normalized_relations.2.2
  have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
  have htau : tau ≤ vH R := by omega
  have hdepth : A.depth ≤ wH R := by omega
  have hvsplit : vH R = tau + (vH R - tau) := by omega
  have hwsplit : wH R = A.depth + (wH R - A.depth) := by omega
  rw [hsum, hvsplit, hwsplit] at hrel
  simp only [Nat.add_mul] at hF hrel
  ring_nf at hF hrel ⊢
  omega

/-- Exact strict-LT Y source equation. -/
theorem branchB_strictLT_Y_value_identity
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
    A.n + (pH R - sigma) * normalizedB R =
      (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        tau * normalizedC R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
      1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R ∧
      A.depth < wH R at hLT
  change A.n + (pH R - sigma) * normalizedB R =
      (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R +
        tau * normalizedC R
  have hF := branchB_strictLT_F_value_identity R hB hs sigma tau
    ⟨hLT.1, hLT.2.1⟩
  change sigma * normalizedB R + (qH R + tau) * normalizedC R =
      A.n + normalizedA R * A.depth at hF
  have hrel := (branchB_actual_herzog_coordinates R).normalized_relations.1
  have hp : sigma ≤ pH R := by omega
  have hdepth : A.depth ≤ L5A2B4AR4R2B.c1 R := by
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.1
    omega
  have hpsplit : pH R = sigma + (pH R - sigma) := by omega
  have hdsplit : L5A2B4AR4R2B.c1 R =
      A.depth + (L5A2B4AR4R2B.c1 R - A.depth) := by omega
  rw [hpsplit, hdsplit] at hrel
  simp only [Nat.add_mul] at hF hrel
  ring_nf at hF hrel ⊢
  omega

end NS25Lean.L5A2B4AR5B
