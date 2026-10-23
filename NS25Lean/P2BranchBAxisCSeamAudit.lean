import NS25Lean.P2BranchBSelectedAnchorAxis

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2C4H

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Source-exact endpoint of the direct high-axis calculation.  A selected
pure-`c` seam anchor puts the pure predecessor of the completed third
critical relation in the nonprincipal prefix carrier.  This is deliberately
not stated as an active-gate contradiction: the third component is inactive
in Branch B. -/
theorem branchB_selected_return_axisC_seam_inactive_pure_prefix_mem
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (haxis :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = 0 ∧
      qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R) :
    (((L5A2B4AR4R2B.c3 R - 1) * normalizedC R : ℕ) : ℤ) ∈
      actualPrefixCarrier P.M.base := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = 0 ∧ qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R at haxis
  let j := A.coordinate.j.toNat
  have hj0 : (0 : ℤ) ≤ A.coordinate.j := by omega
  have hj : A.coordinate.j = (j : ℤ) := (Int.toNat_of_nonneg hj0).symm
  have hjlt : j < L5A2B4AR4R2B.c3 R := by
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    rw [hj] at haxis
    exact_mod_cast (show (j : ℤ) < L5A2B4AR4R2B.c3 R by omega)
  have hc3pos : 0 < L5A2B4AR4R2B.c3 R := by
    have hq := (branchB_actual_herzog_coordinates R).cross_positive.2.1
    have hv := (branchB_actual_herzog_coordinates R).cross_positive.2.2.2.1
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    omega
  have hjle : j ≤ L5A2B4AR4R2B.c3 R - 1 := by omega
  refine ⟨A.ell, A.ell_pos, A.ell_lt_principal, ?_⟩
  rw [mem_returnIdeal_iff]
  constructor
  · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    refine ⟨(L5A2B4AR4R2B.c3 R - 1) * normalizedC R, ?_, rfl⟩
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R)
        (L5A2B4AR4R2B.c3 R - 1)
  · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    let tail : ℕ := A.depth * normalizedA R +
      (L5A2B4AR4R2B.c3 R - 1 - j) * normalizedC R
    refine ⟨tail, ?_, ?_⟩
    · have ha := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedA_mem R) A.depth
      have hc := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R)
        (L5A2B4AR4R2B.c3 R - 1 - j)
      simpa [tail, nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).add_mem ha hc
    · have hn : A.n = A.ell * normalizedM P.M.base := A.n_eq
      have hanchor : (A.n : ℤ) + normalizedA R * A.depth =
          (j : ℤ) * normalizedC R := by
        simpa [hj] using haxis.2.2.2.2
      have hsplit : L5A2B4AR4R2B.c3 R - 1 =
          j + (L5A2B4AR4R2B.c3 R - 1 - j) := by omega
      have hsplitZ : ((L5A2B4AR4R2B.c3 R - 1 : ℕ) : ℤ) =
          (j : ℤ) + ((L5A2B4AR4R2B.c3 R - 1 - j : ℕ) : ℤ) := by
        exact_mod_cast hsplit
      rw [hn] at hanchor
      push_cast at hanchor ⊢
      dsimp [tail]
      rw [hsplitZ]
      ring_nf at hanchor ⊢
      linarith

/-- The exact two-Herzog balance between the inactive pure predecessor and
the active first `c`-inward predecessor.  Both added summands are positive.
The equality therefore exposes the missing cancellation/transport step; it
does not provide either direction of ideal membership by ideal closure alone. -/
theorem branchB_axisC_inactive_active_first_c_balance
    (R : SectorBCriticalRoleBranchB P) :
    (L5A2B4AR4R2B.c3 R - 1) * normalizedC R +
        uH R * normalizedA R =
      (pH R * normalizedB R + (qH R - 1) * normalizedC R) +
        zH R * normalizedB R := by
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, _hw, _hz⟩ := HC.cross_positive
  obtain ⟨_hc1, hc2, hc3⟩ := HC.coefficient_sums
  obtain ⟨_hrel1, hrel2, _hrel3⟩ := HC.normalized_relations
  have hqsplit : qH R = 1 + (qH R - 1) := by omega
  have hc3split : L5A2B4AR4R2B.c3 R - 1 =
      (qH R - 1) + vH R := by omega
  rw [hc2] at hrel2
  rw [hc3split, Nat.add_mul]
  nlinarith only [hrel2]

/-- Event-local F fallback for the residual seam.  If the chosen actual
source support were `bc`, the already-proved F value equality would turn a
strictly subcritical positive multiple of `c` into an `a,b` relation,
contradicting third critical minimality. -/
theorem branchB_selected_return_axisC_seam_F_route_impossible
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (haxis :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = 0 ∧
      qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.bc
        C.data.sourceX C.data.sourceY C.data.sourceZ) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = 0 ∧ qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R at haxis
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.bc
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hF := branchB_individual_return_F_value_pair R hB hs hroute
  change C.data.sourceValue = A.beta ∧
      C.data.returnedValue = A.depth * normalizedA R at hF
  let j := A.coordinate.j.toNat
  have hj0 : (0 : ℤ) ≤ A.coordinate.j := by omega
  have hj : A.coordinate.j = (j : ℤ) := (Int.toNat_of_nonneg hj0).symm
  have hjlt : j < L5A2B4AR4R2B.c3 R := by
    have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.2
    rw [hj] at haxis
    exact_mod_cast (show (j : ℤ) < L5A2B4AR4R2B.c3 R by omega)
  have hsourceValue : C.data.sourceValue = j * normalizedC R := by
    have hbeta : A.beta = (j : ℤ) * normalizedC R := by
      simpa [hj] using haxis.2.2.2.1
    exact_mod_cast hF.1.trans hbeta
  have hsource := C.data.source_factorization
  rw [hroute'.1, hsourceValue] at hsource
  simp only [zero_mul, zero_add] at hsource
  have hypos : 0 < C.data.sourceY := Nat.pos_of_ne_zero hroute'.2.1
  have hbpos : 0 < normalizedB R := by
    have hscale := L5A2B4AR3.normalizedWeight_scale
      P.M.base (R.reindex 1)
    have hweight := L2B.weights_positive P.M.base (R.reindex 1)
    change 0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex 1)
    nlinarith
  have hcpos : 0 < normalizedC R := by
    have hscale := L5A2B4AR3.normalizedWeight_scale
      P.M.base (R.reindex 2)
    have hweight := L2B.weights_positive P.M.base (R.reindex 2)
    change 0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex 2)
    nlinarith
  have hzmullt : C.data.sourceZ * normalizedC R < j * normalizedC R := by
    have hyprod : 0 < C.data.sourceY * normalizedB R := Nat.mul_pos hypos hbpos
    omega
  have hzlt : C.data.sourceZ < j :=
    (Nat.mul_lt_mul_right hcpos).mp hzmullt
  have hdiffpos : 0 < j - C.data.sourceZ := by omega
  have hcritical : (j - C.data.sourceZ) * normalizedC R =
      0 * normalizedA R + C.data.sourceY * normalizedB R := by
    rw [zero_mul, zero_add, Nat.sub_mul]
    omega
  have hmin := branchB_normalizedC_relation_min R
    (j - C.data.sourceZ) 0 C.data.sourceY hdiffpos hcritical
  omega

/-- The event-local support split after the only currently derivable seam
fallback is discharged.  This is a genuine five-route kernel reduction, not
a source-family classification: the remaining alternatives still require a
same-diamond lowering/transport lemma. -/
theorem branchB_selected_return_axisC_seam_nonF_support
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (haxis :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = 0 ∧
      qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
        C.data.sourceX C.data.sourceY C.data.sourceZ ∨
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ ∨
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ ∨
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ ∨
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  obtain ⟨route, hroute⟩ :=
    branchB_selected_return_source_support_route R hB hs
  cases route with
  | bc =>
      exact False.elim
        (branchB_selected_return_axisC_seam_F_route_impossible
          R hB hs haxis hroute)
  | a => exact Or.inl hroute
  | ab => exact Or.inr (Or.inl hroute)
  | ac => exact Or.inr (Or.inr (Or.inl hroute))
  | pureB => exact Or.inr (Or.inr (Or.inr (Or.inl hroute)))
  | pureC => exact Or.inr (Or.inr (Or.inr (Or.inr hroute)))

/-- B50 event-local checkpoint: the B42 source is an actual minimal source of
its individual return ideal, and the axis-`c` seam eliminates precisely the
`bc` (F) routing alternative.  No identification of routes with FOXY
families is made. -/
theorem branchB_actualZeroEdgeBirth_axisC_seam_nonF_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let A := branchB_actual_selected_return_anchor_v2 R hB hsx
      A.coordinate.i = 0 ∧
      qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hsx
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
    (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator
        (branchBActualExceptionalNormalizedSource P R x).val ∧
      (ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
          C.data.sourceX C.data.sourceY C.data.sourceZ ∨
        ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
          C.data.sourceX C.data.sourceY C.data.sourceZ ∨
        ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
          C.data.sourceX C.data.sourceY C.data.sourceZ ∨
        ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
          C.data.sourceX C.data.sourceY C.data.sourceZ ∨
        ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
          C.data.sourceX C.data.sourceY C.data.sourceZ) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hsx
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  have hprov := branchB_actualZeroEdgeBirth_individual_return_source
    R hB x hsx hbirth
  exact ⟨hprov.2.2.2.1,
    branchB_selected_return_axisC_seam_nonF_support R hB hsx haxis⟩

end NS25Lean.L5A2B4AR5B

