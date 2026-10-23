import NS25Lean.P2BranchBActualFamilyClassifier

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The selected strict-RB anchor is the F candidate value. -/
theorem branchB_strictRB_F_value_identity
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    (pH R + sigma) * normalizedB R + tau * normalizedC R =
      A.n + normalizedA R * A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau at hRB
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, hRB.1, hRB.2] at hbeta
  have hanchor := A.anchor_eq
  rw [hbeta] at hanchor
  exact_mod_cast hanchor

/-- Exact strict-RB X source equation. -/
theorem branchB_strictRB_X_value_identity
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
    A.n + (qH R - tau) * normalizedC R =
      sigma * normalizedB R +
        (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change A.n + (qH R - tau) * normalizedC R =
      sigma * normalizedB R +
        (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R
  have hF := branchB_strictRB_F_value_identity R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change (pH R + sigma) * normalizedB R + tau * normalizedC R =
      A.n + normalizedA R * A.depth at hF
  have hrel := (branchB_actual_herzog_coordinates R).normalized_relations.1
  have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.1
  have htau : tau ≤ qH R := by omega
  have hdepth : A.depth ≤ L5A2B4AR4R2B.c1 R := by omega
  have hqsplit : qH R = tau + (qH R - tau) := by omega
  have hdsplit : L5A2B4AR4R2B.c1 R =
      A.depth + (L5A2B4AR4R2B.c1 R - A.depth) := by omega
  rw [hqsplit, hdsplit] at hrel
  simp only [Nat.add_mul] at hF hrel
  ring_nf at hF hrel ⊢
  omega

/-- Exact strict-RB Y source equation. -/
theorem branchB_strictRB_Y_value_identity
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
    A.n + (zH R - sigma) * normalizedB R =
      (tau + vH R) * normalizedC R +
        (uH R - A.depth) * normalizedA R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
      1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R ∧
      A.depth < uH R at hRB
  change A.n + (zH R - sigma) * normalizedB R =
      (tau + vH R) * normalizedC R +
        (uH R - A.depth) * normalizedA R
  have hF := branchB_strictRB_F_value_identity R hB hs sigma tau
    ⟨hRB.1, hRB.2.1⟩
  change (pH R + sigma) * normalizedB R + tau * normalizedC R =
      A.n + normalizedA R * A.depth at hF
  have hrel := (branchB_actual_herzog_coordinates R).normalized_relations.2.1
  have hsum := (branchB_actual_herzog_coordinates R).coefficient_sums.2.1
  have hsigma : sigma ≤ zH R := by omega
  have hdepth : A.depth ≤ uH R := by omega
  have hzsplit : zH R = sigma + (zH R - sigma) := by omega
  have husplit : uH R = A.depth + (uH R - A.depth) := by omega
  rw [hsum, hzsplit, husplit] at hrel
  simp only [Nat.add_mul] at hF hrel
  ring_nf at hF hrel ⊢
  omega

/-- On the actual `bc` support route, a strict-RB return has the genuine F
source packet.  The route only selects the already-proved value theorem;
the numeric and canonical equalities are recovered independently. -/
theorem branchB_strictRB_bc_F_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (sigma tau : ℕ)
    (hRB :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.bc
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
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
      C.returned_coordinate.level = A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau at hRB
  have hvalues := branchB_individual_return_F_value_pair R hB hs hroute
  have hcanonical := branchB_individual_return_F_canonical_packet R hB hs hroute
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, hRB.1, hRB.2] at hbeta
  have hsourceZ : (C.data.sourceValue : ℤ) =
      (pH R + sigma) * normalizedB R + tau * normalizedC R :=
    hvalues.1.trans hbeta
  refine ⟨by exact_mod_cast hsourceZ, hvalues.2, ?_⟩
  exact ⟨hcanonical.1.trans hRB.1, hcanonical.2.1.trans hRB.2,
    hcanonical.2.2.1.trans hlevel, hcanonical.2.2.2.2.1,
    hcanonical.2.2.2.2.2.1, hcanonical.2.2.2.2.2.2⟩

end NS25Lean.L5A2B4AR5B
