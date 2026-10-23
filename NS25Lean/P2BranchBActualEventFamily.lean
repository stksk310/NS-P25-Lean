import NS25Lean.P2BranchBActualZeroEdgeBSP

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open L5A1 L5A2B4AR1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The B42 actual source is a minimal source of the canonical individual
return ideal.  This is the event-local form of the repaired M2 provenance
bridge; the source is not identified with the selected Apéry anchor. -/
theorem branchB_actualZeroEdgeBirth_individual_return_source
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (_hbirth : IsActualZeroEdgeBirth R x hsx) :
    let s := branchBActualExceptionalNormalizedSource P R x
    let A := branchB_actual_selected_return_anchor_v2 R hB hsx
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
    0 < A.ell ∧ A.ell < actualPrincipalIndex P.M.base ∧
      A.n = A.ell * normalizedM P.M.base ∧
      (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator s.val ∧
      (C.data.sourceValue : ℤ) = s.val ∧
      C.source_coordinate.level * normalizedA R +
          C.source_coordinate.i * normalizedB R +
          C.source_coordinate.j * normalizedC R = s.val := by
  let s := branchBActualExceptionalNormalizedSource P R x
  let A := branchB_actual_selected_return_anchor_v2 R hB hsx
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  exact ⟨A.ell_pos, A.ell_lt_principal, A.n_eq, A.source_minimal,
    C.data.source_eq, C.source_coordinate.exact_eq.symm.trans C.data.source_eq⟩

/-- Exact event-local finite symbolic matrix supplied by the corrected M2/M3
API: five anchor regions and six actual-source support routes.  This theorem
keeps the selected anchor and actual source separate and adds no family tag. -/
theorem branchB_actualZeroEdgeBirth_anchor_support_matrix
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (_hbirth : IsActualZeroEdgeBirth R x hsx) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hsx
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
    (InActualPositiveReturnClass R A.coordinate.i A.coordinate.j ∨
      (A.coordinate.i = 0 ∧
        1 ≤ A.coordinate.j ∧ A.coordinate.j < qH R + vH R ∧
        A.beta = A.coordinate.j * normalizedC R ∧
        (A.n : ℤ) + normalizedA R * A.depth =
          A.coordinate.j * normalizedC R) ∨
      (A.coordinate.j = 0 ∧
        1 ≤ A.coordinate.i ∧ A.coordinate.i < pH R + zH R ∧
        A.beta = A.coordinate.i * normalizedB R ∧
        (A.n : ℤ) + normalizedA R * A.depth =
          A.coordinate.i * normalizedB R)) ∧
    ∃ route : ActualSourceSupportRoute,
      ActualSourceSupportRoute.Matches route
        C.data.sourceX C.data.sourceY C.data.sourceZ := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hsx
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  exact ⟨branchB_selected_return_exact_positive_class_or_axis_v2 R hB hsx,
    branchB_selected_return_source_support_route R hB hsx⟩

/-- Positive CENTER is source-exactly reduced to the four existing canonical
F/O/X/Y packets, except for the explicit boundary cells.  The latter are
retained (rather than declared impossible): pure-axis routes and the two
outer-edge route cells are exactly the boundary-axis frontier. -/
theorem branchB_positive_center_core_family_or_pure_axis
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
        C.returned_coordinate.j = 0 ∧ C.returned_coordinate.level = 0) ∨
      (ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
          C.data.sourceX C.data.sourceY C.data.sourceZ ∨
        ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
          C.data.sourceX C.data.sourceY C.data.sourceZ ∨
        (i = pH R ∧ ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
          C.data.sourceX C.data.sourceY C.data.sourceZ) ∨
        (j = qH R ∧ ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
          C.data.sourceX C.data.sourceY C.data.sourceZ))) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  refine ⟨C.data.source_eq, ?_⟩
  obtain ⟨route, hroute⟩ := branchB_selected_return_source_support_route R hB hs
  rcases route with _ | _ | _ | _ | _ | _
  · exact Or.inl (branchB_individual_return_F_canonical_packet R hB hs hroute)
  · exact Or.inr (Or.inl
      (branchB_individual_return_center_O_canonical_packet R hB hs i j hcenter hroute))
  · by_cases hi : i < pH R
    · exact Or.inr (Or.inr (Or.inl ⟨hi,
        branchB_individual_return_center_X_canonical_packet R hB hs i j
          ⟨hcenter.1, hcenter.2.1, hcenter.2.2.1, hi,
            hcenter.2.2.2.2.1, hcenter.2.2.2.2.2.1⟩ hroute⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨by omega, hroute⟩))))))
  · by_cases hj : j < qH R
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hj,
        branchB_individual_return_center_Y_canonical_packet R hB hs i j
          ⟨hcenter.1, hcenter.2.1, hcenter.2.2.1,
            hcenter.2.2.2.1, hcenter.2.2.2.2.1, hj⟩ hroute⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr ⟨by omega, hroute⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hroute))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hroute)))))

/-- Strongest source-complete checkpoint currently derivable for the concrete
B42 event.  CENTER core cells carry canonical packets; every remaining cell
is retained source-exactly as a strict-arm or boundary-axis frontier. -/
theorem branchB_actualZeroEdgeBirth_source_complete_frontier
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
    ((∃ i j : ℕ,
        A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R) ∧
        (C.data.sourceValue : ℤ) =
          (branchBActualExceptionalNormalizedSource P R x).val) ∨
      (∃ route, ActualSourceSupportRoute.Matches route
          C.data.sourceX C.data.sourceY C.data.sourceZ ∧
        ((∃ sigma tau : ℕ,
            A.coordinate.i = pH R + sigma ∧ A.coordinate.j = tau ∧
            1 ≤ sigma ∧ sigma < zH R ∧ 1 ≤ tau ∧ tau < qH R) ∨
          (∃ sigma tau : ℕ,
            A.coordinate.i = sigma ∧ A.coordinate.j = qH R + tau ∧
            1 ≤ sigma ∧ sigma < pH R ∧ 1 ≤ tau ∧ tau < vH R) ∨
          A.coordinate.i = 0 ∨ A.coordinate.j = 0))) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hsx
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  have hprov := branchB_actualZeroEdgeBirth_individual_return_source
    R hB x hsx hbirth
  refine ⟨hprov.2.2.2.1, ?_⟩
  obtain ⟨hclass, route, hroute⟩ :=
    branchB_actualZeroEdgeBirth_anchor_support_matrix R hB x hsx hbirth
  rcases hclass with hpos | haxisC | haxisB
  · rcases hpos with hcenter | hRB | hLT
    · obtain ⟨i, j, hi, hj, hi0, hip, hj0, hjq, hcorner⟩ := hcenter
      exact Or.inl ⟨i, j, hi, hj, hi0, hip, hj0, hjq, hcorner, C.data.source_eq⟩
    · exact Or.inr ⟨route, hroute, Or.inl hRB⟩
    · exact Or.inr ⟨route, hroute, Or.inr (Or.inl hLT)⟩
  · exact Or.inr ⟨route, hroute, Or.inr (Or.inr (Or.inl haxisC.1))⟩
  · exact Or.inr ⟨route, hroute, Or.inr (Or.inr (Or.inr haxisB.1))⟩

end NS25Lean.L5A2B4AR5B
