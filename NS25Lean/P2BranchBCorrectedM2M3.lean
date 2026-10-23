import NS25Lean.P2BranchBFOXYV2

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open L5A1 L5A2B4AR1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The exact three positive-coordinate regions used by the corrected M2/M3
route.  This deliberately contains no depth bound or source-family premise. -/
def InActualPositiveReturnClass
    (R : SectorBCriticalRoleBranchB P) (i j : ℤ) : Prop :=
  (∃ x y : ℕ,
      i = x ∧ j = y ∧
      1 ≤ x ∧ x ≤ pH R ∧ 1 ≤ y ∧ y ≤ qH R ∧
      (x, y) ≠ (pH R, qH R)) ∨
  (∃ s tau : ℕ,
      i = pH R + s ∧ j = tau ∧
      1 ≤ s ∧ s < zH R ∧ 1 ≤ tau ∧ tau < qH R) ∨
  (∃ s tau : ℕ,
      i = s ∧ j = qH R + tau ∧
      1 ≤ s ∧ s < pH R ∧ 1 ≤ tau ∧ tau < vH R)

/-- A positive selected anchor has exactly one of the corrected CENTER,
strict-RB, or strict-LT parameter shapes.  Boundary equality with `pH` or
`qH` is retained in CENTER, and the forbidden inner corner is excluded by
the actual L-shape. -/
theorem branchB_selected_return_exact_positive_class_v2
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (hpos :
      1 ≤ (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.i ∧
      1 ≤ (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.j) :
    InActualPositiveReturnClass R
      (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.i
      (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.j := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change 1 ≤ A.coordinate.i ∧ 1 ≤ A.coordinate.j at hpos
  change InActualPositiveReturnClass R A.coordinate.i A.coordinate.j
  rcases A.coordinate.in_lShape with ⟨hi0, hj0, hibound, hjbound, hcorner⟩
  let i := A.coordinate.i.toNat
  let j := A.coordinate.j.toNat
  have hi : (i : ℤ) = A.coordinate.i := Int.toNat_of_nonneg hi0
  have hj : (j : ℤ) = A.coordinate.j := Int.toNat_of_nonneg hj0
  by_cases hip : i ≤ pH R
  · by_cases hjq : j ≤ qH R
    · left
      refine ⟨i, j, hi.symm, hj.symm, ?_, hip, ?_, hjq, ?_⟩
      · omega
      · omega
      · intro hcornerEq
        have hieq := congrArg Prod.fst hcornerEq
        have hjeq := congrArg Prod.snd hcornerEq
        omega
    · right
      right
      let tau := j - qH R
      refine ⟨i, tau, hi.symm, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · have hilt : A.coordinate.i < pH R := hcorner.resolve_right (by omega)
        omega
      · omega
      · omega
  · right
    left
    let sigma := i - pH R
    refine ⟨sigma, j, ?_, hj.symm, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · omega
    · have hjlt : A.coordinate.j < qH R := hcorner.resolve_left (by omega)
      omega

/-- Strongest axis-honest return-class checkpoint: the selected anchor is in
one of the three exact positive regions, or it is one of the two source-exact
axis obstructions with its full fourth-generator return equation retained. -/
theorem branchB_selected_return_exact_positive_class_or_axis_v2
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    InActualPositiveReturnClass R A.coordinate.i A.coordinate.j ∨
      (A.coordinate.i = 0 ∧
        1 ≤ A.coordinate.j ∧ A.coordinate.j < qH R + vH R ∧
        A.beta = A.coordinate.j * normalizedC R ∧
        (A.n : ℤ) + normalizedA R * A.depth =
          A.coordinate.j * normalizedC R) ∨
      (A.coordinate.j = 0 ∧
        1 ≤ A.coordinate.i ∧ A.coordinate.i < pH R + zH R ∧
        A.beta = A.coordinate.i * normalizedB R ∧
        (A.n : ℤ) + normalizedA R * A.depth =
          A.coordinate.i * normalizedB R) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  have h := branchB_selected_return_anchor_positive_or_axis_obstruction R hB hs
  change (1 ≤ A.coordinate.i ∧ 1 ≤ A.coordinate.j) ∨ _ ∨ _ at h
  rcases h with hpos | haxisC | haxisB
  · exact Or.inl (branchB_selected_return_exact_positive_class_v2 R hB hs hpos)
  · exact Or.inr (Or.inl haxisC)
  · exact Or.inr (Or.inr haxisB)

/-- Exact balance between the actual source/returned factorizations and the
independently selected Apéry anchor.  It is the first load-bearing equality
needed for F/O/X/Y completeness and does not identify source with anchor. -/
theorem branchB_actual_source_anchor_balance_v2
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.ell = A.ell ∧
      (C.data.sourceValue : ℤ) + normalizedA R * A.depth =
        C.data.returnedValue + A.beta ∧
      ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R +
          C.data.sourceY * normalizedB R + C.data.sourceZ * normalizedC R =
        C.data.returnedX * normalizedA R +
          C.data.returnedY * normalizedB R +
          C.data.returnedZ * normalizedC R +
          A.coordinate.i * normalizedB R +
          A.coordinate.j * normalizedC R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  have hell : C.data.ell = A.ell := by
    rfl
  have hn : A.n = C.data.ell * normalizedM P.M.base := by
    rw [A.n_eq, hell]
  have hsource : (C.data.sourceValue : ℤ) = s := C.data.source_eq
  have hreturned : (C.data.returnedValue : ℤ) =
      s - (C.data.ell * normalizedM P.M.base : ℕ) := C.data.returned_eq
  have hbalance : (C.data.sourceValue : ℤ) + normalizedA R * A.depth =
      C.data.returnedValue + A.beta := by
    rw [A.anchor_eq]
    push_cast at hn hsource hreturned ⊢
    omega
  have hsourceFactor := congrArg (fun n : ℕ => (n : ℤ)) C.data.source_factorization
  have hreturnedFactor := congrArg (fun n : ℕ => (n : ℤ)) C.data.returned_factorization
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add] at hbeta
  refine ⟨hell, hbalance, ?_⟩
  push_cast at hsourceFactor hreturnedFactor
  rw [hsourceFactor, hreturnedFactor, hbeta] at hbalance
  change ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R +
      C.data.sourceY * normalizedB R + C.data.sourceZ * normalizedC R = _
  calc
    ((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R +
          C.data.sourceY * normalizedB R + C.data.sourceZ * normalizedC R =
        C.data.sourceX * normalizedA R +
          C.data.sourceY * normalizedB R + C.data.sourceZ * normalizedC R +
          normalizedA R * A.depth := by push_cast; ring
    _ = C.data.returnedX * normalizedA R +
          C.data.returnedY * normalizedB R +
          C.data.returnedZ * normalizedC R +
          (A.coordinate.i * normalizedB R +
            A.coordinate.j * normalizedC R) := hbalance
    _ = C.data.returnedX * normalizedA R +
          C.data.returnedY * normalizedB R +
          C.data.returnedZ * normalizedC R +
          A.coordinate.i * normalizedB R +
          A.coordinate.j * normalizedC R := by ring

/-- The independently selected Apéry anchor is an actual element of the same
individual return ideal in which the BranchBirth source is minimal.  This is
the strongest source-exact connection available without identifying the source
with the anchor or assuming uniqueness of return provenance. -/
theorem branchB_selected_return_anchor_mem_returnIdeal
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    A.beta ∈ returnIdeal (normalizedH P.M.base) A.n := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  change A.beta ∈ (normalizedH P.M.base).asRelativeIdeal ∧
    A.beta - (A.n : ℕ) ∈ (normalizedH P.M.base).asRelativeIdeal
  refine ⟨A.beta_mem, ?_⟩
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
  refine ⟨normalizedA R * A.depth, ?_, ?_⟩
  · simpa [nsmul_eq_mul, Nat.mul_comm] using
      (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedA_mem R) A.depth
  · rw [A.anchor_eq]
    push_cast
    ring

/-- Exact same-return-ideal checkpoint for the actual minimal source and the
selected anchor.  In the two axis alternatives it retains the pure-axis
coordinate, its sharp range, and the fourth-generator return equation. -/
theorem branchB_selected_return_source_anchor_same_ideal_or_axis
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    (returnIdeal (normalizedH P.M.base) A.n).IsMinimalGenerator s ∧
      A.beta ∈ returnIdeal (normalizedH P.M.base) A.n ∧
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
            A.coordinate.i * normalizedB R)) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  exact ⟨A.source_minimal,
    branchB_selected_return_anchor_mem_returnIdeal R hB hs,
    branchB_selected_return_exact_positive_class_or_axis_v2 R hB hs⟩

/-- If a minimal generator of an individual return ideal and its returned
value both contain the same nonzero semigroup generator, subtracting that
generator produces a predecessor in the same return ideal. -/
private theorem minimal_return_common_generator_impossible
    (H : NumericalSemigroup) {n g x y : ℕ} {s : ℤ}
    (hmin : (returnIdeal H n).IsMinimalGenerator s)
    (hgH : g ∈ H) (hg0 : g ≠ 0) (hxH : x ∈ H) (hyH : y ∈ H)
    (hsource : s = (g : ℤ) + x)
    (hreturned : s - (n : ℕ) = (g : ℤ) + y) : False := by
  apply hmin.2 g hgH hg0
  change s - (g : ℤ) ∈ H.asRelativeIdeal ∧
    (s - (g : ℤ)) - (n : ℕ) ∈ H.asRelativeIdeal
  constructor
  · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨x, hxH, by omega⟩
  · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨y, hyH, by omega⟩

private theorem branchB_actual_normalizedWeight_pos
    (R : SectorBCriticalRoleBranchB P) (k : Fin 3) :
    0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex k) := by
  have hs := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex k)
  have hw := L2B.weights_positive P.M.base (R.reindex k)
  nlinarith

/-- Actual source/returned sign-corner.  For each normalized generator, at
least one of the two chosen factorizations has zero coefficient. -/
theorem branchB_selected_return_source_returned_sign_corner
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (C.data.sourceX = 0 ∨ C.data.returnedX = 0) ∧
      (C.data.sourceY = 0 ∨ C.data.returnedY = 0) ∧
      (C.data.sourceZ = 0 ∨ C.data.returnedZ = 0) := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz
  have hmin : (returnIdeal H
      (C.data.ell * normalizedM P.M.base)).IsMinimalGenerator s :=
    C.data.return_witness.2.2
  have split_mul {k w : ℕ} (hk : k ≠ 0) :
      k * w = w + (k - 1) * w := by
    have hsplit : k = k - 1 + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)).symm
    calc
      k * w = (k - 1 + 1) * w := congrArg (fun t : ℕ => t * w) hsplit
      _ = w + (k - 1) * w := by simp [Nat.add_mul, Nat.add_comm]
  have contradict (g sourceRest returnedRest : ℕ)
      (hgH : g ∈ H) (hgpos : 0 < g)
      (hsourceRest : sourceRest ∈ H) (hreturnedRest : returnedRest ∈ H)
      (hsourceSplit : C.data.sourceValue = g + sourceRest)
      (hreturnedSplit : C.data.returnedValue = g + returnedRest) : False := by
    apply minimal_return_common_generator_impossible H hmin hgH hgpos.ne'
      hsourceRest hreturnedRest
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (g : ℤ) + sourceRest := by exact_mod_cast hsourceSplit
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (g : ℤ) + returnedRest := by exact_mod_cast hreturnedSplit
  constructor
  · by_cases hsx : C.data.sourceX = 0
    · exact Or.inl hsx
    by_cases hrx : C.data.returnedX = 0
    · exact Or.inr hrx
    exfalso
    let sourceRest := (C.data.sourceX - 1) * normalizedA R +
      C.data.sourceY * normalizedB R + C.data.sourceZ * normalizedC R
    let returnedRest := (C.data.returnedX - 1) * normalizedA R +
      C.data.returnedY * normalizedB R + C.data.returnedZ * normalizedC R
    apply contradict (normalizedA R) sourceRest returnedRest
      (branchB_actual_normalizedA_mem R) (branchB_actual_normalizedA_pos R)
      (hcomb _ _ _) (hcomb _ _ _)
    · dsimp [sourceRest]
      rw [C.data.source_factorization]
      rw [split_mul hsx]
      omega
    · dsimp [returnedRest]
      rw [C.data.returned_factorization]
      rw [split_mul hrx]
      omega
  constructor
  · by_cases hsy : C.data.sourceY = 0
    · exact Or.inl hsy
    by_cases hry : C.data.returnedY = 0
    · exact Or.inr hry
    exfalso
    let sourceRest := C.data.sourceX * normalizedA R +
      (C.data.sourceY - 1) * normalizedB R + C.data.sourceZ * normalizedC R
    let returnedRest := C.data.returnedX * normalizedA R +
      (C.data.returnedY - 1) * normalizedB R + C.data.returnedZ * normalizedC R
    apply contradict (normalizedB R) sourceRest returnedRest
      (branchB_actual_normalizedB_mem R)
      (branchB_actual_normalizedWeight_pos R 1)
      (hcomb _ _ _) (hcomb _ _ _)
    · dsimp [sourceRest]
      rw [C.data.source_factorization]
      rw [split_mul hsy]
      omega
    · dsimp [returnedRest]
      rw [C.data.returned_factorization]
      rw [split_mul hry]
      omega
  · by_cases hsz : C.data.sourceZ = 0
    · exact Or.inl hsz
    by_cases hrz : C.data.returnedZ = 0
    · exact Or.inr hrz
    exfalso
    let sourceRest := C.data.sourceX * normalizedA R +
      C.data.sourceY * normalizedB R + (C.data.sourceZ - 1) * normalizedC R
    let returnedRest := C.data.returnedX * normalizedA R +
      C.data.returnedY * normalizedB R + (C.data.returnedZ - 1) * normalizedC R
    apply contradict (normalizedC R) sourceRest returnedRest
      (branchB_actual_normalizedC_mem R)
      (branchB_actual_normalizedWeight_pos R 2)
      (hcomb _ _ _) (hcomb _ _ _)
    · dsimp [sourceRest]
      rw [C.data.source_factorization]
      rw [split_mul hsz]
      omega
    · dsimp [returnedRest]
      rw [C.data.returned_factorization]
      rw [split_mul hrz]
      omega

/-- Integer coefficient balance for the actual source/returned pair relative
to the independently selected return anchor.  Together with the three
sign-corners and the anchor L-shape condition, this is the source-exact
algebraic input for the finite symbolic F/O/X/Y classification; no source is
identified with the anchor. -/
theorem branchB_selected_return_source_balance_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    ((C.data.sourceX = 0 ∨ C.data.returnedX = 0) ∧
        (C.data.sourceY = 0 ∨ C.data.returnedY = 0) ∧
        (C.data.sourceZ = 0 ∨ C.data.returnedZ = 0)) ∧
      ((((C.data.sourceX : ℤ) + A.depth - C.data.returnedX) *
            normalizedA R) +
          (((C.data.sourceY : ℤ) - C.data.returnedY - A.coordinate.i) *
            normalizedB R) +
          (((C.data.sourceZ : ℤ) - C.data.returnedZ - A.coordinate.j) *
            normalizedC R) = 0) ∧
      L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
        A.coordinate.i A.coordinate.j := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  have hcorner :=
    branchB_selected_return_source_returned_sign_corner R hB hs
  have hweighted := (branchB_actual_source_anchor_balance_v2 R hB hs).2.2
  refine ⟨hcorner, ?_, A.coordinate.in_lShape⟩
  push_cast at hweighted ⊢
  linear_combination hweighted

/-- Nonzero and exact-value packet for the selected individual return. -/
theorem branchB_selected_return_nonzero_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    0 < C.data.ell ∧ C.data.ell < actualPrincipalIndex P.M.base ∧
      A.n ∉ normalizedH P.M.base ∧ C.data.sourceValue ≠ 0 ∧
      C.data.returnedValue ≠ 0 ∧
      C.data.sourceValue = A.n + C.data.returnedValue := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  have hell : C.data.ell = A.ell :=
    (branchB_actual_source_anchor_balance_v2 R hB hs).1
  have hn : A.n = C.data.ell * normalizedM P.M.base := by
    rw [A.n_eq, ← hell]
  have hvalueZ : (C.data.sourceValue : ℤ) =
      A.n + C.data.returnedValue := by
    rw [C.data.source_eq, C.data.returned_eq, hn]
    omega
  have hvalue : C.data.sourceValue = A.n + C.data.returnedValue := by
    exact_mod_cast hvalueZ
  have hn0 : A.n ≠ 0 := by
    intro hzero
    apply A.n_not_mem
    simpa [hzero] using (normalizedH P.M.base).zero_mem
  have hsource0 : C.data.sourceValue ≠ 0 := by
    intro hzero
    rw [hzero] at hvalue
    omega
  have hreturned0 : C.data.returnedValue ≠ 0 := by
    intro hzero
    have hsourceN : C.data.sourceValue = A.n := by simpa [hzero] using hvalue
    apply A.n_not_mem
    rw [← hsourceN]
    exact C.data.source_mem
  exact ⟨A.ell_pos, A.ell_lt_principal, A.n_not_mem,
    hsource0, hreturned0, hvalue⟩

inductive ActualSourceSupportRoute where
  | bc | a | ab | ac | pureB | pureC
  deriving DecidableEq

def ActualSourceSupportRoute.Matches (route : ActualSourceSupportRoute)
    (x y z : ℕ) : Prop :=
  match route with
  | .bc => x = 0 ∧ y ≠ 0 ∧ z ≠ 0
  | .a => x ≠ 0 ∧ y = 0 ∧ z = 0
  | .ab => x ≠ 0 ∧ y ≠ 0 ∧ z = 0
  | .ac => x ≠ 0 ∧ y = 0 ∧ z ≠ 0
  | .pureB => x = 0 ∧ y ≠ 0 ∧ z = 0
  | .pureC => x = 0 ∧ y = 0 ∧ z ≠ 0

/-- The arbitrary chosen source factorization is used only as a six-way
routing device.  The zero and full-support cases are excluded by the actual
nonzero values and the sign-corner, respectively. -/
theorem branchB_selected_return_source_support_route
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    ∃ route : ActualSourceSupportRoute,
      ActualSourceSupportRoute.Matches route
        C.data.sourceX C.data.sourceY C.data.sourceZ := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  have hsource0 := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.1
  have hreturned0 := (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.1
  have hcorner := branchB_selected_return_source_returned_sign_corner R hB hs
  by_cases hx : C.data.sourceX = 0
  · by_cases hy : C.data.sourceY = 0
    · by_cases hz : C.data.sourceZ = 0
      · exfalso
        apply hsource0
        rw [C.data.source_factorization, hx, hy, hz]
        simp
      · exact ⟨ActualSourceSupportRoute.pureC, hx, hy, hz⟩
    · by_cases hz : C.data.sourceZ = 0
      · exact ⟨ActualSourceSupportRoute.pureB, hx, hy, hz⟩
      · exact ⟨ActualSourceSupportRoute.bc, hx, hy, hz⟩
  · by_cases hy : C.data.sourceY = 0
    · by_cases hz : C.data.sourceZ = 0
      · exact ⟨ActualSourceSupportRoute.a, hx, hy, hz⟩
      · exact ⟨ActualSourceSupportRoute.ac, hx, hy, hz⟩
    · by_cases hz : C.data.sourceZ = 0
      · exact ⟨ActualSourceSupportRoute.ab, hx, hy, hz⟩
      · exfalso
        have hrx : C.data.returnedX = 0 := hcorner.1.resolve_left hx
        have hry : C.data.returnedY = 0 := hcorner.2.1.resolve_left hy
        have hrz : C.data.returnedZ = 0 := hcorner.2.2.resolve_left hz
        apply hreturned0
        rw [C.data.returned_factorization, hrx, hry, hrz]
        simp

/-- On the two-axis source route, the actual source is the selected Apéry
anchor and its complementary return is exactly the anchor depth on the
`a`-axis.  The chosen coefficients are used only to expose the support; the
value identification follows from Apéry leastness and source minimality. -/
theorem branchB_individual_return_F_value_pair
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.bc
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceValue = A.beta ∧
      C.data.returnedValue = A.depth * normalizedA R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches, C] using hroute
  have hcorner := branchB_selected_return_source_returned_sign_corner R hB hs
  have hry : C.data.returnedY = 0 := hcorner.2.1.resolve_left hroute'.2.1
  have hrz : C.data.returnedZ = 0 := hcorner.2.2.resolve_left hroute'.2.2
  have hreturned : C.data.returnedValue =
      C.data.returnedX * normalizedA R := by
    rw [C.data.returned_factorization, hry, hrz]
    omega
  have hsource : C.data.sourceValue =
      A.n + C.data.returnedX * normalizedA R := by
    rw [(branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2,
      hreturned]
  letI : NeZero (normalizedA R) :=
    ⟨(branchB_actual_normalizedA_pos R).ne'⟩
  have hsourceRel : (C.data.sourceValue : ℤ) ∈
      (normalizedH P.M.base).asRelativeIdeal := by
    rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
    exact ⟨C.data.sourceValue, C.data.source_mem, rfl⟩
  have hsourceMod : ((C.data.sourceValue : ℤ) : ZMod (normalizedA R)) =
      (A.n : ZMod (normalizedA R)) := by
    rw [Int.cast_natCast]
    have hcast := congrArg
      (fun t : ℕ => (t : ZMod (normalizedA R))) hsource
    simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
      mul_zero, add_zero] using hcast
  have hbetaDef : A.beta =
      (normalizedH P.M.base).asRelativeIdeal.aperyRepresentative
        (normalizedA R) (A.n : ZMod (normalizedA R)) := by
    rw [A.beta_eq]
    simp only [branchBSelectedReturnAnchor, branchBSelectedReturnLevel]
    rw [A.n_eq, A.ell_eq]
  have hbetaLe : A.beta ≤ (C.data.sourceValue : ℤ) := by
    rw [hbetaDef]
    exact (normalizedH P.M.base).asRelativeIdeal.aperyRepresentative_le
      (normalizedA R) (A.n : ZMod (normalizedA R)) hsourceRel hsourceMod
  have hdepthLe : A.depth ≤ C.data.returnedX := by
    have ha := branchB_actual_normalizedA_pos R
    rw [A.anchor_eq] at hbetaLe
    push_cast at hbetaLe
    exact_mod_cast (show (A.depth : ℤ) ≤ C.data.returnedX by nlinarith)
  have hrx : C.data.returnedX = A.depth := by
    by_contra hne
    have hlt : A.depth < C.data.returnedX :=
      lt_of_le_of_ne hdepthLe (Ne.symm hne)
    let g := (C.data.returnedX - A.depth) * normalizedA R
    have hg0 : g ≠ 0 := by
      have ha := branchB_actual_normalizedA_pos R
      dsimp [g]
      exact Nat.mul_ne_zero (Nat.sub_ne_zero_of_lt hlt) ha.ne'
    have hgH : g ∈ normalizedH P.M.base := by
      dsimp [g]
      simpa [nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R)
          (C.data.returnedX - A.depth)
    have hsub : s - (g : ℕ) = A.beta := by
      have hsourceZ : (C.data.sourceValue : ℤ) =
          A.n + C.data.returnedX * normalizedA R := by
        exact_mod_cast hsource
      calc
        s - (g : ℕ) = (C.data.sourceValue : ℤ) - (g : ℕ) := by
          exact congrArg (fun z : ℤ => z - (g : ℕ)) C.data.source_eq.symm
        _ = A.beta := by
          rw [hsourceZ, A.anchor_eq]
          dsimp [g]
          have hcastSub : ((C.data.returnedX - A.depth : ℕ) : ℤ) =
              C.data.returnedX - A.depth := Nat.cast_sub hdepthLe
          rw [hcastSub]
          ring
    apply (A.source_minimal.2 g hgH hg0)
    rw [hsub]
    exact branchB_selected_return_anchor_mem_returnIdeal R hB hs
  constructor
  · have hsourceZ : (C.data.sourceValue : ℤ) =
        A.n + C.data.returnedX * normalizedA R := by
      exact_mod_cast hsource
    calc
      (C.data.sourceValue : ℤ) =
          A.n + C.data.returnedX * normalizedA R := hsourceZ
      _ = A.beta := by rw [hrx, A.anchor_eq]; push_cast; ring
  · rw [hreturned, hrx, Nat.mul_comm]

/-- Family-local CENTER-O value identification.  The CENTER bounds and the
actual `a`-support route force the depth inequality used by O; no global
chart-depth theorem is assumed. -/
theorem branchB_individual_return_center_O_value_pair
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
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    A.depth < L5A2B4AR4R2B.c1 R ∧
      C.data.sourceValue =
        (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R ∧
      C.data.returnedValue =
        (pH R - i) * normalizedB R + (qH R - j) * normalizedC R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hsign := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hsign.1.resolve_left hroute'.1
  have hbalance := (branchB_selected_return_source_balance_packet R hB hs).2.1
  have hcriticalZ :
      (((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R) =
        ((C.data.returnedY + i : ℕ) : ℤ) * normalizedB R +
          ((C.data.returnedZ + j : ℕ) : ℤ) * normalizedC R := by
    rw [hroute'.2.1, hroute'.2.2, hrx, hi, hj] at hbalance
    push_cast at hbalance ⊢
    nlinarith
  have hcritical :
      (C.data.sourceX + A.depth) * normalizedA R =
        (C.data.returnedY + i) * normalizedB R +
          (C.data.returnedZ + j) * normalizedC R := by
    exact_mod_cast hcriticalZ
  have hqpos : 0 < C.data.sourceX + A.depth := by omega
  have hmin : L5A2B4AR4R2B.c1 R ≤ C.data.sourceX + A.depth :=
    branchB_normalizedA_relation_min R _ _ _ hqpos hcritical
  let HC := branchB_actual_herzog_coordinates R
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have hlevel := branchB_selected_return_anchor_level_zero R hB hs
  have hbeta := A.coordinate.exact_eq
  rw [hlevel, zero_mul, zero_add, hi, hj] at hbeta
  have hanchor := A.anchor_eq
  rw [hbeta] at hanchor
  have hnpos : 0 < A.n := by
    have hn0 : A.n ≠ 0 := by
      intro hn
      apply A.n_not_mem
      simpa [hn] using (normalizedH P.M.base).zero_mem
    exact Nat.pos_of_ne_zero hn0
  have hanchorNat :
      i * normalizedB R + j * normalizedC R =
        A.n + normalizedA R * A.depth := by
    exact_mod_cast hanchor
  rw [Nat.mul_comm (normalizedA R) A.depth] at hanchorNat
  have hdepth : A.depth < L5A2B4AR4R2B.c1 R := by
    by_contra hnot
    have hdge : L5A2B4AR4R2B.c1 R ≤ A.depth := Nat.le_of_not_gt hnot
    have hda : L5A2B4AR4R2B.c1 R * normalizedA R ≤
        A.depth * normalizedA R := Nat.mul_le_mul_right _ hdge
    have hib : i * normalizedB R ≤ pH R * normalizedB R :=
      Nat.mul_le_mul_right _ hiLe
    have hjc : j * normalizedC R ≤ qH R * normalizedC R :=
      Nat.mul_le_mul_right _ hjLe
    omega
  have hbaseLe : L5A2B4AR4R2B.c1 R - A.depth ≤ C.data.sourceX := by
    omega
  let sourceCandidate :=
    (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R
  let returnedCandidate :=
    (pH R - i) * normalizedB R + (qH R - j) * normalizedC R
  have hcandidate : sourceCandidate = A.n + returnedCandidate := by
    have hA : sourceCandidate + normalizedA R * A.depth =
        L5A2B4AR4R2B.c1 R * normalizedA R := by
      dsimp [sourceCandidate]
      rw [Nat.mul_comm (normalizedA R) A.depth, ← Nat.add_mul,
        Nat.sub_add_cancel (Nat.le_of_lt hdepth)]
    have hB : (pH R - i) * normalizedB R + i * normalizedB R =
        pH R * normalizedB R := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hiLe]
    have hC : (qH R - j) * normalizedC R + j * normalizedC R =
        qH R * normalizedC R := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hjLe]
    dsimp [returnedCandidate]
    omega
  have hcandidateZ : (sourceCandidate : ℤ) =
      A.n + returnedCandidate := by
    exact_mod_cast hcandidate
  have hsource : C.data.sourceValue = C.data.sourceX * normalizedA R := by
    rw [C.data.source_factorization, hroute'.2.1, hroute'.2.2]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedY * normalizedB R + C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hrx]
    omega
  have hsourceX : C.data.sourceX = L5A2B4AR4R2B.c1 R - A.depth := by
    by_contra hne
    have hlt : L5A2B4AR4R2B.c1 R - A.depth < C.data.sourceX :=
      lt_of_le_of_ne hbaseLe (Ne.symm hne)
    let g := (C.data.sourceX -
      (L5A2B4AR4R2B.c1 R - A.depth)) * normalizedA R
    have hg0 : g ≠ 0 := by
      dsimp [g]
      exact Nat.mul_ne_zero (Nat.sub_ne_zero_of_lt hlt) ha.ne'
    have hgH : g ∈ normalizedH P.M.base := by
      dsimp [g]
      simpa [nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R)
          (C.data.sourceX - (L5A2B4AR4R2B.c1 R - A.depth))
    have hsourceCandidateH : sourceCandidate ∈ normalizedH P.M.base := by
      dsimp [sourceCandidate]
      simpa [nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
          (branchB_actual_normalizedA_mem R)
          (L5A2B4AR4R2B.c1 R - A.depth)
    have hreturnedCandidateH : returnedCandidate ∈ normalizedH P.M.base := by
      dsimp [returnedCandidate]
      have hBmem := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedB_mem R) (pH R - i)
      have hCmem := (normalizedH P.M.base).toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedC_mem R) (qH R - j)
      simpa [nsmul_eq_mul, Nat.mul_comm] using
        (normalizedH P.M.base).add_mem hBmem hCmem
    have hcandidateJ : (sourceCandidate : ℤ) ∈
        returnIdeal (normalizedH P.M.base) A.n := by
      change (sourceCandidate : ℤ) ∈ (normalizedH P.M.base).asRelativeIdeal ∧
        (sourceCandidate : ℤ) - (A.n : ℕ) ∈
          (normalizedH P.M.base).asRelativeIdeal
      constructor
      · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
        exact ⟨sourceCandidate, hsourceCandidateH, rfl⟩
      · rw [hcandidateZ]
        have hdiff :
            (A.n : ℤ) + (returnedCandidate : ℤ) - (A.n : ℤ) =
              (returnedCandidate : ℤ) := by ring
        rw [hdiff]
        rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
        exact ⟨returnedCandidate, hreturnedCandidateH, rfl⟩
    have hsourceSplit : C.data.sourceValue = g + sourceCandidate := by
      rw [hsource]
      dsimp [g, sourceCandidate]
      rw [← Nat.add_mul, Nat.sub_add_cancel hbaseLe]
    have hsub : s - (g : ℕ) = (sourceCandidate : ℤ) := by
      calc
        s - (g : ℕ) = (C.data.sourceValue : ℤ) - (g : ℕ) := by
          exact congrArg (fun z : ℤ => z - (g : ℕ)) C.data.source_eq.symm
        _ = (sourceCandidate : ℤ) := by
          rw [hsourceSplit]
          push_cast
          ring
    apply (A.source_minimal.2 g hgH hg0)
    rw [hsub]
    exact hcandidateJ
  refine ⟨hdepth, ?_, ?_⟩
  · rw [hsource, hsourceX]
  · have hactualBalance :=
      (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.2
    rw [hsource, hsourceX] at hactualBalance
    change sourceCandidate = A.n + C.data.returnedValue at hactualBalance
    rw [hcandidate] at hactualBalance
    change C.data.returnedValue = returnedCandidate
    omega

private theorem nat_relation_of_signed_below
    (a b c A B C i : ℕ) (hBi : B ≤ i)
    (h : (A : ℤ) * a + ((B : ℤ) - i) * b = (C : ℤ) * c) :
    A * a = (i - B) * b + C * c := by
  have hcast : ((i - B : ℕ) : ℤ) = i - B := Nat.cast_sub hBi
  exact_mod_cast (show (A : ℤ) * a = ((i - B : ℕ) : ℤ) * b + C * c by
    rw [hcast]
    nlinarith only [h])

private theorem nat_relation_of_signed_above
    (a b c A B C i : ℕ) (hiB : i ≤ B)
    (h : (A : ℤ) * a + ((B : ℤ) - i) * b = (C : ℤ) * c) :
    C * c = A * a + (B - i) * b := by
  have hcast : ((B - i : ℕ) : ℤ) = B - i := Nat.cast_sub hiB
  exact_mod_cast (show (C : ℤ) * c = (A : ℤ) * a + ((B - i : ℕ) : ℤ) * b by
    rw [hcast]
    nlinarith only [h])

/-- Family-local CENTER-X value identification on the actual `ab` support
route.  The proof derives the X depth bound from the forced positive source
coefficient after eliminating every wrong signed critical relation. -/
theorem branchB_individual_return_center_X_value_pair
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i < pH R ∧ 1 ≤ j ∧ j ≤ qH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    A.depth < wH R ∧
      C.data.sourceValue =
        (wH R - A.depth) * normalizedA R +
          (i + zH R) * normalizedB R ∧
      C.data.returnedValue =
        (L5A2B4AR4R2B.c3 R - j) * normalizedC R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i < pH R ∧ 1 ≤ j ∧ j ≤ qH R at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  rcases hcenter with ⟨hi, hj, hiPos, hiLt, hjPos, hjLe⟩
  have hiLe : i ≤ pH R := Nat.le_of_lt hiLt
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hsign := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hsign.1.resolve_left hroute'.1
  have hry : C.data.returnedY = 0 := hsign.2.1.resolve_left hroute'.2.1
  have hsource : C.data.sourceValue =
      C.data.sourceX * normalizedA R + C.data.sourceY * normalizedB R := by
    rw [C.data.source_factorization, hroute'.2.2]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hrx, hry]
    omega
  have hrz : C.data.returnedZ ≠ 0 := by
    intro hz
    apply (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.1
    rw [hreturned, hz]
    simp
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz
  have commonImpossible (g sourceRest returnedRest : ℕ)
      (hgH : g ∈ H) (hg0 : g ≠ 0)
      (hsH : sourceRest ∈ H) (hrH : returnedRest ∈ H)
      (hsplit : C.data.sourceValue = g + sourceRest)
      (hrsplit : C.data.returnedValue = g + returnedRest) : False := by
    apply minimal_return_common_generator_impossible H C.data.return_witness.2.2
      hgH hg0 hsH hrH
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (g : ℤ) + sourceRest := by exact_mod_cast hsplit
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (g : ℤ) + returnedRest := by exact_mod_cast hrsplit
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  have hdepthC1 : A.depth < L5A2B4AR4R2B.c1 R := by
    have hlevel := branchB_selected_return_anchor_level_zero R hB hs
    have hbeta := A.coordinate.exact_eq
    rw [hlevel, zero_mul, zero_add, hi, hj] at hbeta
    have hanchor := A.anchor_eq
    rw [hbeta] at hanchor
    have hanchorNat : i * normalizedB R + j * normalizedC R =
        A.n + normalizedA R * A.depth := by
      exact_mod_cast hanchor
    rw [Nat.mul_comm (normalizedA R) A.depth] at hanchorNat
    have hnpos : 0 < A.n := by
      have hn0 : A.n ≠ 0 := by
        intro hn
        apply A.n_not_mem
        simpa [hn] using H.zero_mem
      exact Nat.pos_of_ne_zero hn0
    by_contra hnot
    have hdge : L5A2B4AR4R2B.c1 R ≤ A.depth := Nat.le_of_not_gt hnot
    have hda := Nat.mul_le_mul_right (normalizedA R) hdge
    have hib := Nat.mul_le_mul_right (normalizedB R) hiLe
    have hjc := Nat.mul_le_mul_right (normalizedC R) hjLe
    omega
  have hbalance := (branchB_selected_return_source_balance_packet R hB hs).2.1
  have hrelationZ :
      (((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R) +
          (((C.data.sourceY : ℤ) - i) * normalizedB R) =
        ((C.data.returnedZ + j : ℕ) : ℤ) * normalizedC R := by
    rw [hroute'.2.2, hrx, hry, hi, hj] at hbalance
    push_cast at hbalance ⊢
    nlinarith only [hbalance]
  have hsourceX_lt_base :
      C.data.sourceX < L5A2B4AR4R2B.c1 R - A.depth := by
    by_contra hnot
    have hbaseLe : L5A2B4AR4R2B.c1 R - A.depth ≤ C.data.sourceX :=
      Nat.le_of_not_gt hnot
    let sourceO := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R
    let returnedO := (pH R - i) * normalizedB R +
      (qH R - j) * normalizedC R
    have hcandidateO : sourceO = A.n + returnedO := by
      have hlevel := branchB_selected_return_anchor_level_zero R hB hs
      have hbeta := A.coordinate.exact_eq
      rw [hlevel, zero_mul, zero_add, hi, hj] at hbeta
      have hanchor := A.anchor_eq
      rw [hbeta] at hanchor
      have hanchorNat : i * normalizedB R + j * normalizedC R =
          A.n + normalizedA R * A.depth := by exact_mod_cast hanchor
      have hA : sourceO + normalizedA R * A.depth =
          L5A2B4AR4R2B.c1 R * normalizedA R := by
        dsimp [sourceO]
        rw [Nat.mul_comm (normalizedA R) A.depth]
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hdepthC1)]
      have hB : (pH R - i) * normalizedB R + i * normalizedB R =
          pH R * normalizedB R := by rw [← Nat.add_mul, Nat.sub_add_cancel hiLe]
      have hC : (qH R - j) * normalizedC R + j * normalizedC R =
          qH R * normalizedC R := by rw [← Nat.add_mul, Nat.sub_add_cancel hjLe]
      dsimp [returnedO]
      omega
    have hsourceOH : sourceO ∈ H := by
      dsimp [sourceO]
      simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedA_mem R)
        (L5A2B4AR4R2B.c1 R - A.depth)
    have hreturnedOH : returnedO ∈ H := by
      dsimp [returnedO]
      simpa using hcomb 0 (pH R - i) (qH R - j)
    have hsourceOJ : (sourceO : ℤ) ∈ returnIdeal H A.n := by
      change (sourceO : ℤ) ∈ H.asRelativeIdeal ∧
        (sourceO : ℤ) - (A.n : ℕ) ∈ H.asRelativeIdeal
      constructor
      · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
        exact ⟨sourceO, hsourceOH, rfl⟩
      · have hdifference : (sourceO : ℤ) - (A.n : ℕ) = returnedO := by
          have hcZ : (sourceO : ℤ) = (A.n : ℤ) + returnedO := by
            exact_mod_cast hcandidateO
          rw [hcZ]
          ring
        rw [hdifference, NumericalSemigroup.mem_asRelativeIdeal_iff]
        exact ⟨returnedO, hreturnedOH, rfl⟩
    let g := (C.data.sourceX - (L5A2B4AR4R2B.c1 R - A.depth)) *
      normalizedA R + C.data.sourceY * normalizedB R
    have hg0 : g ≠ 0 := by
      dsimp [g]
      have hypos : 0 < C.data.sourceY * normalizedB R :=
        Nat.mul_pos (Nat.pos_of_ne_zero hroute'.2.1) hb
      omega
    have hgH : g ∈ H := by
      dsimp [g]
      simpa using hcomb (C.data.sourceX -
        (L5A2B4AR4R2B.c1 R - A.depth)) C.data.sourceY 0
    have hsplit : C.data.sourceValue = g + sourceO := by
      rw [hsource]
      dsimp [g, sourceO]
      have hxsplit := Nat.sub_add_cancel hbaseLe
      have hmul :
          (C.data.sourceX - (L5A2B4AR4R2B.c1 R - A.depth)) *
              normalizedA R +
            (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R =
              C.data.sourceX * normalizedA R := by
        rw [← Nat.add_mul, hxsplit]
      omega
    have hsub : s - (g : ℕ) = (sourceO : ℤ) := by
      calc
        s - (g : ℕ) = (C.data.sourceValue : ℤ) - (g : ℕ) := by
          exact congrArg (fun z : ℤ => z - (g : ℕ)) C.data.source_eq.symm
        _ = (sourceO : ℤ) := by rw [hsplit]; push_cast; ring
    apply (A.source_minimal.2 g hgH hg0)
    rw [hsub]
    exact hsourceOJ
  have hsy_ge_i : i ≤ C.data.sourceY := by
    by_contra hnot
    have hsylt : C.data.sourceY < i := Nat.lt_of_not_ge hnot
    have hrelA : (C.data.sourceX + A.depth) * normalizedA R =
        (i - C.data.sourceY) * normalizedB R +
          (C.data.returnedZ + j) * normalizedC R := by
      exact nat_relation_of_signed_below (normalizedA R) (normalizedB R)
        (normalizedC R) (C.data.sourceX + A.depth) C.data.sourceY
        (C.data.returnedZ + j) i (Nat.le_of_lt hsylt) hrelationZ
    have hmin := branchB_normalizedA_relation_min R _ _ _
      (by omega) hrelA
    omega
  have hrelC : (C.data.returnedZ + j) * normalizedC R =
      (C.data.sourceX + A.depth) * normalizedA R +
        (C.data.sourceY - i) * normalizedB R := by
    exact nat_relation_of_signed_above (normalizedA R) (normalizedB R)
      (normalizedC R) (C.data.sourceX + A.depth) C.data.sourceY
      (C.data.returnedZ + j) i hsy_ge_i hrelationZ
  have hc3Le : L5A2B4AR4R2B.c3 R ≤ C.data.returnedZ + j :=
    branchB_normalizedC_relation_min R _ _ _ (by omega) hrelC
  have hsourceX_lt_c1 : C.data.sourceX < L5A2B4AR4R2B.c1 R := by omega
  have hsourceY_lt_c2 : C.data.sourceY < L5A2B4AR4R2B.c2 R := by
    by_contra hnot
    have hle : L5A2B4AR4R2B.c2 R ≤ C.data.sourceY := Nat.le_of_not_gt hnot
    let sourceRest := (C.data.sourceX + uH R) * normalizedA R +
      (C.data.sourceY - L5A2B4AR4R2B.c2 R) * normalizedB R +
      (vH R - 1) * normalizedC R
    let returnedRest := (C.data.returnedZ - 1) * normalizedC R
    apply commonImpossible (normalizedC R) sourceRest returnedRest
      (branchB_actual_normalizedC_mem R) hc.ne'
      (hcomb _ _ _) (by
        simpa [returnedRest] using (hcomb 0 0 (C.data.returnedZ - 1)))
    · rw [hsource]
      dsimp [sourceRest]
      have hys := Nat.sub_add_cancel hle
      have hvs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv.ne')
      have hvsplit : vH R * normalizedC R =
          normalizedC R + (vH R - 1) * normalizedC R := by
        calc
          vH R * normalizedC R = (vH R - 1 + 1) * normalizedC R := by rw [hvs]
          _ = normalizedC R + (vH R - 1) * normalizedC R := by ring
      calc
        C.data.sourceX * normalizedA R + C.data.sourceY * normalizedB R =
            C.data.sourceX * normalizedA R +
              ((C.data.sourceY - L5A2B4AR4R2B.c2 R) +
                L5A2B4AR4R2B.c2 R) * normalizedB R := by rw [hys]
        _ = normalizedC R +
              ((C.data.sourceX + uH R) * normalizedA R +
                (C.data.sourceY - L5A2B4AR4R2B.c2 R) * normalizedB R +
                (vH R - 1) * normalizedC R) := by rw [Nat.add_mul, hrel2, hvsplit]; ring
    · rw [hreturned]
      dsimp [returnedRest]
      have hrs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hrz)
      calc
        C.data.returnedZ * normalizedC R =
            (C.data.returnedZ - 1 + 1) * normalizedC R := by rw [hrs]
        _ = normalizedC R + (C.data.returnedZ - 1) * normalizedC R := by ring
  have hreturnedZ_lt_c3 : C.data.returnedZ < L5A2B4AR4R2B.c3 R := by
    by_contra hnot
    have hle : L5A2B4AR4R2B.c3 R ≤ C.data.returnedZ := Nat.le_of_not_gt hnot
    let sourceRest := (C.data.sourceX - 1) * normalizedA R +
      C.data.sourceY * normalizedB R
    let returnedRest := (wH R - 1) * normalizedA R +
      zH R * normalizedB R +
      (C.data.returnedZ - L5A2B4AR4R2B.c3 R) * normalizedC R
    apply commonImpossible (normalizedA R) sourceRest returnedRest
      (branchB_actual_normalizedA_mem R) ha.ne'
      (by
        simpa [sourceRest] using
          (hcomb (C.data.sourceX - 1) C.data.sourceY 0))
      (hcomb _ _ _)
    · rw [hsource]
      dsimp [sourceRest]
      have hxs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hroute'.1)
      calc
        C.data.sourceX * normalizedA R + C.data.sourceY * normalizedB R =
            (C.data.sourceX - 1 + 1) * normalizedA R +
              C.data.sourceY * normalizedB R := by rw [hxs]
        _ = normalizedA R +
              ((C.data.sourceX - 1) * normalizedA R +
                C.data.sourceY * normalizedB R) := by ring
    · rw [hreturned]
      dsimp [returnedRest]
      have hrs := Nat.sub_add_cancel hle
      have hws := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hw.ne')
      have hwsplit : wH R * normalizedA R =
          normalizedA R + (wH R - 1) * normalizedA R := by
        calc
          wH R * normalizedA R = (wH R - 1 + 1) * normalizedA R := by rw [hws]
          _ = normalizedA R + (wH R - 1) * normalizedA R := by ring
      calc
        C.data.returnedZ * normalizedC R =
            ((C.data.returnedZ - L5A2B4AR4R2B.c3 R) +
              L5A2B4AR4R2B.c3 R) * normalizedC R := by rw [hrs]
        _ = normalizedA R +
              ((wH R - 1) * normalizedA R + zH R * normalizedB R +
                (C.data.returnedZ - L5A2B4AR4R2B.c3 R) * normalizedC R) := by
          rw [Nat.add_mul, hrel3, hwsplit]
          ring
  let k := C.data.returnedZ + j - L5A2B4AR4R2B.c3 R
  have hkadd : k + L5A2B4AR4R2B.c3 R = C.data.returnedZ + j :=
    Nat.sub_add_cancel hc3Le
  have hkZ : (k : ℤ) =
      C.data.returnedZ + j - L5A2B4AR4R2B.c3 R := by
    dsimp [k]
    rw [Nat.cast_sub hc3Le]
    push_cast
    rfl
  have hrel3Z : (L5A2B4AR4R2B.c3 R : ℤ) * normalizedC R =
      (wH R : ℤ) * normalizedA R + (zH R : ℤ) * normalizedB R := by
    exact_mod_cast hrel3
  have hdiffZ :
      (((C.data.sourceX + A.depth : ℕ) : ℤ) - wH R) * normalizedA R +
          ((C.data.sourceY : ℤ) - i - zH R) * normalizedB R =
        (k : ℤ) * normalizedC R := by
    calc
      (((C.data.sourceX + A.depth : ℕ) : ℤ) - wH R) * normalizedA R +
            ((C.data.sourceY : ℤ) - i - zH R) * normalizedB R =
          (((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R +
              ((C.data.sourceY : ℤ) - i) * normalizedB R) -
            ((wH R : ℤ) * normalizedA R + (zH R : ℤ) * normalizedB R) := by ring
      _ = ((C.data.returnedZ : ℤ) + j) * normalizedC R -
            (L5A2B4AR4R2B.c3 R : ℤ) * normalizedC R := by
          rw [hrelationZ, hrel3Z]
          push_cast
          rfl
      _ = (k : ℤ) * normalizedC R := by rw [hkZ]; push_cast; ring
  rw [Nat.cast_add] at hdiffZ
  have hxsum_lt : C.data.sourceX + A.depth < L5A2B4AR4R2B.c1 R := by
    omega
  have hxge : wH R ≤ C.data.sourceX + A.depth := by
    by_contra hnot
    have hxlt : C.data.sourceX + A.depth < wH R := Nat.lt_of_not_ge hnot
    have hygt : i + zH R < C.data.sourceY := by
      by_contra hynot
      have hyle : C.data.sourceY ≤ i + zH R := Nat.le_of_not_gt hynot
      have hzeroZ :
          ((wH R - (C.data.sourceX + A.depth) : ℕ) : ℤ) * normalizedA R +
              ((i + zH R - C.data.sourceY : ℕ) : ℤ) * normalizedB R +
              (k : ℤ) * normalizedC R = 0 := by
        have hxcast :
            ((wH R - (C.data.sourceX + A.depth) : ℕ) : ℤ) =
              (wH R : ℤ) - (C.data.sourceX + A.depth) :=
          Nat.cast_sub (Nat.le_of_lt hxlt)
        have hycast : ((i + zH R - C.data.sourceY : ℕ) : ℤ) =
            (i + zH R : ℤ) - C.data.sourceY := Nat.cast_sub hyle
        rw [hxcast, hycast]
        calc
          ((wH R : ℤ) - (C.data.sourceX + A.depth)) * normalizedA R +
                ((i + zH R : ℤ) - C.data.sourceY) * normalizedB R +
                (k : ℤ) * normalizedC R =
              -((((C.data.sourceX + A.depth : ℕ) : ℤ) - wH R) * normalizedA R +
                ((C.data.sourceY : ℤ) - i - zH R) * normalizedB R) +
                (k : ℤ) * normalizedC R := by push_cast; ring
          _ = 0 := by
            push_cast only [Nat.cast_add]
            rw [hdiffZ]
            ring
      have hpositive : 0 <
          ((wH R - (C.data.sourceX + A.depth)) * normalizedA R) :=
        Nat.mul_pos (Nat.sub_pos_of_lt hxlt) ha
      have hzeroNat :
          (wH R - (C.data.sourceX + A.depth)) * normalizedA R +
              (i + zH R - C.data.sourceY) * normalizedB R +
              k * normalizedC R = 0 := by
        exact_mod_cast hzeroZ
      omega
    have hrelB : (C.data.sourceY - (i + zH R)) * normalizedB R =
        (wH R - (C.data.sourceX + A.depth)) * normalizedA R +
          k * normalizedC R := by
      have hyLe : i + zH R ≤ C.data.sourceY := Nat.le_of_lt hygt
      have hxc : ((wH R - (C.data.sourceX + A.depth) : ℕ) : ℤ) =
          (wH R : ℤ) - (C.data.sourceX + A.depth) :=
        Nat.cast_sub (Nat.le_of_lt hxlt)
      have hyc : ((C.data.sourceY - (i + zH R) : ℕ) : ℤ) =
          (C.data.sourceY : ℤ) - (i + zH R) := Nat.cast_sub hyLe
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    have hminB := branchB_normalizedB_relation_min R _ _ _
      (Nat.sub_pos_of_lt hygt) hrelB
    omega
  have hyge : i + zH R ≤ C.data.sourceY := by
    by_contra hnot
    have hylt : C.data.sourceY < i + zH R := Nat.lt_of_not_ge hnot
    have hrelA : (C.data.sourceX + A.depth - wH R) * normalizedA R =
        (i + zH R - C.data.sourceY) * normalizedB R + k * normalizedC R := by
      have hxc : ((C.data.sourceX + A.depth - wH R : ℕ) : ℤ) =
          (C.data.sourceX + A.depth : ℤ) - wH R := Nat.cast_sub hxge
      have hyc : ((i + zH R - C.data.sourceY : ℕ) : ℤ) =
          (i + zH R : ℤ) - C.data.sourceY := Nat.cast_sub (Nat.le_of_lt hylt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    have hqpos : 0 < C.data.sourceX + A.depth - wH R := by
      by_contra hzq
      have heq : C.data.sourceX + A.depth = wH R := by omega
      rw [heq, Nat.sub_self, zero_mul] at hrelA
      have hbpos := Nat.mul_pos (Nat.sub_pos_of_lt hylt) hb
      omega
    have hminA := branchB_normalizedA_relation_min R _ _ _ hqpos hrelA
    omega
  have hk0 : k = 0 := by
    by_contra hkne
    have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
    have hrelK : k * normalizedC R =
        (C.data.sourceX + A.depth - wH R) * normalizedA R +
          (C.data.sourceY - (i + zH R)) * normalizedB R := by
      have hxc : ((C.data.sourceX + A.depth - wH R : ℕ) : ℤ) =
          (C.data.sourceX + A.depth : ℤ) - wH R := Nat.cast_sub hxge
      have hyc : ((C.data.sourceY - (i + zH R) : ℕ) : ℤ) =
          (C.data.sourceY : ℤ) - (i + zH R) := Nat.cast_sub hyge
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    have hminK := branchB_normalizedC_relation_min R _ _ _ hkpos hrelK
    have hklt : k < L5A2B4AR4R2B.c3 R := by
      dsimp [k]
      omega
    omega
  have hxEq : C.data.sourceX + A.depth = wH R := by
    have hzero :
        (C.data.sourceX + A.depth - wH R) * normalizedA R +
          (C.data.sourceY - (i + zH R)) * normalizedB R = 0 := by
      have hrelK : k * normalizedC R =
          (C.data.sourceX + A.depth - wH R) * normalizedA R +
            (C.data.sourceY - (i + zH R)) * normalizedB R := by
        have hxc : ((C.data.sourceX + A.depth - wH R : ℕ) : ℤ) =
            (C.data.sourceX + A.depth : ℤ) - wH R := Nat.cast_sub hxge
        have hyc : ((C.data.sourceY - (i + zH R) : ℕ) : ℤ) =
            (C.data.sourceY : ℤ) - (i + zH R) := Nat.cast_sub hyge
        apply Int.ofNat_inj.mp
        push_cast only [Nat.cast_mul, Nat.cast_add]
        rw [hxc, hyc]
        nlinarith only [hdiffZ]
      rw [hk0, zero_mul] at hrelK
      exact hrelK.symm
    have hxzero : C.data.sourceX + A.depth - wH R = 0 := by
      by_contra hn
      have hp0 := Nat.mul_pos (Nat.pos_of_ne_zero hn) ha
      omega
    omega
  have hyEq : C.data.sourceY = i + zH R := by
    have hrjEq : C.data.returnedZ + j = L5A2B4AR4R2B.c3 R := by omega
    have hrel0 : (C.data.returnedZ + j) * normalizedC R =
        wH R * normalizedA R + zH R * normalizedB R := by
      rw [hrjEq]
      exact hrel3
    rw [hxEq] at hrelC
    have hmul : (C.data.sourceY - i) * normalizedB R =
        zH R * normalizedB R := by omega
    have hcoef : C.data.sourceY - i = zH R :=
      Nat.eq_of_mul_eq_mul_right hb hmul
    omega
  have hrEq : C.data.returnedZ + j = L5A2B4AR4R2B.c3 R := by omega
  have hdepth : A.depth < wH R := by omega
  refine ⟨hdepth, ?_, ?_⟩
  · rw [hsource]
    have hxsub : C.data.sourceX = wH R - A.depth := by omega
    rw [hxsub, hyEq]
  · rw [hreturned]
    have hrsub : C.data.returnedZ = L5A2B4AR4R2B.c3 R - j := by omega
    rw [hrsub]

/-- Family-local CENTER-Y value identification on the actual `ac` support
route.  As for CENTER-X, the required depth inequality is a conclusion of
the family proof, not a chart-global premise. -/
theorem branchB_individual_return_center_Y_value_pair
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j < qH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    A.depth < uH R ∧
      C.data.sourceValue =
        (uH R - A.depth) * normalizedA R +
          (j + vH R) * normalizedC R ∧
      C.data.returnedValue =
        (L5A2B4AR4R2B.c2 R - i) * normalizedB R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j < qH R at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLt⟩
  have hjLe : j ≤ qH R := Nat.le_of_lt hjLt
  have hroute' : C.data.sourceX ≠ 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hsign := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrx : C.data.returnedX = 0 := hsign.1.resolve_left hroute'.1
  have hrz : C.data.returnedZ = 0 := hsign.2.2.resolve_left hroute'.2.2
  have hsource : C.data.sourceValue =
      C.data.sourceX * normalizedA R + C.data.sourceZ * normalizedC R := by
    rw [C.data.source_factorization, hroute'.2.1]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedY * normalizedB R := by
    rw [C.data.returned_factorization, hrx, hrz]
    omega
  have hry : C.data.returnedY ≠ 0 := by
    intro hy
    apply (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.1
    rw [hreturned, hy]
    simp
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz
  have commonImpossible (g sourceRest returnedRest : ℕ)
      (hgH : g ∈ H) (hg0 : g ≠ 0)
      (hsH : sourceRest ∈ H) (hrH : returnedRest ∈ H)
      (hsplit : C.data.sourceValue = g + sourceRest)
      (hrsplit : C.data.returnedValue = g + returnedRest) : False := by
    apply minimal_return_common_generator_impossible H C.data.return_witness.2.2
      hgH hg0 hsH hrH
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (g : ℤ) + sourceRest := by exact_mod_cast hsplit
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (g : ℤ) + returnedRest := by exact_mod_cast hrsplit
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  have hdepthC1 : A.depth < L5A2B4AR4R2B.c1 R := by
    have hlevel := branchB_selected_return_anchor_level_zero R hB hs
    have hbeta := A.coordinate.exact_eq
    rw [hlevel, zero_mul, zero_add, hi, hj] at hbeta
    have hanchor := A.anchor_eq
    rw [hbeta] at hanchor
    have hanchorNat : i * normalizedB R + j * normalizedC R =
        A.n + normalizedA R * A.depth := by exact_mod_cast hanchor
    rw [Nat.mul_comm (normalizedA R) A.depth] at hanchorNat
    have hnpos : 0 < A.n := by
      have hn0 : A.n ≠ 0 := by
        intro hn
        apply A.n_not_mem
        simpa [hn] using H.zero_mem
      exact Nat.pos_of_ne_zero hn0
    by_contra hnot
    have hdge : L5A2B4AR4R2B.c1 R ≤ A.depth := Nat.le_of_not_gt hnot
    have hda := Nat.mul_le_mul_right (normalizedA R) hdge
    have hib := Nat.mul_le_mul_right (normalizedB R) hiLe
    have hjc := Nat.mul_le_mul_right (normalizedC R) hjLe
    omega
  have hbalance := (branchB_selected_return_source_balance_packet R hB hs).2.1
  have hrelationZ :
      (((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R) +
          (((C.data.sourceZ : ℤ) - j) * normalizedC R) =
        ((C.data.returnedY + i : ℕ) : ℤ) * normalizedB R := by
    rw [hroute'.2.1, hrx, hrz, hi, hj] at hbalance
    push_cast at hbalance ⊢
    nlinarith only [hbalance]
  have hsourceX_lt_base :
      C.data.sourceX < L5A2B4AR4R2B.c1 R - A.depth := by
    by_contra hnot
    have hbaseLe : L5A2B4AR4R2B.c1 R - A.depth ≤ C.data.sourceX :=
      Nat.le_of_not_gt hnot
    let sourceO := (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R
    let returnedO := (pH R - i) * normalizedB R +
      (qH R - j) * normalizedC R
    have hcandidateO : sourceO = A.n + returnedO := by
      have hlevel := branchB_selected_return_anchor_level_zero R hB hs
      have hbeta := A.coordinate.exact_eq
      rw [hlevel, zero_mul, zero_add, hi, hj] at hbeta
      have hanchor := A.anchor_eq
      rw [hbeta] at hanchor
      have hanchorNat : i * normalizedB R + j * normalizedC R =
          A.n + normalizedA R * A.depth := by exact_mod_cast hanchor
      have hA : sourceO + normalizedA R * A.depth =
          L5A2B4AR4R2B.c1 R * normalizedA R := by
        dsimp [sourceO]
        rw [Nat.mul_comm (normalizedA R) A.depth]
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hdepthC1)]
      have hB : (pH R - i) * normalizedB R + i * normalizedB R =
          pH R * normalizedB R := by rw [← Nat.add_mul, Nat.sub_add_cancel hiLe]
      have hC : (qH R - j) * normalizedC R + j * normalizedC R =
          qH R * normalizedC R := by rw [← Nat.add_mul, Nat.sub_add_cancel hjLe]
      dsimp [returnedO]
      omega
    have hsourceOH : sourceO ∈ H := by
      dsimp [sourceO]
      simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem
        (branchB_actual_normalizedA_mem R)
        (L5A2B4AR4R2B.c1 R - A.depth)
    have hreturnedOH : returnedO ∈ H := by
      dsimp [returnedO]
      simpa using hcomb 0 (pH R - i) (qH R - j)
    have hsourceOJ : (sourceO : ℤ) ∈ returnIdeal H A.n := by
      change (sourceO : ℤ) ∈ H.asRelativeIdeal ∧
        (sourceO : ℤ) - (A.n : ℕ) ∈ H.asRelativeIdeal
      constructor
      · rw [NumericalSemigroup.mem_asRelativeIdeal_iff]
        exact ⟨sourceO, hsourceOH, rfl⟩
      · have hdifference : (sourceO : ℤ) - (A.n : ℕ) = returnedO := by
          have hcZ : (sourceO : ℤ) = (A.n : ℤ) + returnedO := by
            exact_mod_cast hcandidateO
          rw [hcZ]
          ring
        rw [hdifference, NumericalSemigroup.mem_asRelativeIdeal_iff]
        exact ⟨returnedO, hreturnedOH, rfl⟩
    let g := (C.data.sourceX - (L5A2B4AR4R2B.c1 R - A.depth)) *
      normalizedA R + C.data.sourceZ * normalizedC R
    have hg0 : g ≠ 0 := by
      dsimp [g]
      have hzpos : 0 < C.data.sourceZ * normalizedC R :=
        Nat.mul_pos (Nat.pos_of_ne_zero hroute'.2.2) hc
      omega
    have hgH : g ∈ H := by
      dsimp [g]
      simpa using hcomb (C.data.sourceX -
        (L5A2B4AR4R2B.c1 R - A.depth)) 0 C.data.sourceZ
    have hsplit : C.data.sourceValue = g + sourceO := by
      rw [hsource]
      dsimp [g, sourceO]
      have hxsplit := Nat.sub_add_cancel hbaseLe
      have hmul :
          (C.data.sourceX - (L5A2B4AR4R2B.c1 R - A.depth)) *
              normalizedA R +
            (L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R =
              C.data.sourceX * normalizedA R := by
        rw [← Nat.add_mul, hxsplit]
      omega
    have hsub : s - (g : ℕ) = (sourceO : ℤ) := by
      calc
        s - (g : ℕ) = (C.data.sourceValue : ℤ) - (g : ℕ) := by
          exact congrArg (fun z : ℤ => z - (g : ℕ)) C.data.source_eq.symm
        _ = (sourceO : ℤ) := by rw [hsplit]; push_cast; ring
    apply (A.source_minimal.2 g hgH hg0)
    rw [hsub]
    exact hsourceOJ
  have hsz_ge_j : j ≤ C.data.sourceZ := by
    by_contra hnot
    have hszlt : C.data.sourceZ < j := Nat.lt_of_not_ge hnot
    have hrelA : (C.data.sourceX + A.depth) * normalizedA R =
        (C.data.returnedY + i) * normalizedB R +
          (j - C.data.sourceZ) * normalizedC R := by
      simpa [Nat.add_comm] using
        (nat_relation_of_signed_below (normalizedA R) (normalizedC R)
          (normalizedB R) (C.data.sourceX + A.depth) C.data.sourceZ
          (C.data.returnedY + i) j (Nat.le_of_lt hszlt) hrelationZ)
    have hmin := branchB_normalizedA_relation_min R _ _ _ (by omega) hrelA
    omega
  have hrelB : (C.data.returnedY + i) * normalizedB R =
      (C.data.sourceX + A.depth) * normalizedA R +
        (C.data.sourceZ - j) * normalizedC R := by
    exact nat_relation_of_signed_above (normalizedA R) (normalizedC R)
      (normalizedB R) (C.data.sourceX + A.depth) C.data.sourceZ
      (C.data.returnedY + i) j hsz_ge_j hrelationZ
  have hc2Le : L5A2B4AR4R2B.c2 R ≤ C.data.returnedY + i :=
    branchB_normalizedB_relation_min R _ _ _ (by omega) hrelB
  have hsourceX_lt_c1 : C.data.sourceX < L5A2B4AR4R2B.c1 R := by omega
  have hsourceZ_lt_c3 : C.data.sourceZ < L5A2B4AR4R2B.c3 R := by
    by_contra hnot
    have hle : L5A2B4AR4R2B.c3 R ≤ C.data.sourceZ := Nat.le_of_not_gt hnot
    let sourceRest := (C.data.sourceX + wH R) * normalizedA R +
      (zH R - 1) * normalizedB R +
      (C.data.sourceZ - L5A2B4AR4R2B.c3 R) * normalizedC R
    let returnedRest := (C.data.returnedY - 1) * normalizedB R
    apply commonImpossible (normalizedB R) sourceRest returnedRest
      (branchB_actual_normalizedB_mem R) hb.ne' (hcomb _ _ _)
      (by simpa [returnedRest] using hcomb 0 (C.data.returnedY - 1) 0)
    · rw [hsource]
      dsimp [sourceRest]
      have hzs := Nat.sub_add_cancel hle
      have hzs1 := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz.ne')
      have hzsplit : zH R * normalizedB R =
          normalizedB R + (zH R - 1) * normalizedB R := by
        calc
          zH R * normalizedB R = (zH R - 1 + 1) * normalizedB R := by rw [hzs1]
          _ = normalizedB R + (zH R - 1) * normalizedB R := by ring
      calc
        C.data.sourceX * normalizedA R + C.data.sourceZ * normalizedC R =
            C.data.sourceX * normalizedA R +
              ((C.data.sourceZ - L5A2B4AR4R2B.c3 R) +
                L5A2B4AR4R2B.c3 R) * normalizedC R := by rw [hzs]
        _ = normalizedB R +
              ((C.data.sourceX + wH R) * normalizedA R +
                (zH R - 1) * normalizedB R +
                (C.data.sourceZ - L5A2B4AR4R2B.c3 R) * normalizedC R) := by
          rw [Nat.add_mul, hrel3, hzsplit]
          ring
    · rw [hreturned]
      dsimp [returnedRest]
      have hrys := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hry)
      calc
        C.data.returnedY * normalizedB R =
            (C.data.returnedY - 1 + 1) * normalizedB R := by rw [hrys]
        _ = normalizedB R + (C.data.returnedY - 1) * normalizedB R := by ring
  have hreturnedY_lt_c2 : C.data.returnedY < L5A2B4AR4R2B.c2 R := by
    by_contra hnot
    have hle : L5A2B4AR4R2B.c2 R ≤ C.data.returnedY := Nat.le_of_not_gt hnot
    let sourceRest := (C.data.sourceX - 1) * normalizedA R +
      C.data.sourceZ * normalizedC R
    let returnedRest := (uH R - 1) * normalizedA R +
      (C.data.returnedY - L5A2B4AR4R2B.c2 R) * normalizedB R +
      vH R * normalizedC R
    apply commonImpossible (normalizedA R) sourceRest returnedRest
      (branchB_actual_normalizedA_mem R) ha.ne'
      (by simpa [sourceRest] using hcomb (C.data.sourceX - 1) 0 C.data.sourceZ)
      (hcomb _ _ _)
    · rw [hsource]
      dsimp [sourceRest]
      have hxs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hroute'.1)
      calc
        C.data.sourceX * normalizedA R + C.data.sourceZ * normalizedC R =
            (C.data.sourceX - 1 + 1) * normalizedA R +
              C.data.sourceZ * normalizedC R := by rw [hxs]
        _ = normalizedA R +
              ((C.data.sourceX - 1) * normalizedA R +
                C.data.sourceZ * normalizedC R) := by ring
    · rw [hreturned]
      dsimp [returnedRest]
      have hrys := Nat.sub_add_cancel hle
      have hus := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hu.ne')
      have husplit : uH R * normalizedA R =
          normalizedA R + (uH R - 1) * normalizedA R := by
        calc
          uH R * normalizedA R = (uH R - 1 + 1) * normalizedA R := by rw [hus]
          _ = normalizedA R + (uH R - 1) * normalizedA R := by ring
      calc
        C.data.returnedY * normalizedB R =
            ((C.data.returnedY - L5A2B4AR4R2B.c2 R) +
              L5A2B4AR4R2B.c2 R) * normalizedB R := by rw [hrys]
        _ = normalizedA R +
              ((uH R - 1) * normalizedA R +
                (C.data.returnedY - L5A2B4AR4R2B.c2 R) * normalizedB R +
                vH R * normalizedC R) := by
          rw [Nat.add_mul, hrel2, husplit]
          ring
  let k := C.data.returnedY + i - L5A2B4AR4R2B.c2 R
  have hkadd : k + L5A2B4AR4R2B.c2 R = C.data.returnedY + i :=
    Nat.sub_add_cancel hc2Le
  have hkZ : (k : ℤ) = C.data.returnedY + i - L5A2B4AR4R2B.c2 R := by
    dsimp [k]
    rw [Nat.cast_sub hc2Le]
    push_cast
    rfl
  have hrel2Z : (L5A2B4AR4R2B.c2 R : ℤ) * normalizedB R =
      (uH R : ℤ) * normalizedA R + (vH R : ℤ) * normalizedC R := by
    exact_mod_cast hrel2
  have hdiffZ :
      (((C.data.sourceX + A.depth : ℕ) : ℤ) - uH R) * normalizedA R +
          ((C.data.sourceZ : ℤ) - j - vH R) * normalizedC R =
        (k : ℤ) * normalizedB R := by
    calc
      (((C.data.sourceX + A.depth : ℕ) : ℤ) - uH R) * normalizedA R +
            ((C.data.sourceZ : ℤ) - j - vH R) * normalizedC R =
          (((C.data.sourceX + A.depth : ℕ) : ℤ) * normalizedA R +
              ((C.data.sourceZ : ℤ) - j) * normalizedC R) -
            ((uH R : ℤ) * normalizedA R + (vH R : ℤ) * normalizedC R) := by ring
      _ = ((C.data.returnedY : ℤ) + i) * normalizedB R -
            (L5A2B4AR4R2B.c2 R : ℤ) * normalizedB R := by
          rw [hrelationZ, hrel2Z]
          push_cast
          rfl
      _ = (k : ℤ) * normalizedB R := by rw [hkZ]; push_cast; ring
  rw [Nat.cast_add] at hdiffZ
  have hxsum_lt : C.data.sourceX + A.depth < L5A2B4AR4R2B.c1 R := by omega
  have hxge : uH R ≤ C.data.sourceX + A.depth := by
    by_contra hnot
    have hxlt : C.data.sourceX + A.depth < uH R := Nat.lt_of_not_ge hnot
    have hzgt : j + vH R < C.data.sourceZ := by
      by_contra hznot
      have hzle : C.data.sourceZ ≤ j + vH R := Nat.le_of_not_gt hznot
      have hzeroZ :
          ((uH R - (C.data.sourceX + A.depth) : ℕ) : ℤ) * normalizedA R +
              ((j + vH R - C.data.sourceZ : ℕ) : ℤ) * normalizedC R +
              (k : ℤ) * normalizedB R = 0 := by
        have hxcast : ((uH R - (C.data.sourceX + A.depth) : ℕ) : ℤ) =
            (uH R : ℤ) - (C.data.sourceX + A.depth) :=
          Nat.cast_sub (Nat.le_of_lt hxlt)
        have hzcast : ((j + vH R - C.data.sourceZ : ℕ) : ℤ) =
            (j + vH R : ℤ) - C.data.sourceZ := Nat.cast_sub hzle
        rw [hxcast, hzcast]
        calc
          ((uH R : ℤ) - (C.data.sourceX + A.depth)) * normalizedA R +
                ((j + vH R : ℤ) - C.data.sourceZ) * normalizedC R +
                (k : ℤ) * normalizedB R =
              -((((C.data.sourceX + A.depth : ℕ) : ℤ) - uH R) * normalizedA R +
                ((C.data.sourceZ : ℤ) - j - vH R) * normalizedC R) +
                (k : ℤ) * normalizedB R := by push_cast; ring
          _ = 0 := by
            push_cast only [Nat.cast_add]
            rw [hdiffZ]
            ring
      have hpositive : 0 <
          (uH R - (C.data.sourceX + A.depth)) * normalizedA R :=
        Nat.mul_pos (Nat.sub_pos_of_lt hxlt) ha
      have hzeroNat :
          (uH R - (C.data.sourceX + A.depth)) * normalizedA R +
              (j + vH R - C.data.sourceZ) * normalizedC R +
              k * normalizedB R = 0 := by exact_mod_cast hzeroZ
      omega
    have hrelC : (C.data.sourceZ - (j + vH R)) * normalizedC R =
        (uH R - (C.data.sourceX + A.depth)) * normalizedA R +
          k * normalizedB R := by
      have hzLe : j + vH R ≤ C.data.sourceZ := Nat.le_of_lt hzgt
      have hxc : ((uH R - (C.data.sourceX + A.depth) : ℕ) : ℤ) =
          (uH R : ℤ) - (C.data.sourceX + A.depth) :=
        Nat.cast_sub (Nat.le_of_lt hxlt)
      have hzc : ((C.data.sourceZ - (j + vH R) : ℕ) : ℤ) =
          (C.data.sourceZ : ℤ) - (j + vH R) := Nat.cast_sub hzLe
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    have hminC := branchB_normalizedC_relation_min R _ _ _
      (Nat.sub_pos_of_lt hzgt) hrelC
    omega
  have hzge : j + vH R ≤ C.data.sourceZ := by
    by_contra hnot
    have hzlt : C.data.sourceZ < j + vH R := Nat.lt_of_not_ge hnot
    have hrelA : (C.data.sourceX + A.depth - uH R) * normalizedA R =
        k * normalizedB R +
          (j + vH R - C.data.sourceZ) * normalizedC R := by
      have hxc : ((C.data.sourceX + A.depth - uH R : ℕ) : ℤ) =
          (C.data.sourceX + A.depth : ℤ) - uH R := Nat.cast_sub hxge
      have hzc : ((j + vH R - C.data.sourceZ : ℕ) : ℤ) =
          (j + vH R : ℤ) - C.data.sourceZ := Nat.cast_sub (Nat.le_of_lt hzlt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    have hqpos : 0 < C.data.sourceX + A.depth - uH R := by
      by_contra hzq
      have heq : C.data.sourceX + A.depth = uH R := by omega
      rw [heq, Nat.sub_self, zero_mul] at hrelA
      have hcpos := Nat.mul_pos (Nat.sub_pos_of_lt hzlt) hc
      omega
    have hminA := branchB_normalizedA_relation_min R _ _ _ hqpos hrelA
    omega
  have hk0 : k = 0 := by
    by_contra hkne
    have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
    have hrelK : k * normalizedB R =
        (C.data.sourceX + A.depth - uH R) * normalizedA R +
          (C.data.sourceZ - (j + vH R)) * normalizedC R := by
      have hxc : ((C.data.sourceX + A.depth - uH R : ℕ) : ℤ) =
          (C.data.sourceX + A.depth : ℤ) - uH R := Nat.cast_sub hxge
      have hzc : ((C.data.sourceZ - (j + vH R) : ℕ) : ℤ) =
          (C.data.sourceZ : ℤ) - (j + vH R) := Nat.cast_sub hzge
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    have hminK := branchB_normalizedB_relation_min R _ _ _ hkpos hrelK
    have hklt : k < L5A2B4AR4R2B.c2 R := by
      dsimp [k]
      omega
    omega
  have hxEq : C.data.sourceX + A.depth = uH R := by
    have hzero :
        (C.data.sourceX + A.depth - uH R) * normalizedA R +
          (C.data.sourceZ - (j + vH R)) * normalizedC R = 0 := by
      have hrelK : k * normalizedB R =
          (C.data.sourceX + A.depth - uH R) * normalizedA R +
            (C.data.sourceZ - (j + vH R)) * normalizedC R := by
        have hxc : ((C.data.sourceX + A.depth - uH R : ℕ) : ℤ) =
            (C.data.sourceX + A.depth : ℤ) - uH R := Nat.cast_sub hxge
        have hzc : ((C.data.sourceZ - (j + vH R) : ℕ) : ℤ) =
            (C.data.sourceZ : ℤ) - (j + vH R) := Nat.cast_sub hzge
        apply Int.ofNat_inj.mp
        push_cast only [Nat.cast_mul, Nat.cast_add]
        rw [hxc, hzc]
        nlinarith only [hdiffZ]
      rw [hk0, zero_mul] at hrelK
      exact hrelK.symm
    have hxzero : C.data.sourceX + A.depth - uH R = 0 := by
      by_contra hn
      have hp0 := Nat.mul_pos (Nat.pos_of_ne_zero hn) ha
      omega
    omega
  have hzEq : C.data.sourceZ = j + vH R := by
    have hryiEq : C.data.returnedY + i = L5A2B4AR4R2B.c2 R := by omega
    have hrel0 : (C.data.returnedY + i) * normalizedB R =
        uH R * normalizedA R + vH R * normalizedC R := by
      rw [hryiEq]
      exact hrel2
    rw [hxEq] at hrelB
    have hmul : (C.data.sourceZ - j) * normalizedC R =
        vH R * normalizedC R := by omega
    have hcoef : C.data.sourceZ - j = vH R :=
      Nat.eq_of_mul_eq_mul_right hc hmul
    omega
  have hryEq : C.data.returnedY + i = L5A2B4AR4R2B.c2 R := by omega
  have hdepth : A.depth < uH R := by omega
  refine ⟨hdepth, ?_, ?_⟩
  · rw [hsource]
    have hxsub : C.data.sourceX = uH R - A.depth := by omega
    rw [hxsub, hzEq]
  · rw [hreturned]
    have hrsub : C.data.returnedY = L5A2B4AR4R2B.c2 R - i := by omega
    rw [hrsub]

private theorem actual_lShape_coordinate_eq_of_exact
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

theorem branchB_individual_return_center_O_canonical_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.a
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.source_coordinate.i = 0 ∧ C.source_coordinate.j = 0 ∧
      C.source_coordinate.level =
        ((L5A2B4AR4R2B.c1 R - A.depth : ℕ) : ℤ) ∧
      C.returned_coordinate.i = ((pH R - i : ℕ) : ℤ) ∧
      C.returned_coordinate.j = ((qH R - j : ℕ) : ℤ) ∧
      C.returned_coordinate.level = 0 := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hv := branchB_individual_return_center_O_value_pair R hB hs i j
    ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩ hroute
  obtain ⟨hp, hq, hu, hvp, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  obtain ⟨_, hs2, hs3⟩ :=
    (branchB_actual_herzog_coordinates R).coefficient_sums
  have hsShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) 0 0 := by
    unfold L5A2B.InLShape
    omega
  have hrShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      (pH R - i : ℕ) (qH R - j : ℕ) := by
    unfold L5A2B.InLShape
    push_cast
    omega
  have hsExact : (C.data.sourceValue : ℤ) =
      (L5A2B4AR4R2B.c1 R - A.depth : ℕ) * normalizedA R +
        (0 : ℤ) * normalizedB R + (0 : ℤ) * normalizedC R := by
    have hcast : (C.data.sourceValue : ℤ) =
        (((L5A2B4AR4R2B.c1 R - A.depth) * normalizedA R : ℕ) : ℤ) := by
      exact_mod_cast hv.2.1
    simpa using hcast
  have hrExact : (C.data.returnedValue : ℤ) =
      (0 : ℤ) * normalizedA R + (pH R - i : ℕ) * normalizedB R +
        (qH R - j : ℕ) * normalizedC R := by
    have hcast : (C.data.returnedValue : ℤ) =
        (((pH R - i) * normalizedB R +
          (qH R - j) * normalizedC R : ℕ) : ℤ) := by exact_mod_cast hv.2.2
    push_cast at hcast
    simpa using hcast
  obtain ⟨hsi, hsj, hsl⟩ := actual_lShape_coordinate_eq_of_exact R
    C.source_coordinate 0 0
      ((L5A2B4AR4R2B.c1 R - A.depth : ℕ) : ℤ) hsShape hsExact
  obtain ⟨hri, hrj, hrl⟩ := actual_lShape_coordinate_eq_of_exact R
    C.returned_coordinate ((pH R - i : ℕ) : ℤ)
      ((qH R - j : ℕ) : ℤ) 0 hrShape hrExact
  exact ⟨hsi, hsj, hsl, hri, hrj, hrl⟩

theorem branchB_individual_return_center_X_canonical_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i < pH R ∧ 1 ≤ j ∧ j ≤ qH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ab
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.source_coordinate.i = i + zH R ∧ C.source_coordinate.j = 0 ∧
      C.source_coordinate.level = ((wH R - A.depth : ℕ) : ℤ) ∧
      C.returned_coordinate.i = 0 ∧
      C.returned_coordinate.j =
        ((L5A2B4AR4R2B.c3 R - j : ℕ) : ℤ) ∧
      C.returned_coordinate.level = 0 := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i < pH R ∧ 1 ≤ j ∧ j ≤ qH R at hcenter
  rcases hcenter with ⟨hi, hj, hiPos, hiLt, hjPos, hjLe⟩
  have hv := branchB_individual_return_center_X_value_pair R hB hs i j
    ⟨hi, hj, hiPos, hiLt, hjPos, hjLe⟩ hroute
  obtain ⟨hp, hq, hu, hvp, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  obtain ⟨_, hs2, hs3⟩ :=
    (branchB_actual_herzog_coordinates R).coefficient_sums
  have hsShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      (i + zH R : ℕ) 0 := by
    unfold L5A2B.InLShape
    refine ⟨by positivity, by norm_num, ?_, ?_, Or.inr ?_⟩
    · exact_mod_cast Nat.add_lt_add_right hiLt (zH R)
    · exact_mod_cast Nat.add_pos_left hq (vH R)
    · exact_mod_cast hq
  have hrShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      0 (L5A2B4AR4R2B.c3 R - j : ℕ) := by
    unfold L5A2B.InLShape
    have hbound : L5A2B4AR4R2B.c3 R - j < qH R + vH R := by omega
    refine ⟨by norm_num, by positivity, ?_, ?_, Or.inl ?_⟩
    · exact_mod_cast Nat.add_pos_left hp (zH R)
    · exact_mod_cast hbound
    · exact_mod_cast hp
  have hsExact : (C.data.sourceValue : ℤ) =
      (wH R - A.depth : ℕ) * normalizedA R +
        (i + zH R : ℕ) * normalizedB R + (0 : ℤ) * normalizedC R := by
    have hcast : (C.data.sourceValue : ℤ) =
        (((wH R - A.depth) * normalizedA R +
          (i + zH R) * normalizedB R : ℕ) : ℤ) := by exact_mod_cast hv.2.1
    push_cast at hcast
    simpa using hcast
  have hrExact : (C.data.returnedValue : ℤ) =
      (0 : ℤ) * normalizedA R + (0 : ℤ) * normalizedB R +
        (L5A2B4AR4R2B.c3 R - j : ℕ) * normalizedC R := by
    have hcast : (C.data.returnedValue : ℤ) =
        (((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) : ℤ) := by
      exact_mod_cast hv.2.2
    simpa using hcast
  obtain ⟨hsi, hsj, hsl⟩ := actual_lShape_coordinate_eq_of_exact R
    C.source_coordinate ((i + zH R : ℕ) : ℤ) 0
      ((wH R - A.depth : ℕ) : ℤ) hsShape hsExact
  obtain ⟨hri, hrj, hrl⟩ := actual_lShape_coordinate_eq_of_exact R
    C.returned_coordinate 0
      ((L5A2B4AR4R2B.c3 R - j : ℕ) : ℤ) 0 hrShape hrExact
  exact ⟨hsi, hsj, hsl, hri, hrj, hrl⟩

theorem branchB_individual_return_center_Y_canonical_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j < qH R)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.ac
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.source_coordinate.i = 0 ∧ C.source_coordinate.j = j + vH R ∧
      C.source_coordinate.level = ((uH R - A.depth : ℕ) : ℤ) ∧
      C.returned_coordinate.i =
        ((L5A2B4AR4R2B.c2 R - i : ℕ) : ℤ) ∧
      C.returned_coordinate.j = 0 ∧ C.returned_coordinate.level = 0 := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j < qH R at hcenter
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLt⟩
  have hv := branchB_individual_return_center_Y_value_pair R hB hs i j
    ⟨hi, hj, hiPos, hiLe, hjPos, hjLt⟩ hroute
  obtain ⟨hp, hq, hu, hvp, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  obtain ⟨_, hs2, hs3⟩ :=
    (branchB_actual_herzog_coordinates R).coefficient_sums
  have hsShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      0 (j + vH R : ℕ) := by
    unfold L5A2B.InLShape
    refine ⟨by norm_num, by positivity, ?_, ?_, Or.inl ?_⟩
    · exact_mod_cast Nat.add_pos_left hp (zH R)
    · exact_mod_cast Nat.add_lt_add_right hjLt (vH R)
    · exact_mod_cast hp
  have hrShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      (L5A2B4AR4R2B.c2 R - i : ℕ) 0 := by
    unfold L5A2B.InLShape
    have hbound : L5A2B4AR4R2B.c2 R - i < pH R + zH R := by omega
    refine ⟨by positivity, by norm_num, ?_, ?_, Or.inr ?_⟩
    · exact_mod_cast hbound
    · exact_mod_cast Nat.add_pos_left hq (vH R)
    · exact_mod_cast hq
  have hsExact : (C.data.sourceValue : ℤ) =
      (uH R - A.depth : ℕ) * normalizedA R + (0 : ℤ) * normalizedB R +
        (j + vH R : ℕ) * normalizedC R := by
    have hcast : (C.data.sourceValue : ℤ) =
        (((uH R - A.depth) * normalizedA R +
          (j + vH R) * normalizedC R : ℕ) : ℤ) := by exact_mod_cast hv.2.1
    push_cast at hcast
    simpa using hcast
  have hrExact : (C.data.returnedValue : ℤ) =
      (0 : ℤ) * normalizedA R +
        (L5A2B4AR4R2B.c2 R - i : ℕ) * normalizedB R +
        (0 : ℤ) * normalizedC R := by
    have hcast : (C.data.returnedValue : ℤ) =
        (((L5A2B4AR4R2B.c2 R - i) * normalizedB R : ℕ) : ℤ) := by
      exact_mod_cast hv.2.2
    simpa using hcast
  obtain ⟨hsi, hsj, hsl⟩ := actual_lShape_coordinate_eq_of_exact R
    C.source_coordinate 0 ((j + vH R : ℕ) : ℤ)
      ((uH R - A.depth : ℕ) : ℤ) hsShape hsExact
  obtain ⟨hri, hrj, hrl⟩ := actual_lShape_coordinate_eq_of_exact R
    C.returned_coordinate ((L5A2B4AR4R2B.c2 R - i : ℕ) : ℤ)
      0 0 hrShape hrExact
  exact ⟨hsi, hsj, hsl, hri, hrj, hrl⟩

/-- Canonical-coordinate recovery for the F value pair.  This is deliberately
proved only after equality of the actual values; no chosen factorization is
declared canonical. -/
theorem branchB_individual_return_F_canonical_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.bc
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.source_coordinate.i = A.coordinate.i ∧
      C.source_coordinate.j = A.coordinate.j ∧
      C.source_coordinate.level = A.coordinate.level ∧
      C.source_chart = A.chart ∧
      C.returned_coordinate.i = 0 ∧
      C.returned_coordinate.j = 0 ∧
      C.returned_coordinate.level = A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  have hvalues := branchB_individual_return_F_value_pair R hB hs hroute
  have hsourceZ : (C.data.sourceValue : ℤ) = A.beta := hvalues.1
  have hsourceMod : Int.ModEq (normalizedA R)
      (C.source_coordinate.i * normalizedB R +
        C.source_coordinate.j * normalizedC R) A.beta := by
    rw [Int.modEq_iff_dvd]
    refine ⟨C.source_coordinate.level, ?_⟩
    rw [← hsourceZ] at ⊢
    nlinarith [C.source_coordinate.exact_eq]
  obtain ⟨hsi, hsj⟩ := A.coordinate.pair_unique
    C.source_coordinate.i C.source_coordinate.j
    C.source_coordinate.in_lShape hsourceMod
  have hsl : C.source_coordinate.level = A.coordinate.level := by
    apply A.coordinate.level_unique C.source_coordinate.level
    calc
      A.beta = (C.data.sourceValue : ℤ) := hsourceZ.symm
      _ = C.source_coordinate.level * normalizedA R +
          C.source_coordinate.i * normalizedB R +
          C.source_coordinate.j * normalizedC R :=
        C.source_coordinate.exact_eq
      _ = C.source_coordinate.level * normalizedA R +
          A.coordinate.i * normalizedB R +
          A.coordinate.j * normalizedC R := by rw [hsi, hsj]
  have hsourceChartAtAnchor :
      InActualLShapeChart R C.source_chart A.coordinate.i A.coordinate.j := by
    simpa [hsi, hsj] using C.source_in_chart
  have hchart : C.source_chart = A.chart := by
    let hu := branchB_actual_center_rb_lt_chart_unique R A.coordinate.in_lShape
    exact (hu.choose_spec.2 C.source_chart hsourceChartAtAnchor).trans
      (hu.choose_spec.2 A.chart A.coordinate_in_chart).symm
  obtain ⟨hp, hq, hz, hv, _, _⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  have hzeroShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R) 0 0 := by
    simp only [L5A2B.InLShape]
    omega
  have hreturnedZ : (C.data.returnedValue : ℤ) =
      A.depth * normalizedA R := by
    exact_mod_cast hvalues.2
  have hreturnedMod : Int.ModEq (normalizedA R) (0 * normalizedB R +
      0 * normalizedC R) C.data.returnedValue := by
    rw [Int.modEq_iff_dvd]
    refine ⟨A.depth, ?_⟩
    rw [hreturnedZ]
    push_cast
    ring
  obtain ⟨hri, hrj⟩ := C.returned_coordinate.pair_unique 0 0
    hzeroShape hreturnedMod
  have hrl : C.returned_coordinate.level = A.depth := by
    symm
    apply C.returned_coordinate.level_unique A.depth
    calc
      (C.data.returnedValue : ℤ) =
          A.depth * normalizedA R := hreturnedZ
      _ = A.depth * normalizedA R +
          C.returned_coordinate.i * normalizedB R +
          C.returned_coordinate.j * normalizedC R := by
        rw [← hri, ← hrj]
        push_cast
        ring
  exact ⟨hsi, hsj, hsl, hchart, hri.symm, hrj.symm, hrl⟩

/-- The depth bound common to every positive CENTER anchor.  It is derived
locally from the anchor equation and the first actual Herzog relation; it is
not a global chart-depth premise. -/
theorem branchB_positive_center_depth_lt_c1
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hcenter :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R)) :
    (branchB_actual_selected_return_anchor_v2 R hB hs).depth <
      L5A2B4AR4R2B.c1 R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
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
  rw [Nat.mul_comm (normalizedA R) A.depth] at hanchorNat
  have hnpos : 0 < A.n := by
    have hn0 : A.n ≠ 0 := by
      intro hn
      apply A.n_not_mem
      simpa [hn] using (normalizedH P.M.base).zero_mem
    exact Nat.pos_of_ne_zero hn0
  have hrel1 := (branchB_actual_herzog_coordinates R).normalized_relations.1
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  by_contra hnot
  have hdge : L5A2B4AR4R2B.c1 R ≤ A.depth := Nat.le_of_not_gt hnot
  have hda := Nat.mul_le_mul_right (normalizedA R) hdge
  have hib := Nat.mul_le_mul_right (normalizedB R) hiLe
  have hjc := Nat.mul_le_mul_right (normalizedC R) hjLe
  omega

/-- On a chosen pure-`b` source support the returned support is exactly one
of `a`, `c`, or `a+c`.  This is a derived split, not an oracle and not a
selected-anchor axis statement. -/
theorem branchB_positive_center_pureB_returned_support_split
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.returnedY = 0 ∧
      ((C.data.returnedX ≠ 0 ∧ C.data.returnedZ = 0) ∨
       (C.data.returnedX = 0 ∧ C.data.returnedZ ≠ 0) ∨
       (C.data.returnedX ≠ 0 ∧ C.data.returnedZ ≠ 0)) := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hsign := branchB_selected_return_source_returned_sign_corner R hB hs
  have hry : C.data.returnedY = 0 := hsign.2.1.resolve_left hroute'.2.1
  have hreturned0 :=
    (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.1
  refine ⟨hry, ?_⟩
  by_cases hrx : C.data.returnedX = 0
  · right
    left
    refine ⟨hrx, ?_⟩
    intro hrz
    apply hreturned0
    rw [C.data.returned_factorization, hrx, hry, hrz]
    simp
  · by_cases hrz : C.data.returnedZ = 0
    · exact Or.inl ⟨hrx, hrz⟩
    · exact Or.inr (Or.inr ⟨hrx, hrz⟩)

/-- Exact signed balance retained on a chosen pure-`b` source support. -/
theorem branchB_positive_center_pureB_signed_balance
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hij :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceY : ℤ) - i) * normalizedB R) =
      ((C.data.returnedZ + j : ℕ) : ℤ) * normalizedC R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j at hij
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hry := (branchB_positive_center_pureB_returned_support_split
    R hB hs hroute).1
  have hbalance := (branchB_selected_return_source_balance_packet R hB hs).2.1
  rw [hroute'.1, hroute'.2.2, hry, hij.1, hij.2] at hbalance
  push_cast at hbalance ⊢
  nlinarith only [hbalance]

/-- Cyclic-dual returned-support split for a chosen pure-`c` source support. -/
theorem branchB_positive_center_pureC_returned_support_split
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.returnedZ = 0 ∧
      ((C.data.returnedX ≠ 0 ∧ C.data.returnedY = 0) ∨
       (C.data.returnedX = 0 ∧ C.data.returnedY ≠ 0) ∨
       (C.data.returnedX ≠ 0 ∧ C.data.returnedY ≠ 0)) := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hsign := branchB_selected_return_source_returned_sign_corner R hB hs
  have hrz : C.data.returnedZ = 0 := hsign.2.2.resolve_left hroute'.2.2
  have hreturned0 :=
    (branchB_selected_return_nonzero_packet R hB hs).2.2.2.2.1
  refine ⟨hrz, ?_⟩
  by_cases hrx : C.data.returnedX = 0
  · right
    left
    refine ⟨hrx, ?_⟩
    intro hry
    apply hreturned0
    rw [C.data.returned_factorization, hrx, hry, hrz]
    simp
  · by_cases hry : C.data.returnedY = 0
    · exact Or.inl ⟨hrx, hry⟩
    · exact Or.inr (Or.inr ⟨hrx, hry⟩)

/-- Exact cyclic-dual signed balance retained on a chosen pure-`c` source
support. -/
theorem branchB_positive_center_pureC_signed_balance
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (i j : ℕ)
    (hij :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.coordinate.i = i ∧ A.coordinate.j = j)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
        (((C.data.sourceZ : ℤ) - j) * normalizedC R) =
      ((C.data.returnedY + i : ℕ) : ℤ) * normalizedB R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j at hij
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hrz := (branchB_positive_center_pureC_returned_support_split
    R hB hs hroute).1
  have hbalance := (branchB_selected_return_source_balance_packet R hB hs).2.1
  rw [hroute'.1, hroute'.2.1, hrz, hij.1, hij.2] at hbalance
  push_cast at hbalance ⊢
  nlinarith only [hbalance]

/-- The pure-`b` / returned-`a` subcase is impossible.  The two signed
orientations are discharged respectively by first/third critical minimality;
the only remaining orientation exposes a common positive `a` in source and
return after substituting the second actual Herzog relation, contradicting
minimality in the individual return ideal. -/
theorem branchB_positive_center_pureB_returnedX_impossible
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ = 0) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX ≠ 0 at hrx
  change C.data.returnedZ = 0 at hrz
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hry := (branchB_positive_center_pureB_returned_support_split
    R hB hs hroute).1
  have hbalance := branchB_positive_center_pureB_signed_balance R hB hs i j
    ⟨hi, hj⟩ hroute
  change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
      (((C.data.sourceY : ℤ) - i) * normalizedB R) =
    ((C.data.returnedZ + j : ℕ) : ℤ) * normalizedC R at hbalance
  rw [hrz, zero_add] at hbalance
  have hdepth := branchB_positive_center_depth_lt_c1 R hB hs i j
    ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  by_cases hyLe : C.data.sourceY ≤ i
  · have hxLt : C.data.returnedX < A.depth := by
      by_contra hnot
      have hdLe : A.depth ≤ C.data.returnedX := Nat.le_of_not_gt hnot
      have hja : 0 < (j : ℤ) * normalizedC R := by positivity
      have hya : ((C.data.sourceY : ℤ) - i) * normalizedB R ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (by exact_mod_cast hyLe)) (by positivity)
      have hda : ((A.depth : ℤ) - C.data.returnedX) * normalizedA R ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (by exact_mod_cast hdLe)) (by positivity)
      nlinarith only [hbalance, hja, hya, hda]
    have hrelA : (A.depth - C.data.returnedX) * normalizedA R =
        (i - C.data.sourceY) * normalizedB R + j * normalizedC R := by
      have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
          A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxLt)
      have hyCast : ((i - C.data.sourceY : ℕ) : ℤ) =
          i - C.data.sourceY := Nat.cast_sub hyLe
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hyCast]
      nlinarith only [hbalance]
    have hminA := branchB_normalizedA_relation_min R _ _ _
      (Nat.sub_pos_of_lt hxLt) hrelA
    have hsmall : A.depth - C.data.returnedX < L5A2B4AR4R2B.c1 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hdepth
    omega
  · have hyGt : i < C.data.sourceY := Nat.lt_of_not_ge hyLe
    have hdLt : A.depth < C.data.returnedX := by
      by_contra hnot
      have hxLe : C.data.returnedX ≤ A.depth := Nat.le_of_not_gt hnot
      have hrelC : j * normalizedC R =
          (A.depth - C.data.returnedX) * normalizedA R +
            (C.data.sourceY - i) * normalizedB R := by
        have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
            A.depth - C.data.returnedX := Nat.cast_sub hxLe
        have hyCast : ((C.data.sourceY - i : ℕ) : ℤ) =
            C.data.sourceY - i := Nat.cast_sub (Nat.le_of_lt hyGt)
        apply Int.ofNat_inj.mp
        push_cast only [Nat.cast_mul, Nat.cast_add]
        rw [hxCast, hyCast]
        nlinarith only [hbalance]
      have hminC := branchB_normalizedC_relation_min R _ _ _ hjPos hrelC
      have hjSmall : j < L5A2B4AR4R2B.c3 R := by omega
      omega
    have hrelB : (C.data.sourceY - i) * normalizedB R =
        (C.data.returnedX - A.depth) * normalizedA R +
          j * normalizedC R := by
      have hxCast : ((C.data.returnedX - A.depth : ℕ) : ℤ) =
          C.data.returnedX - A.depth := Nat.cast_sub (Nat.le_of_lt hdLt)
      have hyCast : ((C.data.sourceY - i : ℕ) : ℤ) =
          C.data.sourceY - i := Nat.cast_sub (Nat.le_of_lt hyGt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hyCast]
      nlinarith only [hbalance]
    have hminB := branchB_normalizedB_relation_min R _ _ _
      (Nat.sub_pos_of_lt hyGt) hrelB
    have hcy : L5A2B4AR4R2B.c2 R ≤ C.data.sourceY := by omega
    have hsource : C.data.sourceValue = C.data.sourceY * normalizedB R := by
      rw [C.data.source_factorization, hroute'.1, hroute'.2.2]
      omega
    have hreturned : C.data.returnedValue =
        C.data.returnedX * normalizedA R := by
      rw [C.data.returned_factorization, hry, hrz]
      omega
    let H := normalizedH P.M.base
    have hcomb (x y z : ℕ) :
        x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
      have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
      have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
      have hz' := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
      simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz'
    let sourceRest := (uH R - 1) * normalizedA R +
      (C.data.sourceY - L5A2B4AR4R2B.c2 R) * normalizedB R +
      vH R * normalizedC R
    let returnedRest := (C.data.returnedX - 1) * normalizedA R
    apply minimal_return_common_generator_impossible H
      C.data.return_witness.2.2
      (branchB_actual_normalizedA_mem R) ha.ne'
      (hcomb _ _ _) (by simpa [returnedRest] using hcomb (C.data.returnedX - 1) 0 0)
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (normalizedA R : ℤ) + sourceRest := by
          rw [hsource]
          have hys := Nat.sub_add_cancel hcy
          have hus := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hu.ne')
          have huSplit : uH R * normalizedA R =
              normalizedA R + (uH R - 1) * normalizedA R := by
            calc
              uH R * normalizedA R = (uH R - 1 + 1) * normalizedA R := by rw [hus]
              _ = normalizedA R + (uH R - 1) * normalizedA R := by ring
          have hNat : C.data.sourceY * normalizedB R =
              normalizedA R + sourceRest := by
            dsimp [sourceRest]
            calc
              C.data.sourceY * normalizedB R =
                  ((C.data.sourceY - L5A2B4AR4R2B.c2 R) +
                    L5A2B4AR4R2B.c2 R) * normalizedB R := by rw [hys]
              _ = normalizedA R +
                  ((uH R - 1) * normalizedA R +
                    (C.data.sourceY - L5A2B4AR4R2B.c2 R) * normalizedB R +
                    vH R * normalizedC R) := by
                rw [Nat.add_mul, hrel2, huSplit]
                ring
          exact_mod_cast hNat
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (normalizedA R : ℤ) + returnedRest := by
          rw [hreturned]
          have hrs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hrx)
          have hNat : C.data.returnedX * normalizedA R =
              normalizedA R + returnedRest := by
            dsimp [returnedRest]
            calc
              C.data.returnedX * normalizedA R =
                  (C.data.returnedX - 1 + 1) * normalizedA R := by rw [hrs]
              _ = normalizedA R +
                  (C.data.returnedX - 1) * normalizedA R := by ring
          exact_mod_cast hNat

/-- Cyclic-dual pure-`c` / returned-`a` subcase impossibility. -/
theorem branchB_positive_center_pureC_returnedX_impossible
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hry :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedY = 0) : False := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX ≠ 0 at hrx
  change C.data.returnedY = 0 at hry
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hrz := (branchB_positive_center_pureC_returned_support_split
    R hB hs hroute).1
  have hbalance := branchB_positive_center_pureC_signed_balance R hB hs i j
    ⟨hi, hj⟩ hroute
  change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
      (((C.data.sourceZ : ℤ) - j) * normalizedC R) =
    ((C.data.returnedY + i : ℕ) : ℤ) * normalizedB R at hbalance
  rw [hry, zero_add] at hbalance
  have hdepth := branchB_positive_center_depth_lt_c1 R hB hs i j
    ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  by_cases hzLe : C.data.sourceZ ≤ j
  · have hxLt : C.data.returnedX < A.depth := by
      by_contra hnot
      have hdLe : A.depth ≤ C.data.returnedX := Nat.le_of_not_gt hnot
      have hib : 0 < (i : ℤ) * normalizedB R := by positivity
      have hza : ((C.data.sourceZ : ℤ) - j) * normalizedC R ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (by exact_mod_cast hzLe)) (by positivity)
      have hda : ((A.depth : ℤ) - C.data.returnedX) * normalizedA R ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (by exact_mod_cast hdLe)) (by positivity)
      nlinarith only [hbalance, hib, hza, hda]
    have hrelA : (A.depth - C.data.returnedX) * normalizedA R =
        i * normalizedB R + (j - C.data.sourceZ) * normalizedC R := by
      have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
          A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxLt)
      have hzCast : ((j - C.data.sourceZ : ℕ) : ℤ) =
          j - C.data.sourceZ := Nat.cast_sub hzLe
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hzCast]
      nlinarith only [hbalance]
    have hminA := branchB_normalizedA_relation_min R _ _ _
      (Nat.sub_pos_of_lt hxLt) hrelA
    have hsmall : A.depth - C.data.returnedX < L5A2B4AR4R2B.c1 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hdepth
    omega
  · have hzGt : j < C.data.sourceZ := Nat.lt_of_not_ge hzLe
    have hdLt : A.depth < C.data.returnedX := by
      by_contra hnot
      have hxLe : C.data.returnedX ≤ A.depth := Nat.le_of_not_gt hnot
      have hrelB : i * normalizedB R =
          (A.depth - C.data.returnedX) * normalizedA R +
            (C.data.sourceZ - j) * normalizedC R := by
        have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
            A.depth - C.data.returnedX := Nat.cast_sub hxLe
        have hzCast : ((C.data.sourceZ - j : ℕ) : ℤ) =
            C.data.sourceZ - j := Nat.cast_sub (Nat.le_of_lt hzGt)
        apply Int.ofNat_inj.mp
        push_cast only [Nat.cast_mul, Nat.cast_add]
        rw [hxCast, hzCast]
        nlinarith only [hbalance]
      have hminB := branchB_normalizedB_relation_min R _ _ _ hiPos hrelB
      have hiSmall : i < L5A2B4AR4R2B.c2 R := by omega
      omega
    have hrelC : (C.data.sourceZ - j) * normalizedC R =
        (C.data.returnedX - A.depth) * normalizedA R +
          i * normalizedB R := by
      have hxCast : ((C.data.returnedX - A.depth : ℕ) : ℤ) =
          C.data.returnedX - A.depth := Nat.cast_sub (Nat.le_of_lt hdLt)
      have hzCast : ((C.data.sourceZ - j : ℕ) : ℤ) =
          C.data.sourceZ - j := Nat.cast_sub (Nat.le_of_lt hzGt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hzCast]
      nlinarith only [hbalance]
    have hminC := branchB_normalizedC_relation_min R _ _ _
      (Nat.sub_pos_of_lt hzGt) hrelC
    have hcz : L5A2B4AR4R2B.c3 R ≤ C.data.sourceZ := by omega
    have hsource : C.data.sourceValue = C.data.sourceZ * normalizedC R := by
      rw [C.data.source_factorization, hroute'.1, hroute'.2.1]
      omega
    have hreturned : C.data.returnedValue =
        C.data.returnedX * normalizedA R := by
      rw [C.data.returned_factorization, hry, hrz]
      omega
    let H := normalizedH P.M.base
    have hcomb (x y z : ℕ) :
        x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
      have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
      have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
      have hz' := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
      simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz'
    let sourceRest := (wH R - 1) * normalizedA R +
      zH R * normalizedB R +
      (C.data.sourceZ - L5A2B4AR4R2B.c3 R) * normalizedC R
    let returnedRest := (C.data.returnedX - 1) * normalizedA R
    apply minimal_return_common_generator_impossible H
      C.data.return_witness.2.2
      (branchB_actual_normalizedA_mem R) ha.ne'
      (hcomb _ _ _) (by simpa [returnedRest] using hcomb (C.data.returnedX - 1) 0 0)
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (normalizedA R : ℤ) + sourceRest := by
          rw [hsource]
          have hzs := Nat.sub_add_cancel hcz
          have hws := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hw.ne')
          have hwSplit : wH R * normalizedA R =
              normalizedA R + (wH R - 1) * normalizedA R := by
            calc
              wH R * normalizedA R = (wH R - 1 + 1) * normalizedA R := by rw [hws]
              _ = normalizedA R + (wH R - 1) * normalizedA R := by ring
          have hNat : C.data.sourceZ * normalizedC R =
              normalizedA R + sourceRest := by
            dsimp [sourceRest]
            calc
              C.data.sourceZ * normalizedC R =
                  ((C.data.sourceZ - L5A2B4AR4R2B.c3 R) +
                    L5A2B4AR4R2B.c3 R) * normalizedC R := by rw [hzs]
              _ = normalizedA R +
                  ((wH R - 1) * normalizedA R + zH R * normalizedB R +
                    (C.data.sourceZ - L5A2B4AR4R2B.c3 R) * normalizedC R) := by
                rw [Nat.add_mul, hrel3, hwSplit]
                ring
          exact_mod_cast hNat
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (normalizedA R : ℤ) + returnedRest := by
          rw [hreturned]
          have hrs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hrx)
          have hNat : C.data.returnedX * normalizedA R =
              normalizedA R + returnedRest := by
            dsimp [returnedRest]
            calc
              C.data.returnedX * normalizedA R =
                  (C.data.returnedX - 1 + 1) * normalizedA R := by rw [hrs]
              _ = normalizedA R +
                  (C.data.returnedX - 1) * normalizedA R := by ring
          exact_mod_cast hNat

/-- Exact kernel constraints for the first surviving pure-support case:
pure `b` source and pure `c` return.  They retain the sharp third-critical
equality range instead of silently discarding it. -/
theorem branchB_positive_center_pureB_returnedZ_constraints
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX = 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ ≠ 0) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    i ≤ C.data.sourceY ∧
      L5A2B4AR4R2B.c3 R ≤ C.data.returnedZ + j ∧
      C.data.returnedZ < L5A2B4AR4R2B.c3 R ∧
      L5A2B4AR4R2B.c3 R - j ≤ C.data.returnedZ := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX = 0 at hrx
  change C.data.returnedZ ≠ 0 at hrz
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hry := (branchB_positive_center_pureB_returned_support_split
    R hB hs hroute).1
  have hbalance := branchB_positive_center_pureB_signed_balance R hB hs i j
    ⟨hi, hj⟩ hroute
  change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
      (((C.data.sourceY : ℤ) - i) * normalizedB R) =
    ((C.data.returnedZ + j : ℕ) : ℤ) * normalizedC R at hbalance
  rw [hrx, Nat.cast_zero, sub_zero] at hbalance
  have hbalance' :
      (A.depth : ℤ) * normalizedA R +
          ((C.data.sourceY : ℤ) - i) * normalizedB R =
        ((C.data.returnedZ : ℤ) + j) * normalizedC R := by
    simpa only [Nat.cast_add] using hbalance
  have hdepth := branchB_positive_center_depth_lt_c1 R hB hs i j
    ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  have hyLe : i ≤ C.data.sourceY := by
    by_contra hnot
    have hyLt : C.data.sourceY < i := Nat.lt_of_not_ge hnot
    have hrelA : A.depth * normalizedA R =
        (i - C.data.sourceY) * normalizedB R +
          (C.data.returnedZ + j) * normalizedC R := by
      have hyCast : ((i - C.data.sourceY : ℕ) : ℤ) =
          i - C.data.sourceY := Nat.cast_sub (Nat.le_of_lt hyLt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hyCast]
      nlinarith only [hbalance']
    have hminA := branchB_normalizedA_relation_min R _ _ _
      (by
        by_contra hd0
        have : A.depth = 0 := Nat.eq_zero_of_not_pos hd0
        rw [this, zero_mul] at hrelA
        have hpos := Nat.mul_pos (Nat.sub_pos_of_lt hyLt) hb
        omega) hrelA
    have hsmall : A.depth < L5A2B4AR4R2B.c1 R := hdepth
    omega
  have hrelC : (C.data.returnedZ + j) * normalizedC R =
      A.depth * normalizedA R +
        (C.data.sourceY - i) * normalizedB R := by
    have hyCast : ((C.data.sourceY - i : ℕ) : ℤ) =
        C.data.sourceY - i := Nat.cast_sub hyLe
    apply Int.ofNat_inj.mp
    push_cast only [Nat.cast_mul, Nat.cast_add]
    rw [hyCast]
    nlinarith only [hbalance']
  have hc3Le : L5A2B4AR4R2B.c3 R ≤ C.data.returnedZ + j :=
    branchB_normalizedC_relation_min R _ _ _ (by omega) hrelC
  have hsource : C.data.sourceValue = C.data.sourceY * normalizedB R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.2]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hrx, hry]
    omega
  have hrzLt : C.data.returnedZ < L5A2B4AR4R2B.c3 R := by
    by_contra hnot
    have hc3z : L5A2B4AR4R2B.c3 R ≤ C.data.returnedZ := Nat.le_of_not_gt hnot
    let H := normalizedH P.M.base
    have hcomb (x y z : ℕ) :
        x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
      have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
      have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
      have hz' := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
      simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz'
    let sourceRest := (C.data.sourceY - 1) * normalizedB R
    let returnedRest := wH R * normalizedA R +
      (zH R - 1) * normalizedB R +
      (C.data.returnedZ - L5A2B4AR4R2B.c3 R) * normalizedC R
    apply minimal_return_common_generator_impossible H
      C.data.return_witness.2.2
      (branchB_actual_normalizedB_mem R) hb.ne'
      (by simpa [sourceRest] using hcomb 0 (C.data.sourceY - 1) 0)
      (hcomb _ _ _)
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (normalizedB R : ℤ) + sourceRest := by
          rw [hsource]
          have hys := Nat.sub_add_cancel
            (Nat.one_le_iff_ne_zero.mpr hroute'.2.1)
          have hNat : C.data.sourceY * normalizedB R =
              normalizedB R + sourceRest := by
            dsimp [sourceRest]
            calc
              C.data.sourceY * normalizedB R =
                  (C.data.sourceY - 1 + 1) * normalizedB R := by rw [hys]
              _ = normalizedB R +
                  (C.data.sourceY - 1) * normalizedB R := by ring
          exact_mod_cast hNat
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (normalizedB R : ℤ) + returnedRest := by
          rw [hreturned]
          have hzs := Nat.sub_add_cancel hc3z
          have hzOne := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz.ne')
          have hzSplit : zH R * normalizedB R =
              normalizedB R + (zH R - 1) * normalizedB R := by
            calc
              zH R * normalizedB R = (zH R - 1 + 1) * normalizedB R := by rw [hzOne]
              _ = normalizedB R + (zH R - 1) * normalizedB R := by ring
          have hNat : C.data.returnedZ * normalizedC R =
              normalizedB R + returnedRest := by
            dsimp [returnedRest]
            calc
              C.data.returnedZ * normalizedC R =
                  ((C.data.returnedZ - L5A2B4AR4R2B.c3 R) +
                    L5A2B4AR4R2B.c3 R) * normalizedC R := by rw [hzs]
              _ = normalizedB R +
                  (wH R * normalizedA R + (zH R - 1) * normalizedB R +
                    (C.data.returnedZ - L5A2B4AR4R2B.c3 R) * normalizedC R) := by
                rw [Nat.add_mul, hrel3, hzSplit]
                ring
          exact_mod_cast hNat
  have hlast : L5A2B4AR4R2B.c3 R - j ≤ C.data.returnedZ := by
    have hsub := Nat.sub_le_sub_right hc3Le j
    simpa [Nat.add_sub_cancel_right] using hsub
  exact ⟨hyLe, hc3Le, hrzLt, hlast⟩

private theorem branchB_positive_center_pureB_returnedC_degenerate_packet
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX = 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ ≠ 0) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      A.depth = wH R ∧ C.data.sourceY = i + zH R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX = 0 at hrx
  change C.data.returnedZ ≠ 0 at hrz
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hry := (branchB_positive_center_pureB_returned_support_split
    R hB hs hroute).1
  have hconstraints := branchB_positive_center_pureB_returnedZ_constraints
    R hB hs i j ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩ hroute hrx hrz
  change i ≤ C.data.sourceY ∧
      L5A2B4AR4R2B.c3 R ≤ C.data.returnedZ + j ∧
      C.data.returnedZ < L5A2B4AR4R2B.c3 R ∧
      L5A2B4AR4R2B.c3 R - j ≤ C.data.returnedZ at hconstraints
  obtain ⟨hyLe, hc3Le, hrzLt, _⟩ := hconstraints
  have hdepth := branchB_positive_center_depth_lt_c1 R hB hs i j
    ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hbalance := branchB_positive_center_pureB_signed_balance R hB hs i j
    ⟨hi, hj⟩ hroute
  change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
      (((C.data.sourceY : ℤ) - i) * normalizedB R) =
    ((C.data.returnedZ + j : ℕ) : ℤ) * normalizedC R at hbalance
  rw [hrx, Nat.cast_zero, sub_zero] at hbalance
  have hbalance' :
      (A.depth : ℤ) * normalizedA R +
          ((C.data.sourceY : ℤ) - i) * normalizedB R =
        ((C.data.returnedZ : ℤ) + j) * normalizedC R := by
    simpa only [Nat.cast_add] using hbalance
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  have hsource : C.data.sourceValue = C.data.sourceY * normalizedB R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.2]
    omega
  have hreturned : C.data.returnedValue = C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hrx, hry]
    omega
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz' := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz'
  have commonImpossible (g sourceRest returnedRest : ℕ)
      (hgH : g ∈ H) (hg0 : g ≠ 0)
      (hsH : sourceRest ∈ H) (hrH : returnedRest ∈ H)
      (hsplit : C.data.sourceValue = g + sourceRest)
      (hrsplit : C.data.returnedValue = g + returnedRest) : False := by
    apply minimal_return_common_generator_impossible H C.data.return_witness.2.2
      hgH hg0 hsH hrH
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (g : ℤ) + sourceRest := by exact_mod_cast hsplit
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (g : ℤ) + returnedRest := by exact_mod_cast hrsplit
  have hsourceY_lt_c2 : C.data.sourceY < L5A2B4AR4R2B.c2 R := by
    by_contra hnot
    have hle : L5A2B4AR4R2B.c2 R ≤ C.data.sourceY := Nat.le_of_not_gt hnot
    let sourceRest := uH R * normalizedA R +
      (C.data.sourceY - L5A2B4AR4R2B.c2 R) * normalizedB R +
      (vH R - 1) * normalizedC R
    let returnedRest := (C.data.returnedZ - 1) * normalizedC R
    apply commonImpossible (normalizedC R) sourceRest returnedRest
      (branchB_actual_normalizedC_mem R) hc.ne'
      (hcomb _ _ _) (by
        simpa [returnedRest] using hcomb 0 0 (C.data.returnedZ - 1))
    · rw [hsource]
      dsimp [sourceRest]
      have hys := Nat.sub_add_cancel hle
      have hvs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv.ne')
      have hvsplit : vH R * normalizedC R =
          normalizedC R + (vH R - 1) * normalizedC R := by
        calc
          vH R * normalizedC R = (vH R - 1 + 1) * normalizedC R := by rw [hvs]
          _ = normalizedC R + (vH R - 1) * normalizedC R := by ring
      calc
        C.data.sourceY * normalizedB R =
            ((C.data.sourceY - L5A2B4AR4R2B.c2 R) +
              L5A2B4AR4R2B.c2 R) * normalizedB R := by rw [hys]
        _ = normalizedC R +
              (uH R * normalizedA R +
                (C.data.sourceY - L5A2B4AR4R2B.c2 R) * normalizedB R +
                (vH R - 1) * normalizedC R) := by
          rw [Nat.add_mul, hrel2, hvsplit]
          ring
    · rw [hreturned]
      dsimp [returnedRest]
      have hrs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hrz)
      calc
        C.data.returnedZ * normalizedC R =
            (C.data.returnedZ - 1 + 1) * normalizedC R := by rw [hrs]
        _ = normalizedC R + (C.data.returnedZ - 1) * normalizedC R := by ring
  let k := C.data.returnedZ + j - L5A2B4AR4R2B.c3 R
  have hkZ : (k : ℤ) =
      C.data.returnedZ + j - L5A2B4AR4R2B.c3 R := by
    dsimp [k]
    rw [Nat.cast_sub hc3Le]
    push_cast
    rfl
  have hrel3Z : (L5A2B4AR4R2B.c3 R : ℤ) * normalizedC R =
      (wH R : ℤ) * normalizedA R + (zH R : ℤ) * normalizedB R := by
    exact_mod_cast hrel3
  have hdiffZ :
      ((A.depth : ℤ) - wH R) * normalizedA R +
          ((C.data.sourceY : ℤ) - i - zH R) * normalizedB R =
        (k : ℤ) * normalizedC R := by
    calc
      ((A.depth : ℤ) - wH R) * normalizedA R +
            ((C.data.sourceY : ℤ) - i - zH R) * normalizedB R =
          ((A.depth : ℤ) * normalizedA R +
              ((C.data.sourceY : ℤ) - i) * normalizedB R) -
            ((wH R : ℤ) * normalizedA R + (zH R : ℤ) * normalizedB R) := by ring
      _ = ((C.data.returnedZ : ℤ) + j) * normalizedC R -
            (L5A2B4AR4R2B.c3 R : ℤ) * normalizedC R := by
          rw [hbalance', hrel3Z]
      _ = (k : ℤ) * normalizedC R := by rw [hkZ]; ring
  have hxge : wH R ≤ A.depth := by
    by_contra hnot
    have hxlt : A.depth < wH R := Nat.lt_of_not_ge hnot
    have hygt : i + zH R < C.data.sourceY := by
      by_contra hynot
      have hyle : C.data.sourceY ≤ i + zH R := Nat.le_of_not_gt hynot
      have hzeroZ :
          ((wH R - A.depth : ℕ) : ℤ) * normalizedA R +
              ((i + zH R - C.data.sourceY : ℕ) : ℤ) * normalizedB R +
              (k : ℤ) * normalizedC R = 0 := by
        have hxcast : ((wH R - A.depth : ℕ) : ℤ) =
            (wH R : ℤ) - A.depth := Nat.cast_sub (Nat.le_of_lt hxlt)
        have hycast : ((i + zH R - C.data.sourceY : ℕ) : ℤ) =
            (i + zH R : ℤ) - C.data.sourceY := Nat.cast_sub hyle
        rw [hxcast, hycast]
        calc
          ((wH R : ℤ) - A.depth) * normalizedA R +
                ((i + zH R : ℤ) - C.data.sourceY) * normalizedB R +
                (k : ℤ) * normalizedC R =
              -(((A.depth : ℤ) - wH R) * normalizedA R +
                ((C.data.sourceY : ℤ) - i - zH R) * normalizedB R) +
                (k : ℤ) * normalizedC R := by push_cast; ring
          _ = 0 := by rw [hdiffZ]; ring
      have hpositive : 0 < (wH R - A.depth) * normalizedA R :=
        Nat.mul_pos (Nat.sub_pos_of_lt hxlt) ha
      have hzeroNat :
          (wH R - A.depth) * normalizedA R +
              (i + zH R - C.data.sourceY) * normalizedB R +
              k * normalizedC R = 0 := by exact_mod_cast hzeroZ
      omega
    have hrelB : (C.data.sourceY - (i + zH R)) * normalizedB R =
        (wH R - A.depth) * normalizedA R + k * normalizedC R := by
      have hyge' : i + zH R ≤ C.data.sourceY := Nat.le_of_lt hygt
      have hxc : ((wH R - A.depth : ℕ) : ℤ) =
          (wH R : ℤ) - A.depth := Nat.cast_sub (Nat.le_of_lt hxlt)
      have hyc : ((C.data.sourceY - (i + zH R) : ℕ) : ℤ) =
          (C.data.sourceY : ℤ) - (i + zH R) := Nat.cast_sub hyge'
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    have hminB := branchB_normalizedB_relation_min R _ _ _
      (Nat.sub_pos_of_lt hygt) hrelB
    omega
  have hyge : i + zH R ≤ C.data.sourceY := by
    by_contra hnot
    have hylt : C.data.sourceY < i + zH R := Nat.lt_of_not_ge hnot
    have hrelA : (A.depth - wH R) * normalizedA R =
        (i + zH R - C.data.sourceY) * normalizedB R + k * normalizedC R := by
      have hxc : ((A.depth - wH R : ℕ) : ℤ) =
          (A.depth : ℤ) - wH R := Nat.cast_sub hxge
      have hyc : ((i + zH R - C.data.sourceY : ℕ) : ℤ) =
          (i + zH R : ℤ) - C.data.sourceY :=
        Nat.cast_sub (Nat.le_of_lt hylt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    have hqpos : 0 < A.depth - wH R := by
      by_contra hzq
      have heq : A.depth = wH R := by omega
      rw [heq, Nat.sub_self, zero_mul] at hrelA
      have hbpos := Nat.mul_pos (Nat.sub_pos_of_lt hylt) hb
      omega
    have hminA := branchB_normalizedA_relation_min R _ _ _ hqpos hrelA
    have hsmall : A.depth - wH R < L5A2B4AR4R2B.c1 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hdepth
    exact (Nat.not_le_of_gt hsmall) hminA
  have hk0 : k = 0 := by
    by_contra hkne
    have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
    have hrelK : k * normalizedC R =
        (A.depth - wH R) * normalizedA R +
          (C.data.sourceY - (i + zH R)) * normalizedB R := by
      have hxc : ((A.depth - wH R : ℕ) : ℤ) =
          (A.depth : ℤ) - wH R := Nat.cast_sub hxge
      have hyc : ((C.data.sourceY - (i + zH R) : ℕ) : ℤ) =
          (C.data.sourceY : ℤ) - (i + zH R) := Nat.cast_sub hyge
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    have hminK := branchB_normalizedC_relation_min R _ _ _ hkpos hrelK
    have hklt : k < L5A2B4AR4R2B.c3 R := by
      dsimp [k]
      omega
    omega
  have hsumEq : C.data.returnedZ + j = L5A2B4AR4R2B.c3 R := by
    dsimp [k] at hk0
    omega
  have hzero :
      (A.depth - wH R) * normalizedA R +
        (C.data.sourceY - (i + zH R)) * normalizedB R = 0 := by
    have hrelK : k * normalizedC R =
        (A.depth - wH R) * normalizedA R +
          (C.data.sourceY - (i + zH R)) * normalizedB R := by
      have hxc : ((A.depth - wH R : ℕ) : ℤ) =
          (A.depth : ℤ) - wH R := Nat.cast_sub hxge
      have hyc : ((C.data.sourceY - (i + zH R) : ℕ) : ℤ) =
          (C.data.sourceY : ℤ) - (i + zH R) := Nat.cast_sub hyge
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    rw [hk0, zero_mul] at hrelK
    exact hrelK.symm
  have hxzero : A.depth - wH R = 0 := by
    by_contra hn
    have hpos := Nat.mul_pos (Nat.pos_of_ne_zero hn) ha
    omega
  have hyzero : C.data.sourceY - (i + zH R) = 0 := by
    by_contra hn
    have hpos := Nat.mul_pos (Nat.pos_of_ne_zero hn) hb
    omega
  have hxEq : A.depth = wH R := by omega
  have hyEq : C.data.sourceY = i + zH R := by omega
  have hrEq : C.data.returnedZ = L5A2B4AR4R2B.c3 R - j := by omega
  exact ⟨hrEq, hxEq, hyEq⟩

theorem branchB_positive_center_pureB_returnedZ_eq
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX = 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ ≠ 0) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.returnedZ = L5A2B4AR4R2B.c3 R - j := by
  exact (branchB_positive_center_pureB_returnedC_degenerate_packet
    R hB hs i j hcenter hroute hrx hrz).1

theorem branchB_positive_center_pureB_returnedC_degenerate
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX = 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ ≠ 0) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      A.depth = wH R ∧ C.data.sourceY = i + zH R := by
  exact branchB_positive_center_pureB_returnedC_degenerate_packet
    R hB hs i j hcenter hroute hrx hrz

theorem branchB_positive_center_pureC_returnedB_degenerate
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX = 0)
    (hry :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedY ≠ 0) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.returnedY = L5A2B4AR4R2B.c2 R - i ∧
      A.depth = uH R ∧ C.data.sourceZ = j + vH R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX = 0 at hrx
  change C.data.returnedY ≠ 0 at hry
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hrz := (branchB_positive_center_pureC_returned_support_split
    R hB hs hroute).1
  have hdepth := branchB_positive_center_depth_lt_c1 R hB hs i j
    ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hbalance := branchB_positive_center_pureC_signed_balance R hB hs i j
    ⟨hi, hj⟩ hroute
  change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
      (((C.data.sourceZ : ℤ) - j) * normalizedC R) =
    ((C.data.returnedY + i : ℕ) : ℤ) * normalizedB R at hbalance
  rw [hrx, Nat.cast_zero, sub_zero] at hbalance
  have hbalance' :
      (A.depth : ℤ) * normalizedA R +
          ((C.data.sourceZ : ℤ) - j) * normalizedC R =
        ((C.data.returnedY : ℤ) + i) * normalizedB R := by
    simpa only [Nat.cast_add] using hbalance
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  have hzLe : j ≤ C.data.sourceZ := by
    by_contra hnot
    have hzLt : C.data.sourceZ < j := Nat.lt_of_not_ge hnot
    have hrelA : A.depth * normalizedA R =
        (C.data.returnedY + i) * normalizedB R +
          (j - C.data.sourceZ) * normalizedC R := by
      have hzCast : ((j - C.data.sourceZ : ℕ) : ℤ) =
          j - C.data.sourceZ := Nat.cast_sub (Nat.le_of_lt hzLt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hzCast]
      nlinarith only [hbalance']
    have hapos : 0 < A.depth := by
      by_contra hd0
      have : A.depth = 0 := Nat.eq_zero_of_not_pos hd0
      rw [this, zero_mul] at hrelA
      have hpos := Nat.mul_pos (Nat.sub_pos_of_lt hzLt) hc
      omega
    have hminA := branchB_normalizedA_relation_min R _ _ _ hapos hrelA
    exact (Nat.not_le_of_gt hdepth) hminA
  have hrelB : (C.data.returnedY + i) * normalizedB R =
      A.depth * normalizedA R + (C.data.sourceZ - j) * normalizedC R := by
    have hzCast : ((C.data.sourceZ - j : ℕ) : ℤ) =
        C.data.sourceZ - j := Nat.cast_sub hzLe
    apply Int.ofNat_inj.mp
    push_cast only [Nat.cast_mul, Nat.cast_add]
    rw [hzCast]
    nlinarith only [hbalance']
  have hc2Le : L5A2B4AR4R2B.c2 R ≤ C.data.returnedY + i :=
    branchB_normalizedB_relation_min R _ _ _ (by omega) hrelB
  have hsource : C.data.sourceValue = C.data.sourceZ * normalizedC R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.1]
    omega
  have hreturned : C.data.returnedValue = C.data.returnedY * normalizedB R := by
    rw [C.data.returned_factorization, hrx, hrz]
    omega
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz' := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz'
  have commonImpossible (g sourceRest returnedRest : ℕ)
      (hgH : g ∈ H) (hg0 : g ≠ 0)
      (hsH : sourceRest ∈ H) (hrH : returnedRest ∈ H)
      (hsplit : C.data.sourceValue = g + sourceRest)
      (hrsplit : C.data.returnedValue = g + returnedRest) : False := by
    apply minimal_return_common_generator_impossible H C.data.return_witness.2.2
      hgH hg0 hsH hrH
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (g : ℤ) + sourceRest := by exact_mod_cast hsplit
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (g : ℤ) + returnedRest := by exact_mod_cast hrsplit
  have hreturnedY_lt_c2 : C.data.returnedY < L5A2B4AR4R2B.c2 R := by
    by_contra hnot
    have hle : L5A2B4AR4R2B.c2 R ≤ C.data.returnedY := Nat.le_of_not_gt hnot
    let sourceRest := (C.data.sourceZ - 1) * normalizedC R
    let returnedRest := uH R * normalizedA R +
      (C.data.returnedY - L5A2B4AR4R2B.c2 R) * normalizedB R +
      (vH R - 1) * normalizedC R
    apply commonImpossible (normalizedC R) sourceRest returnedRest
      (branchB_actual_normalizedC_mem R) hc.ne'
      (by simpa [sourceRest] using hcomb 0 0 (C.data.sourceZ - 1))
      (hcomb _ _ _)
    · rw [hsource]
      dsimp [sourceRest]
      have hzs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hroute'.2.2)
      calc
        C.data.sourceZ * normalizedC R =
            (C.data.sourceZ - 1 + 1) * normalizedC R := by rw [hzs]
        _ = normalizedC R + (C.data.sourceZ - 1) * normalizedC R := by ring
    · rw [hreturned]
      dsimp [returnedRest]
      have hys := Nat.sub_add_cancel hle
      have hvs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv.ne')
      have hvsplit : vH R * normalizedC R =
          normalizedC R + (vH R - 1) * normalizedC R := by
        calc
          vH R * normalizedC R = (vH R - 1 + 1) * normalizedC R := by rw [hvs]
          _ = normalizedC R + (vH R - 1) * normalizedC R := by ring
      calc
        C.data.returnedY * normalizedB R =
            ((C.data.returnedY - L5A2B4AR4R2B.c2 R) +
              L5A2B4AR4R2B.c2 R) * normalizedB R := by rw [hys]
        _ = normalizedC R +
              (uH R * normalizedA R +
                (C.data.returnedY - L5A2B4AR4R2B.c2 R) * normalizedB R +
                (vH R - 1) * normalizedC R) := by
          rw [Nat.add_mul, hrel2, hvsplit]
          ring
  have hreturnedY_ge_z : zH R ≤ C.data.returnedY := by omega
  have hsourceZ_lt_c3 : C.data.sourceZ < L5A2B4AR4R2B.c3 R := by
    by_contra hnot
    have hle : L5A2B4AR4R2B.c3 R ≤ C.data.sourceZ := Nat.le_of_not_gt hnot
    let sourceRest := wH R * normalizedA R +
      (zH R - 1) * normalizedB R +
      (C.data.sourceZ - L5A2B4AR4R2B.c3 R) * normalizedC R
    let returnedRest := (C.data.returnedY - 1) * normalizedB R
    apply commonImpossible (normalizedB R) sourceRest returnedRest
      (branchB_actual_normalizedB_mem R) hb.ne'
      (hcomb _ _ _) (by
        simpa [returnedRest] using hcomb 0 (C.data.returnedY - 1) 0)
    · rw [hsource]
      dsimp [sourceRest]
      have hzs := Nat.sub_add_cancel hle
      have hzOne := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz.ne')
      have hzSplit : zH R * normalizedB R =
          normalizedB R + (zH R - 1) * normalizedB R := by
        calc
          zH R * normalizedB R = (zH R - 1 + 1) * normalizedB R := by rw [hzOne]
          _ = normalizedB R + (zH R - 1) * normalizedB R := by ring
      calc
        C.data.sourceZ * normalizedC R =
            ((C.data.sourceZ - L5A2B4AR4R2B.c3 R) +
              L5A2B4AR4R2B.c3 R) * normalizedC R := by rw [hzs]
        _ = normalizedB R +
              (wH R * normalizedA R + (zH R - 1) * normalizedB R +
                (C.data.sourceZ - L5A2B4AR4R2B.c3 R) * normalizedC R) := by
          rw [Nat.add_mul, hrel3, hzSplit]
          ring
    · rw [hreturned]
      dsimp [returnedRest]
      have hys := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hry)
      calc
        C.data.returnedY * normalizedB R =
            (C.data.returnedY - 1 + 1) * normalizedB R := by rw [hys]
        _ = normalizedB R + (C.data.returnedY - 1) * normalizedB R := by ring
  let k := C.data.returnedY + i - L5A2B4AR4R2B.c2 R
  have hkZ : (k : ℤ) =
      C.data.returnedY + i - L5A2B4AR4R2B.c2 R := by
    dsimp [k]
    rw [Nat.cast_sub hc2Le]
    push_cast
    rfl
  have hrel2Z : (L5A2B4AR4R2B.c2 R : ℤ) * normalizedB R =
      (uH R : ℤ) * normalizedA R + (vH R : ℤ) * normalizedC R := by
    exact_mod_cast hrel2
  have hdiffZ :
      ((A.depth : ℤ) - uH R) * normalizedA R +
          ((C.data.sourceZ : ℤ) - j - vH R) * normalizedC R =
        (k : ℤ) * normalizedB R := by
    calc
      ((A.depth : ℤ) - uH R) * normalizedA R +
            ((C.data.sourceZ : ℤ) - j - vH R) * normalizedC R =
          ((A.depth : ℤ) * normalizedA R +
              ((C.data.sourceZ : ℤ) - j) * normalizedC R) -
            ((uH R : ℤ) * normalizedA R + (vH R : ℤ) * normalizedC R) := by ring
      _ = ((C.data.returnedY : ℤ) + i) * normalizedB R -
            (L5A2B4AR4R2B.c2 R : ℤ) * normalizedB R := by
          rw [hbalance', hrel2Z]
      _ = (k : ℤ) * normalizedB R := by rw [hkZ]; ring
  have hxge : uH R ≤ A.depth := by
    by_contra hnot
    have hxlt : A.depth < uH R := Nat.lt_of_not_ge hnot
    have hzgt : j + vH R < C.data.sourceZ := by
      by_contra hznot
      have hzle : C.data.sourceZ ≤ j + vH R := Nat.le_of_not_gt hznot
      have hzeroZ :
          ((uH R - A.depth : ℕ) : ℤ) * normalizedA R +
              ((j + vH R - C.data.sourceZ : ℕ) : ℤ) * normalizedC R +
              (k : ℤ) * normalizedB R = 0 := by
        have hxcast : ((uH R - A.depth : ℕ) : ℤ) =
            (uH R : ℤ) - A.depth := Nat.cast_sub (Nat.le_of_lt hxlt)
        have hzcast : ((j + vH R - C.data.sourceZ : ℕ) : ℤ) =
            (j + vH R : ℤ) - C.data.sourceZ := Nat.cast_sub hzle
        rw [hxcast, hzcast]
        calc
          ((uH R : ℤ) - A.depth) * normalizedA R +
                ((j + vH R : ℤ) - C.data.sourceZ) * normalizedC R +
                (k : ℤ) * normalizedB R =
              -(((A.depth : ℤ) - uH R) * normalizedA R +
                ((C.data.sourceZ : ℤ) - j - vH R) * normalizedC R) +
                (k : ℤ) * normalizedB R := by push_cast; ring
          _ = 0 := by rw [hdiffZ]; ring
      have hpositive : 0 < (uH R - A.depth) * normalizedA R :=
        Nat.mul_pos (Nat.sub_pos_of_lt hxlt) ha
      have hzeroNat :
          (uH R - A.depth) * normalizedA R +
              (j + vH R - C.data.sourceZ) * normalizedC R +
              k * normalizedB R = 0 := by exact_mod_cast hzeroZ
      omega
    have hrelC : (C.data.sourceZ - (j + vH R)) * normalizedC R =
        (uH R - A.depth) * normalizedA R + k * normalizedB R := by
      have hzge' : j + vH R ≤ C.data.sourceZ := Nat.le_of_lt hzgt
      have hxc : ((uH R - A.depth : ℕ) : ℤ) =
          (uH R : ℤ) - A.depth := Nat.cast_sub (Nat.le_of_lt hxlt)
      have hzc : ((C.data.sourceZ - (j + vH R) : ℕ) : ℤ) =
          (C.data.sourceZ : ℤ) - (j + vH R) := Nat.cast_sub hzge'
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    have hminC := branchB_normalizedC_relation_min R _ _ _
      (Nat.sub_pos_of_lt hzgt) hrelC
    exact (Nat.not_le_of_gt (lt_of_le_of_lt (Nat.sub_le _ _) hsourceZ_lt_c3)) hminC
  have hzge : j + vH R ≤ C.data.sourceZ := by
    by_contra hnot
    have hzlt : C.data.sourceZ < j + vH R := Nat.lt_of_not_ge hnot
    have hrelA : (A.depth - uH R) * normalizedA R =
        k * normalizedB R + (j + vH R - C.data.sourceZ) * normalizedC R := by
      have hxc : ((A.depth - uH R : ℕ) : ℤ) =
          (A.depth : ℤ) - uH R := Nat.cast_sub hxge
      have hzc : ((j + vH R - C.data.sourceZ : ℕ) : ℤ) =
          (j + vH R : ℤ) - C.data.sourceZ := Nat.cast_sub (Nat.le_of_lt hzlt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    have hqpos : 0 < A.depth - uH R := by
      by_contra hzq
      have heq : A.depth = uH R := by omega
      rw [heq, Nat.sub_self, zero_mul] at hrelA
      have hcpos := Nat.mul_pos (Nat.sub_pos_of_lt hzlt) hc
      omega
    have hminA := branchB_normalizedA_relation_min R _ _ _ hqpos hrelA
    have hsmall : A.depth - uH R < L5A2B4AR4R2B.c1 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hdepth
    exact (Nat.not_le_of_gt hsmall) hminA
  have hk0 : k = 0 := by
    by_contra hkne
    have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
    have hrelK : k * normalizedB R =
        (A.depth - uH R) * normalizedA R +
          (C.data.sourceZ - (j + vH R)) * normalizedC R := by
      have hxc : ((A.depth - uH R : ℕ) : ℤ) =
          (A.depth : ℤ) - uH R := Nat.cast_sub hxge
      have hzc : ((C.data.sourceZ - (j + vH R) : ℕ) : ℤ) =
          (C.data.sourceZ : ℤ) - (j + vH R) := Nat.cast_sub hzge
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    have hminK := branchB_normalizedB_relation_min R _ _ _ hkpos hrelK
    have hklt : k < L5A2B4AR4R2B.c2 R := by
      dsimp [k]
      omega
    exact (Nat.not_le_of_gt hklt) hminK
  have hsumEq : C.data.returnedY + i = L5A2B4AR4R2B.c2 R := by
    dsimp [k] at hk0
    omega
  have hzero :
      (A.depth - uH R) * normalizedA R +
        (C.data.sourceZ - (j + vH R)) * normalizedC R = 0 := by
    have hrelK : k * normalizedB R =
        (A.depth - uH R) * normalizedA R +
          (C.data.sourceZ - (j + vH R)) * normalizedC R := by
      have hxc : ((A.depth - uH R : ℕ) : ℤ) =
          (A.depth : ℤ) - uH R := Nat.cast_sub hxge
      have hzc : ((C.data.sourceZ - (j + vH R) : ℕ) : ℤ) =
          (C.data.sourceZ : ℤ) - (j + vH R) := Nat.cast_sub hzge
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    rw [hk0, zero_mul] at hrelK
    exact hrelK.symm
  have hxzero : A.depth - uH R = 0 := by
    by_contra hn
    have hpos := Nat.mul_pos (Nat.pos_of_ne_zero hn) ha
    omega
  have hzzero : C.data.sourceZ - (j + vH R) = 0 := by
    by_contra hn
    have hpos := Nat.mul_pos (Nat.pos_of_ne_zero hn) hc
    omega
  have hxEq : A.depth = uH R := by omega
  have hzEq : C.data.sourceZ = j + vH R := by omega
  have hrEq : C.data.returnedY = L5A2B4AR4R2B.c2 R - i := by omega
  exact ⟨hrEq, hxEq, hzEq⟩

theorem branchB_positive_center_pureB_mixed_sourceY_lt_c2
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ ≠ 0) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceY < L5A2B4AR4R2B.c2 R := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
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
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz
  obtain ⟨_, _, hu, hv, _, _⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  obtain ⟨_, hrel2, _⟩ :=
    (branchB_actual_herzog_coordinates R).normalized_relations
  by_contra hnot
  have hle : L5A2B4AR4R2B.c2 R ≤ C.data.sourceY := Nat.le_of_not_gt hnot
  let sourceRest := (uH R - 1) * normalizedA R +
    (C.data.sourceY - L5A2B4AR4R2B.c2 R) * normalizedB R +
    vH R * normalizedC R
  let returnedRest := (C.data.returnedX - 1) * normalizedA R +
    C.data.returnedZ * normalizedC R
  apply minimal_return_common_generator_impossible
    (g := normalizedA R) (x := sourceRest) (y := returnedRest)
    H C.data.return_witness.2.2
    (branchB_actual_normalizedA_mem R)
    (branchB_actual_normalizedA_pos R).ne'
    (by simpa [sourceRest] using
      (hcomb (uH R - 1) (C.data.sourceY - L5A2B4AR4R2B.c2 R) (vH R)))
    (by simpa [returnedRest] using
      (hcomb (C.data.returnedX - 1) 0 C.data.returnedZ))
  · calc
      s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
      _ = (normalizedA R : ℤ) + sourceRest := by
        rw [hsource]
        have hys := Nat.sub_add_cancel hle
        have hus := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hu.ne')
        have huSplit : uH R * normalizedA R =
            normalizedA R + (uH R - 1) * normalizedA R := by
          calc
            uH R * normalizedA R = (uH R - 1 + 1) * normalizedA R := by rw [hus]
            _ = normalizedA R + (uH R - 1) * normalizedA R := by ring
        have hNat : C.data.sourceY * normalizedB R =
            normalizedA R + sourceRest := by
          dsimp [sourceRest]
          calc
            C.data.sourceY * normalizedB R =
                ((C.data.sourceY - L5A2B4AR4R2B.c2 R) +
                  L5A2B4AR4R2B.c2 R) * normalizedB R := by rw [hys]
            _ = normalizedA R +
                ((uH R - 1) * normalizedA R +
                  (C.data.sourceY - L5A2B4AR4R2B.c2 R) * normalizedB R +
                  vH R * normalizedC R) := by
              rw [Nat.add_mul, hrel2, huSplit]
              ring
        exact_mod_cast hNat
  · calc
      s - (C.data.ell * normalizedM P.M.base : ℕ) =
          (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
      _ = (normalizedA R : ℤ) + returnedRest := by
        rw [hreturned]
        have hxs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hrx)
        have hNat : C.data.returnedX * normalizedA R +
            C.data.returnedZ * normalizedC R =
            normalizedA R + returnedRest := by
          dsimp [returnedRest]
          calc
            C.data.returnedX * normalizedA R + C.data.returnedZ * normalizedC R =
                (C.data.returnedX - 1 + 1) * normalizedA R +
                  C.data.returnedZ * normalizedC R := by rw [hxs]
            _ = normalizedA R +
                ((C.data.returnedX - 1) * normalizedA R +
                  C.data.returnedZ * normalizedC R) := by ring
        exact_mod_cast hNat

theorem branchB_positive_center_pureC_mixed_sourceZ_lt_c3
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s)
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hry :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedY ≠ 0) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.sourceZ < L5A2B4AR4R2B.c3 R := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
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
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz
  obtain ⟨_, _, _, _, hw, hz⟩ :=
    (branchB_actual_herzog_coordinates R).cross_positive
  obtain ⟨_, _, hrel3⟩ :=
    (branchB_actual_herzog_coordinates R).normalized_relations
  by_contra hnot
  have hle : L5A2B4AR4R2B.c3 R ≤ C.data.sourceZ := Nat.le_of_not_gt hnot
  let sourceRest := (wH R - 1) * normalizedA R +
    zH R * normalizedB R +
    (C.data.sourceZ - L5A2B4AR4R2B.c3 R) * normalizedC R
  let returnedRest := (C.data.returnedX - 1) * normalizedA R +
    C.data.returnedY * normalizedB R
  apply minimal_return_common_generator_impossible
    (g := normalizedA R) (x := sourceRest) (y := returnedRest)
    H C.data.return_witness.2.2
    (branchB_actual_normalizedA_mem R)
    (branchB_actual_normalizedA_pos R).ne'
    (by simpa [sourceRest] using (hcomb (wH R - 1) (zH R)
      (C.data.sourceZ - L5A2B4AR4R2B.c3 R)))
    (by simpa [returnedRest] using
      (hcomb (C.data.returnedX - 1) C.data.returnedY 0))
  · calc
      s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
      _ = (normalizedA R : ℤ) + sourceRest := by
        rw [hsource]
        have hzs := Nat.sub_add_cancel hle
        have hws := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hw.ne')
        have hwSplit : wH R * normalizedA R =
            normalizedA R + (wH R - 1) * normalizedA R := by
          calc
            wH R * normalizedA R = (wH R - 1 + 1) * normalizedA R := by rw [hws]
            _ = normalizedA R + (wH R - 1) * normalizedA R := by ring
        have hNat : C.data.sourceZ * normalizedC R =
            normalizedA R + sourceRest := by
          dsimp [sourceRest]
          calc
            C.data.sourceZ * normalizedC R =
                ((C.data.sourceZ - L5A2B4AR4R2B.c3 R) +
                  L5A2B4AR4R2B.c3 R) * normalizedC R := by rw [hzs]
            _ = normalizedA R +
                ((wH R - 1) * normalizedA R + zH R * normalizedB R +
                  (C.data.sourceZ - L5A2B4AR4R2B.c3 R) * normalizedC R) := by
              rw [Nat.add_mul, hrel3, hwSplit]
              ring
        exact_mod_cast hNat
  · calc
      s - (C.data.ell * normalizedM P.M.base : ℕ) =
          (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
      _ = (normalizedA R : ℤ) + returnedRest := by
        rw [hreturned]
        have hxs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hrx)
        have hNat : C.data.returnedX * normalizedA R +
            C.data.returnedY * normalizedB R =
            normalizedA R + returnedRest := by
          dsimp [returnedRest]
          calc
            C.data.returnedX * normalizedA R + C.data.returnedY * normalizedB R =
                (C.data.returnedX - 1 + 1) * normalizedA R +
                  C.data.returnedY * normalizedB R := by rw [hxs]
            _ = normalizedA R +
                ((C.data.returnedX - 1) * normalizedA R +
                  C.data.returnedY * normalizedB R) := by ring
        exact_mod_cast hNat

/-- A mixed returned support over a chosen pure-`b` source is still forced
onto the same `c`-boundary packet as the one-tail case.  The positive
returned `a` coefficient is absorbed into the depth, so the resulting depth
strictly exceeds `wH`. -/
theorem branchB_positive_center_pureB_mixed_degenerate
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hrz :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedZ ≠ 0) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      C.data.sourceY = i + zH R ∧
      A.depth = wH R + C.data.returnedX ∧ wH R < A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX ≠ 0 at hrx
  change C.data.returnedZ ≠ 0 at hrz
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hry := (branchB_positive_center_pureB_returned_support_split
    R hB hs hroute).1
  have hdepth := branchB_positive_center_depth_lt_c1 R hB hs i j
    ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hsourceYlt := branchB_positive_center_pureB_mixed_sourceY_lt_c2
    R hB hs hroute hrx hrz
  change C.data.sourceY < L5A2B4AR4R2B.c2 R at hsourceYlt
  have hbalance := branchB_positive_center_pureB_signed_balance R hB hs i j
    ⟨hi, hj⟩ hroute
  change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
      (((C.data.sourceY : ℤ) - i) * normalizedB R) =
    ((C.data.returnedZ + j : ℕ) : ℤ) * normalizedC R at hbalance
  have hbalanceExpanded :
      (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
          (((C.data.sourceY : ℤ) - i) * normalizedB R) =
        ((C.data.returnedZ : ℤ) + j) * normalizedC R := by
    simpa only [Nat.cast_add] using hbalance
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  have hxLt : C.data.returnedX < A.depth := by
    by_contra hnot
    have hdLe : A.depth ≤ C.data.returnedX := Nat.le_of_not_gt hnot
    have hyGt : i < C.data.sourceY := by
      by_contra hynot
      have hyLe : C.data.sourceY ≤ i := Nat.le_of_not_gt hynot
      have hleftA : ((A.depth : ℤ) - C.data.returnedX) * normalizedA R ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (by exact_mod_cast hdLe)) (by positivity)
      have hleftB : ((C.data.sourceY : ℤ) - i) * normalizedB R ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (by exact_mod_cast hyLe)) (by positivity)
      have hright : 0 < ((C.data.returnedZ + j : ℕ) : ℤ) * normalizedC R := by
        positivity
      nlinarith only [hbalance, hleftA, hleftB, hright]
    have hrelB : (C.data.sourceY - i) * normalizedB R =
        (C.data.returnedX - A.depth) * normalizedA R +
          (C.data.returnedZ + j) * normalizedC R := by
      have hxCast : ((C.data.returnedX - A.depth : ℕ) : ℤ) =
          C.data.returnedX - A.depth := Nat.cast_sub hdLe
      have hyCast : ((C.data.sourceY - i : ℕ) : ℤ) =
          C.data.sourceY - i := Nat.cast_sub (Nat.le_of_lt hyGt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hyCast]
      nlinarith only [hbalanceExpanded]
    have hminB := branchB_normalizedB_relation_min R _ _ _
      (Nat.sub_pos_of_lt hyGt) hrelB
    have hsmall : C.data.sourceY - i < L5A2B4AR4R2B.c2 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hsourceYlt
    omega
  have hyGt : i < C.data.sourceY := by
    by_contra hnot
    have hyLe : C.data.sourceY ≤ i := Nat.le_of_not_gt hnot
    have hrelA : (A.depth - C.data.returnedX) * normalizedA R =
        (i - C.data.sourceY) * normalizedB R +
          (C.data.returnedZ + j) * normalizedC R := by
      have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
          A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxLt)
      have hyCast : ((i - C.data.sourceY : ℕ) : ℤ) =
          i - C.data.sourceY := Nat.cast_sub hyLe
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hyCast]
      nlinarith only [hbalanceExpanded]
    have hminA := branchB_normalizedA_relation_min R _ _ _
      (Nat.sub_pos_of_lt hxLt) hrelA
    have hsmall : A.depth - C.data.returnedX < L5A2B4AR4R2B.c1 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hdepth
    omega
  have hc3Le : L5A2B4AR4R2B.c3 R ≤ C.data.returnedZ + j := by
    have hrelC : (C.data.returnedZ + j) * normalizedC R =
        (A.depth - C.data.returnedX) * normalizedA R +
          (C.data.sourceY - i) * normalizedB R := by
      have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
          A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxLt)
      have hyCast : ((C.data.sourceY - i : ℕ) : ℤ) =
          C.data.sourceY - i := Nat.cast_sub (Nat.le_of_lt hyGt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hyCast]
      nlinarith only [hbalanceExpanded]
    exact branchB_normalizedC_relation_min R _ _ _ (by omega) hrelC
  have hsource : C.data.sourceValue = C.data.sourceY * normalizedB R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.2]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedX * normalizedA R + C.data.returnedZ * normalizedC R := by
    rw [C.data.returned_factorization, hry]
    omega
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz' := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz'
  have commonImpossible (g sourceRest returnedRest : ℕ)
      (hgH : g ∈ H) (hg0 : g ≠ 0)
      (hsH : sourceRest ∈ H) (hrH : returnedRest ∈ H)
      (hsplit : C.data.sourceValue = g + sourceRest)
      (hrsplit : C.data.returnedValue = g + returnedRest) : False := by
    apply minimal_return_common_generator_impossible H C.data.return_witness.2.2
      hgH hg0 hsH hrH
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (g : ℤ) + sourceRest := by exact_mod_cast hsplit
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (g : ℤ) + returnedRest := by exact_mod_cast hrsplit
  have hrzLt : C.data.returnedZ < L5A2B4AR4R2B.c3 R := by
    by_contra hnot
    have hle : L5A2B4AR4R2B.c3 R ≤ C.data.returnedZ := Nat.le_of_not_gt hnot
    let sourceRest := (C.data.sourceY - 1) * normalizedB R
    let returnedRest := (C.data.returnedX + wH R) * normalizedA R +
      (zH R - 1) * normalizedB R +
      (C.data.returnedZ - L5A2B4AR4R2B.c3 R) * normalizedC R
    apply commonImpossible (normalizedB R) sourceRest returnedRest
      (branchB_actual_normalizedB_mem R) hb.ne'
      (by simpa [sourceRest] using hcomb 0 (C.data.sourceY - 1) 0)
      (by simpa [returnedRest] using (hcomb (C.data.returnedX + wH R)
        (zH R - 1) (C.data.returnedZ - L5A2B4AR4R2B.c3 R)))
    · rw [hsource]
      dsimp [sourceRest]
      have hys := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hroute'.2.1)
      calc
        C.data.sourceY * normalizedB R =
            (C.data.sourceY - 1 + 1) * normalizedB R := by rw [hys]
        _ = normalizedB R + (C.data.sourceY - 1) * normalizedB R := by ring
    · rw [hreturned]
      dsimp [returnedRest]
      have hrs := Nat.sub_add_cancel hle
      have hzs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz.ne')
      have hzSplit : zH R * normalizedB R =
          normalizedB R + (zH R - 1) * normalizedB R := by
        calc
          zH R * normalizedB R = (zH R - 1 + 1) * normalizedB R := by rw [hzs]
          _ = normalizedB R + (zH R - 1) * normalizedB R := by ring
      calc
        C.data.returnedX * normalizedA R + C.data.returnedZ * normalizedC R =
            C.data.returnedX * normalizedA R +
              ((C.data.returnedZ - L5A2B4AR4R2B.c3 R) +
                L5A2B4AR4R2B.c3 R) * normalizedC R := by rw [hrs]
        _ = normalizedB R + returnedRest := by
          rw [Nat.add_mul, hrel3, hzSplit]
          ring
  let D := A.depth - C.data.returnedX
  have hDpos : 0 < D := Nat.sub_pos_of_lt hxLt
  have hDlt : D < L5A2B4AR4R2B.c1 R :=
    lt_of_le_of_lt (Nat.sub_le _ _) hdepth
  have hbalance' : (D : ℤ) * normalizedA R +
      ((C.data.sourceY : ℤ) - i) * normalizedB R =
      ((C.data.returnedZ : ℤ) + j) * normalizedC R := by
    change (((A.depth - C.data.returnedX : ℕ) : ℤ) * normalizedA R) +
        ((C.data.sourceY : ℤ) - i) * normalizedB R =
      ((C.data.returnedZ : ℤ) + j) * normalizedC R
    rw [Nat.cast_sub (Nat.le_of_lt hxLt)]
    exact hbalanceExpanded
  let k := C.data.returnedZ + j - L5A2B4AR4R2B.c3 R
  have hkZ : (k : ℤ) =
      C.data.returnedZ + j - L5A2B4AR4R2B.c3 R := by
    dsimp [k]
    rw [Nat.cast_sub hc3Le]
    push_cast
    rfl
  have hrel3Z : (L5A2B4AR4R2B.c3 R : ℤ) * normalizedC R =
      (wH R : ℤ) * normalizedA R + (zH R : ℤ) * normalizedB R := by
    exact_mod_cast hrel3
  have hdiffZ :
      ((D : ℤ) - wH R) * normalizedA R +
          ((C.data.sourceY : ℤ) - i - zH R) * normalizedB R =
        (k : ℤ) * normalizedC R := by
    calc
      ((D : ℤ) - wH R) * normalizedA R +
            ((C.data.sourceY : ℤ) - i - zH R) * normalizedB R =
          ((D : ℤ) * normalizedA R +
              ((C.data.sourceY : ℤ) - i) * normalizedB R) -
            ((wH R : ℤ) * normalizedA R + (zH R : ℤ) * normalizedB R) := by ring
      _ = ((C.data.returnedZ : ℤ) + j) * normalizedC R -
            (L5A2B4AR4R2B.c3 R : ℤ) * normalizedC R := by
          rw [hbalance', hrel3Z]
      _ = (k : ℤ) * normalizedC R := by rw [hkZ]; ring
  have hDge : wH R ≤ D := by
    by_contra hnot
    have hDsmall : D < wH R := Nat.lt_of_not_ge hnot
    have hyBig : i + zH R < C.data.sourceY := by
      by_contra hynot
      have hyLe : C.data.sourceY ≤ i + zH R := Nat.le_of_not_gt hynot
      have hzeroZ :
          ((wH R - D : ℕ) : ℤ) * normalizedA R +
              ((i + zH R - C.data.sourceY : ℕ) : ℤ) * normalizedB R +
              (k : ℤ) * normalizedC R = 0 := by
        have hxc : ((wH R - D : ℕ) : ℤ) = (wH R : ℤ) - D :=
          Nat.cast_sub (Nat.le_of_lt hDsmall)
        have hyc : ((i + zH R - C.data.sourceY : ℕ) : ℤ) =
            (i : ℤ) + zH R - C.data.sourceY := by
          rw [Nat.cast_sub hyLe]
          push_cast
          ring
        rw [hxc, hyc]
        nlinarith only [hdiffZ]
      have hpositive : 0 < (wH R - D) * normalizedA R :=
        Nat.mul_pos (Nat.sub_pos_of_lt hDsmall) ha
      have hzeroNat :
          (wH R - D) * normalizedA R +
              (i + zH R - C.data.sourceY) * normalizedB R +
              k * normalizedC R = 0 := by exact_mod_cast hzeroZ
      omega
    have hrelB : (C.data.sourceY - (i + zH R)) * normalizedB R =
        (wH R - D) * normalizedA R + k * normalizedC R := by
      have hyLe : i + zH R ≤ C.data.sourceY := Nat.le_of_lt hyBig
      have hxc : ((wH R - D : ℕ) : ℤ) = (wH R : ℤ) - D :=
        Nat.cast_sub (Nat.le_of_lt hDsmall)
      have hyc : ((C.data.sourceY - (i + zH R) : ℕ) : ℤ) =
          (C.data.sourceY : ℤ) - i - zH R := by
        rw [Nat.cast_sub hyLe]
        push_cast
        ring
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    have hminB := branchB_normalizedB_relation_min R _ _ _
      (Nat.sub_pos_of_lt hyBig) hrelB
    have hsmall : C.data.sourceY - (i + zH R) < L5A2B4AR4R2B.c2 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hsourceYlt
    omega
  have hyGe : i + zH R ≤ C.data.sourceY := by
    by_contra hnot
    have hySmall : C.data.sourceY < i + zH R := Nat.lt_of_not_ge hnot
    have hrelA : (D - wH R) * normalizedA R =
        (i + zH R - C.data.sourceY) * normalizedB R + k * normalizedC R := by
      have hxc : ((D - wH R : ℕ) : ℤ) = (D : ℤ) - wH R :=
        Nat.cast_sub hDge
      have hyc : ((i + zH R - C.data.sourceY : ℕ) : ℤ) =
          (i : ℤ) + zH R - C.data.sourceY := by
        rw [Nat.cast_sub (Nat.le_of_lt hySmall)]
        push_cast
        ring
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    have hpos : 0 < D - wH R := by
      by_contra hzq
      have heq : D = wH R := by omega
      rw [heq, Nat.sub_self, zero_mul] at hrelA
      have hbpos := Nat.mul_pos (Nat.sub_pos_of_lt hySmall) hb
      omega
    have hminA := branchB_normalizedA_relation_min R _ _ _ hpos hrelA
    have hsmall : D - wH R < L5A2B4AR4R2B.c1 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hDlt
    omega
  have hk0 : k = 0 := by
    by_contra hkne
    have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
    have hrelK : k * normalizedC R =
        (D - wH R) * normalizedA R +
          (C.data.sourceY - (i + zH R)) * normalizedB R := by
      have hxc : ((D - wH R : ℕ) : ℤ) = (D : ℤ) - wH R :=
        Nat.cast_sub hDge
      have hyc : ((C.data.sourceY - (i + zH R) : ℕ) : ℤ) =
          (C.data.sourceY : ℤ) - i - zH R := by
        rw [Nat.cast_sub hyGe]
        push_cast
        ring
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    have hminK := branchB_normalizedC_relation_min R _ _ _ hkpos hrelK
    have hklt : k < L5A2B4AR4R2B.c3 R := by
      dsimp [k]
      omega
    omega
  have hsumEq : C.data.returnedZ + j = L5A2B4AR4R2B.c3 R := by
    dsimp [k] at hk0
    omega
  have hzero : (D - wH R) * normalizedA R +
      (C.data.sourceY - (i + zH R)) * normalizedB R = 0 := by
    have hrelK : k * normalizedC R =
        (D - wH R) * normalizedA R +
          (C.data.sourceY - (i + zH R)) * normalizedB R := by
      have hxc : ((D - wH R : ℕ) : ℤ) = (D : ℤ) - wH R :=
        Nat.cast_sub hDge
      have hyc : ((C.data.sourceY - (i + zH R) : ℕ) : ℤ) =
          (C.data.sourceY : ℤ) - i - zH R := by
        rw [Nat.cast_sub hyGe]
        push_cast
        ring
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hyc]
      nlinarith only [hdiffZ]
    rw [hk0, zero_mul] at hrelK
    exact hrelK.symm
  have hDEq : D = wH R := by
    have : D - wH R = 0 := by
      by_contra hn
      have hpos := Nat.mul_pos (Nat.pos_of_ne_zero hn) ha
      omega
    omega
  have hyEq : C.data.sourceY = i + zH R := by
    have : C.data.sourceY - (i + zH R) = 0 := by
      by_contra hn
      have hpos := Nat.mul_pos (Nat.pos_of_ne_zero hn) hb
      omega
    omega
  have hrEq : C.data.returnedZ = L5A2B4AR4R2B.c3 R - j := by omega
  have hdEq : A.depth = wH R + C.data.returnedX := by
    dsimp [D] at hDEq
    omega
  have hrxPos : 0 < C.data.returnedX := Nat.pos_of_ne_zero hrx
  refine ⟨hrEq, hyEq, hdEq, ?_⟩
  rw [hdEq]
  omega

/-- The exact dual mixed degeneration over a chosen pure-`c` source. -/
theorem branchB_positive_center_pureC_mixed_degenerate
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hrx :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedX ≠ 0)
    (hry :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
      C.data.returnedY ≠ 0) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.returnedY = L5A2B4AR4R2B.c2 R - i ∧
      C.data.sourceZ = j + vH R ∧
      A.depth = uH R + C.data.returnedX ∧ uH R < A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedX ≠ 0 at hrx
  change C.data.returnedY ≠ 0 at hry
  rcases hcenter with ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hrz := (branchB_positive_center_pureC_returned_support_split
    R hB hs hroute).1
  have hdepth := branchB_positive_center_depth_lt_c1 R hB hs i j
    ⟨hi, hj, hiPos, hiLe, hjPos, hjLe, hcorner⟩
  have hsourceZlt := branchB_positive_center_pureC_mixed_sourceZ_lt_c3
    R hB hs hroute hrx hry
  change C.data.sourceZ < L5A2B4AR4R2B.c3 R at hsourceZlt
  have hbalance := branchB_positive_center_pureC_signed_balance R hB hs i j
    ⟨hi, hj⟩ hroute
  change (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
      (((C.data.sourceZ : ℤ) - j) * normalizedC R) =
    ((C.data.returnedY + i : ℕ) : ℤ) * normalizedB R at hbalance
  have hbalanceExpanded :
      (((A.depth : ℤ) - C.data.returnedX) * normalizedA R) +
          (((C.data.sourceZ : ℤ) - j) * normalizedC R) =
        ((C.data.returnedY : ℤ) + i) * normalizedB R := by
    simpa only [Nat.cast_add] using hbalance
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, hu, hv, hw, hz⟩ := HC.cross_positive
  obtain ⟨hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨hrel1, hrel2, hrel3⟩ := HC.normalized_relations
  have ha : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hb : 0 < normalizedB R := branchB_actual_normalizedWeight_pos R 1
  have hc : 0 < normalizedC R := branchB_actual_normalizedWeight_pos R 2
  have hxLt : C.data.returnedX < A.depth := by
    by_contra hnot
    have hdLe : A.depth ≤ C.data.returnedX := Nat.le_of_not_gt hnot
    have hzGt : j < C.data.sourceZ := by
      by_contra hznot
      have hzLe : C.data.sourceZ ≤ j := Nat.le_of_not_gt hznot
      have hleftA : ((A.depth : ℤ) - C.data.returnedX) * normalizedA R ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (by exact_mod_cast hdLe)) (by positivity)
      have hleftC : ((C.data.sourceZ : ℤ) - j) * normalizedC R ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (by exact_mod_cast hzLe)) (by positivity)
      have hright : 0 < ((C.data.returnedY + i : ℕ) : ℤ) * normalizedB R := by
        positivity
      nlinarith only [hbalance, hleftA, hleftC, hright]
    have hrelC : (C.data.sourceZ - j) * normalizedC R =
        (C.data.returnedX - A.depth) * normalizedA R +
          (C.data.returnedY + i) * normalizedB R := by
      have hxCast : ((C.data.returnedX - A.depth : ℕ) : ℤ) =
          C.data.returnedX - A.depth := Nat.cast_sub hdLe
      have hzCast : ((C.data.sourceZ - j : ℕ) : ℤ) =
          C.data.sourceZ - j := Nat.cast_sub (Nat.le_of_lt hzGt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hzCast]
      nlinarith only [hbalanceExpanded]
    have hminC := branchB_normalizedC_relation_min R _ _ _
      (Nat.sub_pos_of_lt hzGt) hrelC
    have hsmall : C.data.sourceZ - j < L5A2B4AR4R2B.c3 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hsourceZlt
    omega
  have hzGt : j < C.data.sourceZ := by
    by_contra hnot
    have hzLe : C.data.sourceZ ≤ j := Nat.le_of_not_gt hnot
    have hrelA : (A.depth - C.data.returnedX) * normalizedA R =
        (C.data.returnedY + i) * normalizedB R +
          (j - C.data.sourceZ) * normalizedC R := by
      have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
          A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxLt)
      have hzCast : ((j - C.data.sourceZ : ℕ) : ℤ) =
          j - C.data.sourceZ := Nat.cast_sub hzLe
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hzCast]
      nlinarith only [hbalanceExpanded]
    have hminA := branchB_normalizedA_relation_min R _ _ _
      (Nat.sub_pos_of_lt hxLt) hrelA
    have hsmall : A.depth - C.data.returnedX < L5A2B4AR4R2B.c1 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hdepth
    omega
  have hc2Le : L5A2B4AR4R2B.c2 R ≤ C.data.returnedY + i := by
    have hrelB : (C.data.returnedY + i) * normalizedB R =
        (A.depth - C.data.returnedX) * normalizedA R +
          (C.data.sourceZ - j) * normalizedC R := by
      have hxCast : ((A.depth - C.data.returnedX : ℕ) : ℤ) =
          A.depth - C.data.returnedX := Nat.cast_sub (Nat.le_of_lt hxLt)
      have hzCast : ((C.data.sourceZ - j : ℕ) : ℤ) =
          C.data.sourceZ - j := Nat.cast_sub (Nat.le_of_lt hzGt)
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxCast, hzCast]
      nlinarith only [hbalanceExpanded]
    exact branchB_normalizedB_relation_min R _ _ _ (by omega) hrelB
  have hsource : C.data.sourceValue = C.data.sourceZ * normalizedC R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.1]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedX * normalizedA R + C.data.returnedY * normalizedB R := by
    rw [C.data.returned_factorization, hrz]
    omega
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz' := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz'
  have commonImpossible (g sourceRest returnedRest : ℕ)
      (hgH : g ∈ H) (hg0 : g ≠ 0)
      (hsH : sourceRest ∈ H) (hrH : returnedRest ∈ H)
      (hsplit : C.data.sourceValue = g + sourceRest)
      (hrsplit : C.data.returnedValue = g + returnedRest) : False := by
    apply minimal_return_common_generator_impossible H C.data.return_witness.2.2
      hgH hg0 hsH hrH
    · calc
        s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
        _ = (g : ℤ) + sourceRest := by exact_mod_cast hsplit
    · calc
        s - (C.data.ell * normalizedM P.M.base : ℕ) =
            (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
        _ = (g : ℤ) + returnedRest := by exact_mod_cast hrsplit
  have hryLt : C.data.returnedY < L5A2B4AR4R2B.c2 R := by
    by_contra hnot
    have hle : L5A2B4AR4R2B.c2 R ≤ C.data.returnedY := Nat.le_of_not_gt hnot
    let sourceRest := (C.data.sourceZ - 1) * normalizedC R
    let returnedRest := (C.data.returnedX + uH R) * normalizedA R +
      (C.data.returnedY - L5A2B4AR4R2B.c2 R) * normalizedB R +
      (vH R - 1) * normalizedC R
    apply commonImpossible (normalizedC R) sourceRest returnedRest
      (branchB_actual_normalizedC_mem R) hc.ne'
      (by simpa [sourceRest] using hcomb 0 0 (C.data.sourceZ - 1))
      (by simpa [returnedRest] using (hcomb (C.data.returnedX + uH R)
        (C.data.returnedY - L5A2B4AR4R2B.c2 R) (vH R - 1)))
    · rw [hsource]
      dsimp [sourceRest]
      have hzs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hroute'.2.2)
      calc
        C.data.sourceZ * normalizedC R =
            (C.data.sourceZ - 1 + 1) * normalizedC R := by rw [hzs]
        _ = normalizedC R + (C.data.sourceZ - 1) * normalizedC R := by ring
    · rw [hreturned]
      dsimp [returnedRest]
      have hys := Nat.sub_add_cancel hle
      have hvs := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv.ne')
      have hvSplit : vH R * normalizedC R =
          normalizedC R + (vH R - 1) * normalizedC R := by
        calc
          vH R * normalizedC R = (vH R - 1 + 1) * normalizedC R := by rw [hvs]
          _ = normalizedC R + (vH R - 1) * normalizedC R := by ring
      calc
        C.data.returnedX * normalizedA R + C.data.returnedY * normalizedB R =
            C.data.returnedX * normalizedA R +
              ((C.data.returnedY - L5A2B4AR4R2B.c2 R) +
                L5A2B4AR4R2B.c2 R) * normalizedB R := by rw [hys]
        _ = normalizedC R + returnedRest := by
          rw [Nat.add_mul, hrel2, hvSplit]
          ring
  let D := A.depth - C.data.returnedX
  have hDpos : 0 < D := Nat.sub_pos_of_lt hxLt
  have hDlt : D < L5A2B4AR4R2B.c1 R :=
    lt_of_le_of_lt (Nat.sub_le _ _) hdepth
  have hbalance' : (D : ℤ) * normalizedA R +
      ((C.data.sourceZ : ℤ) - j) * normalizedC R =
      ((C.data.returnedY : ℤ) + i) * normalizedB R := by
    change (((A.depth - C.data.returnedX : ℕ) : ℤ) * normalizedA R) +
        ((C.data.sourceZ : ℤ) - j) * normalizedC R =
      ((C.data.returnedY : ℤ) + i) * normalizedB R
    rw [Nat.cast_sub (Nat.le_of_lt hxLt)]
    exact hbalanceExpanded
  let k := C.data.returnedY + i - L5A2B4AR4R2B.c2 R
  have hkZ : (k : ℤ) =
      C.data.returnedY + i - L5A2B4AR4R2B.c2 R := by
    dsimp [k]
    rw [Nat.cast_sub hc2Le]
    push_cast
    rfl
  have hrel2Z : (L5A2B4AR4R2B.c2 R : ℤ) * normalizedB R =
      (uH R : ℤ) * normalizedA R + (vH R : ℤ) * normalizedC R := by
    exact_mod_cast hrel2
  have hdiffZ :
      ((D : ℤ) - uH R) * normalizedA R +
          ((C.data.sourceZ : ℤ) - j - vH R) * normalizedC R =
        (k : ℤ) * normalizedB R := by
    calc
      ((D : ℤ) - uH R) * normalizedA R +
            ((C.data.sourceZ : ℤ) - j - vH R) * normalizedC R =
          ((D : ℤ) * normalizedA R +
              ((C.data.sourceZ : ℤ) - j) * normalizedC R) -
            ((uH R : ℤ) * normalizedA R + (vH R : ℤ) * normalizedC R) := by ring
      _ = ((C.data.returnedY : ℤ) + i) * normalizedB R -
            (L5A2B4AR4R2B.c2 R : ℤ) * normalizedB R := by
          rw [hbalance', hrel2Z]
      _ = (k : ℤ) * normalizedB R := by rw [hkZ]; ring
  have hDge : uH R ≤ D := by
    by_contra hnot
    have hDsmall : D < uH R := Nat.lt_of_not_ge hnot
    have hzBig : j + vH R < C.data.sourceZ := by
      by_contra hznot
      have hzLe : C.data.sourceZ ≤ j + vH R := Nat.le_of_not_gt hznot
      have hzeroZ :
          ((uH R - D : ℕ) : ℤ) * normalizedA R +
              ((j + vH R - C.data.sourceZ : ℕ) : ℤ) * normalizedC R +
              (k : ℤ) * normalizedB R = 0 := by
        have hxc : ((uH R - D : ℕ) : ℤ) = (uH R : ℤ) - D :=
          Nat.cast_sub (Nat.le_of_lt hDsmall)
        have hzc : ((j + vH R - C.data.sourceZ : ℕ) : ℤ) =
            (j : ℤ) + vH R - C.data.sourceZ := by
          rw [Nat.cast_sub hzLe]
          push_cast
          ring
        rw [hxc, hzc]
        nlinarith only [hdiffZ]
      have hpositive : 0 < (uH R - D) * normalizedA R :=
        Nat.mul_pos (Nat.sub_pos_of_lt hDsmall) ha
      have hzeroNat :
          (uH R - D) * normalizedA R +
              (j + vH R - C.data.sourceZ) * normalizedC R +
              k * normalizedB R = 0 := by exact_mod_cast hzeroZ
      omega
    have hrelC : (C.data.sourceZ - (j + vH R)) * normalizedC R =
        (uH R - D) * normalizedA R + k * normalizedB R := by
      have hxc : ((uH R - D : ℕ) : ℤ) = (uH R : ℤ) - D :=
        Nat.cast_sub (Nat.le_of_lt hDsmall)
      have hzc : ((C.data.sourceZ - (j + vH R) : ℕ) : ℤ) =
          (C.data.sourceZ : ℤ) - j - vH R := by
        rw [Nat.cast_sub (Nat.le_of_lt hzBig)]
        push_cast
        ring
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    have hminC := branchB_normalizedC_relation_min R _ _ _
      (Nat.sub_pos_of_lt hzBig) hrelC
    have hsmall : C.data.sourceZ - (j + vH R) < L5A2B4AR4R2B.c3 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hsourceZlt
    omega
  have hzGe : j + vH R ≤ C.data.sourceZ := by
    by_contra hnot
    have hzSmall : C.data.sourceZ < j + vH R := Nat.lt_of_not_ge hnot
    have hrelA : (D - uH R) * normalizedA R =
        k * normalizedB R + (j + vH R - C.data.sourceZ) * normalizedC R := by
      have hxc : ((D - uH R : ℕ) : ℤ) = (D : ℤ) - uH R := Nat.cast_sub hDge
      have hzc : ((j + vH R - C.data.sourceZ : ℕ) : ℤ) =
          (j : ℤ) + vH R - C.data.sourceZ := by
        rw [Nat.cast_sub (Nat.le_of_lt hzSmall)]
        push_cast
        ring
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    have hpos : 0 < D - uH R := by
      by_contra hzq
      have heq : D = uH R := by omega
      rw [heq, Nat.sub_self, zero_mul] at hrelA
      have hcpos := Nat.mul_pos (Nat.sub_pos_of_lt hzSmall) hc
      omega
    have hminA := branchB_normalizedA_relation_min R _ _ _ hpos hrelA
    have hsmall : D - uH R < L5A2B4AR4R2B.c1 R :=
      lt_of_le_of_lt (Nat.sub_le _ _) hDlt
    omega
  have hk0 : k = 0 := by
    by_contra hkne
    have hkpos : 0 < k := Nat.pos_of_ne_zero hkne
    have hrelK : k * normalizedB R =
        (D - uH R) * normalizedA R +
          (C.data.sourceZ - (j + vH R)) * normalizedC R := by
      have hxc : ((D - uH R : ℕ) : ℤ) = (D : ℤ) - uH R := Nat.cast_sub hDge
      have hzc : ((C.data.sourceZ - (j + vH R) : ℕ) : ℤ) =
          (C.data.sourceZ : ℤ) - j - vH R := by
        rw [Nat.cast_sub hzGe]
        push_cast
        ring
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    have hminK := branchB_normalizedB_relation_min R _ _ _ hkpos hrelK
    have hklt : k < L5A2B4AR4R2B.c2 R := by
      dsimp [k]
      omega
    omega
  have hsumEq : C.data.returnedY + i = L5A2B4AR4R2B.c2 R := by
    dsimp [k] at hk0
    omega
  have hzero : (D - uH R) * normalizedA R +
      (C.data.sourceZ - (j + vH R)) * normalizedC R = 0 := by
    have hrelK : k * normalizedB R =
        (D - uH R) * normalizedA R +
          (C.data.sourceZ - (j + vH R)) * normalizedC R := by
      have hxc : ((D - uH R : ℕ) : ℤ) = (D : ℤ) - uH R := Nat.cast_sub hDge
      have hzc : ((C.data.sourceZ - (j + vH R) : ℕ) : ℤ) =
          (C.data.sourceZ : ℤ) - j - vH R := by
        rw [Nat.cast_sub hzGe]
        push_cast
        ring
      apply Int.ofNat_inj.mp
      push_cast only [Nat.cast_mul, Nat.cast_add]
      rw [hxc, hzc]
      nlinarith only [hdiffZ]
    rw [hk0, zero_mul] at hrelK
    exact hrelK.symm
  have hDEq : D = uH R := by
    have : D - uH R = 0 := by
      by_contra hn
      have hpos := Nat.mul_pos (Nat.pos_of_ne_zero hn) ha
      omega
    omega
  have hzEq : C.data.sourceZ = j + vH R := by
    have : C.data.sourceZ - (j + vH R) = 0 := by
      by_contra hn
      have hpos := Nat.mul_pos (Nat.pos_of_ne_zero hn) hc
      omega
    omega
  have hrEq : C.data.returnedY = L5A2B4AR4R2B.c2 R - i := by omega
  have hdEq : A.depth = uH R + C.data.returnedX := by
    dsimp [D] at hDEq
    omega
  have hrxPos : 0 < C.data.returnedX := Nat.pos_of_ne_zero hrx
  refine ⟨hrEq, hzEq, hdEq, ?_⟩
  rw [hdEq]
  omega

/-- Every chosen pure-`b` support at a positive CENTER has depth on or beyond
the `wH` boundary, independently of its returned-support subcase. -/
theorem branchB_positive_center_pureB_depth_ge_wH
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
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    wH R ≤ A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  have hsplit := branchB_positive_center_pureB_returned_support_split R hB hs hroute
  change C.data.returnedY = 0 ∧
      ((C.data.returnedX ≠ 0 ∧ C.data.returnedZ = 0) ∨
       (C.data.returnedX = 0 ∧ C.data.returnedZ ≠ 0) ∨
       (C.data.returnedX ≠ 0 ∧ C.data.returnedZ ≠ 0)) at hsplit
  rcases hsplit.2 with hA | hC | hmix
  · exact False.elim (branchB_positive_center_pureB_returnedX_impossible
      R hB hs i j hcenter hroute hA.1 hA.2)
  · have hpacket := branchB_positive_center_pureB_returnedC_degenerate
      R hB hs i j hcenter hroute hC.1 hC.2
    change C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
        A.depth = wH R ∧ C.data.sourceY = i + zH R at hpacket
    change wH R ≤ A.depth
    exact (Nat.le_of_eq hpacket.2.1.symm)
  · have hpacket := branchB_positive_center_pureB_mixed_degenerate
      R hB hs i j hcenter hroute hmix.1 hmix.2
    change C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
        C.data.sourceY = i + zH R ∧
        A.depth = wH R + C.data.returnedX ∧ wH R < A.depth at hpacket
    change wH R ≤ A.depth
    exact Nat.le_of_lt hpacket.2.2.2

/-- Exact cyclic dual of `branchB_positive_center_pureB_depth_ge_wH`. -/
theorem branchB_positive_center_pureC_depth_ge_uH
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
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    uH R ≤ A.depth := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  have hsplit := branchB_positive_center_pureC_returned_support_split R hB hs hroute
  change C.data.returnedZ = 0 ∧
      ((C.data.returnedX ≠ 0 ∧ C.data.returnedY = 0) ∨
       (C.data.returnedX = 0 ∧ C.data.returnedY ≠ 0) ∨
       (C.data.returnedX ≠ 0 ∧ C.data.returnedY ≠ 0)) at hsplit
  rcases hsplit.2 with hA | hB' | hmix
  · exact False.elim (branchB_positive_center_pureC_returnedX_impossible
      R hB hs i j hcenter hroute hA.1 hA.2)
  · have hpacket := branchB_positive_center_pureC_returnedB_degenerate
      R hB hs i j hcenter hroute hB'.1 hB'.2
    change C.data.returnedY = L5A2B4AR4R2B.c2 R - i ∧
        A.depth = uH R ∧ C.data.sourceZ = j + vH R at hpacket
    change uH R ≤ A.depth
    exact Nat.le_of_eq hpacket.2.1.symm
  · have hpacket := branchB_positive_center_pureC_mixed_degenerate
      R hB hs i j hcenter hroute hmix.1 hmix.2
    change C.data.returnedY = L5A2B4AR4R2B.c2 R - i ∧
        C.data.sourceZ = j + vH R ∧
        A.depth = uH R + C.data.returnedX ∧ uH R < A.depth at hpacket
    change uH R ≤ A.depth
    exact Nat.le_of_lt hpacket.2.2.2

/-- At the pure-`b` CENTER boundary, subtracting the actual normalized
`b`-generator gives the source-exact predecessor candidate.  The candidate
is in `H`, but source minimality forces it out of both the final and prefix
carriers.  Thus the remaining strict-depth step is exactly a carrier-survival
statement, not further Herzog arithmetic. -/
theorem branchB_positive_center_pureB_boundary_predecessor_candidate
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hboundary :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.depth = wH R) :
    let H := normalizedH P.M.base
    ∃ g : ℕ,
      g = normalizedB R ∧ g ∈ H ∧ g ≠ 0 ∧
      s - (g : ℤ) = (((i + zH R - 1) * normalizedB R : ℕ) : ℤ) ∧
      s - (g : ℤ) ∈ H.asRelativeIdeal ∧
      s - (g : ℤ) ∉ actualFinalCarrier P.M.base ∧
      s - (g : ℤ) ∉ actualPrefixCarrier P.M.base := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  let H := normalizedH P.M.base
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change A.depth = wH R at hboundary
  have hsplit := branchB_positive_center_pureB_returned_support_split R hB hs hroute
  change C.data.returnedY = 0 ∧
      ((C.data.returnedX ≠ 0 ∧ C.data.returnedZ = 0) ∨
       (C.data.returnedX = 0 ∧ C.data.returnedZ ≠ 0) ∨
       (C.data.returnedX ≠ 0 ∧ C.data.returnedZ ≠ 0)) at hsplit
  have hsourceY : C.data.sourceY = i + zH R := by
    rcases hsplit.2 with hA | hC | hmix
    · exact False.elim (branchB_positive_center_pureB_returnedX_impossible
        R hB hs i j hcenter hroute hA.1 hA.2)
    · exact (branchB_positive_center_pureB_returnedC_degenerate
        R hB hs i j hcenter hroute hC.1 hC.2).2.2
    · have hp := branchB_positive_center_pureB_mixed_degenerate
        R hB hs i j hcenter hroute hmix.1 hmix.2
      change C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
          C.data.sourceY = i + zH R ∧
          A.depth = wH R + C.data.returnedX ∧ wH R < A.depth at hp
      exact False.elim ((Nat.ne_of_lt hp.2.2.2) hboundary.symm)
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hsource : C.data.sourceValue = C.data.sourceY * normalizedB R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.2]
    omega
  have hsourceNat : C.data.sourceValue =
      (i + zH R) * normalizedB R := by
    rw [hsource, hsourceY]
  have hcoeffPos : 0 < i + zH R := by omega
  have hsplitNat : (i + zH R) * normalizedB R =
      normalizedB R + (i + zH R - 1) * normalizedB R := by
    calc
      (i + zH R) * normalizedB R =
          ((i + zH R - 1) + 1) * normalizedB R := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ i + zH R)]
      _ = normalizedB R + (i + zH R - 1) * normalizedB R := by ring
  let g := normalizedB R
  have hgH : g ∈ H := branchB_actual_normalizedB_mem R
  have hg0 : g ≠ 0 := (branchB_actual_normalizedWeight_pos R 1).ne'
  have hpred : s - (g : ℤ) =
      (((i + zH R - 1) * normalizedB R : ℕ) : ℤ) := by
    calc
      s - (g : ℤ) = (C.data.sourceValue : ℤ) - (g : ℤ) := by
        rw [C.data.source_eq]
      _ = (((i + zH R) * normalizedB R : ℕ) : ℤ) -
          (normalizedB R : ℤ) := by
            dsimp [g]
            exact congrArg (fun x : ℤ => x - (normalizedB R : ℤ))
              (congrArg (fun x : ℕ => (x : ℤ)) hsourceNat)
      _ = (((i + zH R - 1) * normalizedB R : ℕ) : ℤ) := by
        rw [congrArg (fun x : ℕ => (x : ℤ)) hsplitNat]
        push_cast
        ring
  have hpredH : s - (g : ℤ) ∈ H.asRelativeIdeal := by
    rw [hpred, NumericalSemigroup.mem_asRelativeIdeal_iff]
    refine ⟨(i + zH R - 1) * normalizedB R, ?_, rfl⟩
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R)
        (i + zH R - 1)
  have hnotFinal : s - (g : ℤ) ∉ actualFinalCarrier P.M.base :=
    hs.1.2 g hgH hg0
  have hnotPrefix : s - (g : ℤ) ∉ actualPrefixCarrier P.M.base := by
    intro hp
    exact hnotFinal (Or.inl hp)
  exact ⟨g, rfl, hgH, hg0, hpred, hpredH, hnotFinal, hnotPrefix⟩

/-- Cyclic-dual predecessor candidate at the pure-`c` CENTER boundary. -/
theorem branchB_positive_center_pureC_boundary_predecessor_candidate
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hboundary :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.depth = uH R) :
    let H := normalizedH P.M.base
    ∃ g : ℕ,
      g = normalizedC R ∧ g ∈ H ∧ g ≠ 0 ∧
      s - (g : ℤ) = (((j + vH R - 1) * normalizedC R : ℕ) : ℤ) ∧
      s - (g : ℤ) ∈ H.asRelativeIdeal ∧
      s - (g : ℤ) ∉ actualFinalCarrier P.M.base ∧
      s - (g : ℤ) ∉ actualPrefixCarrier P.M.base := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  let H := normalizedH P.M.base
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change A.depth = uH R at hboundary
  have hsplit := branchB_positive_center_pureC_returned_support_split R hB hs hroute
  change C.data.returnedZ = 0 ∧
      ((C.data.returnedX ≠ 0 ∧ C.data.returnedY = 0) ∨
       (C.data.returnedX = 0 ∧ C.data.returnedY ≠ 0) ∨
       (C.data.returnedX ≠ 0 ∧ C.data.returnedY ≠ 0)) at hsplit
  have hsourceZ : C.data.sourceZ = j + vH R := by
    rcases hsplit.2 with hA | hB' | hmix
    · exact False.elim (branchB_positive_center_pureC_returnedX_impossible
        R hB hs i j hcenter hroute hA.1 hA.2)
    · exact (branchB_positive_center_pureC_returnedB_degenerate
        R hB hs i j hcenter hroute hB'.1 hB'.2).2.2
    · have hp := branchB_positive_center_pureC_mixed_degenerate
        R hB hs i j hcenter hroute hmix.1 hmix.2
      change C.data.returnedY = L5A2B4AR4R2B.c2 R - i ∧
          C.data.sourceZ = j + vH R ∧
          A.depth = uH R + C.data.returnedX ∧ uH R < A.depth at hp
      exact False.elim ((Nat.ne_of_lt hp.2.2.2) hboundary.symm)
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY = 0 ∧
      C.data.sourceZ ≠ 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hsource : C.data.sourceValue = C.data.sourceZ * normalizedC R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.1]
    omega
  have hsourceNat : C.data.sourceValue =
      (j + vH R) * normalizedC R := hsource.trans (by rw [hsourceZ])
  have hcoeffPos : 0 < j + vH R := by omega
  have hsplitNat : (j + vH R) * normalizedC R =
      normalizedC R + (j + vH R - 1) * normalizedC R := by
    calc
      (j + vH R) * normalizedC R =
          ((j + vH R - 1) + 1) * normalizedC R := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ j + vH R)]
      _ = normalizedC R + (j + vH R - 1) * normalizedC R := by ring
  let g := normalizedC R
  have hgH : g ∈ H := branchB_actual_normalizedC_mem R
  have hg0 : g ≠ 0 := (branchB_actual_normalizedWeight_pos R 2).ne'
  have hpred : s - (g : ℤ) =
      (((j + vH R - 1) * normalizedC R : ℕ) : ℤ) := by
    calc
      s - (g : ℤ) = (C.data.sourceValue : ℤ) - (g : ℤ) := by
        rw [C.data.source_eq]
      _ = (((j + vH R) * normalizedC R : ℕ) : ℤ) -
          (normalizedC R : ℤ) := by
            dsimp [g]
            exact congrArg (fun x : ℤ => x - (normalizedC R : ℤ))
              (congrArg (fun x : ℕ => (x : ℤ)) hsourceNat)
      _ = (((j + vH R - 1) * normalizedC R : ℕ) : ℤ) := by
        rw [congrArg (fun x : ℕ => (x : ℤ)) hsplitNat]
        push_cast
        ring
  have hpredH : s - (g : ℤ) ∈ H.asRelativeIdeal := by
    rw [hpred, NumericalSemigroup.mem_asRelativeIdeal_iff]
    refine ⟨(j + vH R - 1) * normalizedC R, ?_, rfl⟩
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R)
        (j + vH R - 1)
  have hnotFinal : s - (g : ℤ) ∉ actualFinalCarrier P.M.base :=
    hs.1.2 g hgH hg0
  have hnotPrefix : s - (g : ℤ) ∉ actualPrefixCarrier P.M.base := by
    intro hp
    exact hnotFinal (Or.inl hp)
  exact ⟨g, rfl, hgH, hg0, hpred, hpredH, hnotFinal, hnotPrefix⟩

/-- Subtracting the selected return level from a one-generator predecessor
commutes with taking the complementary return.  This equality is independent
of any CENTER classification and fixes the first source-exact candidate level
for the B23 carrier-survival problem. -/
theorem branchB_predecessor_selected_level_tail_eq
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (g : ℕ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (s - (g : ℤ)) - (C.data.ell * normalizedM P.M.base : ℕ) =
      (C.data.returnedValue : ℤ) - (g : ℤ) := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change (s - (g : ℤ)) - (C.data.ell * normalizedM P.M.base : ℕ) =
    (C.data.returnedValue : ℤ) - (g : ℤ)
  calc
    (s - (g : ℤ)) - (C.data.ell * normalizedM P.M.base : ℕ) =
        (s - (C.data.ell * normalizedM P.M.base : ℕ)) - (g : ℤ) := by ring
    _ = (C.data.returnedValue : ℤ) - (g : ℤ) := by
      rw [C.data.returned_eq]

/-- The other natural candidate `k = ell-1` has one additional copy of the
fourth generator in its tail.  This exact formula also explains why the
current three-generator API cannot establish its `H`-membership. -/
theorem branchB_predecessor_previous_level_tail_eq
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) (g : ℕ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (s - (g : ℤ)) -
        ((C.data.ell - 1) * normalizedM P.M.base : ℕ) =
      (C.data.returnedValue : ℤ) - (g : ℤ) +
        (normalizedM P.M.base : ℤ) := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  have hellpos : 0 < C.data.ell := C.data.return_witness.1
  have hselected := branchB_predecessor_selected_level_tail_eq R hB hs g
  change (s - (g : ℤ)) -
      (C.data.ell * normalizedM P.M.base : ℕ) =
    (C.data.returnedValue : ℤ) - (g : ℤ) at hselected
  change (s - (g : ℤ)) -
      ((C.data.ell - 1) * normalizedM P.M.base : ℕ) =
    (C.data.returnedValue : ℤ) - (g : ℤ) +
      (normalizedM P.M.base : ℤ)
  have hell : C.data.ell = (C.data.ell - 1) + 1 := by omega
  push_cast at hselected ⊢
  rw [hell] at hselected
  push_cast at hselected
  nlinarith

/-- Source minimality rules out the pure-`b` boundary predecessor at every
nonprincipal return level.  Consequently any proof of carrier survival must
supply genuinely new CENTER/RECORD semantics; membership in `H` alone cannot
choose a return level. -/
theorem branchB_positive_center_pureB_boundary_predecessor_tail_not_mem
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hboundary :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.depth = wH R)
    (k : ℕ) (hkpos : 0 < k) (hklt : k < actualPrincipalIndex P.M.base) :
    (s - (normalizedB R : ℤ)) - (k * normalizedM P.M.base : ℕ) ∉
      (normalizedH P.M.base).asRelativeIdeal := by
  let H := normalizedH P.M.base
  have hp := branchB_positive_center_pureB_boundary_predecessor_candidate
    R hB hs i j hcenter hroute hboundary
  change ∃ g : ℕ,
      g = normalizedB R ∧ g ∈ H ∧ g ≠ 0 ∧
      s - (g : ℤ) = (((i + zH R - 1) * normalizedB R : ℕ) : ℤ) ∧
      s - (g : ℤ) ∈ H.asRelativeIdeal ∧
      s - (g : ℤ) ∉ actualFinalCarrier P.M.base ∧
      s - (g : ℤ) ∉ actualPrefixCarrier P.M.base at hp
  obtain ⟨g, rfl, _hgH, _hg0, _hpred, hpredH, _hnotFinal, hnotPrefix⟩ := hp
  intro htail
  apply hnotPrefix
  exact ⟨k, hkpos, hklt, hpredH, htail⟩

/-- Exact cyclic dual of
`branchB_positive_center_pureB_boundary_predecessor_tail_not_mem`. -/
theorem branchB_positive_center_pureC_boundary_predecessor_tail_not_mem
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hboundary :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.depth = uH R)
    (k : ℕ) (hkpos : 0 < k) (hklt : k < actualPrincipalIndex P.M.base) :
    (s - (normalizedC R : ℤ)) - (k * normalizedM P.M.base : ℕ) ∉
      (normalizedH P.M.base).asRelativeIdeal := by
  let H := normalizedH P.M.base
  have hp := branchB_positive_center_pureC_boundary_predecessor_candidate
    R hB hs i j hcenter hroute hboundary
  change ∃ g : ℕ,
      g = normalizedC R ∧ g ∈ H ∧ g ≠ 0 ∧
      s - (g : ℤ) = (((j + vH R - 1) * normalizedC R : ℕ) : ℤ) ∧
      s - (g : ℤ) ∈ H.asRelativeIdeal ∧
      s - (g : ℤ) ∉ actualFinalCarrier P.M.base ∧
      s - (g : ℤ) ∉ actualPrefixCarrier P.M.base at hp
  obtain ⟨g, rfl, _hgH, _hg0, _hpred, hpredH, _hnotFinal, hnotPrefix⟩ := hp
  intro htail
  apply hnotPrefix
  exact ⟨k, hkpos, hklt, hpredH, htail⟩

/-- At the selected return level, the pure-`b` boundary predecessor has the
exact tail `(c3-j)c-b`.  This is the source-exact obstruction for the most
natural candidate `k = ell`: the expression is not a nonnegative
`a,b,c`-combination, and the preceding theorem proves that it is not in `H`. -/
theorem branchB_positive_center_pureB_boundary_selected_tail_eq
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hboundary :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.depth = wH R) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (s - (normalizedB R : ℤ)) -
        (C.data.ell * normalizedM P.M.base : ℕ) =
      (((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) : ℤ) -
        (normalizedB R : ℤ) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change A.depth = wH R at hboundary
  have hsplit := branchB_positive_center_pureB_returned_support_split R hB hs hroute
  change C.data.returnedY = 0 ∧
      ((C.data.returnedX ≠ 0 ∧ C.data.returnedZ = 0) ∨
       (C.data.returnedX = 0 ∧ C.data.returnedZ ≠ 0) ∨
       (C.data.returnedX ≠ 0 ∧ C.data.returnedZ ≠ 0)) at hsplit
  have hcoords : C.data.returnedX = 0 ∧ C.data.returnedY = 0 ∧
      C.data.returnedZ = L5A2B4AR4R2B.c3 R - j := by
    rcases hsplit.2 with hA | hC | hmix
    · exact False.elim (branchB_positive_center_pureB_returnedX_impossible
        R hB hs i j hcenter hroute hA.1 hA.2)
    · exact ⟨hC.1, hsplit.1,
        (branchB_positive_center_pureB_returnedC_degenerate
          R hB hs i j hcenter hroute hC.1 hC.2).1⟩
    · have hp := branchB_positive_center_pureB_mixed_degenerate
        R hB hs i j hcenter hroute hmix.1 hmix.2
      change C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
          C.data.sourceY = i + zH R ∧
          A.depth = wH R + C.data.returnedX ∧ wH R < A.depth at hp
      exact False.elim ((Nat.ne_of_lt hp.2.2.2) hboundary.symm)
  have hreturned : C.data.returnedValue =
      (L5A2B4AR4R2B.c3 R - j) * normalizedC R := by
    rw [C.data.returned_factorization, hcoords.1, hcoords.2.1,
      hcoords.2.2]
    simp
  calc
    (s - (normalizedB R : ℤ)) -
        (C.data.ell * normalizedM P.M.base : ℕ) =
      (C.data.returnedValue : ℤ) - (normalizedB R : ℤ) :=
        branchB_predecessor_selected_level_tail_eq R hB hs (normalizedB R)
    _ = (((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) : ℤ) -
        (normalizedB R : ℤ) := by rw [hreturned]

/-- Explicit cyclic dual of
`branchB_positive_center_pureB_boundary_selected_tail_eq`. -/
theorem branchB_positive_center_pureC_boundary_selected_tail_eq
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
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hboundary :
      let A := branchB_actual_selected_return_anchor_v2 R hB hs
      A.depth = uH R) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (s - (normalizedC R : ℤ)) -
        (C.data.ell * normalizedM P.M.base : ℕ) =
      (((L5A2B4AR4R2B.c2 R - i) * normalizedB R : ℕ) : ℤ) -
        (normalizedC R : ℤ) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureC
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change A.depth = uH R at hboundary
  have hsplit := branchB_positive_center_pureC_returned_support_split R hB hs hroute
  change C.data.returnedZ = 0 ∧
      ((C.data.returnedX ≠ 0 ∧ C.data.returnedY = 0) ∨
       (C.data.returnedX = 0 ∧ C.data.returnedY ≠ 0) ∨
       (C.data.returnedX ≠ 0 ∧ C.data.returnedY ≠ 0)) at hsplit
  have hcoords : C.data.returnedX = 0 ∧
      C.data.returnedY = L5A2B4AR4R2B.c2 R - i ∧
      C.data.returnedZ = 0 := by
    rcases hsplit.2 with hA | hB' | hmix
    · exact False.elim (branchB_positive_center_pureC_returnedX_impossible
        R hB hs i j hcenter hroute hA.1 hA.2)
    · exact ⟨hB'.1,
        (branchB_positive_center_pureC_returnedB_degenerate
          R hB hs i j hcenter hroute hB'.1 hB'.2).1, hsplit.1⟩
    · have hp := branchB_positive_center_pureC_mixed_degenerate
        R hB hs i j hcenter hroute hmix.1 hmix.2
      change C.data.returnedY = L5A2B4AR4R2B.c2 R - i ∧
          C.data.sourceZ = j + vH R ∧
          A.depth = uH R + C.data.returnedX ∧ uH R < A.depth at hp
      exact False.elim ((Nat.ne_of_lt hp.2.2.2) hboundary.symm)
  have hreturned : C.data.returnedValue =
      (L5A2B4AR4R2B.c2 R - i) * normalizedB R := by
    rw [C.data.returned_factorization, hcoords.1, hcoords.2.1,
      hcoords.2.2]
    simp
  calc
    (s - (normalizedC R : ℤ)) -
        (C.data.ell * normalizedM P.M.base : ℕ) =
      (C.data.returnedValue : ℤ) - (normalizedC R : ℤ) :=
        branchB_predecessor_selected_level_tail_eq R hB hs (normalizedC R)
    _ = (((L5A2B4AR4R2B.c2 R - i) * normalizedB R : ℕ) : ℤ) -
        (normalizedC R : ℤ) := by rw [hreturned]

/-- A positive-CENTER source on chosen pure-`b` support is forced into the
reverse orientation of the audited X packet.  This theorem deliberately does
not declare that orientation impossible: it records both the boundary case
(`returnedX = 0`) and the genuinely mixed case (`0 < returnedX`) together
with the sharp subcritical range needed by the missing source-transport
argument. -/
theorem branchB_positive_center_pureB_reverseX_value_packet
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
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.data.returnedY = 0 ∧
      C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      C.data.sourceY = i + zH R ∧
      A.depth = wH R + C.data.returnedX ∧
      C.data.returnedX < uH R ∧
      (C.data.returnedX = 0 ∨ 0 < C.data.returnedX) ∧
      C.data.sourceValue = (i + zH R) * normalizedB R ∧
      C.data.returnedValue =
        C.data.returnedX * normalizedA R +
          (L5A2B4AR4R2B.c3 R - j) * normalizedC R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  change ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
      C.data.sourceX C.data.sourceY C.data.sourceZ at hroute
  change C.data.returnedY = 0 ∧
      C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      C.data.sourceY = i + zH R ∧
      A.depth = wH R + C.data.returnedX ∧
      C.data.returnedX < uH R ∧
      (C.data.returnedX = 0 ∨ 0 < C.data.returnedX) ∧
      C.data.sourceValue = (i + zH R) * normalizedB R ∧
      C.data.returnedValue =
        C.data.returnedX * normalizedA R +
          (L5A2B4AR4R2B.c3 R - j) * normalizedC R
  have hsplit := branchB_positive_center_pureB_returned_support_split
    R hB hs hroute
  change C.data.returnedY = 0 ∧
      ((C.data.returnedX ≠ 0 ∧ C.data.returnedZ = 0) ∨
       (C.data.returnedX = 0 ∧ C.data.returnedZ ≠ 0) ∨
       (C.data.returnedX ≠ 0 ∧ C.data.returnedZ ≠ 0)) at hsplit
  have hdepth := branchB_positive_center_depth_lt_c1
    R hB hs i j hcenter
  change A.depth < L5A2B4AR4R2B.c1 R at hdepth
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hs1, _hs2, _hs3⟩ := HC.coefficient_sums
  have hcore :
      C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      C.data.sourceY = i + zH R ∧
      A.depth = wH R + C.data.returnedX ∧
      C.data.returnedX < uH R ∧
      (C.data.returnedX = 0 ∨ 0 < C.data.returnedX) := by
    rcases hsplit.2 with hA | hC | hmix
    · exact False.elim (branchB_positive_center_pureB_returnedX_impossible
        R hB hs i j hcenter hroute hA.1 hA.2)
    · have hp := branchB_positive_center_pureB_returnedC_degenerate
        R hB hs i j hcenter hroute hC.1 hC.2
      change C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
          A.depth = wH R ∧ C.data.sourceY = i + zH R at hp
      refine ⟨hp.1, hp.2.2, ?_, ?_, Or.inl hC.1⟩
      · omega
      · omega
    · have hp := branchB_positive_center_pureB_mixed_degenerate
        R hB hs i j hcenter hroute hmix.1 hmix.2
      change C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
          C.data.sourceY = i + zH R ∧
          A.depth = wH R + C.data.returnedX ∧ wH R < A.depth at hp
      refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_,
        Or.inr (Nat.pos_of_ne_zero hmix.1)⟩
      omega
  have hroute' : C.data.sourceX = 0 ∧ C.data.sourceY ≠ 0 ∧
      C.data.sourceZ = 0 := by
    simpa [ActualSourceSupportRoute.Matches] using hroute
  have hsource : C.data.sourceValue =
      (i + zH R) * normalizedB R := by
    rw [C.data.source_factorization, hroute'.1, hroute'.2.2, hcore.2.1]
    omega
  have hreturned : C.data.returnedValue =
      C.data.returnedX * normalizedA R +
        (L5A2B4AR4R2B.c3 R - j) * normalizedC R := by
    rw [C.data.returned_factorization, hsplit.1, hcore.1]
    omega
  exact ⟨hsplit.1, hcore.1, hcore.2.1, hcore.2.2.1,
    hcore.2.2.2.1, hcore.2.2.2.2, hsource, hreturned⟩

/-- Exact separation of the two surviving reverse-X orientations.  In the
boundary branch, B23's universal predecessor exclusion is retained for every
legal nonprincipal return level.  In the mixed branch, the returned
`a`-coefficient is strictly between zero and `uH`, and is exactly the excess
of the selected-anchor depth over `wH`. -/
theorem branchB_positive_center_pureB_reverseX_boundary_or_mixed
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
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    (C.data.returnedX = 0 ∧ A.depth = wH R ∧
      ∀ k : ℕ, 0 < k → k < actualPrincipalIndex P.M.base →
        (s - (normalizedB R : ℤ)) -
            (k * normalizedM P.M.base : ℕ) ∉
          (normalizedH P.M.base).asRelativeIdeal) ∨
    (0 < C.data.returnedX ∧ C.data.returnedX < uH R ∧
      A.depth = wH R + C.data.returnedX ∧ wH R < A.depth) := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change (C.data.returnedX = 0 ∧ A.depth = wH R ∧
      ∀ k : ℕ, 0 < k → k < actualPrincipalIndex P.M.base →
        (s - (normalizedB R : ℤ)) -
            (k * normalizedM P.M.base : ℕ) ∉
          (normalizedH P.M.base).asRelativeIdeal) ∨
    (0 < C.data.returnedX ∧ C.data.returnedX < uH R ∧
      A.depth = wH R + C.data.returnedX ∧ wH R < A.depth)
  have hp := branchB_positive_center_pureB_reverseX_value_packet
    R hB hs i j hcenter hroute
  change C.data.returnedY = 0 ∧
      C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      C.data.sourceY = i + zH R ∧
      A.depth = wH R + C.data.returnedX ∧
      C.data.returnedX < uH R ∧
      (C.data.returnedX = 0 ∨ 0 < C.data.returnedX) ∧
      C.data.sourceValue = (i + zH R) * normalizedB R ∧
      C.data.returnedValue =
        C.data.returnedX * normalizedA R +
          (L5A2B4AR4R2B.c3 R - j) * normalizedC R at hp
  rcases hp.2.2.2.2.2.1 with hx0 | hxpos
  · left
    have hboundary : A.depth = wH R := by omega
    refine ⟨hx0, hboundary, ?_⟩
    intro k hkpos hklt
    exact branchB_positive_center_pureB_boundary_predecessor_tail_not_mem
      R hB hs i j hcenter hroute hboundary k hkpos hklt
  · right
    exact ⟨hxpos, hp.2.2.2.2.1, hp.2.2.2.1, by omega⟩

/-- The reverse-X source cannot sit at the missing inner corner `i = pH`.
At that corner the second Herzog relation gives both the source and its
complementary return a common positive `c`, contradicting actual
individual-return minimality. -/
theorem branchB_positive_center_pureB_anchor_i_lt_pH
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
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    i < pH R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change A.coordinate.i = i ∧ A.coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter
  have hpkt := branchB_positive_center_pureB_reverseX_value_packet
    R hB hs i j hcenter hroute
  change C.data.returnedY = 0 ∧
      C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      C.data.sourceY = i + zH R ∧
      A.depth = wH R + C.data.returnedX ∧
      C.data.returnedX < uH R ∧
      (C.data.returnedX = 0 ∨ 0 < C.data.returnedX) ∧
      C.data.sourceValue = (i + zH R) * normalizedB R ∧
      C.data.returnedValue =
        C.data.returnedX * normalizedA R +
          (L5A2B4AR4R2B.c3 R - j) * normalizedC R at hpkt
  by_contra hnot
  have hiEq : i = pH R := by omega
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨_hp, _hq, _hu, hv, _hw, _hz⟩ := HC.cross_positive
  obtain ⟨_hs1, hs2, hs3⟩ := HC.coefficient_sums
  obtain ⟨_hrel1, hrel2, _hrel3⟩ := HC.normalized_relations
  have hreturnedZPos : 0 < L5A2B4AR4R2B.c3 R - j := by omega
  let H := normalizedH P.M.base
  have hcomb (x y z : ℕ) :
      x * normalizedA R + y * normalizedB R + z * normalizedC R ∈ H := by
    have hx := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedA_mem R) x
    have hy := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedB_mem R) y
    have hz := H.toAddSubmonoid.nsmul_mem (branchB_actual_normalizedC_mem R) z
    simpa [nsmul_eq_mul, Nat.add_assoc] using H.add_mem (H.add_mem hx hy) hz
  let sourceRest := uH R * normalizedA R +
    (vH R - 1) * normalizedC R
  let returnedRest := C.data.returnedX * normalizedA R +
    (L5A2B4AR4R2B.c3 R - j - 1) * normalizedC R
  apply minimal_return_common_generator_impossible H
    C.data.return_witness.2.2
    (branchB_actual_normalizedC_mem R)
    (branchB_actual_normalizedWeight_pos R 2).ne'
    (by simpa [sourceRest] using hcomb (uH R) 0 (vH R - 1))
    (by simpa [returnedRest] using
      hcomb C.data.returnedX 0 (L5A2B4AR4R2B.c3 R - j - 1))
  · calc
      s = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
      _ = (((i + zH R) * normalizedB R : ℕ) : ℤ) := by
        exact congrArg (fun n : ℕ => (n : ℤ)) hpkt.2.2.2.2.2.2.1
      _ = (normalizedC R : ℤ) + sourceRest := by
        have hvSplit : vH R * normalizedC R =
            normalizedC R + (vH R - 1) * normalizedC R := by
          have hvOne := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hv.ne')
          calc
            vH R * normalizedC R = (vH R - 1 + 1) * normalizedC R := by
              rw [hvOne]
            _ = normalizedC R + (vH R - 1) * normalizedC R := by ring
        have hNat : (i + zH R) * normalizedB R =
            normalizedC R + sourceRest := by
          dsimp [sourceRest]
          rw [hiEq, ← hs2, hrel2, hvSplit]
          ring
        exact_mod_cast hNat
  · calc
      s - (C.data.ell * normalizedM P.M.base : ℕ) =
          (C.data.returnedValue : ℤ) := C.data.returned_eq.symm
      _ = (((C.data.returnedX * normalizedA R +
          (L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ)) : ℤ) := by
        exact congrArg (fun n : ℕ => (n : ℤ)) hpkt.2.2.2.2.2.2.2
      _ = (normalizedC R : ℤ) + returnedRest := by
        have hzOne := Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr hreturnedZPos.ne')
        have hNat : C.data.returnedX * normalizedA R +
              (L5A2B4AR4R2B.c3 R - j) * normalizedC R =
            normalizedC R + returnedRest := by
          dsimp [returnedRest]
          calc
            C.data.returnedX * normalizedA R +
                (L5A2B4AR4R2B.c3 R - j) * normalizedC R =
              C.data.returnedX * normalizedA R +
                (L5A2B4AR4R2B.c3 R - j - 1 + 1) * normalizedC R := by
                  rw [hzOne]
            _ = normalizedC R +
                (C.data.returnedX * normalizedA R +
                  (L5A2B4AR4R2B.c3 R - j - 1) * normalizedC R) := by ring
        exact_mod_cast hNat

/-- Canonical-coordinate recovery for the reverse-X packet.  The chosen
pure-`b` factorization is converted into the actual canonical X-axis source,
while the complementary return is converted into the opposite `c`-axis with
level `returnedX`.  This is the exact source/anchor transport checkpoint
available before the missing BranchBirth orientation exclusion. -/
theorem branchB_positive_center_pureB_reverseX_canonical_packet
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
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    C.source_coordinate.i = (i + zH R : ℕ) ∧
      C.source_coordinate.j = 0 ∧
      C.source_coordinate.level = 0 ∧
      C.returned_coordinate.i = 0 ∧
      C.returned_coordinate.j =
        (L5A2B4AR4R2B.c3 R - j : ℕ) ∧
      C.returned_coordinate.level = C.data.returnedX := by
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  change C.source_coordinate.i = (i + zH R : ℕ) ∧
      C.source_coordinate.j = 0 ∧
      C.source_coordinate.level = 0 ∧
      C.returned_coordinate.i = 0 ∧
      C.returned_coordinate.j =
        (L5A2B4AR4R2B.c3 R - j : ℕ) ∧
      C.returned_coordinate.level = C.data.returnedX
  have hpkt := branchB_positive_center_pureB_reverseX_value_packet
    R hB hs i j hcenter hroute
  change C.data.returnedY = 0 ∧
      C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      C.data.sourceY = i + zH R ∧
      (branchB_actual_selected_return_anchor_v2 R hB hs).depth =
        wH R + C.data.returnedX ∧
      C.data.returnedX < uH R ∧
      (C.data.returnedX = 0 ∨ 0 < C.data.returnedX) ∧
      C.data.sourceValue = (i + zH R) * normalizedB R ∧
      C.data.returnedValue =
        C.data.returnedX * normalizedA R +
          (L5A2B4AR4R2B.c3 R - j) * normalizedC R at hpkt
  have hiLt := branchB_positive_center_pureB_anchor_i_lt_pH
    R hB hs i j hcenter hroute
  have hcenter' := hcenter
  change (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.i = i ∧
      (branchB_actual_selected_return_anchor_v2 R hB hs).coordinate.j = j ∧
      1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
      (i, j) ≠ (pH R, qH R) at hcenter'
  let HC := branchB_actual_herzog_coordinates R
  obtain ⟨hp, hq, _hu, _hv, _hw, _hz⟩ := HC.cross_positive
  obtain ⟨_hs1, hs2, hs3⟩ := HC.coefficient_sums
  have hsourceShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      ((i + zH R : ℕ) : ℤ) 0 := by
    unfold L5A2B.InLShape
    constructor
    · positivity
    constructor
    · norm_num
    constructor
    · exact_mod_cast (show i + zH R < pH R + zH R by omega)
    constructor
    · exact_mod_cast (show 0 < qH R + vH R by omega)
    · exact Or.inr (by exact_mod_cast hq)
  have hsourceExact : (C.data.sourceValue : ℤ) =
      (0 : ℤ) * normalizedA R +
        ((i + zH R : ℕ) : ℤ) * normalizedB R +
          (0 : ℤ) * normalizedC R := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hpkt.2.2.2.2.2.2.1
    push_cast at h ⊢
    simpa using h
  have hscoord := actual_lShape_coordinate_eq_of_exact R
    C.source_coordinate ((i + zH R : ℕ) : ℤ) 0 0
    hsourceShape hsourceExact
  have hreturnedShape : L5A2B.InLShape (pH R) (qH R) (zH R) (vH R)
      0 ((L5A2B4AR4R2B.c3 R - j : ℕ) : ℤ) := by
    unfold L5A2B.InLShape
    constructor
    · norm_num
    constructor
    · positivity
    constructor
    · exact_mod_cast (show 0 < pH R + zH R by omega)
    constructor
    · exact_mod_cast (show L5A2B4AR4R2B.c3 R - j < qH R + vH R by
        omega)
    · exact Or.inl (by exact_mod_cast hp)
  have hreturnedExact : (C.data.returnedValue : ℤ) =
      (C.data.returnedX : ℤ) * normalizedA R +
        (0 : ℤ) * normalizedB R +
          ((L5A2B4AR4R2B.c3 R - j : ℕ) : ℤ) * normalizedC R := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hpkt.2.2.2.2.2.2.2
    push_cast at h ⊢
    simpa using h
  have hrcoord := actual_lShape_coordinate_eq_of_exact R
    C.returned_coordinate 0 ((L5A2B4AR4R2B.c3 R - j : ℕ) : ℤ)
      (C.data.returnedX : ℤ) hreturnedShape hreturnedExact
  exact ⟨hscoord.1, hscoord.2.1, hscoord.2.2,
    hrcoord.1, hrcoord.2.1, hrcoord.2.2⟩

/-- Source-exact entry point from the B24 reverse-X packet to the historical
CENTER-X fixed-return candidate table.  The first displayed integer is the
literal candidate numerator at the actual source state: selected return plus
the canonical tail of the complementary return, minus the source value.
It is exactly `a * (wH - depth)`, hence exactly `-returnedX * a`.

This theorem intentionally stops before RECORD/owner transport.  The current
`IsBranchBirth` predicate contains final-source minimality but no branch
diamond or active-owner datum. -/
theorem branchB_positive_center_pureB_reverseX_candidate_transport_packet
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
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    let candidateNumerator : ℤ :=
      (C.data.ell * normalizedM P.M.base : ℕ) +
        ((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) -
          C.data.sourceValue
    candidateNumerator =
        ((wH R : ℤ) - (A.depth : ℤ)) * normalizedA R ∧
      (wH R : ℤ) - (A.depth : ℤ) = -(C.data.returnedX : ℤ) ∧
      candidateNumerator = -(C.data.returnedX : ℤ) * normalizedA R := by
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  let candidateNumerator : ℤ :=
    (C.data.ell * normalizedM P.M.base : ℕ) +
      ((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) -
        C.data.sourceValue
  change candidateNumerator =
        ((wH R : ℤ) - (A.depth : ℤ)) * normalizedA R ∧
      (wH R : ℤ) - (A.depth : ℤ) = -(C.data.returnedX : ℤ) ∧
      candidateNumerator = -(C.data.returnedX : ℤ) * normalizedA R
  have hpkt := branchB_positive_center_pureB_reverseX_value_packet
    R hB hs i j hcenter hroute
  change C.data.returnedY = 0 ∧
      C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
      C.data.sourceY = i + zH R ∧
      A.depth = wH R + C.data.returnedX ∧
      C.data.returnedX < uH R ∧
      (C.data.returnedX = 0 ∨ 0 < C.data.returnedX) ∧
      C.data.sourceValue = (i + zH R) * normalizedB R ∧
      C.data.returnedValue =
        C.data.returnedX * normalizedA R +
          (L5A2B4AR4R2B.c3 R - j) * normalizedC R at hpkt
  have hbalance : (C.data.sourceValue : ℤ) =
      (C.data.ell * normalizedM P.M.base : ℕ) + C.data.returnedValue := by
    rw [C.data.source_eq, C.data.returned_eq]
    ring
  have hreturned : (C.data.returnedValue : ℤ) =
      (C.data.returnedX : ℤ) * normalizedA R +
        (L5A2B4AR4R2B.c3 R - j : ℕ) * normalizedC R := by
    exact_mod_cast hpkt.2.2.2.2.2.2.2
  have hgap : (wH R : ℤ) - (A.depth : ℤ) =
      -(C.data.returnedX : ℤ) := by
    have hdepth := congrArg (fun n : ℕ => (n : ℤ)) hpkt.2.2.2.1
    push_cast at hdepth
    omega
  have hcandidate : candidateNumerator =
      -(C.data.returnedX : ℤ) * normalizedA R := by
    dsimp only [candidateNumerator]
    simp only [Nat.cast_mul] at hbalance ⊢
    rw [hreturned] at hbalance
    nlinarith
  refine ⟨?_, hgap, hcandidate⟩
  · rw [hgap]
    exact hcandidate

end NS25Lean.L5A2B4AR5B
