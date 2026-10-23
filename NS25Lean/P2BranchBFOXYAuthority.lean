import NS25Lean.P2BranchBLShapeCompleteness

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open L5A1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

inductive ActualFOXYFamily
  | F | O | X | Y
  deriving DecidableEq

/-- Two tail coordinates and the authority's depth `eta`. -/
structure ActualFOXYPacket where
  family : ActualFOXYFamily
  bCoord : ℕ
  cCoord : ℕ
  eta : ℕ
  deriving DecidableEq

/-- Exact CENTER parameter range. -/
structure ActualCenterParameters (R : SectorBCriticalRoleBranchB P) where
  i : ℕ
  j : ℕ
  d : ℕ
  i_pos : 1 ≤ i
  i_le : i ≤ pH R
  j_pos : 1 ≤ j
  j_le : j ≤ qH R
  not_inner_corner : (i, j) ≠ (pH R, qH R)
  depth_lt_u : d < uH R
  depth_lt_w : d < wH R

/-- Exact strict-RB parameter range (`s < zH`, `tau < qH` is equivalent to
the displayed `s ≤ zH-1`, `tau ≤ qH-1` under positivity). -/
structure ActualStrictRBParameters (R : SectorBCriticalRoleBranchB P) where
  s : ℕ
  tau : ℕ
  d : ℕ
  s_pos : 1 ≤ s
  s_lt : s < zH R
  tau_pos : 1 ≤ tau
  tau_lt : tau < qH R
  depth_lt_u : d < uH R

/-- Exact strict-LT parameter range. -/
structure ActualStrictLTParameters (R : SectorBCriticalRoleBranchB P) where
  s : ℕ
  tau : ℕ
  d : ℕ
  s_pos : 1 ≤ s
  s_lt : s < pH R
  tau_pos : 1 ≤ tau
  tau_lt : tau < vH R
  depth_lt_w : d < wH R

/-- CENTER has F/O always, X iff `i < pH`, and Y iff `j < qH`. -/
inductive ActualCenterFamily {R : SectorBCriticalRoleBranchB P}
    (Q : ActualCenterParameters R)
  | F
  | O
  | X (eligible : Q.i < pH R)
  | Y (eligible : Q.j < qH R)

/-- Strict RB/LT have exactly F/X/Y, so O is unrepresentable. -/
inductive ActualStrictFOXYFamily
  | F | X | Y
  deriving DecidableEq

def centerFOXYPacket {R : SectorBCriticalRoleBranchB P}
    (Q : ActualCenterParameters R) : ActualCenterFamily Q → ActualFOXYPacket
  | .F => ⟨.F, Q.i, Q.j, 0⟩
  | .O => ⟨.O, 0, 0, L5A2B4AR4R2B.c1 R - Q.d⟩
  | .X _ => ⟨.X, Q.i + zH R, 0, wH R - Q.d⟩
  | .Y _ => ⟨.Y, 0, Q.j + vH R, uH R - Q.d⟩

def strictRBFOXYPacket {R : SectorBCriticalRoleBranchB P}
    (Q : ActualStrictRBParameters R) : ActualStrictFOXYFamily → ActualFOXYPacket
  | .F => ⟨.F, pH R + Q.s, Q.tau, 0⟩
  | .X => ⟨.X, Q.s, 0, L5A2B4AR4R2B.c1 R - Q.d⟩
  | .Y => ⟨.Y, 0, Q.tau + vH R, uH R - Q.d⟩

def strictLTFOXYPacket {R : SectorBCriticalRoleBranchB P}
    (Q : ActualStrictLTParameters R) : ActualStrictFOXYFamily → ActualFOXYPacket
  | .F => ⟨.F, Q.s, qH R + Q.tau, 0⟩
  | .X => ⟨.X, Q.s + zH R, 0, wH R - Q.d⟩
  | .Y => ⟨.Y, 0, Q.tau, L5A2B4AR4R2B.c1 R - Q.d⟩

theorem center_foxy_packet_spec {R : SectorBCriticalRoleBranchB P}
    (Q : ActualCenterParameters R) :
    centerFOXYPacket Q .F = ⟨.F, Q.i, Q.j, 0⟩ ∧
    centerFOXYPacket Q .O =
      ⟨.O, 0, 0, L5A2B4AR4R2B.c1 R - Q.d⟩ ∧
    (∀ h : Q.i < pH R,
      centerFOXYPacket Q (.X h) =
        ⟨.X, Q.i + zH R, 0, wH R - Q.d⟩) ∧
    (∀ h : Q.j < qH R,
      centerFOXYPacket Q (.Y h) =
        ⟨.Y, 0, Q.j + vH R, uH R - Q.d⟩) := by
  exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem strictRB_foxy_packet_spec {R : SectorBCriticalRoleBranchB P}
    (Q : ActualStrictRBParameters R) :
    strictRBFOXYPacket Q .F = ⟨.F, pH R + Q.s, Q.tau, 0⟩ ∧
    strictRBFOXYPacket Q .X =
      ⟨.X, Q.s, 0, L5A2B4AR4R2B.c1 R - Q.d⟩ ∧
    strictRBFOXYPacket Q .Y =
      ⟨.Y, 0, Q.tau + vH R, uH R - Q.d⟩ := by
  exact ⟨rfl, rfl, rfl⟩

theorem strictLT_foxy_packet_spec {R : SectorBCriticalRoleBranchB P}
    (Q : ActualStrictLTParameters R) :
    strictLTFOXYPacket Q .F = ⟨.F, Q.s, qH R + Q.tau, 0⟩ ∧
    strictLTFOXYPacket Q .X =
      ⟨.X, Q.s + zH R, 0, wH R - Q.d⟩ ∧
    strictLTFOXYPacket Q .Y =
      ⟨.Y, 0, Q.tau, L5A2B4AR4R2B.c1 R - Q.d⟩ := by
  exact ⟨rfl, rfl, rfl⟩

/-- All non-F CENTER depths are strictly positive whenever the corresponding
family exists. -/
theorem center_foxy_eta_positive {R : SectorBCriticalRoleBranchB P}
    (Q : ActualCenterParameters R) :
    0 < L5A2B4AR4R2B.c1 R - Q.d ∧
      0 < wH R - Q.d ∧ 0 < uH R - Q.d := by
  have hc1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
  refine ⟨Nat.sub_pos_iff_lt.mpr ?_,
    Nat.sub_pos_iff_lt.mpr Q.depth_lt_w,
    Nat.sub_pos_iff_lt.mpr Q.depth_lt_u⟩
  calc
    Q.d < wH R := Q.depth_lt_w
    _ ≤ uH R + wH R := Nat.le_add_left _ _
    _ = L5A2B4AR4R2B.c1 R := hc1.symm

/-- Strict-RB X/Y depths are strictly positive. -/
theorem strictRB_foxy_eta_positive {R : SectorBCriticalRoleBranchB P}
    (Q : ActualStrictRBParameters R) :
    0 < L5A2B4AR4R2B.c1 R - Q.d ∧ 0 < uH R - Q.d := by
  have hc1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
  exact ⟨Nat.sub_pos_iff_lt.mpr (by
      calc
        Q.d < uH R := Q.depth_lt_u
        _ ≤ uH R + wH R := Nat.le_add_right _ _
        _ = L5A2B4AR4R2B.c1 R := hc1.symm),
    Nat.sub_pos_iff_lt.mpr Q.depth_lt_u⟩

/-- Strict-LT X/Y depths are strictly positive. -/
theorem strictLT_foxy_eta_positive {R : SectorBCriticalRoleBranchB P}
    (Q : ActualStrictLTParameters R) :
    0 < wH R - Q.d ∧ 0 < L5A2B4AR4R2B.c1 R - Q.d := by
  have hc1 := (branchB_actual_herzog_coordinates R).coefficient_sums.1
  exact ⟨Nat.sub_pos_iff_lt.mpr Q.depth_lt_w,
    Nat.sub_pos_iff_lt.mpr (by
      calc
        Q.d < wH R := Q.depth_lt_w
        _ ≤ uH R + wH R := Nat.le_add_left _ _
        _ = L5A2B4AR4R2B.c1 R := hc1.symm)⟩

theorem strict_family_excludes_O (f : ActualStrictFOXYFamily) :
    (match f with | .F => ActualFOXYFamily.F | .X => .X | .Y => .Y) ≠ .O := by
  cases f <;> decide

/-- Boundary CENTER is exactly one axis degeneration; the inner corner is
excluded by the authority range. -/
theorem center_boundary_axis_degeneration {R : SectorBCriticalRoleBranchB P}
    (Q : ActualCenterParameters R) (hboundary : Q.i = pH R ∨ Q.j = qH R) :
    (Q.i = pH R ∧ Q.j < qH R) ∨ (Q.i < pH R ∧ Q.j = qH R) := by
  rcases hboundary with hi | hj
  · left
    refine ⟨hi, ?_⟩
    have hne : Q.j ≠ qH R := by
      intro hj
      exact Q.not_inner_corner (Prod.ext hi hj)
    have hjle := Q.j_le
    omega
  · right
    refine ⟨?_, hj⟩
    have hne : Q.i ≠ pH R := by
      intro hi
      exact Q.not_inner_corner (Prod.ext hi hj)
    have hile := Q.i_le
    omega

/-- The three source-authorized parameter regions. -/
inductive ActualFOXYParameters (R : SectorBCriticalRoleBranchB P)
  | center (Q : ActualCenterParameters R)
  | strictRB (Q : ActualStrictRBParameters R)
  | strictLT (Q : ActualStrictLTParameters R)

def ActualFOXYParameters.selectedI {R : SectorBCriticalRoleBranchB P} :
    ActualFOXYParameters R → ℕ
  | .center Q => Q.i
  | .strictRB Q => pH R + Q.s
  | .strictLT Q => Q.s

def ActualFOXYParameters.selectedJ {R : SectorBCriticalRoleBranchB P} :
    ActualFOXYParameters R → ℕ
  | .center Q => Q.j
  | .strictRB Q => Q.tau
  | .strictLT Q => qH R + Q.tau

def ActualFOXYParameters.depth {R : SectorBCriticalRoleBranchB P} :
    ActualFOXYParameters R → ℕ
  | .center Q => Q.d
  | .strictRB Q => Q.d
  | .strictLT Q => Q.d

/-- The complete family packet attached to one authorized parameter region.
This bundles the exact coordinate/eta equations with the positivity and
exclusion/boundary rules, rather than treating the equations as premises. -/
def ActualFOXYFamilyData {R : SectorBCriticalRoleBranchB P} :
    ActualFOXYParameters R → Prop
  | .center Q =>
      centerFOXYPacket Q .F = ⟨.F, Q.i, Q.j, 0⟩ ∧
      centerFOXYPacket Q .O =
        ⟨.O, 0, 0, L5A2B4AR4R2B.c1 R - Q.d⟩ ∧
      (∀ h : Q.i < pH R,
        centerFOXYPacket Q (.X h) =
          ⟨.X, Q.i + zH R, 0, wH R - Q.d⟩) ∧
      (∀ h : Q.j < qH R,
        centerFOXYPacket Q (.Y h) =
          ⟨.Y, 0, Q.j + vH R, uH R - Q.d⟩) ∧
      (0 < L5A2B4AR4R2B.c1 R - Q.d ∧
        0 < wH R - Q.d ∧ 0 < uH R - Q.d) ∧
      (∀ _hboundary : Q.i = pH R ∨ Q.j = qH R,
        (Q.i = pH R ∧ Q.j < qH R) ∨
          (Q.i < pH R ∧ Q.j = qH R))
  | .strictRB Q =>
      strictRBFOXYPacket Q .F = ⟨.F, pH R + Q.s, Q.tau, 0⟩ ∧
      strictRBFOXYPacket Q .X =
        ⟨.X, Q.s, 0, L5A2B4AR4R2B.c1 R - Q.d⟩ ∧
      strictRBFOXYPacket Q .Y =
        ⟨.Y, 0, Q.tau + vH R, uH R - Q.d⟩ ∧
      (0 < L5A2B4AR4R2B.c1 R - Q.d ∧ 0 < uH R - Q.d) ∧
      (∀ f : ActualStrictFOXYFamily,
        (match f with | .F => ActualFOXYFamily.F | .X => .X | .Y => .Y) ≠ .O)
  | .strictLT Q =>
      strictLTFOXYPacket Q .F = ⟨.F, Q.s, qH R + Q.tau, 0⟩ ∧
      strictLTFOXYPacket Q .X =
        ⟨.X, Q.s + zH R, 0, wH R - Q.d⟩ ∧
      strictLTFOXYPacket Q .Y =
        ⟨.Y, 0, Q.tau, L5A2B4AR4R2B.c1 R - Q.d⟩ ∧
      (0 < wH R - Q.d ∧ 0 < L5A2B4AR4R2B.c1 R - Q.d) ∧
      (∀ f : ActualStrictFOXYFamily,
        (match f with | .F => ActualFOXYFamily.F | .X => .X | .Y => .Y) ≠ .O)

theorem actual_foxy_family_data {R : SectorBCriticalRoleBranchB P}
    (Q : ActualFOXYParameters R) : ActualFOXYFamilyData Q := by
  cases Q with
  | center Q =>
      rcases center_foxy_packet_spec Q with ⟨hF, hO, hX, hY⟩
      exact ⟨hF, hO, hX, hY, center_foxy_eta_positive Q,
        center_boundary_axis_degeneration Q⟩
  | strictRB Q =>
      rcases strictRB_foxy_packet_spec Q with ⟨hF, hX, hY⟩
      exact ⟨hF, hX, hY, strictRB_foxy_eta_positive Q,
        strict_family_excludes_O⟩
  | strictLT Q =>
      rcases strictLT_foxy_packet_spec Q with ⟨hF, hX, hY⟩
      exact ⟨hF, hX, hY, strictLT_foxy_eta_positive Q,
        strict_family_excludes_O⟩

/-- Explicit target predicate connecting an actual birth to the source-exact
authority.  It is a conjunction/existential to be proved, not a field added to
any Branch-B input structure. -/
def ActualSelectedReturnNormalForm
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : L5A2B4AR1.IsBranchBirth (L5A2B4AR1.normalizedH P.M.base)
      (L5A2B4AR1.normalizedM P.M.base)
      (L5A2B4AR1.actualPrincipalIndex P.M.base) s) : Prop :=
  ∃ Q : ActualFOXYParameters R,
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).source_coordinate.i =
        (Q.selectedI : ℤ) ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).source_coordinate.j =
        (Q.selectedJ : ℤ) ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).source_coordinate.level = 0 ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).returned_coordinate.i = 0 ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).returned_coordinate.j = 0 ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).returned_coordinate.level =
      (Q.depth : ℤ)

/-- The required result is concrete: existence of one of the three exact
parameter regions tied to the canonical source and returned coordinates. -/
def ActualFOXYSourceComplete
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : L5A2B4AR1.IsBranchBirth (L5A2B4AR1.normalizedH P.M.base)
      (L5A2B4AR1.normalizedM P.M.base)
      (L5A2B4AR1.actualPrincipalIndex P.M.base) s) : Prop :=
  ∃ Q : ActualFOXYParameters R,
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).source_coordinate.i =
        (Q.selectedI : ℤ) ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).source_coordinate.j =
        (Q.selectedJ : ℤ) ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).source_coordinate.level = 0 ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).returned_coordinate.i = 0 ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).returned_coordinate.j = 0 ∧
    (branchB_actual_prefix_canonical_lShape_coordinates R hB hs).returned_coordinate.level =
      (Q.depth : ℤ) ∧
    ActualFOXYFamilyData Q

/-- Once the actual selected-return normal form is available, every packet,
eta identity, exclusion, and boundary rule is supplied without extra premises. -/
theorem actualFOXYSourceComplete_of_normalForm
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M) {s : ℤ}
    (hs : L5A2B4AR1.IsBranchBirth (L5A2B4AR1.normalizedH P.M.base)
      (L5A2B4AR1.normalizedM P.M.base)
      (L5A2B4AR1.actualPrincipalIndex P.M.base) s)
    (h : ActualSelectedReturnNormalForm R hB hs) :
    ActualFOXYSourceComplete R hB hs := by
  rcases h with ⟨Q, hi, hj, hlevel, hri, hrj, hrlevel⟩
  exact ⟨Q, hi, hj, hlevel, hri, hrj, hrlevel, actual_foxy_family_data Q⟩

end NS25Lean.L5A2B4AR5B
