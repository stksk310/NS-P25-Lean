import NS25Lean.P2BranchBCorrectedM2M3
import NS25Lean.P2BranchBRoutingSourceDictionary

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L5A1 L5A2B4AR1 L5A2B4AR4R1 L5A2C4H

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

@[simp] theorem branchB_routingB_eq_normalizedB
    (R : SectorBCriticalRoleBranchB P) :
    routingB P.M.base R.reindex = normalizedB R := by
  change weights P.M.base (R.reindex 1) /
      routingD P.M.base R.reindex =
    weights P.M.base (R.reindex 1) /
      tailGcd (P.M.base.tailDegrees 0).val
        (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val
  rw [routingD_eq_chosenTailGcd]

/-- Kernel-level semantic audit of the current source-only predicate.  In
particular, this statement contains no routing edge, branch base, RECORD
diamond, or owner datum. -/
theorem current_isBranchBirth_iff_final_nonprincipal_source
    (H : NumericalSemigroup) (m q0 : ℕ) (s : ℤ) :
    IsBranchBirth H m q0 s ↔
      IsSource H (finalCarrier H m q0) s ∧ s ≠ (q0 * m : ℕ) :=
  Iff.rfl

/-- The final normalized source underlying the current `IsBranchBirth`
predicate, transported backwards through the actual routing-source/Apéry
dictionary.  This constructs an actual routing *source state*; it makes no
claim that the state is the target of a branch. -/
noncomputable def branchBActualFinalRoutingSource
    (R : SectorBCriticalRoleBranchB P) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let e := R.reindex
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    {r // (routingData P.M.base e).IsSource r} := by
  dsimp
  let e := R.reindex
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  exact (routingSourceEquivChosenSource P.M.base e).symm
    (chosenSourceOfNormalizedFinalSource P.M.base hs.1)

/-- The inverse dictionary is source-exact: its canonical Apéry
representative is the original numeric final source. -/
theorem branchB_actual_final_routing_source_spec
    (R : SectorBCriticalRoleBranchB P) {s : ℤ}
    (hs : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base) s) :
    let e := R.reindex
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let r := branchBActualFinalRoutingSource R hs
    (routingData P.M.base e).IsSource r.val ∧
      (routingI P.M.base e).aperyRepresentative
        (routingA P.M.base e) r.val = s := by
  let e := R.reindex
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let source := chosenSourceOfNormalizedFinalSource P.M.base hs.1
  let r := branchBActualFinalRoutingSource R hs
  refine ⟨(branchBActualFinalRoutingSource R hs).property, ?_⟩
  calc
    (routingI P.M.base e).aperyRepresentative
        (routingA P.M.base e) r.val =
        (chosenSourceNormalizedGenerator P.M.base
          (routingSourceEquivChosenSource P.M.base e r)).val :=
      (chosenSourceNormalizedGenerator_routing_apply_val
        P.M.base e r).symm
    _ = (chosenSourceNormalizedGenerator P.M.base source).val := by
      congr 2
      exact (routingSourceEquivChosenSource P.M.base e).apply_symm_apply source
    _ = s := chosenSourceNormalizedGenerator_of_finalSource P.M.base hs.1

/-- Maximal source-exact B26 checkpoint for the positive-CENTER pure-B
reverse-X route.  The B24 source coordinate is the actual final routing
source state, and the frozen B25 candidate value is attached to that same
numeric state.  No source-to-branch surjectivity is asserted. -/
theorem branchB_positive_center_pureB_reverseX_actual_source_state
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
    let e := R.reindex
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let G := routingData P.M.base e
    let D := branchBActualFinalRoutingSource R hs
    let A := branchB_actual_selected_return_anchor_v2 R hB hs
    let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
    let candidateNumerator : ℤ :=
      (C.data.ell * normalizedM P.M.base : ℕ) +
        ((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) -
          C.data.sourceValue
    G.IsSource D.val ∧
      D.val = gridResidue P.M.base e (i + zH R) 0 ∧
      (routingI P.M.base e).aperyRepresentative
          (routingA P.M.base e) D.val = (C.data.sourceValue : ℤ) ∧
      C.source_coordinate.i = (i + zH R : ℕ) ∧
      C.source_coordinate.j = 0 ∧
      C.source_coordinate.level = 0 ∧
      candidateNumerator = -(C.data.returnedX : ℤ) * normalizedA R := by
  let e := R.reindex
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let G := routingData P.M.base e
  let D := branchBActualFinalRoutingSource R hs
  let A := branchB_actual_selected_return_anchor_v2 R hB hs
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hs
  let candidateNumerator : ℤ :=
    (C.data.ell * normalizedM P.M.base : ℕ) +
      ((L5A2B4AR4R2B.c3 R - j) * normalizedC R : ℕ) -
        C.data.sourceValue
  have hsource := branchB_actual_final_routing_source_spec R hs
  have hcoord := branchB_positive_center_pureB_reverseX_canonical_packet
    R hB hs i j hcenter hroute
  have hpkt := branchB_positive_center_pureB_reverseX_value_packet
    R hB hs i j hcenter hroute
  have hcandidate :=
    branchB_positive_center_pureB_reverseX_candidate_transport_packet
      R hB hs i j hcenter hroute
  change G.IsSource D.val ∧
      D.val = gridResidue P.M.base e (i + zH R) 0 ∧
      (routingI P.M.base e).aperyRepresentative
          (routingA P.M.base e) D.val = (C.data.sourceValue : ℤ) ∧
      C.source_coordinate.i = (i + zH R : ℕ) ∧
      C.source_coordinate.j = 0 ∧
      C.source_coordinate.level = 0 ∧
      candidateNumerator = -(C.data.returnedX : ℤ) * normalizedA R
  have hrep : (routingI P.M.base e).aperyRepresentative
      (routingA P.M.base e) D.val = (C.data.sourceValue : ℤ) :=
    hsource.2.trans C.data.source_eq.symm
  have hDcoord : D.val = gridResidue P.M.base e (i + zH R) 0 := by
    rw [← routingSource_apery_residue P.M.base e D]
    rw [hrep]
    change C.data.returnedY = 0 ∧
        C.data.returnedZ = L5A2B4AR4R2B.c3 R - j ∧
        C.data.sourceY = i + zH R ∧
        A.depth = wH R + C.data.returnedX ∧
        C.data.returnedX < uH R ∧
        (C.data.returnedX = 0 ∨ 0 < C.data.returnedX) ∧
        C.data.sourceValue = (i + zH R) * normalizedB R ∧
        C.data.returnedValue = C.data.returnedX * normalizedA R +
          (L5A2B4AR4R2B.c3 R - j) * normalizedC R at hpkt
    have hvalueZ : (C.data.sourceValue : ℤ) =
        ((i + zH R) * normalizedB R : ℕ) := by
      exact_mod_cast hpkt.2.2.2.2.2.2.1
    rw [congrArg (fun z : ℤ =>
      (z : ZMod (routingA P.M.base e))) hvalueZ]
    change (((((i + zH R) * normalizedB R : ℕ) : ℤ)) :
        ZMod (routingA P.M.base e)) =
      ((i + zH R : ℕ) : ZMod (routingA P.M.base e)) *
          (routingB P.M.base e : ZMod (routingA P.M.base e)) +
        ((0 : ℕ) : ZMod (routingA P.M.base e)) *
          (routingC P.M.base e : ZMod (routingA P.M.base e))
    rw [branchB_routingB_eq_normalizedB R]
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast,
      Nat.cast_mul, Nat.cast_add, Nat.cast_zero, zero_mul, add_zero]
  refine ⟨hsource.1, hDcoord, hrep,
    hcoord.1, hcoord.2.1, hcoord.2.2.1, ?_⟩
  · exact hcandidate.2.2

end NS25Lean.L5A2B4AR5B
