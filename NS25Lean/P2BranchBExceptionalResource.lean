import NS25Lean.P2BranchBInactiveGateDirect
import NS25Lean.P2BranchAEntryClosure

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2B4AR5B

open L5A1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Exceptional branches in the inactive Branch-B chart whose canonical
endpoint is classified as an actual sink.  This fibre contains no escape
data. -/
def BranchBActualExceptionalBranches (P : P2Data Gamma)
    (R : SectorBCriticalRoleBranchB P) : Type :=
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  {s : L5A2C4I.ResidueData.BExceptionalBranches
      (L5A2C4H.routingData P.M.base e) //
    ∃ x : L5A2C4H.ActualSink
        (L5A2C4H.routingI P.M.base e)
        (L5A2C4H.routingA P.M.base e)
        (L5A2C4H.routingB P.M.base e)
        (L5A2C4H.routingC P.M.base e)
        (L5A2C4H.routingHB P.M.base e)
        (L5A2C4H.routingHC P.M.base e),
      L5A2B4AR5A.exceptionalEndpointActualOrFake P.M.base e s = Sum.inl x}

/-- The complementary exceptional fibre, whose canonical endpoint is a
source-exact fake terminal seat. -/
def BranchBFakeExceptionalBranches (P : P2Data Gamma)
    (R : SectorBCriticalRoleBranchB P) : Type :=
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  {s : L5A2C4I.ResidueData.BExceptionalBranches
      (L5A2C4H.routingData P.M.base e) //
    ¬ ∃ x : L5A2C4H.ActualSink
        (L5A2C4H.routingI P.M.base e)
        (L5A2C4H.routingA P.M.base e)
        (L5A2C4H.routingB P.M.base e)
        (L5A2C4H.routingC P.M.base e)
        (L5A2C4H.routingHB P.M.base e)
        (L5A2C4H.routingHC P.M.base e),
      L5A2B4AR5A.exceptionalEndpointActualOrFake P.M.base e s = Sum.inl x}

/-- The generic endpoint classifier gives an exhaustive, disjoint actual/fake
partition of the inactive-chart exceptional branches. -/
noncomputable def branchBExceptionalActualFakeEquiv
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    L5A2C4I.ResidueData.BExceptionalBranches
        (L5A2C4H.routingData P.M.base e) ≃
      Sum (BranchBActualExceptionalBranches P R)
        (BranchBFakeExceptionalBranches P R) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  simpa only [BranchBActualExceptionalBranches,
    BranchBFakeExceptionalBranches] using
      (L5A2C4I.ResidueData.predicatePartitionEquiv
        (fun s : L5A2C4I.ResidueData.BExceptionalBranches
            (L5A2C4H.routingData P.M.base e) =>
          ∃ x : L5A2C4H.ActualSink
              (L5A2C4H.routingI P.M.base e)
              (L5A2C4H.routingA P.M.base e)
              (L5A2C4H.routingB P.M.base e)
              (L5A2C4H.routingC P.M.base e)
              (L5A2C4H.routingHB P.M.base e)
              (L5A2C4H.routingHC P.M.base e),
            L5A2B4AR5A.exceptionalEndpointActualOrFake P.M.base e s = Sum.inl x))

noncomputable def branchBActualExceptionalSink
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    BranchBActualExceptionalBranches P R →
      L5A2C4H.ActualSink
        (L5A2C4H.routingI P.M.base e)
        (L5A2C4H.routingA P.M.base e)
        (L5A2C4H.routingB P.M.base e)
        (L5A2C4H.routingC P.M.base e)
        (L5A2C4H.routingHB P.M.base e)
        (L5A2C4H.routingHC P.M.base e) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  exact fun x => Classical.choose x.property

theorem branchBActualExceptionalSink_spec
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    L5A2B4AR5A.exceptionalEndpointActualOrFake P.M.base e x.val =
      Sum.inl (branchBActualExceptionalSink P R x) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  exact Classical.choose_spec x.property

theorem branchBActualExceptionalSink_injective
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    Function.Injective (branchBActualExceptionalSink P R) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  change Function.Injective (branchBActualExceptionalSink P R)
  intro x y hxy
  apply Subtype.ext
  apply L5A2B4AR5A.exceptionalEndpointActualOrFake_injective P.M.base e
  rw [branchBActualExceptionalSink_spec P R x,
    branchBActualExceptionalSink_spec P R y, hxy]

/-- The actual classifier output has exactly the canonical endpoint residue;
this is the source-exact bridge from the first-stage branch to the existing
actual-sink subtype. -/
theorem branchB_actualExceptionalSink_val_eq_bEndpoint
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    (branchBActualExceptionalSink P R x).val =
      L5A2C4I.ResidueData.canonicalBEndpoint
        (L5A2C4H.routingData P.M.base e) x.val.val := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  have h := branchBActualExceptionalSink_spec P R x
  let E := L5A2C4N.fullSinkEquivActualSumFake_sourceExact
    (L5A2C4H.routingI P.M.base e) (L5A2C4H.routingA P.M.base e)
    (L5A2C4H.routingB P.M.base e) (L5A2C4H.routingC P.M.base e)
    (L5A2C4H.routingHB P.M.base e) (L5A2C4H.routingHC P.M.base e)
  change E (L5A2B4AR5A.exceptionalEndpointFullSink P.M.base e x.val) =
    Sum.inl (branchBActualExceptionalSink P R x) at h
  have hinv := congrArg E.symm h
  rw [E.symm_apply_apply] at hinv
  have hv := congrArg Subtype.val hinv
  have hs : (E.symm (Sum.inl (branchBActualExceptionalSink P R x))).val =
      (branchBActualExceptionalSink P R x).val := by
    rfl
  rw [hs] at hv
  simpa [L5A2B4AR5A.exceptionalEndpointFullSink] using hv.symm

/-- Every actual exceptional branch supplies all endpoint facts available
before choosing an OX/OY orientation: raw sink semantics, actual integrality,
positive endpoint height, the terminal B-boundary zero, and exceptional
C-cross positivity. -/
theorem branchB_actualExceptional_endpoint_kernel
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    let D := L5A2C4H.routingData P.M.base e
    let p := L5A2C4I.ResidueData.canonicalBEndpoint D x.val.val
    D.IsSink p ∧
      (L5A2C4H.routingI P.M.base e).aperyRepresentative
          (L5A2C4H.routingA P.M.base e) p -
        L5A2C4H.routingA P.M.base e ∈
          (L5A2C4H.routingH P.M.base e).asRelativeIdeal ∧
      0 < D.v p ∧ D.v (D.b p) = 0 ∧ 0 < D.u (D.c p) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  let D := L5A2C4H.routingData P.M.base e
  let p := L5A2C4I.ResidueData.canonicalBEndpoint D x.val.val
  have hrun := L5A2C4I.ResidueData.canonicalBRun_spec D x.val.val
  have hpval := branchB_actualExceptionalSink_val_eq_bEndpoint P R x
  have hactual := (branchBActualExceptionalSink P R x).property
  refine ⟨L5A2B4AR5A.ExceptionalEndpoint.isSink D x.val, ?_,
    hrun.2.choose_spec.2.2.2.1, hrun.2.choose_spec.2.2.2.2, ?_⟩
  · simpa [p, ← hpval] using hactual.2
  · exact Nat.pos_of_ne_zero x.val.property

theorem branchBFakeExceptionalSeat_exists
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    ∀ x : BranchBFakeExceptionalBranches P R,
      ∃ y : L5A2C4N.ActualFakeTerminalSeats P.M.base e,
        L5A2B4AR5A.exceptionalEndpointActualOrFake P.M.base e x.val = Sum.inr y := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  dsimp only
  intro x
  cases h : L5A2B4AR5A.exceptionalEndpointActualOrFake P.M.base e x.val with
  | inl y => exact (x.property ⟨y, h⟩).elim
  | inr y => exact ⟨y, rfl⟩

noncomputable def branchBFakeExceptionalSeat
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    BranchBFakeExceptionalBranches P R →
      L5A2C4N.ActualFakeTerminalSeats P.M.base e := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  dsimp only
  intro x
  exact Classical.choose (branchBFakeExceptionalSeat_exists P R x)

theorem branchBFakeExceptionalSeat_spec
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBFakeExceptionalBranches P R) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    L5A2B4AR5A.exceptionalEndpointActualOrFake P.M.base e x.val =
      Sum.inr (branchBFakeExceptionalSeat P R x) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  dsimp only
  exact Classical.choose_spec (branchBFakeExceptionalSeat_exists P R x)

theorem branchBFakeExceptionalSeat_injective
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    Function.Injective (branchBFakeExceptionalSeat P R) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  change Function.Injective (branchBFakeExceptionalSeat P R)
  intro x y hxy
  apply Subtype.ext
  apply L5A2B4AR5A.exceptionalEndpointActualOrFake_injective P.M.base e
  rw [branchBFakeExceptionalSeat_spec P R x,
    branchBFakeExceptionalSeat_spec P R y, hxy]

/-- ENTRY cannot pay every exceptional endpoint with a fake terminal seat:
the first-stage partition already pays every nonexceptional branch with an
exact unused merge, so the frozen `+1` equality forces an actual exceptional
endpoint. -/
theorem branchB_entry_exists_actual_exceptional
    (R : SectorBCriticalRoleBranchB P) (hentry : P.W = 1) :
    Nonempty (BranchBActualExceptionalBranches P R) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  let D := L5A2C4H.routingData P.M.base e
  by_contra hactual
  let fake : L5A2C4I.ResidueData.BExceptionalBranches D →
      L5A2C4N.ActualFakeTerminalSeats P.M.base e := fun s =>
    match h : L5A2B4AR5A.exceptionalEndpointActualOrFake P.M.base e s with
    | Sum.inl x => (hactual ⟨⟨s, x, h⟩⟩).elim
    | Sum.inr x => x
  have hfake_spec (s : L5A2C4I.ResidueData.BExceptionalBranches D) :
      L5A2B4AR5A.exceptionalEndpointActualOrFake P.M.base e s =
        Sum.inr (fake s) := by
    simp only [fake]
    split
    next x h => exact (hactual ⟨⟨s, x, h⟩⟩).elim
    next x h => exact h
  have hfake : Function.Injective fake := by
    intro x y hxy
    apply L5A2B4AR5A.exceptionalEndpointActualOrFake_injective P.M.base e
    rw [hfake_spec x, hfake_spec y, hxy]
  letI : Finite (L5A2C4I.ResidueData.BSourceTargetBranches D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.BExceptionalBranches D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.ExactUnusedMergeBases D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.BUsedFirstStageBases D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.BFreshUnusedMergeBases D) := Subtype.finite
  letI : Finite (L5A2C4N.ActualFakeTerminalSeats P.M.base e) :=
    L5A2C4N.actualFakeTerminalSeats_finite P.M.base e
  have hNbE : L5A2C4M.ResidueData.Nb D ≤ L5A2C4N.E P.M.base e := by
    simpa [L5A2C4M.ResidueData.Nb,
      L5A2C4I.ResidueData.bExceptionalCount, L5A2C4N.E] using
      Nat.card_le_card_of_injective fake hfake
  have hres : L5A2C4M.ResidueData.Nb D ≤
      L5A2C4M.ResidueData.UexB D + L5A2C4N.E P.M.base e := by
    omega
  have hbound : L5A2C4M.ResidueData.Cbr D ≤
      L5A2C4M.ResidueData.U D + L5A2C4N.E P.M.base e :=
    (L5A2C4M.ResidueData.residual_inequality_iff D
      (L5A2C4N.E P.M.base e)).1 hres
  have hentryEq := branchB_entry_unpaid_channel R hentry
  change (L5A2C4M.ResidueData.Cbr D : ℤ) =
    L5A2C4M.ResidueData.U D + L5A2C4N.E P.M.base e + 1 at hentryEq
  omega

end NS25Lean.L5A2B4AR5B
