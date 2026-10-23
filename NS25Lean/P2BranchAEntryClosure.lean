import NS25Lean.P2SymmetricTailNormalForm
import NS25Lean.P2SectorBActualRouting
import NS25Lean.P2SectorCLocalCollisionAccounting
import NS25Lean.P2SectorCFakeTerminalResourceBridge

set_option linter.style.header false

noncomputable section
namespace NS25Lean

namespace CombinatorialCore

variable {R : Type*} [Fintype R]

/-- If every branch closes at a merge (rather than at a new source), the
diamond balance improves from `T ≤ 2S` to the sharp inequality `T ≤ S`. -/
theorem ResidueData.sinkCount_le_sourceCount_of_branchTargets_merge
    (D : ResidueData R)
    (hmerge : ∀ r, D.IsBranch r → D.IsMerge (D.branchTarget r)) :
    D.sinkCount ≤ D.sourceCount := by
  classical
  let target : {r // D.IsBranch r} → {s // D.IsMerge s} :=
    fun r => ⟨D.branchTarget r, hmerge r r.property⟩
  have htarget : Function.Injective target := by
    intro r s hrs
    apply Subtype.ext
    apply D.branchTarget_injective
    exact congrArg Subtype.val hrs
  have hbranch : D.branchCount ≤ D.mergeCount := by
    simpa [ResidueData.branchCount, ResidueData.mergeCount,
      Nat.card_eq_fintype_card] using Fintype.card_le_of_injective target htarget
  have hbalance : D.sinkCount + D.mergeCount =
      D.sourceCount + D.branchCount :=
    ResidueData.edge_count_balance D.outgoing_edge_count D.incoming_edge_count
  omega

end CombinatorialCore

namespace L5A2B4AR5A

open ChosenBase FourGeneratedBridge CombinatorialCore L2B L5A1
open L5A2B2 L5A2B4AR3 L5A2B4AR4R1 L5A2B4AR4R2A

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-! ### Generic first-stage exceptional endpoint checkpoint -/

namespace ExceptionalEndpoint

open L5A2C4I

variable {R : Type*} [Fintype R]

private theorem canonicalBEndpoint_injective
    (D : CombinatorialCore.ResidueData R) :
    Function.Injective (L5A2C4I.ResidueData.canonicalBEndpoint D) := by
  let start : L5A2C4I.ResidueData.BSourceTargetBranches D → R := fun s => s.val
  let hzero : ∀ s, D.v (start s) = 0 := fun s => s.property.1.2
  have hseed : ∀ s, 0 < D.v (D.b (start s)) := fun s => by
    have h := (L5A2C4I.ResidueData.sourceTargetBranch_iff_positive_cross D).1
      s.property
    rw [← h.2.1]
    exact h.2.2
  have hi := L5A2C4I.ResidueData.firstBlockEndpoint_injective D.b D.v start
    (fun _ _ h => Subtype.ext h) hzero hseed
  intro x y hxy
  apply hi
  simpa [L5A2C4I.ResidueData.canonicalBEndpoint,
    L5A2C4I.ResidueData.bFirstZeroIndex,
    L5A2C4I.ResidueData.firstBlockEndpoint,
    L5A2C4I.ResidueData.firstBlockIndex, start, hzero] using hxy

/-- An exceptional first-stage endpoint is already a full raw sink.  This is
the exact generic part of the proposed discharge; no Branch-A geometry is
used or hidden in its statement. -/
theorem isSink (D : CombinatorialCore.ResidueData R)
    (s : L5A2C4I.ResidueData.BExceptionalBranches D) :
    D.IsSink (L5A2C4I.ResidueData.canonicalBEndpoint D s.val) := by
  have hrun := L5A2C4I.ResidueData.canonicalBRun_spec D s.val
  have hv : 0 < D.v (L5A2C4I.ResidueData.canonicalBEndpoint D s.val) :=
    hrun.2.choose_spec.2.2.2.1
  have huc : 0 < D.u
      (D.c (L5A2C4I.ResidueData.canonicalBEndpoint D s.val)) :=
    Nat.pos_of_ne_zero s.property
  have hvb : D.v
      (D.b (L5A2C4I.ResidueData.canonicalBEndpoint D s.val)) = 0 :=
    hrun.2.choose_spec.2.2.2.2
  have hdiamond := D.diamond
    (L5A2C4I.ResidueData.canonicalBEndpoint D s.val)
  constructor
  · rw [hvb, Nat.add_zero] at hdiamond
    omega
  · exact Nat.ne_of_gt hv

theorem injective (D : CombinatorialCore.ResidueData R) :
    Function.Injective (fun s : L5A2C4I.ResidueData.BExceptionalBranches D =>
      L5A2C4I.ResidueData.canonicalBEndpoint D s.val) := by
  intro x y hxy
  apply Subtype.ext
  apply canonicalBEndpoint_injective D
  exact hxy

end ExceptionalEndpoint

/-! The actual chosen-base specialization packages that endpoint as the
existing full-sink subtype and then uses the source-exact actual/fake
partition. -/

noncomputable def exceptionalEndpointFullSink
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (L5A2C4H.routingA B e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
    L5A2C4I.ResidueData.BExceptionalBranches (L5A2C4H.routingData B e) →
      L5A2C4H.FullSink (L5A2C4H.routingI B e)
        (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
        (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
        (L5A2C4H.routingHC B e) := by
  letI : NeZero (L5A2C4H.routingA B e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
  intro s
  exact ⟨L5A2C4I.ResidueData.canonicalBEndpoint
      (L5A2C4H.routingData B e) s.val,
    ExceptionalEndpoint.isSink (L5A2C4H.routingData B e) s⟩

theorem exceptionalEndpointFullSink_injective
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (L5A2C4H.routingA B e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
    Function.Injective (exceptionalEndpointFullSink B e) := by
  letI : NeZero (L5A2C4H.routingA B e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
  intro x y hxy
  apply ExceptionalEndpoint.injective (L5A2C4H.routingData B e)
  exact congrArg Subtype.val hxy

noncomputable def exceptionalEndpointActualOrFake
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (L5A2C4H.routingA B e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
    L5A2C4I.ResidueData.BExceptionalBranches (L5A2C4H.routingData B e) →
      Sum
        (L5A2C4H.ActualSink (L5A2C4H.routingI B e)
          (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
          (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
          (L5A2C4H.routingHC B e))
        (L5A2C4N.ActualFakeTerminalSeats B e) := by
  letI : NeZero (L5A2C4H.routingA B e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
  exact (L5A2C4N.fullSinkEquivActualSumFake_sourceExact
    (L5A2C4H.routingI B e) (L5A2C4H.routingA B e)
    (L5A2C4H.routingB B e) (L5A2C4H.routingC B e)
    (L5A2C4H.routingHB B e) (L5A2C4H.routingHC B e)) ∘
      exceptionalEndpointFullSink B e

theorem exceptionalEndpointActualOrFake_injective
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (L5A2C4H.routingA B e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
    Function.Injective (exceptionalEndpointActualOrFake B e) := by
  letI : NeZero (L5A2C4H.routingA B e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
  exact (L5A2C4N.fullSinkEquivActualSumFake_sourceExact
    (L5A2C4H.routingI B e) (L5A2C4H.routingA B e)
    (L5A2C4H.routingB B e) (L5A2C4H.routingC B e)
    (L5A2C4H.routingHB B e) (L5A2C4H.routingHC B e)).injective.comp
      (exceptionalEndpointFullSink_injective B e)

/-! ### R7 phase 0: the two actual classifier fibres -/

/-- Exceptional Branch-A source-target branches whose frozen endpoint
classifier lands in the actual-sink summand.  The subtype contains only the
classifier equation; in particular it contains no merge witness. -/
def BranchAActualExceptionalBranches (P : P2Data Gamma)
    (A : SectorBCriticalRoleBranchA P) : Type :=
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  {s : L5A2C4I.ResidueData.BExceptionalBranches
      (L5A2C4H.routingData P.M.base A.reindex) //
    ∃ x : L5A2C4H.ActualSink
        (L5A2C4H.routingI P.M.base A.reindex)
        (L5A2C4H.routingA P.M.base A.reindex)
        (L5A2C4H.routingB P.M.base A.reindex)
        (L5A2C4H.routingC P.M.base A.reindex)
        (L5A2C4H.routingHB P.M.base A.reindex)
        (L5A2C4H.routingHC P.M.base A.reindex),
      exceptionalEndpointActualOrFake P.M.base A.reindex s = Sum.inl x}

/-- The complementary classifier fibre, landing in the already constructed
actual fake-terminal-seat summand. -/
def BranchAFakeExceptionalBranches (P : P2Data Gamma)
    (A : SectorBCriticalRoleBranchA P) : Type :=
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  {s : L5A2C4I.ResidueData.BExceptionalBranches
      (L5A2C4H.routingData P.M.base A.reindex) //
    ∃ x : L5A2C4N.ActualFakeTerminalSeats P.M.base A.reindex,
      exceptionalEndpointActualOrFake P.M.base A.reindex s = Sum.inr x}

noncomputable def branchAActualExceptionalSink
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    BranchAActualExceptionalBranches P A →
      L5A2C4H.ActualSink
        (L5A2C4H.routingI P.M.base A.reindex)
        (L5A2C4H.routingA P.M.base A.reindex)
        (L5A2C4H.routingB P.M.base A.reindex)
        (L5A2C4H.routingC P.M.base A.reindex)
        (L5A2C4H.routingHB P.M.base A.reindex)
        (L5A2C4H.routingHC P.M.base A.reindex) := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  intro x
  exact Classical.choose x.property

theorem branchAActualExceptionalSink_spec
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P)
    (x : BranchAActualExceptionalBranches P A) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    exceptionalEndpointActualOrFake P.M.base A.reindex x.val =
      Sum.inl (branchAActualExceptionalSink P A x) := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  exact Classical.choose_spec x.property

theorem branchAActualExceptionalSink_injective
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    Function.Injective (branchAActualExceptionalSink P A) := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  intro x y hxy
  apply Subtype.ext
  apply exceptionalEndpointActualOrFake_injective P.M.base A.reindex
  rw [branchAActualExceptionalSink_spec P A x,
    branchAActualExceptionalSink_spec P A y, hxy]

noncomputable def branchAFakeExceptionalSeat
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    BranchAFakeExceptionalBranches P A →
      L5A2C4N.ActualFakeTerminalSeats P.M.base A.reindex := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  intro x
  exact Classical.choose x.property

theorem branchAFakeExceptionalSeat_spec
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P)
    (x : BranchAFakeExceptionalBranches P A) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    exceptionalEndpointActualOrFake P.M.base A.reindex x.val =
      Sum.inr (branchAFakeExceptionalSeat P A x) := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  exact Classical.choose_spec x.property

theorem branchAFakeExceptionalSeat_injective
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    Function.Injective (branchAFakeExceptionalSeat P A) := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  intro x y hxy
  apply Subtype.ext
  apply exceptionalEndpointActualOrFake_injective P.M.base A.reindex
  rw [branchAFakeExceptionalSeat_spec P A x,
    branchAFakeExceptionalSeat_spec P A y, hxy]

noncomputable def branchAFakeExceptionalResidualResource
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    BranchAFakeExceptionalBranches P A →
      L5A2C4N.ActualResidualResourceSeats P.M.base A.reindex := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  exact fun x => Sum.inr (branchAFakeExceptionalSeat P A x)

theorem branchAFakeExceptionalResidualResource_injective
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    Function.Injective (branchAFakeExceptionalResidualResource P A) := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  intro x y hxy
  apply branchAFakeExceptionalSeat_injective P A
  exact Sum.inr.inj hxy

private theorem branchA_canonicalCEndpoint_injective
    {R : Type*} [Fintype R] (D : CombinatorialCore.ResidueData R) :
    Function.Injective (L5A2C4I.ResidueData.canonicalCEndpoint D) := by
  let start : L5A2C4I.ResidueData.CSourceTargetBranches D → R := fun s => s.val
  let hzero : ∀ s, D.u (start s) = 0 := fun s => s.property.1.1
  have hseed : ∀ s, 0 < D.u (D.c (start s)) := fun s =>
    (L5A2C4I.ResidueData.sourceTargetBranch_iff_positive_cross D).1
      s.property |>.2.2
  have hi := L5A2C4I.ResidueData.firstBlockEndpoint_injective D.c D.u start
    (fun _ _ h => Subtype.ext h) hzero hseed
  intro x y hxy
  apply hi
  simpa [L5A2C4I.ResidueData.canonicalCEndpoint,
    L5A2C4I.ResidueData.cFirstZeroIndex,
    L5A2C4I.ResidueData.firstBlockEndpoint,
    L5A2C4I.ResidueData.firstBlockIndex, start, hzero] using hxy

/-- The source-exact opposite endpoint proposed by the symmetric-rectangle
route.  This is a residue, not an asserted merge witness. -/
noncomputable def branchAActualExceptionalCandidateBase
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    BranchAActualExceptionalBranches P A →
      ZMod (L5A2C4H.routingA P.M.base A.reindex) := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  intro x
  exact L5A2C4I.ResidueData.canonicalCEndpoint
    (L5A2C4H.routingData P.M.base A.reindex)
    ⟨x.val.val.val, x.val.val.property⟩

theorem branchAActualExceptionalCandidateBase_injective
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    Function.Injective (branchAActualExceptionalCandidateBase P A) := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg Subtype.val
    (branchA_canonicalCEndpoint_injective
      (L5A2C4H.routingData P.M.base A.reindex) hxy)

/-- Once the single opposite-corner zero is established, the existing
first-stage theorem supplies all four literal exact-unused-merge equations. -/
theorem branchAActualExceptionalCandidate_exact
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P)
    (x : BranchAActualExceptionalBranches P A)
    (hopposite :
      letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
        ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
      let D := L5A2C4H.routingData P.M.base A.reindex
      L5A2C4I.ResidueData.CFirstStageNonexceptional D
        ⟨x.val.val.val, x.val.val.property⟩) :
    letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase
      (L5A2C4H.routingData P.M.base A.reindex)
      (branchAActualExceptionalCandidateBase P A x) := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  exact L5A2C4I.ResidueData.nonexceptional_c_endpoint_exact_unusedMerge
    (L5A2C4H.routingData P.M.base A.reindex)
    ⟨x.val.val.val, x.val.val.property⟩ hopposite

/-- Exact cardinal checkpoint: first-stage exceptional branches inject into
the disjoint actual/fake terminal partition.  The remaining R6 work is
precisely to replace the actual summand by fresh unused merges. -/
theorem exceptionalEndpoint_card_le_actual_add_fake
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (L5A2C4H.routingA B e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
    Nat.card
        (L5A2C4I.ResidueData.BExceptionalBranches
          (L5A2C4H.routingData B e)) ≤
      L5A2C4H.actualSinkCount (L5A2C4H.routingI B e)
          (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
          (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
          (L5A2C4H.routingHC B e) +
        L5A2C4H.fakeSinkCount (L5A2C4H.routingI B e)
          (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
          (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
          (L5A2C4H.routingHC B e) := by
  letI : NeZero (L5A2C4H.routingA B e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
  letI : Finite
      (L5A2C4I.ResidueData.BSourceTargetBranches
        (L5A2C4H.routingData B e)) := Subtype.finite
  letI : Finite
      (L5A2C4I.ResidueData.BExceptionalBranches
        (L5A2C4H.routingData B e)) := Subtype.finite
  letI : Finite
      (L5A2C4H.ActualSink (L5A2C4H.routingI B e)
        (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
        (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
        (L5A2C4H.routingHC B e)) := Subtype.finite
  letI : Finite (L5A2C4N.ActualFakeTerminalSeats B e) :=
    L5A2C4N.actualFakeTerminalSeats_finite B e
  have h := Nat.card_le_card_of_injective
    (exceptionalEndpointActualOrFake B e)
    (exceptionalEndpointActualOrFake_injective B e)
  rw [Nat.card_sum] at h
  exact h

private abbrev routingN0 (P : P2Data Gamma) : ℕ :=
  (P.M.base.tailDegrees 0).val

private abbrev routingN1 (P : P2Data Gamma) : ℕ :=
  (P.M.base.tailDegrees 1).val

private abbrev routingN2 (P : P2Data Gamma) : ℕ :=
  (P.M.base.tailDegrees 2).val

private abbrev routingA (P : P2Data Gamma) : ℕ :=
  routingN0 P / tailGcd (routingN0 P) (routingN1 P) (routingN2 P)

private abbrev routingB (P : P2Data Gamma) : ℕ :=
  routingN1 P / tailGcd (routingN0 P) (routingN1 P) (routingN2 P)

private abbrev routingC (P : P2Data Gamma) : ℕ :=
  routingN2 P / tailGcd (routingN0 P) (routingN1 P) (routingN2 P)

private abbrev routingH (P : P2Data Gamma) : NumericalSemigroup :=
  normalizedSemigroup (routingN0 P) (routingN1 P) (routingN2 P)
    (chosenBase_minimalFour P.M.base).n₁_pos

private abbrev routingI (P : P2Data Gamma) : RelativeIdeal (routingH P) :=
  normalizedTailIdeal Gamma P.M.base.q.val
    (routingN0 P) (routingN1 P) (routingN2 P)
    (chosenBase_minimalFour P.M.base)

private theorem routingA_pos (P : P2Data Gamma) : 0 < routingA P :=
  quotient_pos_of_dvd (chosenBase_minimalFour P.M.base).n₁_pos
    (tailGcd_dvd (routingN0 P) (routingN1 P) (routingN2 P)).1

private theorem routing_minimal (P : P2Data Gamma) :
    (routingH P).IsMinimallyGeneratedByThree
      (routingA P) (routingB P) (routingC P) :=
  normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base)

private theorem routingB_mem (P : P2Data Gamma) : routingB P ∈ routingH P :=
  (NumericalSemigroup.mem_generatedByThree_iff (routing_minimal P).1).2
    (AddSubmonoid.subset_closure (by simp))

private theorem routingC_mem (P : P2Data Gamma) : routingC P ∈ routingH P :=
  (NumericalSemigroup.mem_generatedByThree_iff (routing_minimal P).1).2
    (AddSubmonoid.subset_closure (by simp))

/-- The canonical normalized Apéry routing attached to the original chosen
pivot.  In particular, this definition does not introduce a new pivot whose
source count would need comparison with `P.sourceCount`. -/
noncomputable def normalizedRoutingData (P : P2Data Gamma) :
    ResidueData (ZMod (routingA P)) := by
  letI : NeZero (routingA P) := ⟨Nat.ne_of_gt (routingA_pos P)⟩
  exact ((routingI P).toAperyStepData (routingA P) (routingB P) (routingC P)
    (routingB_mem P) (routingC_mem P)).toResidueData
      ((routingI P).toAperyStepData_isValid (routingA P) (routingB P) (routingC P)
        (routingB_mem P) (routingC_mem P))

/-- The structural sufficient condition selected by the routing route: every
branch in the original-pivot normalized routing closes at a merge.  No claim
is made here that the frozen Branch-A tail package already implies it. -/
def NormalizedRoutingMergeClosed (P : P2Data Gamma) : Prop :=
  ∀ x, (normalizedRoutingData P).IsBranch x →
    (normalizedRoutingData P).IsMerge ((normalizedRoutingData P).branchTarget x)

private theorem normalizedRoutingData_sourceCount (P : P2Data Gamma) :
    (normalizedRoutingData P).sourceCount = P.sourceCount := by
  letI : NeZero (routingA P) := ⟨Nat.ne_of_gt (routingA_pos P)⟩
  have hb : routingB P ≠ 0 := by
    intro hz
    apply (routing_minimal P).2.2.1
    rw [hz]
    exact AddSubmonoid.zero_mem _
  have hc : routingC P ≠ 0 := by
    intro hz
    apply (routing_minimal P).2.2.2
    rw [hz]
    exact AddSubmonoid.zero_mem _
  calc
    (normalizedRoutingData P).sourceCount = (routingI P).generatorCount := by
      exact (routingI P).concrete_sourceCount_eq_generatorCount
        (routingA P) (routingB P) (routingC P) (routing_minimal P).1
        (routingB_mem P) (routingC_mem P) hb hc
    _ = tailGeneratorCount
        (generatedThree (routingN0 P) (routingN1 P) (routingN2 P))
        (aperyTail Gamma.toAddSubmonoid
          (generatedThree (routingN0 P) (routingN1 P) (routingN2 P))
          P.M.base.q.val) :=
      normalizedTail_generatorCount Gamma P.M.base.q.val
        (routingN0 P) (routingN1 P) (routingN2 P)
        (chosenBase_minimalFour P.M.base)
    _ = P.sourceCount := by
      rw [P2Data.sourceCount, L2B.sourceCount, Data.K,
        chosenBase_tail_eq_generatedThree P.M.base]

private theorem type_le_normalizedRoutingData_sinkCount (P : P2Data Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ (normalizedRoutingData P).sinkCount := by
  letI : NeZero (routingA P) := ⟨Nat.ne_of_gt (routingA_pos P)⟩
  have haH : routingA P ∈ routingH P :=
    (NumericalSemigroup.mem_generatedByThree_iff (routing_minimal P).1).2
      (AddSubmonoid.subset_closure (by simp))
  have hb : routingB P ≠ 0 := by
    intro hz
    apply (routing_minimal P).2.2.1
    rw [hz]
    exact AddSubmonoid.zero_mem _
  have hc : routingC P ≠ 0 := by
    intro hz
    apply (routing_minimal P).2.2.2
    rw [hz]
    exact AddSubmonoid.zero_mem _
  have hsink : (normalizedRoutingData P).sinkCount = (routingI P).idealType := by
    change (((routingI P).toAperyStepData
      (routingA P) (routingB P) (routingC P) (routingB_mem P) (routingC_mem P)).toResidueData
        ((routingI P).toAperyStepData_isValid
          (routingA P) (routingB P) (routingC P)
          (routingB_mem P) (routingC_mem P))).sinkCount = (routingI P).idealType
    exact (routingI P).concrete_sinkCount_eq_idealType
      (routingA P) (routingB P) (routingC P) (routing_minimal P).1
      haH (routingB_mem P) (routingC_mem P) hb hc
  rw [hsink]
  exact (fourGenerated_normalization_chain Gamma P.M.base.q.val
    (routingN0 P) (routingN1 P) (routingN2 P)
    (chosenBase_minimalFour P.M.base)).1

/-- Strongest closed routing checkpoint currently obtained.  It reduces the
requested original-pivot inequality to `NormalizedRoutingMergeClosed`; no
ENTRY exclusion and no cross-pivot source-count identification is assumed. -/
theorem type_le_sourceCount_of_normalized_branchTargets_merge
    (P : P2Data Gamma) (hmerge : NormalizedRoutingMergeClosed P) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  letI : NeZero (routingA P) := ⟨Nat.ne_of_gt (routingA_pos P)⟩
  calc
    Gamma.asRelativeIdeal.idealType ≤ (normalizedRoutingData P).sinkCount :=
      type_le_normalizedRoutingData_sinkCount P
    _ ≤ (normalizedRoutingData P).sourceCount :=
      (normalizedRoutingData P).sinkCount_le_sourceCount_of_branchTargets_merge hmerge
    _ = P.sourceCount := normalizedRoutingData_sourceCount P

private theorem branchA_mixed_support (A : SectorBCriticalRoleBranchA P) :
    componentSupport P.M.base A.mixedDegree A.mixed.mixedComponent =
      {A.reindex 0, A.reindex 1} := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨i, rfl⟩ := A.reindex.surjective j
    fin_cases i
    · simp
    · simp
    · change A.reindex 2 ∈
        componentSupport P.M.base A.mixedDegree A.mixed.mixedComponent at hj
      change A.reindex 2 ∈ {A.reindex 0, A.reindex 1}
      rw [A.reindex_two, A.mixed.mixedSupport] at hj
      simp [A.mixed.pure_ne_left, A.mixed.pure_ne_right] at hj
  · rw [A.mixed.mixedSupport]
    simp [A.mixed.other_ne, A.reindex.injective.eq_iff]

/-- Actual Sector-B zero-killed data excludes all five inward boundary
predecessors at the two Branch-A critical fibers.  This is the source-exact
ideal-membership input that a symmetric-rectangle discharge must consume. -/
theorem branchA_critical_boundary_exclusions
    (P : P2Data Gamma) (hB : SectorB P.M)
    (A : SectorBCriticalRoleBranchA P) :
    A.pairDegree - weights P.M.base (A.reindex 0) ∉ P.M.base.K ∧
      A.pairDegree - weights P.M.base (A.reindex 1) ∉ P.M.base.K ∧
      A.mixedDegree - weights P.M.base (A.reindex 0) ∉ P.M.base.K ∧
      A.mixedDegree - weights P.M.base (A.reindex 1) ∉ P.M.base.K ∧
      A.mixedDegree - weights P.M.base (A.reindex 2) ∉ P.M.base.K := by
  classical
  obtain ⟨h, g, _hne, hdegrees, _hhcount, _hgcount, _hhzero, _hgzero,
    hhgenuine, hggenuine⟩ := L5A2B3.sectorB_actualFiberData P hB
  have hgenuine (d : ℕ) (hd : d ∈ positiveDegrees P.M)
      (C : FiberComponent P.M.base d) : ¬BoundaryKilled P.M d C := by
    rw [hdegrees] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact hhgenuine C
    · exact hggenuine C
  have hpair_mem : A.pairDegree ∈ positiveDegrees P.M := by
    rw [A.positiveDegrees_eq]
    simp
  have hmixed_mem : A.mixedDegree ∈ positiveDegrees P.M := by
    rw [A.positiveDegrees_eq]
    simp
  have hleft_pos : 0 < A.pair.leftWitness.val A.pair.leftRole := by
    by_contra hn
    have hz : A.pair.leftWitness.val A.pair.leftRole = 0 :=
      Nat.eq_zero_of_not_pos hn
    have hval : A.pair.leftWitness.val = 0 := by
      rw [A.pair.leftWitness_pure, hz]
      simp
    have hdegree := A.pair.leftWitness.property
    rw [hval, map_zero] at hdegree
    exact (Nat.ne_of_gt A.pair.degree_pos) hdegree.symm
  have hright_pos : 0 < A.pair.rightWitness.val A.pair.rightRole := by
    by_contra hn
    have hz : A.pair.rightWitness.val A.pair.rightRole = 0 :=
      Nat.eq_zero_of_not_pos hn
    have hval : A.pair.rightWitness.val = 0 := by
      rw [A.pair.rightWitness_pure, hz]
      simp
    have hdegree := A.pair.rightWitness.property
    rw [hval, map_zero] at hdegree
    exact (Nat.ne_of_gt A.pair.degree_pos) hdegree.symm
  have hmixed0_pos : 0 < A.mixed.witness.val (A.reindex 0) := by
    apply A.mixed.witness_pos_of_mem_mixedSupport
    rw [branchA_mixed_support A]
    simp
  have hmixed1_pos : 0 < A.mixed.witness.val (A.reindex 1) := by
    apply A.mixed.witness_pos_of_mem_mixedSupport
    rw [branchA_mixed_support A]
    simp
  obtain ⟨pureWitness, hpureComponent, hpurePos⟩ :=
    (mem_componentSupport P.M.base A.mixedDegree A.mixed.pureComponent
      (A.reindex 2)).mp (by rw [A.reindex_two, A.mixed.pureSupport]; simp)
  constructor
  · intro hmem
    apply hgenuine A.pairDegree hpair_mem A.pair.leftComponent
    refine ⟨A.pair.leftWitness, A.pair.leftWitness_component,
      A.reindex 0, ?_, hmem⟩
    simpa [A.reindex_zero] using hleft_pos
  constructor
  · intro hmem
    apply hgenuine A.pairDegree hpair_mem A.pair.rightComponent
    refine ⟨A.pair.rightWitness, A.pair.rightWitness_component,
      A.reindex 1, ?_, hmem⟩
    simpa [A.reindex_one] using hright_pos
  constructor
  · intro hmem
    apply hgenuine A.mixedDegree hmixed_mem A.mixed.mixedComponent
    exact ⟨A.mixed.witness, A.mixed.witness_component,
      A.reindex 0, hmixed0_pos, hmem⟩
  constructor
  · intro hmem
    apply hgenuine A.mixedDegree hmixed_mem A.mixed.mixedComponent
    exact ⟨A.mixed.witness, A.mixed.witness_component,
      A.reindex 1, hmixed1_pos, hmem⟩
  · intro hmem
    apply hgenuine A.mixedDegree hmixed_mem A.mixed.pureComponent
    exact ⟨pureWitness, hpureComponent, A.reindex 2, hpurePos, hmem⟩

/-- The five critical exclusions expressed as lower bounds on the actual
eta-height function at the five corresponding rectangle boundary points. -/
theorem branchA_critical_eta_bounds
    (P : P2Data Gamma) (hB : SectorB P.M)
    (A : SectorBCriticalRoleBranchA P) :
    let S := L5A2B4AR4R2A.branchA_symmetricTailData A
    beta A ≤ L5A2C4C.eta P.M.base A.reindex 0 0 ∧
      1 ≤ L5A2C4C.eta P.M.base A.reindex (alpha A - 1) 0 ∧
      r A ≤ L5A2C4C.eta P.M.base A.reindex (s A) 0 ∧
      r A < L5A2C4C.eta P.M.base A.reindex (s A - 1) 0 ∧
      1 ≤ L5A2C4C.eta P.M.base A.reindex 0 (d A - 1) := by
  let S := L5A2B4AR4R2A.branchA_symmetricTailData A
  have hex := branchA_critical_boundary_exclusions P hB A
  have hpair0 : A.pairDegree =
      beta A * weights P.M.base (A.reindex 0) := by
    calc
      A.pairDegree = c0 A * weights P.M.base (A.reindex 0) := by
        change A.pairDegree = criticalExponent P.M.base (A.reindex 0) *
          weights P.M.base (A.reindex 0)
        simpa only [A.reindex_zero] using A.pair.left_degree_eq_critical
      _ = beta A * weights P.M.base (A.reindex 0) := by rw [S.c0_eq_beta]
  have hpair1 : A.pairDegree =
      alpha A * weights P.M.base (A.reindex 1) := by
    calc
      A.pairDegree = c1 A * weights P.M.base (A.reindex 1) := by
        change A.pairDegree = criticalExponent P.M.base (A.reindex 1) *
          weights P.M.base (A.reindex 1)
        simpa only [A.reindex_one] using A.pair.right_degree_eq_critical
      _ = alpha A * weights P.M.base (A.reindex 1) := by rw [S.c1_eq_alpha]
  have hmixed2 : A.mixedDegree =
      d A * weights P.M.base (A.reindex 2) := by
    calc
      A.mixedDegree = c2 A * weights P.M.base (A.reindex 2) := by
        change A.mixedDegree = criticalExponent P.M.base (A.reindex 2) *
          weights P.M.base (A.reindex 2)
        simpa only [A.reindex_two] using A.mixed.degree_eq_critical
      _ = d A * weights P.M.base (A.reindex 2) := by rw [S.c2_eq_d]
  have hmixed01 : A.mixedDegree =
      r A * weights P.M.base (A.reindex 0) +
        s A * weights P.M.base (A.reindex 1) := by
    let D := tailGcd (P.M.base.tailDegrees 0).val
      (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val
    rw [hmixed2]
    calc
      d A * weights P.M.base (A.reindex 2) = D * (d A * n2 A) := by
        rw [← normalizedWeight_scale P.M.base (A.reindex 2)]
        ring
      _ = D * (r A * n0 A + s A * n1 A) := by rw [S.mixed_relation]
      _ = r A * weights P.M.base (A.reindex 0) +
          s A * weights P.M.base (A.reindex 1) := by
        rw [← normalizedWeight_scale P.M.base (A.reindex 0),
          ← normalizedWeight_scale P.M.base (A.reindex 1)]
        ring
  have h0 : L5A2C4C.gridDegree P.M.base A.reindex (beta A - 1) 0 0 ∉
      P.M.base.K := by
    intro hm
    apply hex.1
    rw [hpair0]
    simpa [L5A2C4C.gridDegree, Nat.sub_mul] using hm
  have h1 : L5A2C4C.gridDegree P.M.base A.reindex 0 (alpha A - 1) 0 ∉
      P.M.base.K := by
    intro hm
    apply hex.2.1
    rw [hpair1]
    simpa [L5A2C4C.gridDegree, Nat.sub_mul] using hm
  have h2 : L5A2C4C.gridDegree P.M.base A.reindex (r A - 1) (s A) 0 ∉
      P.M.base.K := by
    intro hm
    apply hex.2.2.1
    rw [hmixed01]
    have hle : weights P.M.base (A.reindex 0) ≤
        r A * weights P.M.base (A.reindex 0) := by
      nlinarith [S.r_pos]
    rw [Nat.sub_add_comm hle]
    simpa [L5A2C4C.gridDegree, Nat.sub_mul] using hm
  have h3 : L5A2C4C.gridDegree P.M.base A.reindex (r A) (s A - 1) 0 ∉
      P.M.base.K := by
    intro hm
    apply hex.2.2.2.1
    rw [hmixed01]
    have hle : weights P.M.base (A.reindex 1) ≤
        s A * weights P.M.base (A.reindex 1) := by
      nlinarith [S.s_pos]
    rw [Nat.add_sub_assoc hle]
    simpa [L5A2C4C.gridDegree, Nat.sub_mul] using hm
  have h4 : L5A2C4C.gridDegree P.M.base A.reindex 0 0 (d A - 1) ∉
      P.M.base.K := by
    intro hm
    apply hex.2.2.2.2
    rw [hmixed2]
    simpa [L5A2C4C.gridDegree, Nat.sub_mul] using hm
  have hn0 : ¬ L5A2C4C.eta P.M.base A.reindex 0 0 ≤ beta A - 1 := by
    intro h
    exact h0 ((L5A2C4C.gridDegree_mem_K_iff_eta_le P.M.base A.reindex 0 0
      (beta A - 1)).2 h)
  have hn1 : ¬ L5A2C4C.eta P.M.base A.reindex (alpha A - 1) 0 ≤ 0 := by
    intro h
    exact h1 ((L5A2C4C.gridDegree_mem_K_iff_eta_le P.M.base A.reindex
      (alpha A - 1) 0 0).2 h)
  have hn2 : ¬ L5A2C4C.eta P.M.base A.reindex (s A) 0 ≤ r A - 1 := by
    intro h
    exact h2 ((L5A2C4C.gridDegree_mem_K_iff_eta_le P.M.base A.reindex
      (s A) 0 (r A - 1)).2 h)
  have hn3 : ¬ L5A2C4C.eta P.M.base A.reindex (s A - 1) 0 ≤ r A := by
    intro h
    exact h3 ((L5A2C4C.gridDegree_mem_K_iff_eta_le P.M.base A.reindex
      (s A - 1) 0 (r A)).2 h)
  have hn4 : ¬ L5A2C4C.eta P.M.base A.reindex 0 (d A - 1) ≤ 0 := by
    intro h
    exact h4 ((L5A2C4C.gridDegree_mem_K_iff_eta_le P.M.base A.reindex
      0 (d A - 1) 0).2 h)
  omega

/-! ### Exact weak accounting route on the coherent Branch-A reindexing -/

/-- The precise weak routing condition needed after full sinks are split into
actual and fake sinks.  Unlike all-merge, this permits branches whose opposite
corner is a source, provided that they are paid for by genuinely unused merges
or fake sinks. -/
def BranchAResourceBound (P : P2Data Gamma)
    (A : SectorBCriticalRoleBranchA P) : Prop := by
  letI : NeZero (L5A2C4H.routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base A.reindex)⟩
  let D := L5A2C4H.routingData P.M.base A.reindex
  exact L5A2C4I.ResidueData.sourceTargetBranchCount D ≤
    L5A2C4J.ResidueData.exactUnusedMergeCount D +
      L5A2C4H.fakeSinkCount
        (L5A2C4H.routingI P.M.base A.reindex)
        (L5A2C4H.routingA P.M.base A.reindex)
        (L5A2C4H.routingB P.M.base A.reindex)
        (L5A2C4H.routingC P.M.base A.reindex)
        (L5A2C4H.routingHB P.M.base A.reindex)
        (L5A2C4H.routingHC P.M.base A.reindex)

theorem actualSinkCount_le_sourceCount_of_resourceBound
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hresource :
      letI : NeZero (L5A2C4H.routingA B e) :=
        ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
      let D := L5A2C4H.routingData B e
      L5A2C4I.ResidueData.sourceTargetBranchCount D ≤
        L5A2C4J.ResidueData.exactUnusedMergeCount D +
          L5A2C4H.fakeSinkCount (L5A2C4H.routingI B e)
            (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
            (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
            (L5A2C4H.routingHC B e)) :
    letI : NeZero (L5A2C4H.routingA B e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
    L5A2C4H.actualSinkCount (L5A2C4H.routingI B e)
      (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
      (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
      (L5A2C4H.routingHC B e) ≤
        (L5A2C4H.routingData B e).sourceCount := by
  letI : NeZero (L5A2C4H.routingA B e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
  let D := L5A2C4H.routingData B e
  let T := L5A2C4H.actualSinkCount (L5A2C4H.routingI B e)
    (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
    (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
    (L5A2C4H.routingHC B e)
  let E := L5A2C4H.fakeSinkCount (L5A2C4H.routingI B e)
    (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
    (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
    (L5A2C4H.routingHC B e)
  let Z := L5A2C4J.ResidueData.pairedZeroDiamondCount D
  let C := L5A2C4I.ResidueData.sourceTargetBranchCount D
  let U := L5A2C4J.ResidueData.exactUnusedMergeCount D
  have hsinks : D.sinkCount = T + E := by
    exact L5A2C4H.fullSinkCount_eq_actual_add_fake
      (L5A2C4H.routingI B e) (L5A2C4H.routingA B e)
      (L5A2C4H.routingB B e) (L5A2C4H.routingC B e)
      (L5A2C4H.routingHB B e) (L5A2C4H.routingHC B e)
  have hbranches : D.branchCount = Z + C :=
    L5A2C4J.ResidueData.branchCount_raw_decomposition D
  have hmerges : D.mergeCount = Z + U :=
    L5A2C4J.ResidueData.mergeCount_raw_decomposition D
  have hbalance : D.sinkCount + D.mergeCount =
      D.sourceCount + D.branchCount :=
    CombinatorialCore.ResidueData.edge_count_balance
      D.outgoing_edge_count D.incoming_edge_count
  change C ≤ U + E at hresource
  change T ≤ D.sourceCount
  omega

/-- Source-exact closure from the weakest raw-routing resource inequality.
The coherent reindexing permutes only the three tail generators; the chosen
pivot is unchanged, and the source count is proved equal to the original
`P.sourceCount` by the frozen actual-routing core. -/
theorem type_le_sourceCount_of_branchA_resourceBound
    (P : P2Data Gamma) (_hB : SectorB P.M)
    (A : SectorBCriticalRoleBranchA P) (hresource : BranchAResourceBound P A) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  let e := A.reindex
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  have hactual := L5A2C4H.exists_actualRouting_with_exact_actualSinkCount P e
  have hcore := L5A2C4H.exists_actualRoutingCore P e
  rcases hactual with ⟨_ha, hactual, _hfull⟩
  rcases hcore with ⟨_ha', hsource, _hsink, _hout, _hin⟩
  have hle := actualSinkCount_le_sourceCount_of_resourceBound
    P.M.base e hresource
  rw [hactual, hsource] at hle
  exact hle

end L5A2B4AR5A
end NS25Lean
