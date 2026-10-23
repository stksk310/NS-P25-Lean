import NS25Lean.P2SectorCActualCMGateBridgeR15
import NS25Lean.P2BranchAEntryClosure

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR16

open L2B L5A1 L5A2C3G L5A2C4A L5A2C4D L5A2C4G L5A2C4H
  L5A2C4OR1 L5A2C4OR3 L5A2C4OR7 L5A2C4OR8 L5A2C4OR15

variable {Gamma : NumericalSemigroup}

/-- Exact C4N residual-domain identity: the exceptional token type has
cardinality `Nb`, not `Cbr`. -/
theorem actual_exceptional_token_card
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Nat.card
        (L5A2C4I.ResidueData.BExceptionalBranches (routingData B e)) =
      L5A2C4M.ResidueData.Nb (routingData B e) := by
  exact L5A2C4M.ResidueData.exceptionalBranches_card (routingData B e)

/-- `Cbr` counts all source-target branches.  Its exact B-side decomposition
is the already-used first-stage seats plus the exceptional residual tokens. -/
theorem actual_cbr_token_decomposition
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    L5A2C4M.ResidueData.UsedB (routingData B e) +
        Nat.card
          (L5A2C4I.ResidueData.BExceptionalBranches (routingData B e)) =
      L5A2C4M.ResidueData.Cbr (routingData B e) := by
  simpa [L5A2C4M.ResidueData.UsedB, L5A2C4M.ResidueData.Cbr,
    L5A2C4I.ResidueData.bUsedFirstStageCount,
    L5A2C4I.ResidueData.bExceptionalCount,
    L5A2C4I.ResidueData.sourceTargetBranchCount] using
      (L5A2C4I.ResidueData.b_firstStage_card_identity (routingData B e))

/-- Every residual exceptional token has the canonical zero-length rooted
history already provided by R7.  That history genuinely source-hits itself;
no endpoint equality between different histories is used. -/
theorem exceptionalBranch_selfSourceHit
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e)) :
    let H := exceptionalBranchRootedHistory B e s
    L5A2C4K.ResidueData.SourceHit (routingData B e) H.raw H.raw := by
  let H := exceptionalBranchRootedHistory B e s
  exact L5A2C4K.ResidueData.sourceHit_of_common_start (routingData B e) rfl

/-- On canonical exceptional rooted histories, literal decorated replay is
exactly equality of the original residual token.  This does not identify
arbitrary histories having the same endpoint. -/
theorem canonicalExceptional_literalReplay_iff
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x y : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e)) :
    L5A2C4L.ResidueData.LiteralDecoratedReplay (routingData B e)
        (exceptionalBranchRootedHistory B e x)
        (exceptionalBranchRootedHistory B e y) ↔
      x = y := by
  constructor
  · intro h
    apply Subtype.ext
    exact h.1
  · rintro rfl
    exact L5A2C4L.ResidueData.literalDecoratedReplay_of_package_eq_word_eq
      (routingData B e) rfl rfl

/-- R15 unit normalization attached to the original C4N residual token and
its canonical rooted source/run history.  The chosen zero-center is derived
from the self source-hit; it is not used as a resource seat. -/
theorem actual_cm_exceptional_decorated_unit_normalization {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD)
    (s : L5A2C4I.ResidueData.BExceptionalBranches
      (routingData P.M.base e)) :
    let H := exceptionalBranchRootedHistory P.M.base e s
    ∃ hit : L5A2C4K.ResidueData.SourceHit
        (routingData P.M.base e) H.raw H.raw,
      ∃ Y d,
        PhysicalZeroCenter P.M.base e Y d ∧
        currentSelector P.M.base e (unitZeroCenter P.M.base e Y d) = 1 ∧
        physicalHeight P.M.base e (unitZeroCenter P.M.base e Y d) = 0 ∧
        unitZeroCenter P.M.base e Y d - (routingM P.M.base e : ℕ) =
          zeroCenterShadow P.M.base e Y d ∧
        RawMinimizers P.M.base e (unitZeroCenter P.M.base e Y d) = {1} := by
  let H := exceptionalBranchRootedHistory P.M.base e s
  let hit : L5A2C4K.ResidueData.SourceHit
      (routingData P.M.base e) H.raw H.raw :=
    exceptionalBranch_selfSourceHit P.M.base e s
  refine ⟨hit, ?_⟩
  exact actual_cm_sourceHit_unit_normalization G boundaryPure boundaryMixed
    e HD hInactive hMixed hNotch H.raw H hit

/-! The frozen injective endpoint classifier gives a disjoint actual/fake
partition.  Only the fake fibre is already a legal C4N resource. -/

def CMActualExceptionalBranches
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) : Type :=
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  {s : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e) //
    ∃ x : ActualSink (routingI B e) (routingA B e) (routingB B e)
        (routingC B e) (routingHB B e) (routingHC B e),
      L5A2B4AR5A.exceptionalEndpointActualOrFake B e s = Sum.inl x}

def CMFakeExceptionalBranches
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) : Type :=
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  {s : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e) //
    ¬ ∃ x : ActualSink (routingI B e) (routingA B e) (routingB B e)
        (routingC B e) (routingHB B e) (routingHC B e),
      L5A2B4AR5A.exceptionalEndpointActualOrFake B e s = Sum.inl x}

/-- Exact partition of residual tokens by the existing source-exact full-sink
classifier. -/
noncomputable def cmExceptionalActualFakeEquiv
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    L5A2C4I.ResidueData.BExceptionalBranches (routingData B e) ≃
      Sum (CMActualExceptionalBranches B e)
        (CMFakeExceptionalBranches B e) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  simpa only [CMActualExceptionalBranches, CMFakeExceptionalBranches] using
    (L5A2C4I.ResidueData.predicatePartitionEquiv
      (fun s : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e) =>
        ∃ x : ActualSink (routingI B e) (routingA B e) (routingB B e)
            (routingC B e) (routingHB B e) (routingHC B e),
          L5A2B4AR5A.exceptionalEndpointActualOrFake B e s = Sum.inl x))

theorem cmFakeExceptionalSeat_exists
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x : CMFakeExceptionalBranches B e) :
    ∃ y : L5A2C4N.ActualFakeTerminalSeats B e,
      L5A2B4AR5A.exceptionalEndpointActualOrFake B e x.val = Sum.inr y := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  cases h : L5A2B4AR5A.exceptionalEndpointActualOrFake B e x.val with
  | inl y => exact (x.property ⟨y, h⟩).elim
  | inr y => exact ⟨y, rfl⟩

noncomputable def cmFakeExceptionalSeat
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    CMFakeExceptionalBranches B e →
      L5A2C4N.ActualFakeTerminalSeats B e :=
  fun x => Classical.choose (cmFakeExceptionalSeat_exists B e x)

theorem cmFakeExceptionalSeat_spec
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x : CMFakeExceptionalBranches B e) :
    L5A2B4AR5A.exceptionalEndpointActualOrFake B e x.val =
      Sum.inr (cmFakeExceptionalSeat B e x) :=
  Classical.choose_spec (cmFakeExceptionalSeat_exists B e x)

theorem cmFakeExceptionalSeat_injective
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Function.Injective (cmFakeExceptionalSeat B e) := by
  intro x y hxy
  apply Subtype.ext
  apply L5A2B4AR5A.exceptionalEndpointActualOrFake_injective B e
  rw [cmFakeExceptionalSeat_spec B e x,
    cmFakeExceptionalSeat_spec B e y, hxy]

noncomputable def cmFakeExceptionalResidualResource
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    CMFakeExceptionalBranches B e →
      L5A2C4N.ActualResidualResourceSeats B e :=
  fun x => Sum.inr (cmFakeExceptionalSeat B e x)

theorem cmFakeExceptionalResidualResource_injective
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Function.Injective (cmFakeExceptionalResidualResource B e) := by
  intro x y hxy
  apply cmFakeExceptionalSeat_injective B e
  exact Sum.inr.inj hxy

/-- Given precisely the still-missing actual-sink-to-fresh injection, the
actual/fake partition assembles the complete residual C4N map. -/
noncomputable def cmExceptionalResourceOfActualFresh
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (f : CMActualExceptionalBranches B e →
      L5A2C4I.ResidueData.BFreshUnusedMergeBases (routingData B e)) :
    L5A2C4I.ResidueData.BExceptionalBranches (routingData B e) →
      L5A2C4N.ActualResidualResourceSeats B e :=
  (Sum.map f (cmFakeExceptionalSeat B e)) ∘
    (cmExceptionalActualFakeEquiv B e)

theorem cmExceptionalResourceOfActualFresh_injective
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (f : CMActualExceptionalBranches B e →
      L5A2C4I.ResidueData.BFreshUnusedMergeBases (routingData B e))
    (hf : Function.Injective f) :
    Function.Injective (cmExceptionalResourceOfActualFresh B e f) := by
  have hfake := cmFakeExceptionalSeat_injective B e
  have hsum : Function.Injective (Sum.map f (cmFakeExceptionalSeat B e)) := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (hf (Sum.inl.inj hxy))
    · simp at hxy
    · simp at hxy
    · exact congrArg Sum.inr (hfake (Sum.inr.inj hxy))
  exact hsum.comp (cmExceptionalActualFakeEquiv B e).injective

theorem actual_cm_injective_discharge_of_actual_fresh
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (f : CMActualExceptionalBranches B e →
      L5A2C4I.ResidueData.BFreshUnusedMergeBases (routingData B e))
    (hf : Function.Injective f) :
    ∃ g : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e) →
        L5A2C4N.ActualResidualResourceSeats B e,
      Function.Injective g := by
  exact ⟨cmExceptionalResourceOfActualFresh B e f,
    cmExceptionalResourceOfActualFresh_injective B e f hf⟩

theorem actual_cm_global_bound_of_actual_fresh
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (f : CMActualExceptionalBranches B e →
      L5A2C4I.ResidueData.BFreshUnusedMergeBases (routingData B e))
    (hf : Function.Injective f) :
    L5A2C4M.ResidueData.Cbr (routingData B e) ≤
      L5A2C4M.ResidueData.U (routingData B e) + L5A2C4N.E B e := by
  exact L5A2C4N.actual_injective_discharge_closes B e
    (cmExceptionalResourceOfActualFresh B e f)
    (cmExceptionalResourceOfActualFresh_injective B e f hf)

end NS25Lean.L5A2C4OR16
