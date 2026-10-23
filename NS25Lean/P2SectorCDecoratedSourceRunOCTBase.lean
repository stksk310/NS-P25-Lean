import NS25Lean.P2SectorCHistoryCollisionCore

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4L

open CombinatorialCore
open L5A2C4H
open L5A2C4I
open L5A2C4K

namespace ResidueData

variable {R : Type*} [Fintype R] (D : CombinatorialCore.ResidueData R)

/-! ### L1: the intrinsic B-side source/run package -/

/-- At this layer the semantic package is exactly the intrinsic source branch.
The endpoint and run certificate are derived functions, not supplied fields. -/
abbrev BSourceRunPackage := L5A2C4I.ResidueData.BSourceTargetBranches D

def bSourceRunEndpoint (P : BSourceRunPackage D) : R :=
  L5A2C4I.ResidueData.canonicalBEndpoint D P

theorem bSourceRun_canonical (P : BSourceRunPackage D) :
    L5A2C4I.ResidueData.CanonicalBRun D P.val (bSourceRunEndpoint D P) := by
  exact L5A2C4I.ResidueData.canonicalBRun_spec D P

/-! ### L2: the unique source paired with a used first-stage B merge -/

noncomputable def bPairedSource
    (β : L5A2C4I.ResidueData.BUsedFirstStageBases D) :
    L5A2C4I.ResidueData.BNonexceptionalBranches D :=
  Classical.choose β.property

theorem bPairedSource_roundTrip
    (β : L5A2C4I.ResidueData.BUsedFirstStageBases D) :
    L5A2C4I.ResidueData.bFirstStagePairing D (bPairedSource D β) = β.val :=
  Classical.choose_spec β.property

theorem bPairedSource_unique
    (β : L5A2C4I.ResidueData.BUsedFirstStageBases D)
    (s : L5A2C4I.ResidueData.BNonexceptionalBranches D)
    (hs : L5A2C4I.ResidueData.bFirstStagePairing D s = β.val) :
    s = bPairedSource D β := by
  apply L5A2C4I.ResidueData.bFirstStagePairing_injective D
  exact hs.trans (bPairedSource_roundTrip D β).symm

noncomputable def bUsedFirstStageEquiv :
    L5A2C4I.ResidueData.BUsedFirstStageBases D ≃
      L5A2C4I.ResidueData.BNonexceptionalBranches D where
  toFun := bPairedSource D
  invFun := fun s =>
    ⟨L5A2C4I.ResidueData.bFirstStagePairing D s, ⟨s, rfl⟩⟩
  left_inv := by
    intro β
    apply Subtype.ext
    exact bPairedSource_roundTrip D β
  right_inv := by
    intro s
    exact (bPairedSource_unique D
      ⟨L5A2C4I.ResidueData.bFirstStagePairing D s, ⟨s, rfl⟩⟩ s rfl).symm

/-! ### L3: occupied-charge transfer is deterministic and is not fresh -/

/-- A transfer remembers only the already-used seat. Its semantic target is
the unique source computed by `bPairedSource`. -/
structure BOccupiedChargeTransfer where
  seat : L5A2C4I.ResidueData.BUsedFirstStageBases D

def octSource (τ : BOccupiedChargeTransfer D) :
    L5A2C4I.ResidueData.BNonexceptionalBranches D :=
  bPairedSource D τ.seat

theorem oct_roundTrip (τ : BOccupiedChargeTransfer D) :
    L5A2C4I.ResidueData.bFirstStagePairing D (octSource D τ) = τ.seat.val :=
  bPairedSource_roundTrip D τ.seat

theorem oct_unique (τ : BOccupiedChargeTransfer D)
    (s : L5A2C4I.ResidueData.BNonexceptionalBranches D)
    (hs : L5A2C4I.ResidueData.bFirstStagePairing D s = τ.seat.val) :
    s = octSource D τ :=
  bPairedSource_unique D τ.seat s hs

theorem oct_isUsed (τ : BOccupiedChargeTransfer D) :
    ∃ s : L5A2C4I.ResidueData.BNonexceptionalBranches D,
      L5A2C4I.ResidueData.bFirstStagePairing D s = τ.seat.val :=
  τ.seat.property

theorem oct_not_bFresh (τ : BOccupiedChargeTransfer D) :
    ¬ ∃ f : L5A2C4I.ResidueData.BFreshUnusedMergeBases D,
      f.val = τ.seat.val := by
  rintro ⟨f, hf⟩
  apply f.property
  exact ⟨octSource D τ, (oct_roundTrip D τ).trans hf.symm⟩

/-! ### L4: source-rooted raw histories with only intrinsic decoration -/

structure BSourceRootedHistory where
  package : BSourceRunPackage D
  raw : L5A2C4K.ResidueData.RawHistory D
  start_eq : raw.start = package.val

theorem rooted_run_canonical (H : BSourceRootedHistory D) :
    L5A2C4I.ResidueData.CanonicalBRun D H.package.val
      (bSourceRunEndpoint D H.package) :=
  bSourceRun_canonical D H.package

/-! ### L5: raw source-hit reset, with no owner conclusion -/

noncomputable def sourceHitIndex
    (incoming : L5A2C4K.ResidueData.RawHistory D)
    (target : BSourceRootedHistory D)
    (h : L5A2C4K.ResidueData.SourceHit D incoming target.raw) : ℕ := by
  classical
  exact Nat.find h

theorem sourceHitIndex_le
    (incoming : L5A2C4K.ResidueData.RawHistory D)
    (target : BSourceRootedHistory D)
    (h : L5A2C4K.ResidueData.SourceHit D incoming target.raw) :
    sourceHitIndex D incoming target h ≤
      L5A2C4K.ResidueData.RawHistory.length D incoming := by
  classical
  exact (Nat.find_spec h).1

theorem sourceHitIndex_state
    (incoming : L5A2C4K.ResidueData.RawHistory D)
    (target : BSourceRootedHistory D)
    (h : L5A2C4K.ResidueData.SourceHit D incoming target.raw) :
    L5A2C4K.ResidueData.RawHistory.stateAt D incoming
        (sourceHitIndex D incoming target h) = target.raw.start := by
  classical
  exact (Nat.find_spec h).2

noncomputable def sourceHitReset
    (incoming : L5A2C4K.ResidueData.RawHistory D)
    (target : BSourceRootedHistory D)
    (h : L5A2C4K.ResidueData.SourceHit D incoming target.raw) :
    BSourceRootedHistory D where
  package := target.package
  raw := L5A2C4K.ResidueData.RawHistory.suffix D incoming
    (sourceHitIndex D incoming target h)
  start_eq := by
    rw [L5A2C4K.ResidueData.RawHistory.suffix_start,
      sourceHitIndex_state D incoming target h]
    exact target.start_eq

theorem sourceHitReset_start
    (incoming : L5A2C4K.ResidueData.RawHistory D)
    (target : BSourceRootedHistory D)
    (h : L5A2C4K.ResidueData.SourceHit D incoming target.raw) :
    (sourceHitReset D incoming target h).raw.start = target.package.val :=
  (sourceHitReset D incoming target h).start_eq

theorem sourceHitReset_endpoint
    (incoming : L5A2C4K.ResidueData.RawHistory D)
    (target : BSourceRootedHistory D)
    (h : L5A2C4K.ResidueData.SourceHit D incoming target.raw) :
    L5A2C4K.ResidueData.RawHistory.endpoint D
        (sourceHitReset D incoming target h).raw =
      L5A2C4K.ResidueData.RawHistory.endpoint D incoming := by
  exact L5A2C4K.ResidueData.RawHistory.endpoint_suffix D incoming
    (sourceHitIndex D incoming target h)

theorem sourceHitReset_legal
    (incoming : L5A2C4K.ResidueData.RawHistory D)
    (target : BSourceRootedHistory D)
    (h : L5A2C4K.ResidueData.SourceHit D incoming target.raw) :
    L5A2C4K.ResidueData.WordLegal D
      (sourceHitReset D incoming target h).raw.start
      (sourceHitReset D incoming target h).raw.word :=
  (sourceHitReset D incoming target h).raw.legal

/-! ### L6: decorated replay requires semantic and literal raw equality -/

def LiteralDecoratedReplay (H₁ H₂ : BSourceRootedHistory D) : Prop :=
  H₁.package = H₂.package ∧
    L5A2C4K.ResidueData.LiteralRawReplay D H₁.raw H₂.raw

theorem literalDecoratedReplay_raw {H₁ H₂ : BSourceRootedHistory D}
    (h : LiteralDecoratedReplay D H₁ H₂) :
    L5A2C4K.ResidueData.LiteralRawReplay D H₁.raw H₂.raw :=
  h.2

theorem literalDecoratedReplay_package {H₁ H₂ : BSourceRootedHistory D}
    (h : LiteralDecoratedReplay D H₁ H₂) : H₁.package = H₂.package :=
  h.1

theorem literalDecoratedReplay_of_package_eq_word_eq
    {H₁ H₂ : BSourceRootedHistory D}
    (hp : H₁.package = H₂.package) (hw : H₁.raw.word = H₂.raw.word) :
    LiteralDecoratedReplay D H₁ H₂ := by
  refine ⟨hp, ?_, hw⟩
  calc
    H₁.raw.start = H₁.package.val := H₁.start_eq
    _ = H₂.package.val := congrArg Subtype.val hp
    _ = H₂.raw.start := H₂.start_eq.symm

end ResidueData

/-! ### L7: unconditional specialization to the actual routing data -/

variable {Gamma : NumericalSemigroup}

theorem actual_bSourceRun_canonical
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ P : ResidueData.BSourceRunPackage D,
      L5A2C4I.ResidueData.CanonicalBRun D P.val
        (ResidueData.bSourceRunEndpoint D P) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  exact ResidueData.bSourceRun_canonical (routingData B e)

noncomputable def actual_bUsedFirstStageEquiv
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    L5A2C4I.ResidueData.BUsedFirstStageBases D ≃
      L5A2C4I.ResidueData.BNonexceptionalBranches D := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact ResidueData.bUsedFirstStageEquiv (routingData B e)

noncomputable def actual_oct
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    L5A2C4I.ResidueData.BUsedFirstStageBases D →
      ResidueData.BOccupiedChargeTransfer D := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact fun β => ⟨β⟩

theorem actual_oct_spec
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ β : L5A2C4I.ResidueData.BUsedFirstStageBases D,
      let τ := actual_oct B e β
      L5A2C4I.ResidueData.bFirstStagePairing D
          (ResidueData.octSource D τ) = β.val ∧
        ¬ ∃ f : L5A2C4I.ResidueData.BFreshUnusedMergeBases D,
          f.val = β.val := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro β
  exact ⟨ResidueData.oct_roundTrip (routingData B e) (actual_oct B e β),
    ResidueData.oct_not_bFresh (routingData B e) (actual_oct B e β)⟩

noncomputable def actual_sourceHitReset
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ (incoming : L5A2C4K.ResidueData.RawHistory D)
      (target : ResidueData.BSourceRootedHistory D),
      L5A2C4K.ResidueData.SourceHit D incoming target.raw →
        ResidueData.BSourceRootedHistory D := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro incoming target h
  exact ResidueData.sourceHitReset (routingData B e) incoming target h

theorem actual_sourceHitReset_spec
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ (incoming : L5A2C4K.ResidueData.RawHistory D)
      (target : ResidueData.BSourceRootedHistory D)
      (h : L5A2C4K.ResidueData.SourceHit D incoming target.raw),
      let reset := actual_sourceHitReset B e incoming target h
      reset.raw.start = target.package.val ∧
        L5A2C4K.ResidueData.RawHistory.endpoint D reset.raw =
          L5A2C4K.ResidueData.RawHistory.endpoint D incoming ∧
        L5A2C4K.ResidueData.WordLegal D reset.raw.start reset.raw.word := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro incoming target h
  exact ⟨ResidueData.sourceHitReset_start (routingData B e) incoming target h,
    ResidueData.sourceHitReset_endpoint (routingData B e) incoming target h,
    ResidueData.sourceHitReset_legal (routingData B e) incoming target h⟩

theorem actual_literalDecoratedReplay_raw
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ H₁ H₂ : ResidueData.BSourceRootedHistory D,
      ResidueData.LiteralDecoratedReplay D H₁ H₂ →
        L5A2C4K.ResidueData.LiteralRawReplay D H₁.raw H₂.raw := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro H₁ H₂ h
  exact ResidueData.literalDecoratedReplay_raw (routingData B e) h

end NS25Lean.L5A2C4L
