import NS25Lean.P2SectorCZeroCenterNormalizationR8

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR9

open L5A2C4H

variable {Gamma : NumericalSemigroup}

/-- The actual routing state at which a raw incoming history first hits the
source-rooted target.  This is the source-exact `Q` available before the
still-missing C-M candidate-transport calculation. -/
noncomputable def actualSourceHitState
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit
      (routingData B e) incoming target.raw) :
    ZMod (routingA B e) :=
  L5A2C4K.ResidueData.RawHistory.stateAt (routingData B e) incoming
    (L5A2C4L.ResidueData.sourceHitIndex (routingData B e) incoming target hit)

/-- The source-hit state is literally the hit history state, the rooted source
residue, and the legal reset start.  Endpoint and legality are inherited from
the actual suffix, with no owner or local arithmetic conclusion inserted. -/
theorem actual_sourceHit_state_identification
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit
      (routingData B e) incoming target.raw) :
    let Q := actualSourceHitState B e incoming target hit
    let reset := L5A2C4L.ResidueData.sourceHitReset
      (routingData B e) incoming target hit
    Q = target.raw.start ∧
      Q = target.package.val ∧
      reset.raw.start = Q ∧
      L5A2C4K.ResidueData.RawHistory.endpoint (routingData B e) reset.raw =
        L5A2C4K.ResidueData.RawHistory.endpoint (routingData B e) incoming ∧
      L5A2C4K.ResidueData.WordLegal (routingData B e)
        reset.raw.start reset.raw.word := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  have hstate := L5A2C4L.ResidueData.sourceHitIndex_state
    (routingData B e) incoming target hit
  have hpackage : actualSourceHitState B e incoming target hit =
      target.package.val := hstate.trans target.start_eq
  refine ⟨hstate, hpackage, ?_,
    L5A2C4L.ResidueData.sourceHitReset_endpoint
      (routingData B e) incoming target hit,
    L5A2C4L.ResidueData.sourceHitReset_legal
      (routingData B e) incoming target hit⟩
  exact (L5A2C4L.ResidueData.sourceHitReset_start
    (routingData B e) incoming target hit).trans hpackage.symm

end NS25Lean.L5A2C4OR9
