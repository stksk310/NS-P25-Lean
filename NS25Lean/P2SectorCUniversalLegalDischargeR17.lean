import NS25Lean.P2SectorCDecoratedDischargeR16

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR17

open L2B L5A1 L5A2C3G L5A2C4A L5A2C4D L5A2C4G L5A2C4H
  L5A2C4OR1 L5A2C4OR3 L5A2C4OR7 L5A2C4OR8 L5A2C4OR16

variable {Gamma : NumericalSemigroup}

/-- The R16 unit-normalized owner-one data, indexed by the original
exceptional token.  The index retains its canonical source/run/rooted-history
provenance.  No discharge outcome, freshness, replay, termination, or wall
claim is stored in this structure. -/
structure CMDecoratedUnitOwnerOneState
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e)) where
  hit :
    let H := exceptionalBranchRootedHistory B e s
    L5A2C4K.ResidueData.SourceHit (routingData B e) H.raw H.raw
  Y : ZMod (routingA B e)
  d : ℕ
  zero : PhysicalZeroCenter B e Y d
  selector_one : currentSelector B e (unitZeroCenter B e Y d) = 1
  floor_zero : physicalHeight B e (unitZeroCenter B e Y d) = 0
  shadow_eq :
    unitZeroCenter B e Y d - (routingM B e : ℕ) =
      zeroCenterShadow B e Y d
  minimizers : RawMinimizers B e (unitZeroCenter B e Y d) = {1}

/-- The source-exact R16 existential repackaged without losing its original
exceptional-token index. -/
theorem actual_cm_decorated_unit_ownerOne_state {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD)
    (s : L5A2C4I.ResidueData.BExceptionalBranches
      (routingData P.M.base e)) :
    Nonempty (CMDecoratedUnitOwnerOneState P.M.base e s) := by
  rcases actual_cm_exceptional_decorated_unit_normalization G boundaryPure
      boundaryMixed e HD hInactive hMixed hNotch s with
    ⟨hit, Y, d, hzero, hselector, hfloor, hshadow, hmin⟩
  exact ⟨⟨hit, Y, d, hzero, hselector, hfloor, hshadow, hmin⟩⟩

/-- A canonical choice of the already-proved R16 state, bundled with its
original exceptional token. -/
structure CMDecoratedUnitToken
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) where
  token : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e)
  state : CMDecoratedUnitOwnerOneState B e token

noncomputable def actual_cm_decoratedUnitToken {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD) :
    L5A2C4I.ResidueData.BExceptionalBranches (routingData P.M.base e) →
      CMDecoratedUnitToken P.M.base e :=
  fun s => ⟨s, Classical.choice
    (actual_cm_decorated_unit_ownerOne_state G boundaryPure boundaryMixed
      e HD hInactive hMixed hNotch s)⟩

theorem actual_cm_decoratedUnitToken_token {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD)
    (s : L5A2C4I.ResidueData.BExceptionalBranches
      (routingData P.M.base e)) :
    (actual_cm_decoratedUnitToken G boundaryPure boundaryMixed e HD
      hInactive hMixed hNotch s).token = s := rfl

theorem actual_cm_decoratedUnitToken_injective {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD) :
    Function.Injective (actual_cm_decoratedUnitToken G boundaryPure
      boundaryMixed e HD hInactive hMixed hNotch) := by
  intro x y hxy
  exact congrArg CMDecoratedUnitToken.token hxy

/-- For the chosen R17 starting states, literal decorated replay is still
exactly original-token equality.  No equality of endpoints or zero-centres is
used. -/
theorem actual_cm_decoratedUnitToken_replay_iff {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD)
    (x y : L5A2C4I.ResidueData.BExceptionalBranches
      (routingData P.M.base e)) :
    L5A2C4L.ResidueData.LiteralDecoratedReplay (routingData P.M.base e)
        (exceptionalBranchRootedHistory P.M.base e x)
        (exceptionalBranchRootedHistory P.M.base e y) ↔
      actual_cm_decoratedUnitToken G boundaryPure boundaryMixed e HD
          hInactive hMixed hNotch x =
        actual_cm_decoratedUnitToken G boundaryPure boundaryMixed e HD
          hInactive hMixed hNotch y := by
  constructor
  · intro h
    have hxy := (canonicalExceptional_literalReplay_iff P.M.base e x y).1 h
    subst y
    rfl
  · intro h
    have hxy : x = y := congrArg CMDecoratedUnitToken.token h
    exact (canonicalExceptional_literalReplay_iff P.M.base e x y).2 hxy

end NS25Lean.L5A2C4OR17

