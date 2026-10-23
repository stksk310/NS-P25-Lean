import NS25Lean.P2SectorCActualSourceHitLocalReductionR9

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR10

open L5A2C4H

variable {Gamma : NumericalSemigroup}

/-- An actual source hit lands on the intrinsic source-target branch carried by
the rooted target.  The positive cross is consequently obtained directly from
the routing diamond, before any Herzog-coordinate localization. -/
theorem actual_sourceHit_sourceTarget_cross
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit
      (routingData B e) incoming target.raw) :
    let D := routingData B e
    let Q := L5A2C4OR9.actualSourceHitState B e incoming target hit
    D.IsBranch Q ∧
      D.u Q = 0 ∧ D.v Q = 0 ∧
      D.u (D.c Q) = D.v (D.b Q) ∧
      0 < D.u (D.c Q) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  have hQ : L5A2C4OR9.actualSourceHitState B e incoming target hit =
      target.package.val :=
    (L5A2C4OR9.actual_sourceHit_state_identification
      B e incoming target hit).2.1
  have hcross :=
    (L5A2C4I.ResidueData.sourceTargetBranch_iff_positive_cross
      (routingData B e)).1 target.package.property
  rw [hQ]
  exact ⟨hcross.1, hcross.1.1, hcross.1.2, hcross.2.1, hcross.2.2⟩

/-- The actual source-hit cross value, with its positivity and opposite-arm
equality exported as a small reusable packet. -/
theorem actual_sourceHit_cross_value_spec
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit
      (routingData B e) incoming target.raw) :
    let D := routingData B e
    let Q := L5A2C4OR9.actualSourceHitState B e incoming target hit
    let w := D.u (D.c Q)
    0 < w ∧ w = D.v (D.b Q) := by
  dsimp only
  have h := actual_sourceHit_sourceTarget_cross B e incoming target hit
  exact ⟨h.2.2.2.2, h.2.2.2.1⟩

/-- The actual source-hit residue has a unique coordinate in the coherent
Herzog L-shape.  This is residue localization only: it inserts no C-M local
square, carry bound, or candidate-transport conclusion. -/
theorem actual_sourceHit_unique_lShape_index
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit
      (routingData B e) incoming target.raw) :
    let Q := L5A2C4OR9.actualSourceHitState B e incoming target hit
    ∃! x : GenericLShape.Index (L5A2C4D.cr12 HD) (L5A2C4D.cr13 HD)
        (L5A2C4D.cr32 HD) (L5A2C4D.cr23 HD),
      GenericLShape.residue (routingA B e) (routingB B e) (routingC B e)
        (L5A2C4D.cr12 HD) (L5A2C4D.cr13 HD)
        (L5A2C4D.cr32 HD) (L5A2C4D.cr23 HD) x = Q := by
  dsimp only
  let f := GenericLShape.residue (routingA B e) (routingB B e)
    (routingC B e) (L5A2C4D.cr12 HD) (L5A2C4D.cr13 HD)
      (L5A2C4D.cr32 HD) (L5A2C4D.cr23 HD)
  have hf := L5A2C4OR6.coherent_lShape_residue_bijective B e HD
  obtain ⟨x, hx⟩ := hf.2
    (L5A2C4OR9.actualSourceHitState B e incoming target hit)
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hf.1 (hy.trans hx.symm)

end NS25Lean.L5A2C4OR10
