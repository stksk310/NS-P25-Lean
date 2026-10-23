import NS25Lean.P2SectorCFakeTerminalResourceBridge

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4O

open L5A2C4H

private theorem exists_injective_of_fintypeCard_le
    {α β : Type*} [Fintype α] [Fintype β]
    (h : Fintype.card α ≤ Fintype.card β) :
    ∃ f : α → β, Function.Injective f := by
  classical
  let f : α → β := fun x =>
    (Fintype.equivFin β).symm (Fin.castLE h (Fintype.equivFin α x))
  refine ⟨f, ?_⟩
  intro x y hxy
  apply (Fintype.equivFin α).injective
  apply Fin.castLE_injective h
  exact (Fintype.equivFin β).symm.injective hxy

/-- The safe C4O checkpoint: once the actual owner-component argument supplies
the global cardinality bound, finite cardinality comparison produces a
classical noncanonical discharge injection.  This theorem does not assign a
semantic private owner to any fake terminal. -/
theorem actual_exists_injective_discharge_of_global_bound
    {Gamma : NumericalSemigroup}
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hglobal :
      letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
      let D := routingData B e
      L5A2C4M.ResidueData.Cbr D ≤
        L5A2C4M.ResidueData.U D + L5A2C4N.E B e) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∃ f : L5A2C4I.ResidueData.BExceptionalBranches D →
        L5A2C4N.ActualResidualResourceSeats B e,
      Function.Injective f := by
  classical
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let D := routingData B e
  have hresidual :
      L5A2C4M.ResidueData.Nb D ≤
        L5A2C4M.ResidueData.UexB D + L5A2C4N.E B e :=
    (L5A2C4M.ResidueData.residual_inequality_iff
      D (L5A2C4N.E B e)).2 hglobal
  have hcard :
      Nat.card (L5A2C4I.ResidueData.BExceptionalBranches D) ≤
        Nat.card (L5A2C4N.ActualResidualResourceSeats B e) := by
    rw [L5A2C4M.ResidueData.exceptionalBranches_card D,
      L5A2C4N.actualResidualResourceSeats_card B e]
    exact hresidual
  letI : Fintype (L5A2C4I.ResidueData.BSourceTargetBranches D) := by
    unfold L5A2C4I.ResidueData.BSourceTargetBranches
    infer_instance
  letI : Fintype (L5A2C4I.ResidueData.BExceptionalBranches D) := by
    unfold L5A2C4I.ResidueData.BExceptionalBranches
    infer_instance
  letI : Fintype (L5A2C4I.ResidueData.ExactUnusedMergeBases D) := by
    unfold L5A2C4I.ResidueData.ExactUnusedMergeBases
    infer_instance
  letI : Fintype (L5A2C4I.ResidueData.BFreshUnusedMergeBases D) := by
    unfold L5A2C4I.ResidueData.BFreshUnusedMergeBases
    infer_instance
  letI : Fintype (L5A2C4N.ActualFakeTerminalSeats B e) := by
    unfold L5A2C4N.ActualFakeTerminalSeats L5A2C4H.FakeSink
    infer_instance
  letI : Fintype (L5A2C4N.ActualResidualResourceSeats B e) := by
    unfold L5A2C4N.ActualResidualResourceSeats
    infer_instance
  exact exists_injective_of_fintypeCard_le (by
    simpa [Nat.card_eq_fintype_card] using hcard)

/-- The noncanonical injection obtained from the cardinality bound instantiates
the frozen C4N conditional closing theorem.  The global bound remains an
explicit premise because its source-exact owner/selector dynamics are absent
from the frozen actual routing API. -/
theorem actual_global_bound_closes_through_c4n
    {Gamma : NumericalSemigroup}
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hglobal :
      letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
      let D := routingData B e
      L5A2C4M.ResidueData.Cbr D ≤
        L5A2C4M.ResidueData.U D + L5A2C4N.E B e) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    L5A2C4M.ResidueData.Cbr D ≤
      L5A2C4M.ResidueData.U D + L5A2C4N.E B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  obtain ⟨f, hf⟩ := actual_exists_injective_discharge_of_global_bound B e hglobal
  exact L5A2C4N.actual_injective_discharge_closes B e f hf

end NS25Lean.L5A2C4O
