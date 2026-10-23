import NS25Lean.P2SectorCDecoratedSourceRunOCTBase

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4M

open CombinatorialCore
open L5A2C4H
open L5A2C4I

namespace ResidueData

variable {R : Type*} [Fintype R] (D : CombinatorialCore.ResidueData R)

/-! ### M1: safe aliases for the frozen finite counts -/

noncomputable def Cbr : ℕ :=
  L5A2C4I.ResidueData.sourceTargetBranchCount D

noncomputable def Nb : ℕ :=
  L5A2C4I.ResidueData.bExceptionalCount D

noncomputable def UsedB : ℕ :=
  L5A2C4I.ResidueData.bUsedFirstStageCount D

noncomputable def U : ℕ :=
  Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases D)

noncomputable def UexB : ℕ :=
  Nat.card (L5A2C4I.ResidueData.BFreshUnusedMergeBases D)

/-! ### M2: residual resource seats for an arbitrary finite terminal type -/

def BResidualResourceSeats (F : Type*) :=
  Sum (L5A2C4I.ResidueData.BFreshUnusedMergeBases D) F

theorem residualResourceSeats_card (F : Type*) [Finite F] :
    Nat.card (BResidualResourceSeats D F) = UexB D + Nat.card F := by
  letI : Finite (L5A2C4I.ResidueData.ExactUnusedMergeBases D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.BFreshUnusedMergeBases D) := Subtype.finite
  exact Nat.card_sum

/-! ### M3--M4: exceptional tokens and an arbitrary injective discharge -/

theorem exceptionalBranches_card :
    Nat.card (L5A2C4I.ResidueData.BExceptionalBranches D) = Nb D := rfl

theorem injective_discharge_residual_bound
    (F : Type*) [Finite F]
    (f : L5A2C4I.ResidueData.BExceptionalBranches D →
      BResidualResourceSeats D F)
    (hf : Function.Injective f) :
    Nb D ≤ UexB D + Nat.card F := by
  letI : Finite (L5A2C4I.ResidueData.BSourceTargetBranches D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.BExceptionalBranches D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.ExactUnusedMergeBases D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.BFreshUnusedMergeBases D) := Subtype.finite
  letI : Finite (BResidualResourceSeats D F) := by
    unfold BResidualResourceSeats
    infer_instance
  have h := Nat.card_le_card_of_injective f hf
  rw [residualResourceSeats_card D F] at h
  exact h

/-! ### M5: exact subtraction-free residual identity -/

theorem residual_count_identity :
    U D + Nb D = UexB D + Cbr D := by
  letI : Finite (L5A2C4I.ResidueData.ExactUnusedMergeBases D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.BUsedFirstStageBases D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.BFreshUnusedMergeBases D) := Subtype.finite
  have hpartition :=
    Nat.card_congr (L5A2C4I.ResidueData.bUnusedMergeUsedFreshEquiv D)
  rw [Nat.card_sum] at hpartition
  have hstage := L5A2C4I.ResidueData.b_firstStage_card_identity D
  simp only [L5A2C4I.ResidueData.bUsedFirstStageCount,
    L5A2C4I.ResidueData.bExceptionalCount,
    L5A2C4I.ResidueData.sourceTargetBranchCount] at hstage
  simp only [U, Nb, UexB, Cbr,
    L5A2C4I.ResidueData.bExceptionalCount,
    L5A2C4I.ResidueData.sourceTargetBranchCount]
  omega

/-! ### M6: the residual and global inequalities are equivalent -/

theorem residual_inequality_iff (E : ℕ) :
    Nb D ≤ UexB D + E ↔ Cbr D ≤ U D + E := by
  have hledger := residual_count_identity D
  omega

/-! ### M7: the single abstract closing interface -/

theorem injective_discharge_closes
    (F : Type*) [Finite F]
    (f : L5A2C4I.ResidueData.BExceptionalBranches D →
      BResidualResourceSeats D F)
    (hf : Function.Injective f) :
    Cbr D ≤ U D + Nat.card F := by
  exact (residual_inequality_iff D (Nat.card F)).1
    (injective_discharge_residual_bound D F f hf)

end ResidueData

/-! ### M8: actual chosen-base routing specialization -/

variable {Gamma : NumericalSemigroup}

theorem actual_residual_count_identity
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ResidueData.U D + ResidueData.Nb D =
      ResidueData.UexB D + ResidueData.Cbr D := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact ResidueData.residual_count_identity (routingData B e)

theorem actual_residualResourceSeats_card
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (F : Type*) [Finite F] :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    Nat.card (ResidueData.BResidualResourceSeats D F) =
      ResidueData.UexB D + Nat.card F := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact ResidueData.residualResourceSeats_card (routingData B e) F

theorem actual_residual_inequality_iff
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (E : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ResidueData.Nb D ≤ ResidueData.UexB D + E ↔
      ResidueData.Cbr D ≤ ResidueData.U D + E := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact ResidueData.residual_inequality_iff (routingData B e) E

theorem actual_injective_discharge_closes
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (F : Type*) [Finite F] :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ (f : L5A2C4I.ResidueData.BExceptionalBranches D →
        ResidueData.BResidualResourceSeats D F),
      Function.Injective f →
        ResidueData.Cbr D ≤ ResidueData.U D + Nat.card F := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro f hf
  exact ResidueData.injective_discharge_closes (routingData B e) F f hf

end NS25Lean.L5A2C4M
