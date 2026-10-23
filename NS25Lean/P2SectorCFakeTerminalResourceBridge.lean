import NS25Lean.P2SectorCResidualResourceLedger

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4N

open CombinatorialCore
open L5A2C4H

variable {H : NumericalSemigroup}

/-! ### N1--N2: the source-exact full-sink partition -/

/-- The full raw sinks split by the defining integral-membership proposition.
The equivalence is the C4H classifier; no partition premise is introduced. -/
noncomputable def fullSinkEquivActualSumFake_sourceExact
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) :
    FullSink I a b c hbH hcH ≃
      Sum (ActualSink I a b c hbH hcH) (FakeSink I a b c hbH hcH) :=
  fullSinkEquivActualSumFake I a b c hbH hcH

theorem fullSink_card_eq_actual_add_fake
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) :
    Nat.card (FullSink I a b c hbH hcH) =
      Nat.card (ActualSink I a b c hbH hcH) +
        Nat.card (FakeSink I a b c hbH hcH) := by
  letI : Finite (ActualSink I a b c hbH hcH) := Subtype.finite
  letI : Finite (FakeSink I a b c hbH hcH) := Subtype.finite
  exact (Nat.card_congr
    (fullSinkEquivActualSumFake_sourceExact I a b c hbH hcH)).trans Nat.card_sum

/-! ### N3--N4: actual chosen-base fake terminal seats -/

variable {Gamma : NumericalSemigroup}

/-- The actual terminal-resource type is exactly the frozen C4H fake-sink
subtype for the chosen-base normalized routing data.  It carries no owner or
history decoration. -/
def ActualFakeTerminalSeats (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) : Type :=
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  FakeSink (routingI B e) (routingA B e) (routingB B e) (routingC B e)
    (routingHB B e) (routingHC B e)

noncomputable instance actualFakeTerminalSeats_finite
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Finite (ActualFakeTerminalSeats B e) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  unfold ActualFakeTerminalSeats
  exact Subtype.finite

theorem actualFakeTerminalSeats_card
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Nat.card (ActualFakeTerminalSeats B e) =
      letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
      fakeSinkCount (routingI B e) (routingA B e) (routingB B e) (routingC B e)
        (routingHB B e) (routingHC B e) := by
  rfl

theorem actualFakeTerminalSeat_isFullRawSink
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x : ActualFakeTerminalSeats B e) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingData B e).IsSink x.val := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact x.property.1

/-- A fake terminal fails precisely the ideal-membership condition which
defines an actual/integral sink. -/
theorem actualFakeTerminalSeat_not_integral
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x : ActualFakeTerminalSeats B e) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingI B e).aperyRepresentative (routingA B e) x.val - routingA B e ∉
      (routingH B e).asRelativeIdeal := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact x.property.2

theorem actualFakeTerminalSeat_not_actual
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x : ActualFakeTerminalSeats B e) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ¬ ∃ y : ActualSink (routingI B e) (routingA B e) (routingB B e)
        (routingC B e) (routingHB B e) (routingHC B e), y.val = x.val := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  rintro ⟨y, hy⟩
  exact x.property.2 (hy ▸ y.property.2)

/-! ### N5: instantiate the frozen C4M residual resource ledger -/

def ActualResidualResourceSeats
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) : Type :=
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  Sum (L5A2C4I.ResidueData.BFreshUnusedMergeBases (routingData B e))
    (ActualFakeTerminalSeats B e)

noncomputable def E (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) : ℕ :=
  Nat.card (ActualFakeTerminalSeats B e)

theorem actualResidualResourceSeats_card
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    Nat.card (ActualResidualResourceSeats B e) =
      L5A2C4M.ResidueData.UexB (routingData B e) + E B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  simpa only [ActualResidualResourceSeats, E,
    L5A2C4M.ResidueData.BResidualResourceSeats] using
      (L5A2C4M.ResidueData.residualResourceSeats_card
        (routingData B e) (ActualFakeTerminalSeats B e))

/-! ### N6: the conditional actual closing interface -/

theorem actual_injective_discharge_closes
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ∀ (f : L5A2C4I.ResidueData.BExceptionalBranches (routingData B e) →
        ActualResidualResourceSeats B e),
      Function.Injective f →
        L5A2C4M.ResidueData.Cbr (routingData B e) ≤
          L5A2C4M.ResidueData.U (routingData B e) + E B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  intro f hf
  exact L5A2C4M.ResidueData.injective_discharge_closes
    (routingData B e) (ActualFakeTerminalSeats B e) f hf

end NS25Lean.L5A2C4N
