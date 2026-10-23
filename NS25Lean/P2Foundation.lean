import NS25Lean.BasePivotSharp
import NS25Lean.BoundarySourceCoordinates
import NS25Lean.TailIdealNormalization

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A1

open FourGeneratedBridge

variable {Gamma : NumericalSemigroup}

/-- The typed multiplicity-base data for the `p = 2` branch. -/
structure P2Data (Gamma : NumericalSemigroup) where
  M : L2B.MultiplicityBase Gamma
  hp : L2B.chosenDefect M.base = 2

namespace P2Data

/-- The actual number of minimal sources of the chosen Apéry tail. -/
abbrev sourceCount (P : P2Data Gamma) : ℕ := L2B.sourceCount P.M.base

/-- The actual chosen-base ideal in the three-variable polynomial ring. -/
abbrev J (P : P2Data Gamma) (k : Type*) [Field k] := P.M.base.J k

/-- The actual polynomial quotient attached to the chosen multiplicity base. -/
abbrev PolynomialQuotient (P : P2Data Gamma) (k : Type*) [Field k] :=
  MvPolynomial (Fin 3) k ⧸ P.J k

/-- Generator number of the actual chosen-base ideal. -/
def generatorNumber (P : P2Data Gamma) (k : Type*) [Field k] : ℕ :=
  (P.J k).spanFinrank

/-- Socle type of the actual chosen-base polynomial quotient. -/
def quotientType (P : P2Data Gamma) (k : Type*) [Field k] : ℕ :=
  P.M.base.quotientType k

/-- Literal integer slack `W = t - S`; this is not truncated subtraction. -/
def W (P : P2Data Gamma) : ℤ :=
  (Gamma.asRelativeIdeal.idealType : ℤ) - (P.sourceCount : ℤ)

/-- Descriptive alias for the literal integer slack `W`. -/
abbrev slack (P : P2Data Gamma) : ℤ := P.W

end P2Data

/-- Every chosen base has a minimal source: take the least element of its nonempty tail. -/
theorem chosenBase_source_nonempty (B : ChosenBase.Data Gamma) :
    Nonempty (L2B2A2.Source B) := by
  classical
  have hK : B.K.Nonempty :=
    aperyTail_nonempty_of_positive_generator B.q.property
      (B.tailDegrees 0).property (B.degrees_positive (Fin.succ 0))
  let x := Nat.find hK
  have hxK : x ∈ B.K := Nat.find_spec hK
  refine ⟨⟨x, hxK, ?_⟩⟩
  intro h hhH hhzero
  by_cases hxh : x < h
  · exact Or.inl hxh
  · right
    intro hxsub
    exact Nat.find_min hK (by omega) hxsub

/-- Consequently the actual source count is positive for every chosen base. -/
theorem chosenBase_sourceCount_pos (B : ChosenBase.Data Gamma) :
    0 < L2B.sourceCount B := by
  change 0 < Nat.card (L2B2A2.Source B)
  exact Nat.card_pos_iff.mpr ⟨chosenBase_source_nonempty B, inferInstance⟩

/-- The `S = 0` branch is impossible, independently of the defect. -/
theorem chosenBase_sourceCount_ne_zero (B : ChosenBase.Data Gamma) :
    L2B.sourceCount B ≠ 0 :=
  (chosenBase_sourceCount_pos B).ne'

/-- For actual `p = 2` data, the intrinsic presentation number is exactly `S + 2`. -/
theorem p2_rho_eq_sourceCount_add_two (P : P2Data Gamma) :
    Presentation.rho Gamma = P.sourceCount + 2 := by
  have h := L2B.sourceCount_add_defect P.M.base
  rw [P.hp] at h
  exact h.symm

/-- MUJ identifies the actual chosen ideal's generator number with intrinsic `rho`. -/
theorem p2_generatorNumber_eq_rho (P : P2Data Gamma) (k : Type*) [Field k] :
    P.generatorNumber k = Presentation.rho Gamma :=
  P.M.base.muj k

/-- Thus the actual chosen ideal has generator number `S + 2`. -/
theorem p2_generatorNumber_eq_sourceCount_add_two
    (P : P2Data Gamma) (k : Type*) [Field k] :
    P.generatorNumber k = P.sourceCount + 2 := by
  rw [p2_generatorNumber_eq_rho P k, p2_rho_eq_sourceCount_add_two P]

/-- The actual polynomial quotient type is the numerical-semigroup type. -/
theorem p2_quotientType_eq_idealType (P : P2Data Gamma) (k : Type*) [Field k] :
    P.quotientType k = Gamma.asRelativeIdeal.idealType :=
  P.M.base.quotient_type_eq k

/-- Frozen NS-SHARP specializes at `p = 2` to `t ≤ S + 1`. -/
theorem p2_type_le_sourceCount_add_one (P : P2Data Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount + 1 := by
  have hsharp := L4B.ns_sharp_data P.M.base
  have hrho := p2_rho_eq_sourceCount_add_two P
  omega

/-- Failure of the target `t ≤ S` forces the exact extremal equality `t = S + 1`. -/
theorem p2_type_eq_sourceCount_add_one_of_target_failure (P : P2Data Gamma)
    (hfail : ¬ Gamma.asRelativeIdeal.idealType ≤ P.sourceCount) :
    Gamma.asRelativeIdeal.idealType = P.sourceCount + 1 := by
  have hupper := p2_type_le_sourceCount_add_one P
  omega

/-- ENTRY: on a target counterexample, the literal integer slack is exactly one. -/
theorem p2_entry (P : P2Data Gamma)
    (hfail : ¬ Gamma.asRelativeIdeal.idealType ≤ P.sourceCount) :
    P.W = 1 := by
  have heq := p2_type_eq_sourceCount_add_one_of_target_failure P hfail
  unfold P2Data.W
  omega

end NS25Lean.L5A1
