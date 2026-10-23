/-
Copyright (c) 2026 Keisuke Sato. All rights reserved.
Authors: Keisuke Sato
-/
import NS25Lean.CombinatorialCore
import Mathlib.Tactic.LinearCombination

set_option linter.style.header false

/-!
# Bridge from Apéry step equations to the combinatorial core

This layer records exactly the two Apéry step equations needed by the paper.
It proves the diamond identity rather than storing it as an assumption, and
then constructs the abstract `ResidueData` used by `CombinatorialCore`.
-/

namespace NS25Lean

open CombinatorialCore

/-- Apéry representatives together with their two nonnegative step quotients. -/
structure AperyStepData (R : Type*) [AddCommGroup R] where
  modulus : ℕ
  b : R
  c : R
  bValue : ℤ
  cValue : ℤ
  lambda : R → ℤ
  u : R → ℕ
  v : R → ℕ

namespace AperyStepData

variable {R : Type*} [AddCommGroup R] (D : AperyStepData R)

/-- Positivity and the two defining Apéry step equations. -/
structure IsValid : Prop where
  modulus_pos : 0 < D.modulus
  step_b : ∀ r, D.lambda r + D.bValue =
    D.lambda (r + D.b) + D.modulus * D.u r
  step_c : ∀ r, D.lambda r + D.cValue =
    D.lambda (r + D.c) + D.modulus * D.v r

/-- The two ways around an Apéry diamond have the same total quotient. -/
theorem diamond (hD : D.IsValid) (r : R) :
    D.u r + D.v (r + D.b) = D.v r + D.u (r + D.c) := by
  have h₁ := hD.step_b r
  have h₂ := hD.step_c (r + D.b)
  have h₃ := hD.step_c r
  have h₄ := hD.step_b (r + D.c)
  have h₄' : D.lambda (r + D.c) + D.bValue =
      D.lambda ((r + D.b) + D.c) + D.modulus * D.u (r + D.c) := by
    simpa [add_assoc, add_comm, add_left_comm] using h₄
  have path₁ : (D.modulus : ℤ) * (D.u r + D.v (r + D.b)) =
      D.lambda r + D.bValue + D.cValue - D.lambda ((r + D.b) + D.c) := by
    linear_combination -h₁ - h₂
  have path₂ : (D.modulus : ℤ) * (D.v r + D.u (r + D.c)) =
      D.lambda r + D.bValue + D.cValue - D.lambda ((r + D.b) + D.c) := by
    linear_combination -h₃ - h₄'
  have ha : (D.modulus : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hD.modulus_pos)
  have hcast : ((D.u r + D.v (r + D.b) : ℕ) : ℤ) =
      ((D.v r + D.u (r + D.c) : ℕ) : ℤ) := by
    apply mul_left_cancel₀ ha
    exact path₁.trans path₂.symm
  exact Int.ofNat_inj.mp hcast

/-- Package the Apéry step data as the finite combinatorial residue data. -/
def toResidueData [Fintype R] (hD : D.IsValid) : ResidueData R where
  u := D.u
  v := D.v
  b := Equiv.addRight D.b
  c := Equiv.addRight D.c
  commute := by
    intro r
    simp [add_comm, add_left_comm]
  diamond := by
    intro r
    simpa using D.diamond hD r

/-- Every finite Apéry step system satisfies the abstract sink/source bound. -/
theorem sinkCount_le_two_mul_sourceCount [Fintype R] (hD : D.IsValid) :
    (D.toResidueData hD).sinkCount ≤ 2 * (D.toResidueData hD).sourceCount :=
  (D.toResidueData hD).sinkCount_le_two_mul_sourceCount

end AperyStepData
end NS25Lean
