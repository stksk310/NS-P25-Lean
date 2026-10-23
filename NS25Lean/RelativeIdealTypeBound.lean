/-
Copyright (c) 2026 Keisuke Sato. All rights reserved.
Authors: Keisuke Sato
-/
import NS25Lean.AperyConstruction

set_option linter.style.header false

/-!
# The relative-ideal type bound from an Apéry realization

This file makes the remaining interface explicit.  Once an arbitrary relative
ideal supplies valid Apéry step data and the source/sink dictionary, the desired
type inequality follows immediately from the machine-checked combinatorial core.
-/

namespace NS25Lean

open CombinatorialCore

namespace RelativeIdeal

variable {H : NumericalSemigroup} (I : RelativeIdeal H)
variable {R : Type*} [AddCommGroup R] [Fintype R]

/-- The exact source/sink dictionary required from a concrete Apéry construction. -/
def HasCountDictionary (D : AperyStepData R) (hD : D.IsValid) : Prop :=
  (D.toResidueData hD).sourceCount = I.generatorCount ∧
    (D.toResidueData hD).sinkCount = I.idealType

/-- The NS25 relative-ideal inequality, conditional only on a valid Apéry realization. -/
theorem idealType_le_two_mul_generatorCount_of_apery
    (D : AperyStepData R) (hD : D.IsValid) (hcount : I.HasCountDictionary D hD) :
    I.idealType ≤ 2 * I.generatorCount := by
  calc
    I.idealType = (D.toResidueData hD).sinkCount := hcount.2.symm
    _ ≤ 2 * (D.toResidueData hD).sourceCount :=
      D.sinkCount_le_two_mul_sourceCount hD
    _ = 2 * I.generatorCount := by rw [hcount.1]

/-- The relative-ideal type bound for a displayed positive three-generator
presentation. -/
theorem idealType_le_two_mul_generatorCount_of_generatedByThree
    (I : RelativeIdeal H) (a b c : ℕ)
    (hgen : H.IsGeneratedByThree a b c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    I.idealType ≤ 2 * I.generatorCount := by
  letI : NeZero a := ⟨ha⟩
  have haH : a ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  have hbH : b ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  have hcH : c ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  let D := I.toAperyStepData a b c hbH hcH
  let hD := I.toAperyStepData_isValid a b c hbH hcH
  apply I.idealType_le_two_mul_generatorCount_of_apery D hD
  exact ⟨I.concrete_sourceCount_eq_generatorCount a b c hgen hbH hcH hb hc,
    I.concrete_sinkCount_eq_idealType a b c hgen haH hbH hcH hb hc⟩

/-- **NS25 Milestone A.** Every relative ideal of a minimally
three-generated numerical semigroup satisfies `t(I) ≤ 2 μ_H(I)`. -/
theorem idealType_le_two_mul_generatorCount
    (I : RelativeIdeal H) (a b c : ℕ)
    (hmin : H.IsMinimallyGeneratedByThree a b c) :
    I.idealType ≤ 2 * I.generatorCount := by
  have ha : a ≠ 0 := by
    intro hzero
    subst a
    exact hmin.2.1 (AddSubmonoid.zero_mem _)
  have hb : b ≠ 0 := by
    intro hzero
    subst b
    exact hmin.2.2.1 (AddSubmonoid.zero_mem _)
  have hc : c ≠ 0 := by
    intro hzero
    subst c
    exact hmin.2.2.2 (AddSubmonoid.zero_mem _)
  exact I.idealType_le_two_mul_generatorCount_of_generatedByThree
    a b c hmin.1 ha hb hc

end RelativeIdeal
end NS25Lean
