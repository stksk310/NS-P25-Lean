/-
Copyright (c) 2026 Keisuke Sato. All rights reserved.
Authors: Keisuke Sato
-/
import NS25Lean.RelativeIdealTypeBound

set_option linter.style.header false

/-!
# Canonical duality for relative ideals

The standard canonical dual `K_H - I` is characterized by
`z ∈ K_H - I ↔ F(H) - z ∉ I`.  We use this characterization as the
definition, with an arbitrary reflection center `F`.  Taking `F = F(H)` gives
the usual canonical dual; changing `F` only translates it.
-/

namespace NS25Lean
namespace NumericalSemigroup

/-- The Frobenius number, with the standard convention `F(ℕ) = -1` when the
gap set is empty. -/
noncomputable def frobeniusNumber (H : NumericalSemigroup) : ℤ :=
  if H.gaps = ∅ then -1 else (H.gaps_finite.toFinset.sup id : ℕ)

theorem frobeniusNumber_eq_neg_one_of_gaps_empty
    (H : NumericalSemigroup) (hgap : H.gaps = ∅) :
    H.frobeniusNumber = -1 := by
  simp [frobeniusNumber, hgap]

/-- Every gap is at most the Frobenius number. -/
theorem gap_le_frobeniusNumber (H : NumericalSemigroup) {n : ℕ}
    (hn : n ∈ H.gaps) : (n : ℤ) ≤ H.frobeniusNumber := by
  have hne : H.gaps ≠ ∅ := by
    exact Set.nonempty_iff_ne_empty.mp ⟨n, hn⟩
  simp only [frobeniusNumber, hne, ↓reduceIte]
  exact_mod_cast Finset.le_sup (f := id) (H.gaps_finite.mem_toFinset.2 hn)

/-- When gaps exist, the Frobenius number is itself the natural-number cast
of a gap. -/
theorem exists_gap_eq_frobeniusNumber (H : NumericalSemigroup)
    (hne : H.gaps ≠ ∅) :
    ∃ n : ℕ, n ∈ H.gaps ∧ H.frobeniusNumber = n := by
  have hs : H.gaps_finite.toFinset.Nonempty :=
    H.gaps_finite.toFinset_nonempty.mpr (Set.nonempty_iff_ne_empty.mpr hne)
  obtain ⟨n, hn, hsup⟩ := Finset.sup_mem_of_nonempty (f := id) hs
  refine ⟨n, H.gaps_finite.mem_toFinset.mp hn, ?_⟩
  simp only [frobeniusNumber, hne, ↓reduceIte]
  exact_mod_cast hsup.symm

/-- A numerical semigroup, embedded in `ℤ`, as a relative ideal over itself. -/
def asRelativeIdeal (H : NumericalSemigroup) : RelativeIdeal H where
  carrier := {z | ∃ n : ℕ, n ∈ H ∧ z = n}
  nonempty := ⟨0, 0, H.zero_mem, rfl⟩
  bddBelow := by
    refine ⟨0, ?_⟩
    rintro z ⟨n, -, rfl⟩
    exact Int.natCast_nonneg n
  add_mem := by
    rintro z h ⟨n, hn, rfl⟩ hh
    exact ⟨n + h, H.add_mem hn hh, by norm_num⟩

@[simp] theorem mem_asRelativeIdeal_iff (H : NumericalSemigroup) (z : ℤ) :
    z ∈ H.asRelativeIdeal ↔ ∃ n : ℕ, n ∈ H ∧ z = n := Iff.rfl

end NumericalSemigroup

namespace RelativeIdeal

variable {H : NumericalSemigroup}

/-- The ideal difference `A - B = {z | z + B ⊆ A}`. -/
def idealDifference (A B : RelativeIdeal H) : RelativeIdeal H where
  carrier := {z | ∀ x : ℤ, x ∈ B → z + x ∈ A}
  nonempty := by
    obtain ⟨threshold, htail⟩ := A.exists_tail
    obtain ⟨lower, hlower⟩ := B.bddBelow
    refine ⟨threshold - lower, ?_⟩
    intro x hx
    apply htail (threshold - lower + x)
    have := hlower hx
    omega
  bddBelow := by
    obtain ⟨lower, hlower⟩ := A.bddBelow
    obtain ⟨x, hx⟩ := B.nonempty
    refine ⟨lower - x, ?_⟩
    intro z hz
    have := hlower (hz x hx)
    omega
  add_mem := by
    intro z h hz hh x hx
    have hmem := A.add_mem_nat (hz x hx) hh
    convert hmem using 1 <;> omega

@[simp] theorem mem_idealDifference_iff (A B : RelativeIdeal H) (z : ℤ) :
    z ∈ A.idealDifference B ↔ ∀ x : ℤ, x ∈ B → z + x ∈ A := Iff.rfl

/-- Reflection-complement dual at an integer `F`.  At the Frobenius number of
`H`, this is the standard canonical dual `K_H - I`. -/
def canonicalDualAt (I : RelativeIdeal H) (F : ℤ) : RelativeIdeal H where
  carrier := {z | F - z ∉ I}
  nonempty := by
    obtain ⟨lower, hlower⟩ := I.bddBelow
    refine ⟨F - lower + 1, ?_⟩
    intro hmem
    have := hlower hmem
    omega
  bddBelow := by
    obtain ⟨x, hx⟩ := I.nonempty
    obtain ⟨conductor, hconductor⟩ := H.exists_conductor
    refine ⟨F - (x + conductor), ?_⟩
    intro z hz
    by_contra hnot
    have hlt : z < F - (x + conductor) := lt_of_not_ge hnot
    let h : ℕ := (F - z - x).toNat
    have hnonneg : (0 : ℤ) ≤ F - z - x := by omega
    have hcast : (h : ℤ) = F - z - x := Int.toNat_of_nonneg hnonneg
    have hc : conductor ≤ h := by
      have hcInt : (conductor : ℤ) ≤ (h : ℤ) := by rw [hcast]; omega
      exact_mod_cast hcInt
    have hh : h ∈ H := hconductor h hc
    apply hz
    have hmem := I.add_mem_nat hx hh
    convert hmem using 1 <;> omega
  add_mem := by
    intro z h hz hh hmem
    apply hz
    have hadd := I.add_mem_nat hmem hh
    convert hadd using 1 <;> omega

/-- The canonical ideal centered at `F`.  At `F = F(H)`, its carrier is
`{x : ℤ | F(H) - x ∉ H}`. -/
def canonicalIdealAt (H : NumericalSemigroup) (F : ℤ) : RelativeIdeal H :=
  H.asRelativeIdeal.canonicalDualAt F

/-- The standard canonical ideal of a numerical semigroup. -/
noncomputable def canonicalIdeal (H : NumericalSemigroup) : RelativeIdeal H :=
  canonicalIdealAt H H.frobeniusNumber

@[simp] theorem mem_canonicalDualAt_iff (I : RelativeIdeal H) (F z : ℤ) :
    z ∈ I.canonicalDualAt F ↔ F - z ∉ I := Iff.rfl

@[simp] theorem mem_canonicalIdealAt_iff (H : NumericalSemigroup) (F z : ℤ) :
    z ∈ canonicalIdealAt H F ↔ F - z ∉ H.asRelativeIdeal := Iff.rfl

/-- The paper definition `K_H - I` has the reflection-complement membership
characterization used by `canonicalDualAt`. -/
theorem mem_canonicalIdealAt_idealDifference_iff
    (I : RelativeIdeal H) (F z : ℤ) :
    z ∈ (canonicalIdealAt H F).idealDifference I ↔ F - z ∉ I := by
  constructor
  · intro hdiff hmem
    have hk := hdiff (F - z) hmem
    change F - (z + (F - z)) ∉ H.asRelativeIdeal at hk
    apply hk
    convert (show (0 : ℤ) ∈ H.asRelativeIdeal from ⟨0, H.zero_mem, rfl⟩) using 1 <;> omega
  · intro hnot x hx
    change F - (z + x) ∉ H.asRelativeIdeal
    rintro ⟨n, hn, heq⟩
    apply hnot
    have hmem := I.add_mem_nat hx hn
    convert hmem using 1 <;> omega

/-- Equality between the ideal-difference definition `K_H - I` and the direct
reflection-complement construction. -/
theorem canonicalIdealAt_idealDifference_eq_canonicalDualAt
    (I : RelativeIdeal H) (F : ℤ) :
    (canonicalIdealAt H F).idealDifference I = I.canonicalDualAt F := by
  ext z
  exact I.mem_canonicalIdealAt_idealDifference_iff F z

/-- The standard canonical dual, reflected about the Frobenius number. -/
noncomputable def canonicalDual (I : RelativeIdeal H) : RelativeIdeal H :=
  I.canonicalDualAt H.frobeniusNumber

@[simp] theorem mem_canonicalDual_iff (I : RelativeIdeal H) (z : ℤ) :
    z ∈ I.canonicalDual ↔ H.frobeniusNumber - z ∉ I := Iff.rfl

/-- Membership-level involutivity of the canonical dual. -/
theorem mem_canonicalDualAt_canonicalDualAt_iff
    (I : RelativeIdeal H) (F z : ℤ) :
    z ∈ (I.canonicalDualAt F).canonicalDualAt F ↔ z ∈ I := by
  change (¬(F - (F - z) ∉ I)) ↔ z ∈ I
  simp only [not_not]
  constructor <;> intro hmem
  · convert hmem using 1 <;> omega
  · convert hmem using 1 <;> omega

/-- Minimal generators of the dual correspond to pseudo-Frobenius elements
under reflection about `F`. -/
theorem isMinimalGenerator_canonicalDualAt_iff
    (I : RelativeIdeal H) (F z : ℤ) :
    (I.canonicalDualAt F).IsMinimalGenerator z ↔
      I.IsPseudoFrobenius (F - z) := by
  constructor
  · rintro ⟨hz, hmin⟩
    refine ⟨hz, fun h hh hzero ↦ ?_⟩
    by_contra hnot
    apply hmin h hh hzero
    change F - (z - h) ∉ I
    have heq : F - (z - (h : ℤ)) = F - z + h := by omega
    rw [heq]
    exact hnot
  · rintro ⟨hnot, hadd⟩
    refine ⟨hnot, fun h hh hzero hmem ↦ ?_⟩
    have hdualNot : F - (z - h) ∉ I := hmem
    apply hdualNot
    have := hadd h hh hzero
    convert this using 1 <;> omega

/-- Pseudo-Frobenius elements of the dual correspond to minimal generators
under reflection about `F`. -/
theorem isPseudoFrobenius_canonicalDualAt_iff
    (I : RelativeIdeal H) (F f : ℤ) :
    (I.canonicalDualAt F).IsPseudoFrobenius f ↔
      I.IsMinimalGenerator (F - f) := by
  constructor
  · rintro ⟨hf, hadd⟩
    refine ⟨?_, fun h hh hzero hmem ↦ ?_⟩
    · by_contra hnot
      apply hf
      exact hnot
    · have hdual := hadd h hh hzero
      apply hdual
      convert hmem using 1 <;> omega
  · rintro ⟨hmem, hmin⟩
    refine ⟨?_, fun h hh hzero ↦ ?_⟩
    · intro hf
      exact hf hmem
    · change F - (f + h) ∉ I
      have hnot := hmin h hh hzero
      have heq : F - (f + (h : ℤ)) = F - f - h := by omega
      rw [heq]
      exact hnot

/-- Canonical duality exchanges generator number and type. -/
theorem generatorCount_canonicalDualAt (I : RelativeIdeal H) (F : ℤ) :
    (I.canonicalDualAt F).generatorCount = I.idealType := by
  classical
  let E : {z // (I.canonicalDualAt F).IsMinimalGenerator z} ≃
      {f // I.IsPseudoFrobenius f} :=
    { toFun := fun z ↦ ⟨F - z, (I.isMinimalGenerator_canonicalDualAt_iff F z).1 z.property⟩
      invFun := fun f ↦ ⟨F - f, (I.isMinimalGenerator_canonicalDualAt_iff F (F - f)).2
        (by simpa using f.property)⟩
      left_inv := fun z ↦ by
        apply Subtype.ext
        change F - (F - (z : ℤ)) = z
        omega
      right_inv := fun f ↦ by
        apply Subtype.ext
        change F - (F - (f : ℤ)) = f
        omega }
  exact Nat.card_congr E

/-- Canonical duality also exchanges type and generator number in the other
direction. -/
theorem idealType_canonicalDualAt (I : RelativeIdeal H) (F : ℤ) :
    (I.canonicalDualAt F).idealType = I.generatorCount := by
  classical
  let E : {f // (I.canonicalDualAt F).IsPseudoFrobenius f} ≃
      {z // I.IsMinimalGenerator z} :=
    { toFun := fun f ↦ ⟨F - f, (I.isPseudoFrobenius_canonicalDualAt_iff F f).1 f.property⟩
      invFun := fun z ↦ ⟨F - z, (I.isPseudoFrobenius_canonicalDualAt_iff F (F - z)).2
        (by simpa using z.property)⟩
      left_inv := fun f ↦ by
        apply Subtype.ext
        change F - (F - (f : ℤ)) = f
        omega
      right_inv := fun z ↦ by
        apply Subtype.ext
        change F - (F - (z : ℤ)) = z
        omega }
  exact Nat.card_congr E

/-- For the standard canonical dual, generator number equals the original
type. -/
theorem generatorCount_canonicalDual (I : RelativeIdeal H) :
    I.canonicalDual.generatorCount = I.idealType :=
  I.generatorCount_canonicalDualAt H.frobeniusNumber

/-- For the standard canonical dual, type equals the original generator
number. -/
theorem idealType_canonicalDual (I : RelativeIdeal H) :
    I.canonicalDual.idealType = I.generatorCount :=
  I.idealType_canonicalDualAt H.frobeniusNumber

/-- The canonical-dual two-sided estimate, written without division. -/
theorem generatorCount_le_two_mul_idealType_and_idealType_le
    (I : RelativeIdeal H) (a b c : ℕ)
    (hmin : H.IsMinimallyGeneratedByThree a b c) (F : ℤ) :
    I.generatorCount ≤ 2 * I.idealType ∧
      I.idealType ≤ 2 * I.generatorCount := by
  constructor
  · have hdual := (I.canonicalDualAt F).idealType_le_two_mul_generatorCount a b c hmin
    simpa [I.idealType_canonicalDualAt F, I.generatorCount_canonicalDualAt F] using hdual
  · exact I.idealType_le_two_mul_generatorCount a b c hmin

/-- **NS25 Milestone B (inequality).** Canonical duality and Milestone A give
the two-sided generator/type comparison.  The left half is written as the
equivalent division-free inequality `μ_H(I) ≤ 2 t(I)`. -/
theorem canonicalDual_twoSided_bound
    (I : RelativeIdeal H) (a b c : ℕ)
    (hmin : H.IsMinimallyGeneratedByThree a b c) :
    I.generatorCount ≤ 2 * I.idealType ∧
      I.idealType ≤ 2 * I.generatorCount :=
  I.generatorCount_le_two_mul_idealType_and_idealType_le
    a b c hmin H.frobeniusNumber

end RelativeIdeal
end NS25Lean
