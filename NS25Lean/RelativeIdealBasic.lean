/-
Copyright (c) 2026 Keisuke Sato. All rights reserved.
Authors: Keisuke Sato
-/
import NS25Lean.NumericalSemigroupBasic
import Mathlib.Order.Bounds.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option linter.style.header false

/-!
# Relative ideals of numerical semigroups

A relative ideal is represented as a nonempty, lower-bounded subset of `ℤ`
stable under addition by the numerical semigroup.  This is the minimal concrete
layer needed for the Apéry-residue construction.
-/

namespace NS25Lean

/-- A nonempty lower-bounded subset of `ℤ`, stable under addition by `H`. -/
structure RelativeIdeal (H : NumericalSemigroup) where
  carrier : Set ℤ
  nonempty : carrier.Nonempty
  bddBelow : BddBelow carrier
  add_mem : ∀ {x : ℤ} {h : ℕ}, x ∈ carrier → h ∈ H → x + h ∈ carrier

namespace RelativeIdeal

variable {H : NumericalSemigroup}

instance : Membership ℤ (RelativeIdeal H) := ⟨fun I x => x ∈ I.carrier⟩

@[simp] theorem mem_carrier {I : RelativeIdeal H} {x : ℤ} :
    x ∈ I.carrier ↔ x ∈ I := Iff.rfl

/-- Relative ideals are determined by their integer membership predicates. -/
@[ext] theorem ext {I J : RelativeIdeal H} (h : ∀ x : ℤ, x ∈ I ↔ x ∈ J) : I = J := by
  cases I with
  | mk carrierI nonemptyI bddBelowI addMemI =>
      cases J with
      | mk carrierJ nonemptyJ bddBelowJ addMemJ =>
          have hcarrier : carrierI = carrierJ := Set.ext h
          subst carrierJ
          rfl

theorem add_mem_nat (I : RelativeIdeal H) {x : ℤ} {h : ℕ}
    (hx : x ∈ I) (hh : h ∈ H) : x + h ∈ I :=
  I.add_mem hx hh

/-- Every relative ideal contains all sufficiently large integers. -/
theorem exists_tail (I : RelativeIdeal H) :
    ∃ threshold : ℤ, ∀ z : ℤ, threshold ≤ z → z ∈ I := by
  obtain ⟨x, hx⟩ := I.nonempty
  obtain ⟨conductor, hconductor⟩ := H.exists_conductor
  refine ⟨x + conductor, fun z hz ↦ ?_⟩
  let h : ℕ := (z - x).toNat
  have hnonneg : (0 : ℤ) ≤ z - x := by omega
  have hcast : (h : ℤ) = z - x := Int.toNat_of_nonneg hnonneg
  have hc : conductor ≤ h := by
    have hcInt : (conductor : ℤ) ≤ (h : ℤ) := by rw [hcast]; omega
    exact_mod_cast hcInt
  have hh : h ∈ H := hconductor h hc
  have hmem := I.add_mem_nat hx hh
  convert hmem using 1 <;> omega

/-- Translate a relative ideal by an integer. -/
def translate (I : RelativeIdeal H) (z : ℤ) : RelativeIdeal H where
  carrier := {x | x - z ∈ I}
  nonempty := by
    obtain ⟨x, hx⟩ := I.nonempty
    exact ⟨x + z, by simpa using hx⟩
  bddBelow := by
    obtain ⟨L, hL⟩ := I.bddBelow
    refine ⟨L + z, ?_⟩
    intro x hx
    have h := hL hx
    omega
  add_mem := by
    intro x h hx hh
    have hmem := I.add_mem hx hh
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmem

@[simp] theorem mem_translate_iff (I : RelativeIdeal H) (z x : ℤ) :
    x ∈ I.translate z ↔ x - z ∈ I := Iff.rfl

/-- Minimality with respect to subtraction by a nonzero semigroup element. -/
def IsMinimalGenerator (I : RelativeIdeal H) (x : ℤ) : Prop :=
  x ∈ I ∧ ∀ h : ℕ, h ∈ H → h ≠ 0 → x - h ∉ I

/-- The set of minimal `H`-ideal generators. -/
def minimalGenerators (I : RelativeIdeal H) : Set ℤ :=
  {x | I.IsMinimalGenerator x}

/-- For a displayed positive three-generator presentation, it suffices to test
minimality against the three displayed generators. -/
theorem isMinimalGenerator_iff_sub_generators
    (I : RelativeIdeal H) {a b c : ℕ}
    (hgen : H.IsGeneratedByThree a b c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (x : ℤ) :
    I.IsMinimalGenerator x ↔
      x ∈ I ∧ x - a ∉ I ∧ x - b ∉ I ∧ x - c ∉ I := by
  have haH : a ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  have hbH : b ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  have hcH : c ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  constructor
  · intro hmin
    exact ⟨hmin.1, hmin.2 a haH ha, hmin.2 b hbH hb, hmin.2 c hcH hc⟩
  · rintro ⟨hx, hsuba, hsubb, hsubc⟩
    refine ⟨hx, fun h hh hzero ↦ ?_⟩
    have hclosure : h ∈ AddSubmonoid.closure {a, b, c} :=
      (NumericalSemigroup.mem_generatedByThree_iff hgen).1 hh
    have hind : h = 0 ∨ x - h ∉ I := by
      induction hclosure using AddSubmonoid.closure_induction with
      | mem y hy =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · exact Or.inr hsuba
          · exact Or.inr hsubb
          · exact Or.inr hsubc
      | zero => exact Or.inl rfl
      | add m n hm hn ihm ihn =>
          have hmH : m ∈ H :=
            (NumericalSemigroup.mem_generatedByThree_iff hgen).2 hm
          have hnH : n ∈ H :=
            (NumericalSemigroup.mem_generatedByThree_iff hgen).2 hn
          by_cases hmzero : m = 0
          · subst m
            by_cases hnzero : n = 0
            · subst n
              exact Or.inl rfl
            · simpa using ihn hnH hnzero
          · right
            intro hbad
            rcases ihm hmH hmzero with ihmzero | ihmnot
            · exact hmzero ihmzero
            · apply ihmnot
              have hadd := I.add_mem_nat hbad hnH
              convert hadd using 1 <;> omega
    exact hind.resolve_left hzero

/-- Generator count. Finiteness of this subtype will be proved in the Apéry layer. -/
noncomputable def generatorCount (I : RelativeIdeal H) : ℕ :=
  Nat.card {x // I.IsMinimalGenerator x}

/-- A pseudo-Frobenius element of a relative ideal. -/
def IsPseudoFrobenius (I : RelativeIdeal H) (f : ℤ) : Prop :=
  f ∉ I ∧ ∀ h : ℕ, h ∈ H → h ≠ 0 → f + h ∈ I

/-- The pseudo-Frobenius set of a relative ideal. -/
def pseudoFrobeniusSet (I : RelativeIdeal H) : Set ℤ :=
  {f | I.IsPseudoFrobenius f}

/-- For a displayed positive three-generator presentation, the
pseudo-Frobenius condition only needs to be checked on the three generators. -/
theorem isPseudoFrobenius_iff_add_generators
    (I : RelativeIdeal H) {a b c : ℕ}
    (hgen : H.IsGeneratedByThree a b c) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (f : ℤ) :
    I.IsPseudoFrobenius f ↔
      f ∉ I ∧ f + a ∈ I ∧ f + b ∈ I ∧ f + c ∈ I := by
  have haH : a ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  have hbH : b ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  have hcH : c ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  constructor
  · intro hpf
    exact ⟨hpf.1, hpf.2 a haH ha, hpf.2 b hbH hb, hpf.2 c hcH hc⟩
  · rintro ⟨hnot, hadda, haddb, haddc⟩
    refine ⟨hnot, fun h hh hzero ↦ ?_⟩
    have hclosure : h ∈ AddSubmonoid.closure {a, b, c} :=
      (NumericalSemigroup.mem_generatedByThree_iff hgen).1 hh
    have hind : h = 0 ∨ f + h ∈ I := by
      induction hclosure using AddSubmonoid.closure_induction with
      | mem y hy =>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · exact Or.inr hadda
          · exact Or.inr haddb
          · exact Or.inr haddc
      | zero => exact Or.inl rfl
      | add m n hm hn ihm ihn =>
          have hmH : m ∈ H :=
            (NumericalSemigroup.mem_generatedByThree_iff hgen).2 hm
          have hnH : n ∈ H :=
            (NumericalSemigroup.mem_generatedByThree_iff hgen).2 hn
          by_cases hmzero : m = 0
          · subst m
            by_cases hnzero : n = 0
            · subst n
              exact Or.inl rfl
            · simpa using ihn hnH hnzero
          · right
            rcases ihm hmH hmzero with ihmzero | ihmem
            · exact (hmzero ihmzero).elim
            · have hadd := I.add_mem_nat ihmem hnH
              convert hadd using 1 <;> omega
    exact hind.resolve_left hzero

/-- Relative-ideal type. Finiteness will be established before this count is used. -/
noncomputable def idealType (I : RelativeIdeal H) : ℕ :=
  Nat.card {f // I.IsPseudoFrobenius f}

/-- Minimal generators are carried to minimal generators by translation. -/
theorem isMinimalGenerator_translate_add (I : RelativeIdeal H) (z x : ℤ) :
    (I.translate z).IsMinimalGenerator (x + z) ↔ I.IsMinimalGenerator x := by
  constructor
  · rintro ⟨hmem, hmin⟩
    constructor
    · simpa using hmem
    · intro h hh h0 hx
      apply hmin h hh h0
      rw [mem_translate_iff]
      convert hx using 1 <;> omega
  · rintro ⟨hmem, hmin⟩
    constructor
    · simpa using hmem
    · intro h hh h0 hx
      apply hmin h hh h0
      rw [mem_translate_iff] at hx
      convert hx using 1 <;> omega

/-- Pseudo-Frobenius elements are carried to pseudo-Frobenius elements by translation. -/
theorem isPseudoFrobenius_translate_add (I : RelativeIdeal H) (z f : ℤ) :
    (I.translate z).IsPseudoFrobenius (f + z) ↔ I.IsPseudoFrobenius f := by
  constructor
  · rintro ⟨hnot, hadd⟩
    constructor
    · intro hf
      apply hnot
      simpa using hf
    · intro h hh h0
      have hm := hadd h hh h0
      rw [mem_translate_iff] at hm
      convert hm using 1 <;> omega
  · rintro ⟨hnot, hadd⟩
    constructor
    · intro hf
      apply hnot
      simpa using hf
    · intro h hh h0
      rw [mem_translate_iff]
      have hm := hadd h hh h0
      convert hm using 1 <;> omega

/-- Translation preserves the number of minimal generators. -/
theorem generatorCount_translate (I : RelativeIdeal H) (z : ℤ) :
    (I.translate z).generatorCount = I.generatorCount := by
  let E : {x // I.IsMinimalGenerator x} ≃
      {x // (I.translate z).IsMinimalGenerator x} :=
    { toFun := fun x => ⟨x + z, (I.isMinimalGenerator_translate_add z x).2 x.property⟩
      invFun := fun x => ⟨x - z, by
        apply (I.isMinimalGenerator_translate_add z (x - z)).1
        simpa using x.property⟩
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun x => by apply Subtype.ext; simp }
  exact (Nat.card_congr E).symm

/-- Translation preserves relative-ideal type. -/
theorem idealType_translate (I : RelativeIdeal H) (z : ℤ) :
    (I.translate z).idealType = I.idealType := by
  let E : {f // I.IsPseudoFrobenius f} ≃
      {f // (I.translate z).IsPseudoFrobenius f} :=
    { toFun := fun f => ⟨f + z, (I.isPseudoFrobenius_translate_add z f).2 f.property⟩
      invFun := fun f => ⟨f - z, by
        apply (I.isPseudoFrobenius_translate_add z (f - z)).1
        simpa using f.property⟩
      left_inv := fun f => by apply Subtype.ext; simp
      right_inv := fun f => by apply Subtype.ext; simp }
  exact (Nat.card_congr E).symm

end RelativeIdeal
end NS25Lean
