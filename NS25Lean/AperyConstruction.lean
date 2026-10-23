/-
Copyright (c) 2026 Keisuke Sato. All rights reserved.
Authors: Keisuke Sato
-/
import NS25Lean.AperyBridge
import NS25Lean.RelativeIdealBasic
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.ZMod.Basic

set_option linter.style.header false

/-!
# Construction of Apéry representatives for relative ideals

For a positive semigroup element `a`, every residue class modulo `a` meets a
relative ideal.  Since the ideal is bounded below, each such fiber has a least
integer.  This file packages those least elements as the Apéry representative
function needed by the step-data bridge.
-/

namespace NS25Lean
namespace RelativeIdeal

variable {H : NumericalSemigroup}

/-- The elements of `I` lying in a fixed residue class modulo `a`. -/
def residueFiber (I : RelativeIdeal H) (a : ℕ) [NeZero a] (r : ZMod a) : Set ℤ :=
  {x | x ∈ I ∧ (x : ZMod a) = r}

/-- Every residue class modulo a positive modulus meets a relative ideal. -/
theorem residueFiber_nonempty (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (r : ZMod a) : (I.residueFiber a r).Nonempty := by
  obtain ⟨x, hx⟩ := I.nonempty
  obtain ⟨conductor, hconductor⟩ := H.exists_conductor
  let delta : ZMod a := r - (x : ZMod a)
  let h : ℕ := delta.val + a * conductor
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hlarge : conductor ≤ h := by
    have hmul : conductor ≤ a * conductor := Nat.le_mul_of_pos_left conductor ha
    exact hmul.trans (Nat.le_add_left (a * conductor) delta.val)
  have hh : h ∈ H := hconductor h hlarge
  refine ⟨x + h, I.add_mem_nat hx hh, ?_⟩
  rw [Int.cast_add, Int.cast_natCast]
  rw [show (h : ZMod a) = delta by
    simp [h, delta]]
  simp [delta]

/-- Ordered congruent integers differ by a nonnegative multiple of the modulus. -/
theorem exists_eq_add_mul_of_le_of_modEq (a : ℕ) [NeZero a] {w z : ℤ}
    (hle : w ≤ z) (hmod : (z : ZMod a) = (w : ZMod a)) :
    ∃ n : ℕ, z = w + a * n := by
  have hdvd : (a : ℤ) ∣ z - w :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub w z a).mp hmod.symm
  obtain ⟨k, hk⟩ := hdvd
  have ha : (0 : ℤ) < a := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have hmul : (0 : ℤ) ≤ (a : ℤ) * k := by
    rw [← hk]
    exact sub_nonneg.mpr hle
  have hk_nonneg : (0 : ℤ) ≤ k := nonneg_of_mul_nonneg_right hmul ha
  refine ⟨k.toNat, ?_⟩
  have hk_cast : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
  calc
    z = w + (z - w) := by omega
    _ = w + (a : ℤ) * k := by rw [hk]
    _ = w + (a : ℤ) * (k.toNat : ℤ) := by rw [hk_cast]
    _ = w + (a * k.toNat : ℕ) := by norm_num

/-- Each residue fiber inherits the lower bound of the whole relative ideal. -/
theorem residueFiber_bddBelow (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (r : ZMod a) : BddBelow (I.residueFiber a r) := by
  obtain ⟨lower, hlower⟩ := I.bddBelow
  exact ⟨lower, fun _ hx ↦ hlower hx.1⟩

/-- A residue fiber has a least integer. -/
theorem exists_isLeast_residueFiber (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (r : ZMod a) : ∃ x : ℤ, IsLeast (I.residueFiber a r) x := by
  obtain ⟨lower, hlower⟩ := I.residueFiber_bddBelow a r
  obtain ⟨x, hx, hleast⟩ := Int.exists_least_of_bdd
    (P := fun x ↦ x ∈ I.residueFiber a r) ⟨lower, hlower⟩
    (I.residueFiber_nonempty a r)
  exact ⟨x, hx, hleast⟩

/-- The least representative of `I` in residue class `r` modulo `a`. -/
noncomputable def aperyRepresentative (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (r : ZMod a) : ℤ :=
  Classical.choose (I.exists_isLeast_residueFiber a r)

theorem aperyRepresentative_isLeast (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (r : ZMod a) : IsLeast (I.residueFiber a r) (I.aperyRepresentative a r) :=
  Classical.choose_spec (I.exists_isLeast_residueFiber a r)

theorem aperyRepresentative_mem (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (r : ZMod a) : I.aperyRepresentative a r ∈ I :=
  (I.aperyRepresentative_isLeast a r).1.1

theorem aperyRepresentative_mod (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (r : ZMod a) : (I.aperyRepresentative a r : ZMod a) = r :=
  (I.aperyRepresentative_isLeast a r).1.2

theorem aperyRepresentative_le (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (r : ZMod a) {x : ℤ} (hx : x ∈ I) (hmod : (x : ZMod a) = r) :
    I.aperyRepresentative a r ≤ x :=
  (I.aperyRepresentative_isLeast a r).2 ⟨hx, hmod⟩

/-- An Apéry representative cannot be moved backwards by one modulus while
remaining in the relative ideal. -/
theorem aperyRepresentative_sub_modulus_not_mem
    (I : RelativeIdeal H) (a : ℕ) [NeZero a] (r : ZMod a) :
    I.aperyRepresentative a r - a ∉ I := by
  intro hmem
  have hmod : ((I.aperyRepresentative a r - a : ℤ) : ZMod a) = r := by
    rw [Int.cast_sub, Int.cast_natCast, I.aperyRepresentative_mod,
      ZMod.natCast_self, sub_zero]
  have hle := I.aperyRepresentative_le a r hmem hmod
  have ha : (0 : ℤ) < a := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  omega

/-- Adding a semigroup element to an Apéry representative produces a
nonnegative integral step quotient. -/
theorem exists_apery_step (I : RelativeIdeal H) (a h : ℕ) [NeZero a]
    (hh : h ∈ H) (r : ZMod a) :
    ∃ n : ℕ, I.aperyRepresentative a r + h =
      I.aperyRepresentative a (r + h) + a * n := by
  have hmem : I.aperyRepresentative a r + h ∈ I :=
    I.add_mem_nat (I.aperyRepresentative_mem a r) hh
  have hmod : ((I.aperyRepresentative a r + h : ℤ) : ZMod a) = r + h := by
    rw [Int.cast_add, Int.cast_natCast, I.aperyRepresentative_mod]
  have hle : I.aperyRepresentative a (r + h) ≤ I.aperyRepresentative a r + h :=
    I.aperyRepresentative_le a (r + h) hmem hmod
  exact exists_eq_add_mul_of_le_of_modEq a hle (by
    rw [hmod, I.aperyRepresentative_mod])

/-- The nonnegative quotient in the Apéry step equation. -/
noncomputable def aperyStepQuotient (I : RelativeIdeal H) (a h : ℕ) [NeZero a]
    (hh : h ∈ H) (r : ZMod a) : ℕ :=
  Classical.choose (I.exists_apery_step a h hh r)

theorem apery_step_eq (I : RelativeIdeal H) (a h : ℕ) [NeZero a]
    (hh : h ∈ H) (r : ZMod a) :
    I.aperyRepresentative a r + h = I.aperyRepresentative a (r + h) +
      a * I.aperyStepQuotient a h hh r :=
  Classical.choose_spec (I.exists_apery_step a h hh r)

/-- A zero Apéry step is exactly the statement that the representative at the
head can be moved backwards by that semigroup element while staying in `I`. -/
theorem aperyStepQuotient_eq_zero_iff_sub_mem
    (I : RelativeIdeal H) (a h : ℕ) [NeZero a] (hh : h ∈ H) (r : ZMod a) :
    I.aperyStepQuotient a h hh r = 0 ↔
      I.aperyRepresentative a (r + h) - h ∈ I := by
  constructor
  · intro hzero
    have hstep := I.apery_step_eq a h hh r
    rw [hzero] at hstep
    have heq : I.aperyRepresentative a (r + h) - h =
        I.aperyRepresentative a r := by
      norm_num at hstep ⊢
      omega
    rw [heq]
    exact I.aperyRepresentative_mem a r
  · intro hmem
    have hmod : ((I.aperyRepresentative a (r + h) - h : ℤ) : ZMod a) = r := by
      rw [Int.cast_sub, Int.cast_natCast, I.aperyRepresentative_mod]
      simp
    have hle : I.aperyRepresentative a r ≤ I.aperyRepresentative a (r + h) - h :=
      I.aperyRepresentative_le a r hmem hmod
    have hstep := I.apery_step_eq a h hh r
    have hprod : (a : ℤ) * (I.aperyStepQuotient a h hh r : ℤ) = 0 := by
      have hprod_nonpos : (a : ℤ) * (I.aperyStepQuotient a h hh r : ℤ) ≤ 0 := by
        omega
      exact le_antisymm hprod_nonpos (mul_nonneg (Int.natCast_nonneg a)
        (Int.natCast_nonneg (I.aperyStepQuotient a h hh r)))
    have ha : (a : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne a
    exact_mod_cast (mul_eq_zero.mp hprod).resolve_left ha

/-- A nonzero Apéry step is exactly what makes `lambda r - a + h` lie in the
relative ideal. -/
theorem aperyStepQuotient_ne_zero_iff_sub_modulus_add_mem
    (I : RelativeIdeal H) (a h : ℕ) [NeZero a] (haH : a ∈ H) (hh : h ∈ H)
    (r : ZMod a) :
    I.aperyStepQuotient a h hh r ≠ 0 ↔
      I.aperyRepresentative a r - a + h ∈ I := by
  constructor
  · intro hnonzero
    cases hq : I.aperyStepQuotient a h hh r with
    | zero => exact (hnonzero hq).elim
    | succ k =>
        have hakH : a * k ∈ H := by
          have := H.toAddSubmonoid.nsmul_mem haH k
          simpa [nsmul_eq_mul, Nat.mul_comm] using this
        have hmem : I.aperyRepresentative a (r + h) + a * k ∈ I :=
          I.add_mem_nat (I.aperyRepresentative_mem a (r + h)) hakH
        have hstep := I.apery_step_eq a h hh r
        rw [hq] at hstep
        have heq : I.aperyRepresentative a r - a + h =
            I.aperyRepresentative a (r + h) + a * k := by
          push_cast at hstep ⊢
          rw [mul_add] at hstep
          omega
        rw [heq]
        exact hmem
  · intro hmem hzero
    have hstep := I.apery_step_eq a h hh r
    rw [hzero] at hstep
    norm_num at hstep
    apply I.aperyRepresentative_sub_modulus_not_mem a (r + h)
    have heq : I.aperyRepresentative a (r + h) - a =
        I.aperyRepresentative a r - a + h := by omega
    rw [heq]
    exact hmem

/-- Concrete Apéry step data attached to two chosen semigroup elements. -/
noncomputable def toAperyStepData (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) : AperyStepData (ZMod a) where
  modulus := a
  b := b
  c := c
  bValue := b
  cValue := c
  lambda := I.aperyRepresentative a
  u := I.aperyStepQuotient a b hb
  v := I.aperyStepQuotient a c hc

theorem toAperyStepData_isValid (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) : (I.toAperyStepData a b c hb hc).IsValid where
  modulus_pos := Nat.pos_of_ne_zero (NeZero.ne a)
  step_b := I.apery_step_eq a b hb
  step_c := I.apery_step_eq a c hc

/-- In the concrete Apéry graph, sources are exactly the representatives that
cannot be moved backwards by either chosen semigroup element. -/
theorem concrete_isSource_iff
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a] (hb : b ∈ H) (hc : c ∈ H)
    (r : ZMod a) :
    ((I.toAperyStepData a b c hb hc).toResidueData
      (I.toAperyStepData_isValid a b c hb hc)).IsSource r ↔
      I.aperyRepresentative a r - b ∉ I ∧ I.aperyRepresentative a r - c ∉ I := by
  change
    I.aperyStepQuotient a b hb ((Equiv.addRight (b : ZMod a)).symm r) ≠ 0 ∧
      I.aperyStepQuotient a c hc ((Equiv.addRight (c : ZMod a)).symm r) ≠ 0 ↔ _
  constructor
  · rintro ⟨hu, hv⟩
    constructor
    · intro hmem
      apply hu
      apply (I.aperyStepQuotient_eq_zero_iff_sub_mem a b hb
        ((Equiv.addRight (b : ZMod a)).symm r)).2
      simpa using hmem
    · intro hmem
      apply hv
      apply (I.aperyStepQuotient_eq_zero_iff_sub_mem a c hc
        ((Equiv.addRight (c : ZMod a)).symm r)).2
      simpa using hmem
  · rintro ⟨hbnot, hcnot⟩
    constructor
    · intro hzero
      apply hbnot
      have hmem := (I.aperyStepQuotient_eq_zero_iff_sub_mem a b hb
        ((Equiv.addRight (b : ZMod a)).symm r)).1 hzero
      simpa using hmem
    · intro hzero
      apply hcnot
      have hmem := (I.aperyStepQuotient_eq_zero_iff_sub_mem a c hc
        ((Equiv.addRight (c : ZMod a)).symm r)).1 hzero
      simpa using hmem

/-- Under a positive three-generator presentation, graph sources are exactly
the Apéry representatives that are minimal ideal generators. -/
theorem concrete_isSource_iff_isMinimalGenerator
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0) (r : ZMod a) :
    ((I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)).IsSource r ↔
      I.IsMinimalGenerator (I.aperyRepresentative a r) := by
  rw [I.concrete_isSource_iff a b c hbH hcH r,
    I.isMinimalGenerator_iff_sub_generators hgen (NeZero.ne a) hb hc]
  simp [I.aperyRepresentative_mem, I.aperyRepresentative_sub_modulus_not_mem]

/-- A minimal ideal generator is the Apéry representative of its residue. -/
theorem aperyRepresentative_eq_of_isMinimalGenerator
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c) {x : ℤ} (hx : I.IsMinimalGenerator x) :
    I.aperyRepresentative a (x : ZMod a) = x := by
  have hle : I.aperyRepresentative a (x : ZMod a) ≤ x :=
    I.aperyRepresentative_le a (x : ZMod a) hx.1 rfl
  obtain ⟨n, hn⟩ := exists_eq_add_mul_of_le_of_modEq a hle (by
    rw [I.aperyRepresentative_mod])
  cases n with
  | zero => simpa using hn.symm
  | succ k =>
      have haH : a ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
        (AddSubmonoid.subset_closure (by simp))
      have hakH : a * k ∈ H := by
        have := H.toAddSubmonoid.nsmul_mem haH k
        simpa [nsmul_eq_mul, Nat.mul_comm] using this
      have hmem : I.aperyRepresentative a (x : ZMod a) + a * k ∈ I :=
        I.add_mem_nat (I.aperyRepresentative_mem a (x : ZMod a)) hakH
      have hsub : x - a ∈ I := by
        let w : ℤ := I.aperyRepresentative a (x : ZMod a)
        have hn' : x = w + (a : ℤ) * (k + 1 : ℕ) := by
          simpa [w, Nat.mul_succ] using hn
        have heq : x - a = w + (a * k : ℕ) := by
          rw [hn']
          push_cast
          rw [mul_add]
          omega
        rw [heq]
        simpa [w] using hmem
      exact (hx.2 a haH (NeZero.ne a) hsub).elim

/-- The element-level dictionary behind the concrete source-count identity.
A graph source is sent to its actual Apéry representative, and a minimal
generator is sent back to its residue class. -/
noncomputable def concreteSourceEquivMinimalGenerator
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0) :
    let D := (I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)
    {r // D.IsSource r} ≃ {x // I.IsMinimalGenerator x} := by
  let D := (I.toAperyStepData a b c hbH hcH).toResidueData
    (I.toAperyStepData_isValid a b c hbH hcH)
  exact
    { toFun := fun r ↦ ⟨I.aperyRepresentative a r,
        (I.concrete_isSource_iff_isMinimalGenerator a b c hgen hbH hcH hb hc r).1
          r.property⟩
      invFun := fun x ↦ ⟨(x : ZMod a),
        (I.concrete_isSource_iff_isMinimalGenerator a b c hgen hbH hcH hb hc
          (x : ZMod a)).2 (by
            simpa [I.aperyRepresentative_eq_of_isMinimalGenerator a b c hgen x.property]
              using x.property)⟩
      left_inv := fun r ↦ by
        apply Subtype.ext
        exact I.aperyRepresentative_mod a r
      right_inv := fun x ↦ by
        apply Subtype.ext
        exact I.aperyRepresentative_eq_of_isMinimalGenerator a b c hgen x.property }

@[simp] theorem concreteSourceEquivMinimalGenerator_apply_val
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (r : {r // ((I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)).IsSource r}) :
    (I.concreteSourceEquivMinimalGenerator a b c hgen hbH hcH hb hc r).val =
      I.aperyRepresentative a r.val := rfl

@[simp] theorem concreteSourceEquivMinimalGenerator_symm_apply_val
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0) (x : {x // I.IsMinimalGenerator x}) :
    ((I.concreteSourceEquivMinimalGenerator a b c hgen hbH hcH hb hc).symm x).val =
      (x.val : ZMod a) := rfl

/-- The source vertices of the concrete Apéry graph are in bijection with the
minimal generators of the relative ideal. -/
theorem concrete_sourceCount_eq_generatorCount
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0) :
    ((I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)).sourceCount = I.generatorCount := by
  classical
  exact Nat.card_congr
    (I.concreteSourceEquivMinimalGenerator a b c hgen hbH hcH hb hc)

/-- Under a positive three-generator presentation, graph sinks are exactly the
pseudo-Frobenius elements `lambda r - a`. -/
theorem concrete_isSink_iff_isPseudoFrobenius
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c) (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0) (r : ZMod a) :
    ((I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)).IsSink r ↔
      I.IsPseudoFrobenius (I.aperyRepresentative a r - a) := by
  change I.aperyStepQuotient a b hbH r ≠ 0 ∧
      I.aperyStepQuotient a c hcH r ≠ 0 ↔ _
  rw [I.aperyStepQuotient_ne_zero_iff_sub_modulus_add_mem a b haH hbH r,
    I.aperyStepQuotient_ne_zero_iff_sub_modulus_add_mem a c haH hcH r,
    I.isPseudoFrobenius_iff_add_generators hgen (NeZero.ne a) hb hc]
  have hnot := I.aperyRepresentative_sub_modulus_not_mem a r
  have hadda : I.aperyRepresentative a r - a + a ∈ I := by
    convert I.aperyRepresentative_mem a r using 1 <;> omega
  aesop

/-- Every pseudo-Frobenius element is uniquely `lambda r - a` in the residue
class of `f + a`. -/
theorem aperyRepresentative_sub_modulus_eq_of_isPseudoFrobenius
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c) {f : ℤ} (hf : I.IsPseudoFrobenius f) :
    I.aperyRepresentative a (f + a : ZMod a) - a = f := by
  have haH : a ∈ H := (NumericalSemigroup.mem_generatedByThree_iff hgen).2
    (AddSubmonoid.subset_closure (by simp))
  have hfa : f + a ∈ I := hf.2 a haH (NeZero.ne a)
  have hle : I.aperyRepresentative a (f + a : ZMod a) ≤ f + a :=
    I.aperyRepresentative_le a (f + a : ZMod a) hfa (by
      push_cast
      simp)
  obtain ⟨n, hn⟩ := exists_eq_add_mul_of_le_of_modEq a hle (by
    rw [I.aperyRepresentative_mod]
    push_cast
    simp)
  cases n with
  | zero =>
      norm_num at hn ⊢
      omega
  | succ k =>
      have hakH : a * k ∈ H := by
        have := H.toAddSubmonoid.nsmul_mem haH k
        simpa [nsmul_eq_mul, Nat.mul_comm] using this
      have hmem : I.aperyRepresentative a (f + a : ZMod a) + a * k ∈ I :=
        I.add_mem_nat (I.aperyRepresentative_mem a (f + a : ZMod a)) hakH
      apply (hf.1 ?_).elim
      let w : ℤ := I.aperyRepresentative a (f + a : ZMod a)
      have hn' : f + a = w + (a : ℤ) * (k + 1 : ℕ) := by
        simpa [w, Nat.mul_succ] using hn
      have heq : f = w + (a * k : ℕ) := by
        have := hn'
        push_cast at this ⊢
        rw [mul_add] at this
        omega
      rw [heq]
      simpa [w] using hmem

/-- The sink vertices of the concrete Apéry graph are in bijection with the
pseudo-Frobenius elements of the relative ideal. -/
theorem concrete_sinkCount_eq_idealType
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c) (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0) :
    ((I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)).sinkCount = I.idealType := by
  classical
  let D := (I.toAperyStepData a b c hbH hcH).toResidueData
    (I.toAperyStepData_isValid a b c hbH hcH)
  let E : {r // D.IsSink r} ≃ {f // I.IsPseudoFrobenius f} :=
    { toFun := fun r ↦ ⟨I.aperyRepresentative a r - a,
        (I.concrete_isSink_iff_isPseudoFrobenius a b c hgen haH hbH hcH hb hc r).1
          r.property⟩
      invFun := fun f ↦ ⟨(f + a : ZMod a),
        (I.concrete_isSink_iff_isPseudoFrobenius a b c hgen haH hbH hcH hb hc
          (f + a : ZMod a)).2 (by
            rw [I.aperyRepresentative_sub_modulus_eq_of_isPseudoFrobenius
              a b c hgen f.property]
            exact f.property)⟩
      left_inv := fun r ↦ by
        apply Subtype.ext
        change ((I.aperyRepresentative a (r : ZMod a) - a : ℤ) : ZMod a) +
          (a : ZMod a) = r
        rw [Int.cast_sub, Int.cast_natCast, I.aperyRepresentative_mod]
        simp
      right_inv := fun f ↦ by
        apply Subtype.ext
        exact I.aperyRepresentative_sub_modulus_eq_of_isPseudoFrobenius
          a b c hgen f.property }
  exact Nat.card_congr E

/-- The concrete Apéry system of a relative ideal satisfies the finite
sink/source inequality proved by the combinatorial core. -/
theorem apery_sinkCount_le_two_mul_sourceCount
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a] (hb : b ∈ H) (hc : c ∈ H) :
    ((I.toAperyStepData a b c hb hc).toResidueData
      (I.toAperyStepData_isValid a b c hb hc)).sinkCount ≤
      2 * ((I.toAperyStepData a b c hb hc).toResidueData
        (I.toAperyStepData_isValid a b c hb hc)).sourceCount :=
  (I.toAperyStepData a b c hb hc).sinkCount_le_two_mul_sourceCount
    (I.toAperyStepData_isValid a b c hb hc)

end RelativeIdeal
end NS25Lean
