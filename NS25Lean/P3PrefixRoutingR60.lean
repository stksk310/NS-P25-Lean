import NS25Lean.P2BranchBFinalRepairSymmetric

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R60

open CombinatorialCore

variable {H : NumericalSemigroup}

def birthIdeal (H : NumericalSemigroup) (m q : ℕ) (hq : 0 < q) : RelativeIdeal H :=
  L5A2BFinalRepair.principalPrefixIdeal H m (q + 1) (by omega)

@[simp] theorem birthIdeal_carrier (H : NumericalSemigroup) (m q : ℕ) (hq : 0 < q) :
    (birthIdeal H m q hq).carrier = L5A2B4AR1.prefixCarrier H m (q + 1) := rfl

def idealData (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) : ResidueData (ZMod a) :=
  (I.toAperyStepData a b c hb hc).toResidueData
    (I.toAperyStepData_isValid a b c hb hc)

theorem aperyRepresentative_eq_of_mem_not_mem_sub
    (I : RelativeIdeal H) (a : ℕ) [NeZero a] (ha : a ∈ H)
    (x : ℤ) (hx : x ∈ I) (hprev : x - a ∉ I) :
    I.aperyRepresentative a (x : ZMod a) = x := by
  have hle := I.aperyRepresentative_le a (x : ZMod a) hx rfl
  obtain ⟨n, hn⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq a hle (by
    rw [I.aperyRepresentative_mod])
  cases n with
  | zero => simpa using hn.symm
  | succ k =>
    have hak : a * k ∈ H := by
      simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem ha k
    have hmem := I.add_mem_nat (I.aperyRepresentative_mem a (x : ZMod a)) hak
    apply (hprev ?_).elim
    convert hmem using 1
    push_cast at hn ⊢
    nlinarith

theorem semigroup_apery_shift_mem_iff
    (H : NumericalSemigroup) (a : ℕ) [NeZero a] (ha : a ∈ H)
    (x : ℤ) (hx : H.asRelativeIdeal.aperyRepresentative a (x : ZMod a) = x)
    (n : ℤ) : x + (a : ℤ) * n ∈ H.asRelativeIdeal ↔ 0 ≤ n := by
  have haPos : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  constructor
  · intro hmem
    have hle := H.asRelativeIdeal.aperyRepresentative_le a (x : ZMod a) hmem (by simp)
    rw [hx] at hle
    nlinarith
  · intro hn
    have hak : a * n.toNat ∈ H := by
      simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem ha n.toNat
    have hm := H.asRelativeIdeal.add_mem_nat
      (H.asRelativeIdeal.aperyRepresentative_mem a (x : ZMod a)) hak
    simpa [hx, Nat.cast_mul, Int.toNat_of_nonneg hn] using hm

@[simp] theorem idealData_branchTarget
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a] (hb : b ∈ H) (hc : c ∈ H)
    (x : ℤ) : (idealData I a b c hb hc).branchTarget (x : ZMod a) =
      ((x + b + c : ℤ) : ZMod a) := by
  simp [idealData, ResidueData.branchTarget, AperyStepData.toResidueData,
    RelativeIdeal.toAperyStepData]

theorem sourceTargetBranch_iff_of_stencil
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a] (hb : b ∈ H) (hc : c ∈ H)
    (x : ℤ) (k : ℕ)
    (h0 : I.aperyRepresentative a (x : ZMod a) = x + a * k)
    (hb0 : I.aperyRepresentative a ((x + b : ℤ) : ZMod a) = x + b + a * k)
    (hc0 : I.aperyRepresentative a ((x + c : ℤ) : ZMod a) = x + c + a * k)
    (hbc : I.aperyRepresentative a ((x + b + c : ℤ) : ZMod a) = x + b + c) :
    L5A2C4I.ResidueData.SourceTargetBranch (idealData I a b c hb hc) (x : ZMod a) ↔
      0 < k := by
  have haPos : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have huEq := I.apery_step_eq a b hb (x : ZMod a)
  have hvEq := I.apery_step_eq a c hc (x : ZMod a)
  have hcrossEq := I.apery_step_eq a b hb ((x + c : ℤ) : ZMod a)
  have hvCrossEq := I.apery_step_eq a c hc ((x + b : ℤ) : ZMod a)
  simp only [Int.cast_add, Int.cast_natCast] at h0 hb0 hc0 hbc hcrossEq hvCrossEq
  rw [h0, hb0] at huEq
  rw [h0, hc0] at hvEq
  rw [hc0, show (x : ZMod a) + c + b = (x : ZMod a) + b + c by abel, hbc] at hcrossEq
  rw [hb0, hbc] at hvCrossEq
  have hu : I.aperyStepQuotient a b hb (x : ZMod a) = 0 := by
    have : (I.aperyStepQuotient a b hb (x : ZMod a) : ℤ) = 0 := by nlinarith [huEq]
    exact_mod_cast this
  have hv : I.aperyStepQuotient a c hc (x : ZMod a) = 0 := by
    have : (I.aperyStepQuotient a c hc (x : ZMod a) : ℤ) = 0 := by nlinarith [hvEq]
    exact_mod_cast this
  have huc : I.aperyStepQuotient a b hb ((x : ZMod a) + c) = k := by
    have : (I.aperyStepQuotient a b hb ((x : ZMod a) + c) : ℤ) = k := by nlinarith [hcrossEq]
    exact_mod_cast this
  have hvb : I.aperyStepQuotient a c hc ((x : ZMod a) + b) = k := by
    have : (I.aperyStepQuotient a c hc ((x : ZMod a) + b) : ℤ) = k := by nlinarith [hvCrossEq]
    exact_mod_cast this
  rw [L5A2C4I.ResidueData.sourceTargetBranch_iff_positive_cross]
  change (I.aperyStepQuotient a b hb (x : ZMod a) = 0 ∧
      I.aperyStepQuotient a c hc (x : ZMod a) = 0) ∧
      I.aperyStepQuotient a b hb ((x : ZMod a) + c) =
        I.aperyStepQuotient a c hc ((x : ZMod a) + b) ∧
      0 < I.aperyStepQuotient a b hb ((x : ZMod a) + c) ↔ 0 < k
  rw [hu, hv, huc, hvb]
  simp

end NS25Lean.P3R60



