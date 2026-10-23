import NS25Lean.P2SectorCActualRoutingCore
import Mathlib.GroupTheory.Perm.Finite

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4I

open CombinatorialCore
open L5A2C4H

namespace ResidueData

variable {R : Type*} [Fintype R] (D : ResidueData R)

/-! ### I1: the paper-exact unused-merge reverse base -/

def ExactUnusedMergeReverseBase (r : R) : Prop :=
  D.u r = D.v r ∧ 0 < D.u r ∧ D.u (D.c r) = 0 ∧ D.v (D.b r) = 0

theorem exactUnusedMergeReverseBase_iff {r : R} :
    ExactUnusedMergeReverseBase D r ↔ UnusedMergeReverseBase D r := by
  constructor
  · rintro ⟨huv, hu, huc, hvb⟩
    exact ⟨hu, huv ▸ hu, huc, hvb⟩
  · rintro ⟨hu, hv, huc, hvb⟩
    have hdiamond := D.diamond r
    rw [hvb, huc, Nat.add_zero, Nat.add_zero] at hdiamond
    exact ⟨hdiamond, hu, huc, hvb⟩

theorem exactUnusedMergeReverseBase_target_isMerge {r : R}
    (h : ExactUnusedMergeReverseBase D r) : D.IsMerge (D.branchTarget r) := by
  exact unusedMergeReverseBase_isMerge D ((exactUnusedMergeReverseBase_iff D).1 h)

/-- An exact unused-merge target is not the opposite corner of any branch.
The conclusion concerns the underlying target residue, not a tagged copy. -/
theorem exactUnusedMergeReverseBase_target_unused {r : R}
    (h : ExactUnusedMergeReverseBase D r) :
    ∀ q : R, D.IsBranch q → D.branchTarget q ≠ D.branchTarget r := by
  intro q hq heq
  have hqr : q = r := D.branchTarget_injective heq
  subst q
  exact (Nat.ne_of_gt h.2.1) hq.1

/-! ### I2: source-target branches -/

def SourceTargetBranch (r : R) : Prop :=
  D.IsBranch r ∧ D.IsSource (D.branchTarget r)

private theorem b_symm_branchTarget (r : R) :
    D.b.symm (D.branchTarget r) = D.c r := by
  apply D.b.injective
  simpa [ResidueData.branchTarget] using (D.commute r).symm

private theorem c_symm_branchTarget (r : R) :
    D.c.symm (D.branchTarget r) = D.b r := by
  simp [ResidueData.branchTarget]

theorem sourceTargetBranch_iff_positive_cross {r : R} :
    SourceTargetBranch D r ↔
      D.IsBranch r ∧ D.u (D.c r) = D.v (D.b r) ∧ 0 < D.u (D.c r) := by
  constructor
  · rintro ⟨hbranch, hsource⟩
    have hu : D.u (D.c r) ≠ 0 := by
      simpa [ResidueData.IsSource, b_symm_branchTarget D r] using hsource.1
    exact ⟨hbranch, (D.cross_eq_of_isBranch hbranch).symm, Nat.pos_of_ne_zero hu⟩
  · rintro ⟨hbranch, hcross, hpos⟩
    refine ⟨hbranch, ?_⟩
    constructor
    · simpa [ResidueData.IsSource, b_symm_branchTarget D r] using
        (Nat.ne_of_gt hpos)
    · have hv : D.v (D.b r) ≠ 0 := by
        rw [← hcross]
        exact Nat.ne_of_gt hpos
      simpa [ResidueData.IsSource, c_symm_branchTarget D r] using hv

/-! ### I3: canonical maximal positive-carry runs on a finite orbit -/

private theorem finiteOrbit_zero_exists (f : Equiv.Perm R) (w : R → ℕ)
    (r : R) (hr : w r = 0) :
    ∃ n : ℕ, 0 < n ∧ w ((f ^ n) r) = 0 := by
  refine ⟨orderOf f, orderOf_pos f, ?_⟩
  rw [pow_orderOf_eq_one]
  exact hr

noncomputable def firstZeroIndex (f : Equiv.Perm R) (w : R → ℕ)
    (r : R) (hr : w r = 0) : ℕ :=
  Nat.find (finiteOrbit_zero_exists f w r hr)

theorem firstZeroIndex_pos (f : Equiv.Perm R) (w : R → ℕ)
    (r : R) (hr : w r = 0) : 0 < firstZeroIndex f w r hr :=
  (Nat.find_spec (finiteOrbit_zero_exists f w r hr)).1

theorem firstZeroIndex_zero (f : Equiv.Perm R) (w : R → ℕ)
    (r : R) (hr : w r = 0) :
    w ((f ^ firstZeroIndex f w r hr) r) = 0 :=
  (Nat.find_spec (finiteOrbit_zero_exists f w r hr)).2

theorem firstZeroIndex_positive_before (f : Equiv.Perm R) (w : R → ℕ)
    (r : R) (hr : w r = 0) {k : ℕ} (hk : 0 < k)
    (hlt : k < firstZeroIndex f w r hr) :
    0 < w ((f ^ k) r) := by
  apply Nat.pos_of_ne_zero
  intro hz
  have hle : firstZeroIndex f w r hr ≤ k :=
    Nat.find_min' (finiteOrbit_zero_exists f w r hr) ⟨hk, hz⟩
  exact (Nat.not_lt_of_ge hle) hlt

private theorem apply_pow_pred (f : Equiv.Perm R) (r : R) {n : ℕ} (hn : 0 < n) :
    f ((f ^ (n - 1)) r) = (f ^ n) r := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp [pow_succ']

private theorem start_eq_iterate_of_endpoint_eq (f : Equiv.Perm R)
    (x y : R) {nx ny : ℕ} (hnx : 0 < nx) (hny : 0 < ny) (hle : nx ≤ ny)
    (h : (f ^ (nx - 1)) x = (f ^ (ny - 1)) y) :
    x = (f ^ (ny - nx)) y := by
  apply (f ^ (nx - 1)).injective
  rw [h]
  change (f ^ (ny - 1)) y = ((f ^ (nx - 1)) * (f ^ (ny - nx))) y
  rw [← pow_add]
  congr 2
  omega

noncomputable def firstBlockIndex {S : Type*} (f : Equiv.Perm R) (w : R → ℕ)
    (start : S → R) (hzero : ∀ s, w (start s) = 0) (s : S) : ℕ :=
  firstZeroIndex f w (start s) (hzero s)

noncomputable def firstBlockEndpoint {S : Type*} (f : Equiv.Perm R) (w : R → ℕ)
    (start : S → R) (hzero : ∀ s, w (start s) = 0) (s : S) : R :=
  (f ^ (firstBlockIndex f w start hzero s - 1)) (start s)

private theorem firstBlockIndex_gt_one {S : Type*} (f : Equiv.Perm R) (w : R → ℕ)
    (start : S → R) (hzero : ∀ s, w (start s) = 0)
    (hseed : ∀ s, 0 < w (f (start s))) (s : S) :
    1 < firstBlockIndex f w start hzero s := by
  change 1 < firstZeroIndex f w (start s) (hzero s)
  have hz := firstZeroIndex_zero f w (start s) (hzero s)
  have hp := firstZeroIndex_pos f w (start s) (hzero s)
  by_contra h
  have heq : firstZeroIndex f w (start s) (hzero s) = 1 := by omega
  rw [heq] at hz
  have hz' : w (f (start s)) = 0 := by simpa using hz
  exact (Nat.ne_of_gt (hseed s)) hz'

/-- The endpoint itself remembers the unique start of its maximal positive
block. No start label is added to the codomain. -/
theorem firstBlockEndpoint_injective {S : Type*} (f : Equiv.Perm R) (w : R → ℕ)
    (start : S → R) (hstart : Function.Injective start)
    (hzero : ∀ s, w (start s) = 0) (hseed : ∀ s, 0 < w (f (start s))) :
    Function.Injective (firstBlockEndpoint f w start hzero) := by
  intro x y hend
  let nx := firstBlockIndex f w start hzero x
  let ny := firstBlockIndex f w start hzero y
  have hnx : 1 < nx := firstBlockIndex_gt_one f w start hzero hseed x
  have hny : 1 < ny := firstBlockIndex_gt_one f w start hzero hseed y
  have endpoint_eq : (f ^ (nx - 1)) (start x) = (f ^ (ny - 1)) (start y) := by
    simpa [firstBlockEndpoint, nx, ny] using hend
  have forward : nx ≤ ny → x = y := by
    intro hle
    have hxy : start x = (f ^ (ny - nx)) (start y) :=
      start_eq_iterate_of_endpoint_eq f (start x) (start y) (by omega) (by omega)
        hle endpoint_eq
    by_cases hlt : nx < ny
    · have hdpos : 0 < ny - nx := Nat.sub_pos_of_lt hlt
      have hdlt : ny - nx < firstZeroIndex f w (start y) (hzero y) := by
        change ny - nx < ny
        omega
      have hpositive := firstZeroIndex_positive_before f w (start y) (hzero y)
        hdpos hdlt
      have hxzero : w ((f ^ (ny - nx)) (start y)) = 0 := by
        rw [← hxy]
        exact hzero x
      exact False.elim ((Nat.ne_of_gt hpositive) hxzero)
    · have hn : nx = ny := Nat.le_antisymm hle (Nat.le_of_not_gt hlt)
      apply hstart
      apply (f ^ (nx - 1)).injective
      simpa [hn] using endpoint_eq
  by_cases hle : nx ≤ ny
  · exact forward hle
  · have hyx : y = x := by
      have endpoint_eq' : (f ^ (ny - 1)) (start y) = (f ^ (nx - 1)) (start x) :=
        endpoint_eq.symm
      have hle' : ny ≤ nx := Nat.le_of_not_ge hle
      have hyxStart : start y = (f ^ (nx - ny)) (start x) :=
        start_eq_iterate_of_endpoint_eq f (start y) (start x) (by omega) (by omega)
          hle' endpoint_eq'
      by_cases hlt : ny < nx
      · have hdpos : 0 < nx - ny := Nat.sub_pos_of_lt hlt
        have hdlt : nx - ny < firstZeroIndex f w (start x) (hzero x) := by
          change nx - ny < nx
          omega
        have hpositive := firstZeroIndex_positive_before f w (start x) (hzero x)
          hdpos hdlt
        have hyzero : w ((f ^ (nx - ny)) (start x)) = 0 := by
          rw [← hyxStart]
          exact hzero y
        exact False.elim ((Nat.ne_of_gt hpositive) hyzero)
      · have hn : ny = nx := Nat.le_antisymm hle' (Nat.le_of_not_gt hlt)
        apply hstart
        apply (f ^ (ny - 1)).injective
        simpa [hn] using endpoint_eq'
    exact hyx.symm

def CSourceTargetBranches := {r : R // SourceTargetBranch D r}

def BSourceTargetBranches := {r : R // SourceTargetBranch D r}

noncomputable def cFirstZeroIndex (s : CSourceTargetBranches D) : ℕ :=
  firstZeroIndex D.c D.u s.val s.property.1.1

noncomputable def bFirstZeroIndex (s : BSourceTargetBranches D) : ℕ :=
  firstZeroIndex D.b D.v s.val s.property.1.2

noncomputable def canonicalCEndpoint (s : CSourceTargetBranches D) : R :=
  (D.c ^ (cFirstZeroIndex D s - 1)) s.val

noncomputable def canonicalBEndpoint (s : BSourceTargetBranches D) : R :=
  (D.b ^ (bFirstZeroIndex D s - 1)) s.val

def CanonicalCRun (start finish : R) : Prop :=
  SourceTargetBranch D start ∧
    ∃ n : ℕ, 1 < n ∧ finish = (D.c ^ (n - 1)) start ∧
      (∀ k : ℕ, 0 < k → k < n → 0 < D.u ((D.c ^ k) start)) ∧
      0 < D.u finish ∧ D.u (D.c finish) = 0

def CanonicalBRun (start finish : R) : Prop :=
  SourceTargetBranch D start ∧
    ∃ n : ℕ, 1 < n ∧ finish = (D.b ^ (n - 1)) start ∧
      (∀ k : ℕ, 0 < k → k < n → 0 < D.v ((D.b ^ k) start)) ∧
      0 < D.v finish ∧ D.v (D.b finish) = 0

private theorem cFirstZeroIndex_gt_one (s : CSourceTargetBranches D) :
    1 < cFirstZeroIndex D s := by
  change 1 < firstZeroIndex D.c D.u s.val s.property.1.1
  have hseed : 0 < D.u (D.c s.val) :=
    (sourceTargetBranch_iff_positive_cross D).1 s.property |>.2.2
  have hz := firstZeroIndex_zero D.c D.u s.val s.property.1.1
  have hp := firstZeroIndex_pos D.c D.u s.val s.property.1.1
  by_contra h
  have heq : firstZeroIndex D.c D.u s.val s.property.1.1 = 1 := by omega
  rw [heq] at hz
  have hz' : D.u (D.c s.val) = 0 := by simpa using hz
  exact (Nat.ne_of_gt hseed) hz'

private theorem bFirstZeroIndex_gt_one (s : BSourceTargetBranches D) :
    1 < bFirstZeroIndex D s := by
  change 1 < firstZeroIndex D.b D.v s.val s.property.1.2
  have hseed : 0 < D.v (D.b s.val) := by
    have h := (sourceTargetBranch_iff_positive_cross D).1 s.property
    rw [← h.2.1]
    exact h.2.2
  have hz := firstZeroIndex_zero D.b D.v s.val s.property.1.2
  have hp := firstZeroIndex_pos D.b D.v s.val s.property.1.2
  by_contra h
  have heq : firstZeroIndex D.b D.v s.val s.property.1.2 = 1 := by omega
  rw [heq] at hz
  have hz' : D.v (D.b s.val) = 0 := by simpa using hz
  exact (Nat.ne_of_gt hseed) hz'

theorem canonicalCRun_spec (s : CSourceTargetBranches D) :
    CanonicalCRun D s.val (canonicalCEndpoint D s) := by
  let n := cFirstZeroIndex D s
  have hn : 1 < n := cFirstZeroIndex_gt_one D s
  refine ⟨s.property, n, hn, rfl, ?_, ?_, ?_⟩
  · intro k hk hkn
    apply firstZeroIndex_positive_before D.c D.u s.val s.property.1.1 hk
    simpa [n, cFirstZeroIndex] using hkn
  · apply firstZeroIndex_positive_before D.c D.u s.val s.property.1.1 (by omega)
    exact Nat.sub_lt (firstZeroIndex_pos D.c D.u s.val s.property.1.1) Nat.zero_lt_one
  · have hz := firstZeroIndex_zero D.c D.u s.val s.property.1.1
    change D.u (D.c ((D.c ^ (n - 1)) s.val)) = 0
    rw [apply_pow_pred D.c s.val (show 0 < n by omega)]
    simpa [n, cFirstZeroIndex] using hz

theorem canonicalBRun_spec (s : BSourceTargetBranches D) :
    CanonicalBRun D s.val (canonicalBEndpoint D s) := by
  let n := bFirstZeroIndex D s
  have hn : 1 < n := bFirstZeroIndex_gt_one D s
  refine ⟨s.property, n, hn, rfl, ?_, ?_, ?_⟩
  · intro k hk hkn
    apply firstZeroIndex_positive_before D.b D.v s.val s.property.1.2 hk
    simpa [n, bFirstZeroIndex] using hkn
  · apply firstZeroIndex_positive_before D.b D.v s.val s.property.1.2 (by omega)
    exact Nat.sub_lt (firstZeroIndex_pos D.b D.v s.val s.property.1.2) Nat.zero_lt_one
  · have hz := firstZeroIndex_zero D.b D.v s.val s.property.1.2
    change D.v (D.b ((D.b ^ (n - 1)) s.val)) = 0
    rw [apply_pow_pred D.b s.val (show 0 < n by omega)]
    simpa [n, bFirstZeroIndex] using hz

/-! ### I4: nonexceptional endpoints are exact unused-merge reverse bases -/

def CFirstStageNonexceptional (s : CSourceTargetBranches D) : Prop :=
  D.v (D.b (canonicalCEndpoint D s)) = 0

def BFirstStageNonexceptional (s : BSourceTargetBranches D) : Prop :=
  D.u (D.c (canonicalBEndpoint D s)) = 0

def CNonexceptionalBranches := {s : CSourceTargetBranches D // CFirstStageNonexceptional D s}

def BNonexceptionalBranches := {s : BSourceTargetBranches D // BFirstStageNonexceptional D s}

def CExceptionalBranches := {s : CSourceTargetBranches D // ¬ CFirstStageNonexceptional D s}

def BExceptionalBranches := {s : BSourceTargetBranches D // ¬ BFirstStageNonexceptional D s}

theorem nonexceptional_c_endpoint_exact_unusedMerge (s : CSourceTargetBranches D)
    (hne : CFirstStageNonexceptional D s) :
    ExactUnusedMergeReverseBase D (canonicalCEndpoint D s) := by
  have hrun := canonicalCRun_spec D s
  have hu := hrun.2.choose_spec.2.2.2.1
  have huc := hrun.2.choose_spec.2.2.2.2
  have hdiamond := D.diamond (canonicalCEndpoint D s)
  rw [hne, huc, Nat.add_zero, Nat.add_zero] at hdiamond
  exact ⟨hdiamond, hu, huc, hne⟩

theorem nonexceptional_b_endpoint_exact_unusedMerge (s : BSourceTargetBranches D)
    (hne : BFirstStageNonexceptional D s) :
    ExactUnusedMergeReverseBase D (canonicalBEndpoint D s) := by
  have hrun := canonicalBRun_spec D s
  have hv := hrun.2.choose_spec.2.2.2.1
  have hvb := hrun.2.choose_spec.2.2.2.2
  have hdiamond := D.diamond (canonicalBEndpoint D s)
  rw [hvb, hne, Nat.add_zero, Nat.add_zero] at hdiamond
  exact ⟨hdiamond, hdiamond ▸ hv, hne, hvb⟩

/-! ### I5: endpoint-only first-stage injections -/

private theorem cCanonicalEndpoint_injective :
    Function.Injective (canonicalCEndpoint D) := by
  let start : CSourceTargetBranches D → R := fun s => s.val
  let hzero : ∀ s, D.u (start s) = 0 := fun s => s.property.1.1
  have hseed : ∀ s, 0 < D.u (D.c (start s)) := fun s =>
    (sourceTargetBranch_iff_positive_cross D).1 s.property |>.2.2
  have hi := firstBlockEndpoint_injective D.c D.u start
    (fun _ _ h => Subtype.ext h) hzero hseed
  intro x y hxy
  apply hi
  simpa [canonicalCEndpoint, cFirstZeroIndex, firstBlockEndpoint, firstBlockIndex,
    start, hzero] using hxy

private theorem bCanonicalEndpoint_injective :
    Function.Injective (canonicalBEndpoint D) := by
  let start : BSourceTargetBranches D → R := fun s => s.val
  let hzero : ∀ s, D.v (start s) = 0 := fun s => s.property.1.2
  have hseed : ∀ s, 0 < D.v (D.b (start s)) := fun s => by
    have h := (sourceTargetBranch_iff_positive_cross D).1 s.property
    rw [← h.2.1]
    exact h.2.2
  have hi := firstBlockEndpoint_injective D.b D.v start
    (fun _ _ h => Subtype.ext h) hzero hseed
  intro x y hxy
  apply hi
  simpa [canonicalBEndpoint, bFirstZeroIndex, firstBlockEndpoint, firstBlockIndex,
    start, hzero] using hxy

def ExactUnusedMergeBases := {r : R // ExactUnusedMergeReverseBase D r}

noncomputable def cFirstStagePairing (s : CNonexceptionalBranches D) :
    ExactUnusedMergeBases D :=
  ⟨canonicalCEndpoint D s.val,
    nonexceptional_c_endpoint_exact_unusedMerge D s.val s.property⟩

noncomputable def bFirstStagePairing (s : BNonexceptionalBranches D) :
    ExactUnusedMergeBases D :=
  ⟨canonicalBEndpoint D s.val,
    nonexceptional_b_endpoint_exact_unusedMerge D s.val s.property⟩

theorem cFirstStagePairing_injective : Function.Injective (cFirstStagePairing D) := by
  intro x y hxy
  apply Subtype.ext
  apply cCanonicalEndpoint_injective D
  exact congrArg Subtype.val hxy

theorem bFirstStagePairing_injective : Function.Injective (bFirstStagePairing D) := by
  intro x y hxy
  apply Subtype.ext
  apply bCanonicalEndpoint_injective D
  exact congrArg Subtype.val hxy

/-! ### I6: used/fresh and nonexceptional/exceptional partitions -/

def CUsedFirstStageBases :=
  {r : ExactUnusedMergeBases D // ∃ s, cFirstStagePairing D s = r}

def BUsedFirstStageBases :=
  {r : ExactUnusedMergeBases D // ∃ s, bFirstStagePairing D s = r}

def CFreshUnusedMergeBases :=
  {r : ExactUnusedMergeBases D // ¬ ∃ s, cFirstStagePairing D s = r}

def BFreshUnusedMergeBases :=
  {r : ExactUnusedMergeBases D // ¬ ∃ s, bFirstStagePairing D s = r}

noncomputable def predicatePartitionEquiv {α : Type*} (p : α → Prop) :
    α ≃ Sum {x // p x} {x // ¬ p x} := by
  classical
  exact
    { toFun := fun x => if hx : p x then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, hx⟩
      invFun := fun x => match x with
        | Sum.inl y => y.val
        | Sum.inr y => y.val
      left_inv := by
        intro x
        by_cases hx : p x <;> simp [hx]
      right_inv := by
        intro x
        rcases x with x | x
        · simp [x.property]
        · simp [x.property] }

noncomputable def unusedMerge_used_fresh_equiv
    (used : ExactUnusedMergeBases D → Prop) :
    ExactUnusedMergeBases D ≃
      Sum {r : ExactUnusedMergeBases D // used r}
        {r : ExactUnusedMergeBases D // ¬ used r} :=
  predicatePartitionEquiv used

noncomputable def cUnusedMergeUsedFreshEquiv :
    ExactUnusedMergeBases D ≃ Sum (CUsedFirstStageBases D) (CFreshUnusedMergeBases D) :=
  unusedMerge_used_fresh_equiv D (fun r => ∃ s, cFirstStagePairing D s = r)

noncomputable def bUnusedMergeUsedFreshEquiv :
    ExactUnusedMergeBases D ≃ Sum (BUsedFirstStageBases D) (BFreshUnusedMergeBases D) :=
  unusedMerge_used_fresh_equiv D (fun r => ∃ s, bFirstStagePairing D s = r)

noncomputable def cNonexceptionalExceptionalEquiv :
    CSourceTargetBranches D ≃
      Sum (CNonexceptionalBranches D) (CExceptionalBranches D) :=
  predicatePartitionEquiv (CFirstStageNonexceptional D)

noncomputable def bNonexceptionalExceptionalEquiv :
    BSourceTargetBranches D ≃
      Sum (BNonexceptionalBranches D) (BExceptionalBranches D) :=
  predicatePartitionEquiv (BFirstStageNonexceptional D)

noncomputable def cUsedFirstStageCount : ℕ := Nat.card (CUsedFirstStageBases D)

noncomputable def bUsedFirstStageCount : ℕ := Nat.card (BUsedFirstStageBases D)

noncomputable def cExceptionalCount : ℕ := Nat.card (CExceptionalBranches D)

noncomputable def bExceptionalCount : ℕ := Nat.card (BExceptionalBranches D)

noncomputable def sourceTargetBranchCount : ℕ := Nat.card (CSourceTargetBranches D)

theorem c_firstStage_card_identity :
    cUsedFirstStageCount D + cExceptionalCount D = sourceTargetBranchCount D := by
  letI : Finite (CSourceTargetBranches D) := Subtype.finite
  letI : Finite (CNonexceptionalBranches D) := Subtype.finite
  letI : Finite (CExceptionalBranches D) := Subtype.finite
  let usedEquiv : CNonexceptionalBranches D ≃ CUsedFirstStageBases D :=
    Equiv.ofInjective (cFirstStagePairing D) (cFirstStagePairing_injective D)
  have hused : Nat.card (CNonexceptionalBranches D) =
      Nat.card (CUsedFirstStageBases D) := Nat.card_congr usedEquiv
  have hpart := Nat.card_congr (cNonexceptionalExceptionalEquiv D)
  rw [Nat.card_sum] at hpart
  simp only [cUsedFirstStageCount, cExceptionalCount, sourceTargetBranchCount]
  omega

theorem b_firstStage_card_identity :
    bUsedFirstStageCount D + bExceptionalCount D = sourceTargetBranchCount D := by
  letI : Finite (BSourceTargetBranches D) := Subtype.finite
  letI : Finite (BNonexceptionalBranches D) := Subtype.finite
  letI : Finite (BExceptionalBranches D) := Subtype.finite
  let usedEquiv : BNonexceptionalBranches D ≃ BUsedFirstStageBases D :=
    Equiv.ofInjective (bFirstStagePairing D) (bFirstStagePairing_injective D)
  have hused : Nat.card (BNonexceptionalBranches D) =
      Nat.card (BUsedFirstStageBases D) := Nat.card_congr usedEquiv
  have hpart := Nat.card_congr (bNonexceptionalExceptionalEquiv D)
  rw [Nat.card_sum] at hpart
  simp only [bUsedFirstStageCount, bExceptionalCount, sourceTargetBranchCount,
    BSourceTargetBranches, CSourceTargetBranches] at hpart ⊢
  omega

theorem c_used_eq_sourceTarget_sub_exceptional :
    cUsedFirstStageCount D = sourceTargetBranchCount D - cExceptionalCount D := by
  have h := c_firstStage_card_identity D
  omega

theorem b_used_eq_sourceTarget_sub_exceptional :
    bUsedFirstStageCount D = sourceTargetBranchCount D - bExceptionalCount D := by
  have h := b_firstStage_card_identity D
  omega

end ResidueData

variable {Gamma : NumericalSemigroup}

/-- I1--I6 specialize without extra premises to the actual chosen-base routing
object constructed in C4H. -/
theorem actual_firstStage_card_identities (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ResidueData.bUsedFirstStageCount D + ResidueData.bExceptionalCount D =
        ResidueData.sourceTargetBranchCount D ∧
      ResidueData.cUsedFirstStageCount D + ResidueData.cExceptionalCount D =
        ResidueData.sourceTargetBranchCount D := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact ⟨ResidueData.b_firstStage_card_identity (routingData B e),
    ResidueData.c_firstStage_card_identity (routingData B e)⟩

end NS25Lean.L5A2C4I
