import NS25Lean.P2SectorCFirstStagePairingFreshness

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4J

open CombinatorialCore
open L5A2C4H
open L5A2C4I

namespace ResidueData

variable {R : Type*} [Fintype R] (D : CombinatorialCore.ResidueData R)

/-! ### J1: mixed coalescence and CURL -/

def MixedCoalescenceReverseBase (r : R) : Prop :=
  D.u (D.c r) = 0 ∧ D.v (D.b r) = 0

theorem mixedCoalescence_eq {r : R} (h : MixedCoalescenceReverseBase D r) :
    D.u r = D.v r := by
  simpa [h.1, h.2] using D.diamond r

private theorem b_symm_branchTarget (r : R) :
    D.b.symm (D.branchTarget r) = D.c r := by
  apply D.b.injective
  simpa [CombinatorialCore.ResidueData.branchTarget] using (D.commute r).symm

private theorem c_symm_branchTarget (r : R) :
    D.c.symm (D.branchTarget r) = D.b r := by
  simp [CombinatorialCore.ResidueData.branchTarget]

private theorem mixedCoalescence_target_isMerge {r : R}
    (h : MixedCoalescenceReverseBase D r) : D.IsMerge (D.branchTarget r) := by
  constructor
  · simpa [b_symm_branchTarget D r] using h.1
  · simpa [c_symm_branchTarget D r] using h.2

/-! ### J2: positive unused merge versus the paired zero diamond -/

def PairedZeroDiamond (r : R) : Prop :=
  D.IsBranch r ∧ D.IsMerge (D.branchTarget r)

theorem mixedCoalescence_exact_dichotomy {r : R}
    (h : MixedCoalescenceReverseBase D r) :
    (L5A2C4I.ResidueData.ExactUnusedMergeReverseBase D r ∨
        PairedZeroDiamond D r) ∧
      ¬ (L5A2C4I.ResidueData.ExactUnusedMergeReverseBase D r ∧
        PairedZeroDiamond D r) := by
  have huv := mixedCoalescence_eq D h
  constructor
  · by_cases hu : D.u r = 0
    · right
      have hv : D.v r = 0 := by rw [← huv, hu]
      exact ⟨⟨hu, hv⟩, mixedCoalescence_target_isMerge D h⟩
    · left
      exact ⟨huv, Nat.pos_of_ne_zero hu, h.1, h.2⟩
  · rintro ⟨hexact, hzero⟩
    exact (Nat.ne_of_gt hexact.2.1) hzero.1.1

/-! ### J3: every branch has a source target or a paired-zero target -/

theorem sourceTargetBranch_not_pairedZero {r : R} :
    ¬ (L5A2C4I.ResidueData.SourceTargetBranch D r ∧ PairedZeroDiamond D r) := by
  rintro ⟨hsource, hpaired⟩
  exact hsource.2.1 hpaired.2.1

theorem branch_exact_dichotomy {r : R} (h : D.IsBranch r) :
    (L5A2C4I.ResidueData.SourceTargetBranch D r ∨ PairedZeroDiamond D r) ∧
      ¬ (L5A2C4I.ResidueData.SourceTargetBranch D r ∧ PairedZeroDiamond D r) := by
  constructor
  · rcases D.branchTarget_isSource_or_isMerge h with hs | hm
    · exact Or.inl ⟨h, hs⟩
    · exact Or.inr ⟨h, hm⟩
  · exact sourceTargetBranch_not_pairedZero D

/-! ### J4: the unique reverse base of an actual merge -/

def branchTargetEquiv : R ≃ R := D.b.trans D.c

@[simp] theorem branchTargetEquiv_apply (r : R) :
    branchTargetEquiv D r = D.branchTarget r := rfl

def mergeReverseBase (m : R) : R := (branchTargetEquiv D).symm m

@[simp] theorem mergeReverseBase_target (m : R) :
    D.branchTarget (mergeReverseBase D m) = m := by
  change branchTargetEquiv D ((branchTargetEquiv D).symm m) = m
  simp

@[simp] theorem mergeReverseBase_branchTarget (r : R) :
    mergeReverseBase D (D.branchTarget r) = r := by
  apply D.branchTarget_injective
  rw [mergeReverseBase_target]

theorem merge_reverseBase_mixedCoalescence {m : R} (hm : D.IsMerge m) :
    MixedCoalescenceReverseBase D (mergeReverseBase D m) := by
  let r := mergeReverseBase D m
  have ht : D.branchTarget r = m := mergeReverseBase_target D m
  constructor
  · have h := hm.1
    rw [← ht] at h
    simpa [b_symm_branchTarget D r] using h
  · have h := hm.2
    rw [← ht] at h
    simpa [c_symm_branchTarget D r] using h

def BranchImageMerge (m : R) : Prop :=
  D.IsMerge m ∧ D.IsBranch (mergeReverseBase D m)

def ExactUnusedMergeTarget (m : R) : Prop :=
  D.IsMerge m ∧
    L5A2C4I.ResidueData.ExactUnusedMergeReverseBase D (mergeReverseBase D m)

theorem merge_exact_dichotomy {m : R} (hm : D.IsMerge m) :
    (BranchImageMerge D m ∨ ExactUnusedMergeTarget D m) ∧
      ¬ (BranchImageMerge D m ∧ ExactUnusedMergeTarget D m) := by
  have hmix := merge_reverseBase_mixedCoalescence D hm
  have hsplit := mixedCoalescence_exact_dichotomy D hmix
  constructor
  · rcases hsplit.1 with hu | hp
    · exact Or.inr ⟨hm, hu⟩
    · exact Or.inl ⟨hm, hp.1⟩
  · rintro ⟨himage, hunused⟩
    exact (Nat.ne_of_gt hunused.2.2.1) himage.2.1

/-! ### J5: finite equivalences on the underlying residues -/

def AllBranches := {r : R // D.IsBranch r}
def PairedZeroDiamonds := {r : R // PairedZeroDiamond D r}
def BranchImageMerges := {m : R // BranchImageMerge D m}
def ExactUnusedMergeTargets := {m : R // ExactUnusedMergeTarget D m}
def AllMerges := {m : R // D.IsMerge m}

noncomputable def branchPartitionEquiv :
    AllBranches D ≃ Sum (PairedZeroDiamonds D)
      (L5A2C4I.ResidueData.CSourceTargetBranches D) := by
  classical
  exact
    { toFun := fun r =>
        if hm : D.IsMerge (D.branchTarget r.val) then
          Sum.inl ⟨r.val, r.property, hm⟩
        else
          Sum.inr ⟨r.val, r.property,
            (D.branchTarget_isSource_or_isMerge r.property).resolve_right hm⟩
      invFun := fun x => match x with
        | Sum.inl r => ⟨r.val, r.property.1⟩
        | Sum.inr r => ⟨r.val, r.property.1⟩
      left_inv := by
        intro r
        apply Subtype.ext
        by_cases hm : D.IsMerge (D.branchTarget r.val) <;> simp [hm]
      right_inv := by
        intro x
        rcases x with r | r
        · simp only [r.property.2, if_pos]
          exact congrArg Sum.inl (Subtype.ext rfl)
        · have hm : ¬ D.IsMerge (D.branchTarget r.val) := by
            intro hm
            exact r.property.2.1 hm.1
          simp only [hm, if_neg]
          exact congrArg Sum.inr (Subtype.ext rfl) }

noncomputable def mergePartitionEquiv :
    AllMerges D ≃ Sum (BranchImageMerges D) (ExactUnusedMergeTargets D) := by
  classical
  exact
    { toFun := fun m =>
        if hb : D.IsBranch (mergeReverseBase D m.val) then
          Sum.inl ⟨m.val, m.property, hb⟩
        else
          Sum.inr ⟨m.val, m.property,
            ((merge_exact_dichotomy D m.property).1.resolve_left
              (fun h => hb h.2)).2⟩
      invFun := fun x => match x with
        | Sum.inl m => ⟨m.val, m.property.1⟩
        | Sum.inr m => ⟨m.val, m.property.1⟩
      left_inv := by
        intro m
        apply Subtype.ext
        by_cases hb : D.IsBranch (mergeReverseBase D m.val) <;> simp [hb]
      right_inv := by
        intro x
        rcases x with m | m
        · simp only [m.property.2, if_pos]
          exact congrArg Sum.inl (Subtype.ext rfl)
        · have hb : ¬ D.IsBranch (mergeReverseBase D m.val) := by
            intro hb
            exact (Nat.ne_of_gt m.property.2.2.1) hb.1
          simp only [hb, if_neg]
          exact congrArg Sum.inr (Subtype.ext rfl) }

noncomputable def pairedZeroDiamondTargetEquiv :
    PairedZeroDiamonds D ≃ BranchImageMerges D where
  toFun r := ⟨D.branchTarget r.val, r.property.2, by simp [r.property.1]⟩
  invFun m := ⟨mergeReverseBase D m.val, m.property.2, by simp [m.property.1]⟩
  left_inv r := by apply Subtype.ext; simp
  right_inv m := by apply Subtype.ext; simp

noncomputable def exactUnusedMergeTargetEquiv :
    L5A2C4I.ResidueData.ExactUnusedMergeBases D ≃ ExactUnusedMergeTargets D where
  toFun r := ⟨D.branchTarget r.val,
    L5A2C4I.ResidueData.exactUnusedMergeReverseBase_target_isMerge D r.property,
    by simpa using r.property⟩
  invFun m := ⟨mergeReverseBase D m.val, m.property.2⟩
  left_inv r := by apply Subtype.ext; simp
  right_inv m := by apply Subtype.ext; simp

/-! ### J6: raw cardinality decompositions -/

noncomputable def pairedZeroDiamondCount : ℕ := Nat.card (PairedZeroDiamonds D)
noncomputable def exactUnusedMergeCount : ℕ :=
  Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases D)

theorem branchCount_raw_decomposition :
    D.branchCount = pairedZeroDiamondCount D +
      L5A2C4I.ResidueData.sourceTargetBranchCount D := by
  letI : Finite (PairedZeroDiamonds D) := Subtype.finite
  letI : Finite (L5A2C4I.ResidueData.CSourceTargetBranches D) := Subtype.finite
  have h := Nat.card_congr (branchPartitionEquiv D)
  rw [Nat.card_sum] at h
  exact h

theorem mergeCount_raw_decomposition :
    D.mergeCount = pairedZeroDiamondCount D + exactUnusedMergeCount D := by
  letI : Finite (BranchImageMerges D) := Subtype.finite
  letI : Finite (ExactUnusedMergeTargets D) := Subtype.finite
  have h := Nat.card_congr (mergePartitionEquiv D)
  rw [Nat.card_sum] at h
  have hA := Nat.card_congr (pairedZeroDiamondTargetEquiv D)
  have hU := Nat.card_congr (exactUnusedMergeTargetEquiv D)
  change Nat.card (AllMerges D) = Nat.card (PairedZeroDiamonds D) +
    Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases D)
  exact h.trans (congrArg₂ (· + ·) hA.symm hU.symm)

end ResidueData

/-! ### J7: actual chosen-base routing specialization -/

variable {Gamma : NumericalSemigroup}

theorem actual_raw_decomposition (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    D.branchCount = ResidueData.pairedZeroDiamondCount D +
        L5A2C4I.ResidueData.sourceTargetBranchCount D ∧
      D.mergeCount = ResidueData.pairedZeroDiamondCount D +
        ResidueData.exactUnusedMergeCount D := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact ⟨ResidueData.branchCount_raw_decomposition (routingData B e),
    ResidueData.mergeCount_raw_decomposition (routingData B e)⟩

end NS25Lean.L5A2C4J
