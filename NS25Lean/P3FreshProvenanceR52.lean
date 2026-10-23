import NS25Lean.P3ReturnInfrastructureR51

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section

namespace NS25Lean.P3R52
open CombinatorialCore L2B L5A2C4H L5A2C4I

variable {R : Type*} [Fintype R]

omit [Fintype R] in
theorem forward_reverse_cancel (f : Equiv.Perm R) (x : R) (n k : ℕ) (h : k ≤ n) :
    (f ^ k) ((f.symm ^ n) x) = (f.symm ^ (n-k)) x := by
  have hn : n = k + (n-k) := by omega
  rw [hn, pow_add]
  change ((f ^ k) * ((f⁻¹) ^ k) * ((f⁻¹) ^ (n-k))) x = _
  rw [inv_pow, mul_inv_cancel, one_mul]
  congr 2
  omega

def CBlockSeeds (D : ResidueData R) := {r : R // D.u r = 0 ∧ 0 < D.u (D.c r)}

def blockEndpoint (D : ResidueData R) (s : CBlockSeeds D) : R :=
  ResidueData.firstBlockEndpoint D.c D.u Subtype.val (fun s => s.property.1) s

theorem blockEndpoint_injective (D : ResidueData R) : Function.Injective (blockEndpoint D) :=
  ResidueData.firstBlockEndpoint_injective D.c D.u Subtype.val Subtype.val_injective
    (fun s => s.property.1) (fun s => s.property.2)

def reverseIndex (D : ResidueData R) (q : ResidueData.ExactUnusedMergeBases D) : ℕ :=
  ResidueData.firstZeroIndex D.c.symm D.u (D.c q.val) q.property.2.2.1

theorem reverseIndex_gt_one (D : ResidueData R) (q : ResidueData.ExactUnusedMergeBases D) :
    1 < reverseIndex D q := by
  have hp := ResidueData.firstZeroIndex_pos D.c.symm D.u (D.c q.val) q.property.2.2.1
  have hz := ResidueData.firstZeroIndex_zero D.c.symm D.u (D.c q.val) q.property.2.2.1
  change 0 < reverseIndex D q at hp
  change D.u ((D.c.symm ^ reverseIndex D q) (D.c q.val)) = 0 at hz
  by_contra h
  have heq : reverseIndex D q = 1 := by omega
  rw [heq] at hz
  have hz' : D.u q.val = 0 := by simpa using hz
  exact (Nat.ne_of_gt q.property.2.1) hz'

def backwardSeed (D : ResidueData R) (q : ResidueData.ExactUnusedMergeBases D) : CBlockSeeds D :=
  ⟨(D.c.symm ^ reverseIndex D q) (D.c q.val),
    ResidueData.firstZeroIndex_zero D.c.symm D.u (D.c q.val) q.property.2.2.1, by
      have hn := reverseIndex_gt_one D q
      have hp := ResidueData.firstZeroIndex_positive_before D.c.symm D.u (D.c q.val)
        q.property.2.2.1 (k := reverseIndex D q - 1) (by omega) (by change _ < reverseIndex D q; omega)
      change 0 < D.u ((D.c ^ 1) ((D.c.symm ^ reverseIndex D q) (D.c q.val)))
      rw [forward_reverse_cancel D.c (D.c q.val) (reverseIndex D q) 1 (by omega)]
      exact hp⟩

theorem backwardSeed_index (D : ResidueData R) (q : ResidueData.ExactUnusedMergeBases D) :
    ResidueData.firstZeroIndex D.c D.u (backwardSeed D q).val (backwardSeed D q).property.1 =
      reverseIndex D q := by
  let n := reverseIndex D q
  let s := backwardSeed D q
  have hn : 1 < n := reverseIndex_gt_one D q
  have hz : D.u ((D.c ^ n) s.val) = 0 := by
    change D.u ((D.c ^ n) ((D.c.symm ^ n) (D.c q.val))) = 0
    rw [forward_reverse_cancel D.c (D.c q.val) n n le_rfl]
    simpa using q.property.2.2.1
  have hpositive : ∀ k, 0 < k → k < n → 0 < D.u ((D.c ^ k) s.val) := by
    intro k hk hkn
    change 0 < D.u ((D.c ^ k) ((D.c.symm ^ n) (D.c q.val)))
    rw [forward_reverse_cancel D.c (D.c q.val) n k (by omega)]
    exact ResidueData.firstZeroIndex_positive_before D.c.symm D.u (D.c q.val)
      q.property.2.2.1 (by omega) (by change n-k < n; omega)
  apply Nat.le_antisymm
  · unfold ResidueData.firstZeroIndex
    exact Nat.find_min' _ ⟨by omega, hz⟩
  · change n ≤ ResidueData.firstZeroIndex D.c D.u s.val s.property.1
    have hp := ResidueData.firstZeroIndex_pos D.c D.u s.val s.property.1
    have hzero := ResidueData.firstZeroIndex_zero D.c D.u s.val s.property.1
    by_contra h
    exact (Nat.ne_of_gt (hpositive _ hp (by omega))) hzero

theorem backwardSeed_endpoint (D : ResidueData R) (q : ResidueData.ExactUnusedMergeBases D) :
    blockEndpoint D (backwardSeed D q) = q.val := by
  change (D.c ^ (ResidueData.firstZeroIndex D.c D.u (backwardSeed D q).val
    (backwardSeed D q).property.1 - 1)) (backwardSeed D q).val = q.val
  rw [backwardSeed_index]
  change (D.c ^ (reverseIndex D q - 1)) ((D.c.symm ^ reverseIndex D q) (D.c q.val)) = q.val
  rw [forward_reverse_cancel D.c (D.c q.val) (reverseIndex D q)
    (reverseIndex D q - 1) (by omega)]
  have hn := reverseIndex_gt_one D q
  have heq : reverseIndex D q - (reverseIndex D q - 1) = 1 := by omega
  simp [heq]

def branchSeed (D : ResidueData R) (s : ResidueData.CSourceTargetBranches D) : CBlockSeeds D :=
  ⟨s.val, s.property.1.1, (ResidueData.sourceTargetBranch_iff_positive_cross D).1 s.property |>.2.2⟩

theorem branchSeed_endpoint (D : ResidueData R) (s : ResidueData.CSourceTargetBranches D) :
    blockEndpoint D (branchSeed D s) = ResidueData.canonicalCEndpoint D s := rfl

theorem seed_branch_iff_v_zero (D : ResidueData R) (s : CBlockSeeds D) :
    ResidueData.SourceTargetBranch D s.val ↔ D.v s.val = 0 := by
  constructor
  · intro h; exact h.1.2
  · intro hv
    apply (ResidueData.sourceTargetBranch_iff_positive_cross D).2
    have hb : D.IsBranch s.val := ⟨s.property.1, hv⟩
    exact ⟨hb, (D.cross_eq_of_isBranch hb).symm, s.property.2⟩

theorem used_iff_seed_v_zero (D : ResidueData R) (q : ResidueData.ExactUnusedMergeBases D) :
    (∃ s, ResidueData.cFirstStagePairing D s = q) ↔ D.v (backwardSeed D q).val = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    have he : blockEndpoint D (branchSeed D s.val) = blockEndpoint D (backwardSeed D q) := by
      rw [branchSeed_endpoint, backwardSeed_endpoint]
      exact congrArg Subtype.val hs
    have hseed := blockEndpoint_injective D he
    rw [← hseed]
    exact s.val.property.1.2
  · intro hv
    let s : ResidueData.CSourceTargetBranches D :=
      ⟨(backwardSeed D q).val, (seed_branch_iff_v_zero D _).2 hv⟩
    have he : ResidueData.canonicalCEndpoint D s = q.val := backwardSeed_endpoint D q
    have hne : ResidueData.CFirstStageNonexceptional D s := by
      change D.v (D.b (ResidueData.canonicalCEndpoint D s)) = 0
      rw [he]
      exact q.property.2.2.2
    refine ⟨⟨s, hne⟩, ?_⟩
    apply Subtype.ext
    exact he

theorem fresh_iff_seed_v_positive (D : ResidueData R) (q : ResidueData.ExactUnusedMergeBases D) :
    (¬ ∃ s, ResidueData.cFirstStagePairing D s = q) ↔ 0 < D.v (backwardSeed D q).val := by
  rw [used_iff_seed_v_zero]
  omega

theorem used_iff_seed_is_sourceTargetBranch (D : ResidueData R)
    (q : ResidueData.ExactUnusedMergeBases D) :
    (∃ s, ResidueData.cFirstStagePairing D s = q) ↔
      ResidueData.SourceTargetBranch D (backwardSeed D q).val := by
  rw [used_iff_seed_v_zero, seed_branch_iff_v_zero]

/-- Termination and all intermediate positive carries refer to the final D. -/
theorem backward_block_spec (D : ResidueData R) (q : ResidueData.ExactUnusedMergeBases D) :
    1 < reverseIndex D q ∧
    D.u (backwardSeed D q).val = 0 ∧
    (∀ k : ℕ, 0 < k → k < reverseIndex D q →
      0 < D.u ((D.c.symm ^ k) (D.c q.val))) ∧
    blockEndpoint D (backwardSeed D q) = q.val := by
  exact ⟨reverseIndex_gt_one D q, (backwardSeed D q).property.1,
    fun _ hk hlt => ResidueData.firstZeroIndex_positive_before D.c.symm D.u
      (D.c q.val) q.property.2.2.1 hk hlt, backwardSeed_endpoint D q⟩

theorem seed_unique (D : ResidueData R) (q : ResidueData.ExactUnusedMergeBases D)
    (s : CBlockSeeds D) (he : blockEndpoint D s = q.val) : s = backwardSeed D q := by
  apply blockEndpoint_injective D
  rw [backwardSeed_endpoint]
  exact he

/-- Physical candidates have a positive v-carry at the predecessor seed and an exact
unused-merge endpoint. Freshness is a conclusion, not a field of this type. -/
def PositiveSeedCandidates (D : ResidueData R) :=
  {s : CBlockSeeds D // 0 < D.v s.val ∧
    ResidueData.ExactUnusedMergeReverseBase D (blockEndpoint D s)}

def candidateToFresh (D : ResidueData R) (x : PositiveSeedCandidates D) :
    ResidueData.CFreshUnusedMergeBases D := by
  let q : ResidueData.ExactUnusedMergeBases D := ⟨blockEndpoint D x.val, x.property.2⟩
  refine ⟨q, (fresh_iff_seed_v_positive D q).2 ?_⟩
  have hs : x.val = backwardSeed D q := seed_unique D q x.val rfl
  rw [← hs]
  exact x.property.1

theorem candidateToFresh_injective (D : ResidueData R) :
    Function.Injective (candidateToFresh D) := by
  intro x y h
  apply Subtype.ext
  apply blockEndpoint_injective D
  exact congrArg (fun z => z.val.val) h

def freshToCandidate (D : ResidueData R) (q : ResidueData.CFreshUnusedMergeBases D) :
    PositiveSeedCandidates D :=
  ⟨backwardSeed D q.val, (fresh_iff_seed_v_positive D q.val).1 q.property, by
    rw [backwardSeed_endpoint]
    exact q.val.property⟩

def candidateFreshEquiv (D : ResidueData R) :
    PositiveSeedCandidates D ≃ ResidueData.CFreshUnusedMergeBases D where
  toFun := candidateToFresh D
  invFun := freshToCandidate D
  left_inv x := by
    apply Subtype.ext
    exact (seed_unique D _ x.val rfl).symm
  right_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    exact backwardSeed_endpoint D q.val

theorem candidate_count_eq_fresh (D : ResidueData R) :
    Nat.card (PositiveSeedCandidates D) = Nat.card (ResidueData.CFreshUnusedMergeBases D) :=
  Nat.card_congr (candidateFreshEquiv D)

theorem candidate_count_le_fresh (D : ResidueData R) :
    Nat.card (PositiveSeedCandidates D) ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D) := by
  letI : Finite (ResidueData.ExactUnusedMergeBases D) := Subtype.finite
  letI : Finite (ResidueData.CFreshUnusedMergeBases D) := Subtype.finite
  exact Nat.card_le_card_of_injective _ (candidateToFresh_injective D)

/-- Distinct physical seeds give distinct fresh residues; the same corner cannot count twice. -/
theorem two_candidates_give_two_fresh (D : ResidueData R)
    (x y : PositiveSeedCandidates D) (hne : x.val.val ≠ y.val.val) :
    2 ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D) := by
  have hxy : x ≠ y := by intro h; exact hne (congrArg (fun z => z.val.val) h)
  letI : Finite (CBlockSeeds D) := Subtype.finite
  letI : Finite (PositiveSeedCandidates D) := Subtype.finite
  let f : Fin 2 → PositiveSeedCandidates D := fun i => if i = 0 then x else y
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hc : 2 ≤ Nat.card (PositiveSeedCandidates D) := by
    simpa using Nat.card_le_card_of_injective f hf
  exact hc.trans (candidate_count_le_fresh D)

variable {Gamma : NumericalSemigroup}

/-- Same actual M and role e on both sides; no arbitrary replacement graph. -/
theorem actual_used_iff_seed_v_zero (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    ∀ q : ResidueData.ExactUnusedMergeBases D,
      (∃ s, ResidueData.cFirstStagePairing D s = q) ↔ D.v (backwardSeed D q).val = 0 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  exact used_iff_seed_v_zero (routingData M.base e)

theorem actual_fresh_iff_seed_v_positive (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    ∀ q : ResidueData.ExactUnusedMergeBases D,
      (¬ ∃ s, ResidueData.cFirstStagePairing D s = q) ↔ 0 < D.v (backwardSeed D q).val := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  exact fresh_iff_seed_v_positive (routingData M.base e)

theorem actual_candidate_count_le_fresh (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    Nat.card (PositiveSeedCandidates D) ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D) := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  exact candidate_count_le_fresh (routingData M.base e)

/-- A used seed consumes one actual first-stage slot. This is the used-spike
alternative in a two-source-target-branch configuration. -/
theorem exceptional_le_one_of_two_branches_and_used_seed (D : ResidueData R)
    (q : ResidueData.ExactUnusedMergeBases D)
    (hc : ResidueData.sourceTargetBranchCount D ≤ 2)
    (hv : D.v (backwardSeed D q).val = 0) : ResidueData.cExceptionalCount D ≤ 1 := by
  have hu : ∃ s, ResidueData.cFirstStagePairing D s = q := (used_iff_seed_v_zero D q).2 hv
  have hp : 0 < ResidueData.cUsedFirstStageCount D := by
    apply Nat.card_pos_iff.2
    exact ⟨⟨⟨q, hu⟩⟩, by
      letI : Finite (ResidueData.ExactUnusedMergeBases D) := Subtype.finite
      exact Subtype.finite⟩
  have hstage := ResidueData.c_firstStage_card_identity D
  omega

/-- Conditional local compensation from an actual unused merge and at most two
source-target branches. Neither condition is inferred here from a p=3 signature. -/
theorem compensation_of_two_branches_and_unused (D : ResidueData R)
    (hc : ResidueData.sourceTargetBranchCount D ≤ 2)
    (q : ResidueData.ExactUnusedMergeBases D) :
    ResidueData.cExceptionalCount D ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D) + 1 := by
  by_cases hv : D.v (backwardSeed D q).val = 0
  · have h := exceptional_le_one_of_two_branches_and_used_seed D q hc hv
    omega
  · have hf : 0 < Nat.card (ResidueData.CFreshUnusedMergeBases D) := by
      apply Nat.card_pos_iff.2
      exact ⟨⟨⟨q, (fresh_iff_seed_v_positive D q).2 (by omega)⟩⟩, by
        letI : Finite (ResidueData.ExactUnusedMergeBases D) := Subtype.finite
        exact Subtype.finite⟩
    have hstage := ResidueData.c_firstStage_card_identity D
    omega

theorem actual_compensation_of_two_branches_and_unused (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    ResidueData.sourceTargetBranchCount D ≤ 2 →
    ResidueData.ExactUnusedMergeBases D →
    ResidueData.cExceptionalCount D ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D) + 1 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  exact compensation_of_two_branches_and_unused (routingData M.base e)

end NS25Lean.P3R52
