import NS25Lean.P2SectorCLocalCollisionAccounting

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4K

open CombinatorialCore
open L5A2C4H
open L5A2C4I
open L5A2C4J

namespace ResidueData

variable {R : Type*} [Fintype R] (D : CombinatorialCore.ResidueData R)

/-! ### K1: literal legal raw histories -/

inductive RawDirection where
  | b
  | c
deriving DecidableEq, Repr

def step (d : RawDirection) (r : R) : R :=
  match d with
  | .b => D.b r
  | .c => D.c r

def LegalEdge (d : RawDirection) (r : R) : Prop :=
  match d with
  | .b => D.u r = 0
  | .c => D.v r = 0

def follow (r : R) : List RawDirection → R
  | [] => r
  | d :: w => follow (step D d r) w

def WordLegal (r : R) : List RawDirection → Prop
  | [] => True
  | d :: w => LegalEdge D d r ∧ WordLegal (step D d r) w

theorem follow_append (r : R) (w₁ w₂ : List RawDirection) :
    follow D r (w₁ ++ w₂) = follow D (follow D r w₁) w₂ := by
  induction w₁ generalizing r with
  | nil => rfl
  | cons d w ih => simp [follow, ih]

theorem wordLegal_append (r : R) (w₁ w₂ : List RawDirection) :
    WordLegal D r (w₁ ++ w₂) ↔
      WordLegal D r w₁ ∧ WordLegal D (follow D r w₁) w₂ := by
  induction w₁ generalizing r with
  | nil => simp [WordLegal, follow]
  | cons d w ih => simp [WordLegal, follow, ih, and_assoc]

structure RawHistory where
  start : R
  word : List RawDirection
  legal : WordLegal D start word

namespace RawHistory

def length (H : RawHistory D) : ℕ := H.word.length

def stateAt (H : RawHistory D) (n : ℕ) : R :=
  follow D H.start (H.word.take n)

def endpoint (H : RawHistory D) : R := follow D H.start H.word

@[simp] theorem stateAt_zero (H : RawHistory D) : stateAt D H 0 = H.start := by
  simp [stateAt, follow]

@[simp] theorem stateAt_length (H : RawHistory D) :
    stateAt D H (length D H) = endpoint D H := by
  simp [stateAt, length, endpoint]

def prefixHistory (H : RawHistory D) (n : ℕ) : RawHistory D where
  start := H.start
  word := H.word.take n
  legal := by
    have h := H.legal
    rw [← H.word.take_append_drop n] at h
    exact (wordLegal_append D H.start _ _).1 h |>.1

def «prefix» (H : RawHistory D) (n : ℕ) : RawHistory D := prefixHistory D H n

def suffix (H : RawHistory D) (n : ℕ) : RawHistory D where
  start := stateAt D H n
  word := H.word.drop n
  legal := by
    have h := H.legal
    rw [← H.word.take_append_drop n] at h
    exact (wordLegal_append D H.start _ _).1 h |>.2

@[simp] theorem prefix_start (H : RawHistory D) (n : ℕ) :
    (prefixHistory D H n).start = H.start := rfl

@[simp] theorem prefix_word (H : RawHistory D) (n : ℕ) :
    (prefixHistory D H n).word = H.word.take n := rfl

@[simp] theorem suffix_start (H : RawHistory D) (n : ℕ) :
    (suffix D H n).start = stateAt D H n := rfl

@[simp] theorem suffix_word (H : RawHistory D) (n : ℕ) :
    (suffix D H n).word = H.word.drop n := rfl

theorem endpoint_eq_stateAt (H : RawHistory D) :
    endpoint D H = stateAt D H (length D H) := (stateAt_length D H).symm

theorem legal_last_of_append (H : RawHistory D) (p : List RawDirection)
    (d : RawDirection) (hw : H.word = p ++ [d]) :
    LegalEdge D d (follow D H.start p) := by
  have h := H.legal
  rw [hw] at h
  exact ((wordLegal_append D H.start p [d]).1 h).2.1

theorem stateAt_prefix_length (H : RawHistory D) (p : List RawDirection)
    (d : RawDirection) (hw : H.word = p ++ [d]) :
    stateAt D H p.length = follow D H.start p := by
  simp [stateAt, hw]

theorem endpoint_of_append (H : RawHistory D) (p : List RawDirection)
    (d : RawDirection) (hw : H.word = p ++ [d]) :
    endpoint D H = step D d (follow D H.start p) := by
  simp [endpoint, hw, follow_append, follow]

@[simp] theorem endpoint_suffix (H : RawHistory D) (n : ℕ) :
    endpoint D (suffix D H n) = endpoint D H := by
  change follow D (follow D H.start (H.word.take n)) (H.word.drop n) =
    follow D H.start H.word
  rw [← follow_append, H.word.take_append_drop]

end RawHistory

abbrev stateAt (H : RawHistory D) (n : ℕ) : R := RawHistory.stateAt D H n

def «prefix» (H : RawHistory D) (n : ℕ) : RawHistory D :=
  RawHistory.prefixHistory D H n

def suffix (H : RawHistory D) (n : ℕ) : RawHistory D := RawHistory.suffix D H n

/-! ### K2: genuine first coalescence -/

structure FirstCoalescence (H₁ H₂ : RawHistory D) where
  leftPrefix : List RawDirection
  leftLast : RawDirection
  left_word : H₁.word = leftPrefix ++ [leftLast]
  rightPrefix : List RawDirection
  rightLast : RawDirection
  right_word : H₂.word = rightPrefix ++ [rightLast]
  meet : RawHistory.endpoint D H₁ = RawHistory.endpoint D H₂
  earlier_disjoint : ∀ i j,
    i < RawHistory.length D H₁ → j < RawHistory.length D H₂ →
      RawHistory.stateAt D H₁ i ≠ RawHistory.stateAt D H₂ j

theorem firstCoalescence_opposite_last {H₁ H₂ : RawHistory D}
    (h : FirstCoalescence D H₁ H₂) :
    (h.leftLast = RawDirection.b ∧ h.rightLast = RawDirection.c) ∨
      (h.leftLast = RawDirection.c ∧ h.rightLast = RawDirection.b) := by
  have hlen₁ : h.leftPrefix.length < RawHistory.length D H₁ := by
    simp [RawHistory.length, h.left_word]
  have hlen₂ : h.rightPrefix.length < RawHistory.length D H₂ := by
    simp [RawHistory.length, h.right_word]
  have hpred :
      follow D H₁.start h.leftPrefix ≠ follow D H₂.start h.rightPrefix := by
    have hd := h.earlier_disjoint h.leftPrefix.length h.rightPrefix.length hlen₁ hlen₂
    rw [RawHistory.stateAt_prefix_length D H₁ h.leftPrefix h.leftLast h.left_word,
      RawHistory.stateAt_prefix_length D H₂ h.rightPrefix h.rightLast h.right_word] at hd
    exact hd
  have hend :
      step D h.leftLast (follow D H₁.start h.leftPrefix) =
        step D h.rightLast (follow D H₂.start h.rightPrefix) := by
    rw [← RawHistory.endpoint_of_append D H₁ h.leftPrefix h.leftLast h.left_word,
      ← RawHistory.endpoint_of_append D H₂ h.rightPrefix h.rightLast h.right_word]
    exact h.meet
  cases hl : h.leftLast <;> cases hr : h.rightLast
  · exfalso
    apply hpred
    apply D.b.injective
    simpa [step, hl, hr] using hend
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exfalso
    apply hpred
    apply D.c.injective
    simpa [step, hl, hr] using hend

private theorem mixedReverseBase_of_b_c
    {x y T : R} (hbx : D.b x = T) (hcy : D.c y = T)
    (hux : D.u x = 0) (hvy : D.v y = 0) :
    ∃ r, T = D.branchTarget r ∧
      L5A2C4J.ResidueData.MixedCoalescenceReverseBase D r := by
  let r := D.c.symm x
  have hcr : D.c r = x := by simp [r]
  have hbr : D.b r = y := by
    apply D.c.injective
    rw [← D.commute r, hcr, hbx, hcy]
  refine ⟨r, ?_, ?_⟩
  · simp [CombinatorialCore.ResidueData.branchTarget, hbr, hcy]
  · exact ⟨by simpa [hcr] using hux, by simpa [hbr] using hvy⟩

theorem firstCoalescence_mixedReverseBase {H₁ H₂ : RawHistory D}
    (h : FirstCoalescence D H₁ H₂) :
    ∃ r, RawHistory.endpoint D H₁ = D.branchTarget r ∧
      L5A2C4J.ResidueData.MixedCoalescenceReverseBase D r := by
  have hop := firstCoalescence_opposite_last D h
  rcases hop with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · have hleft := RawHistory.endpoint_of_append D H₁ h.leftPrefix h.leftLast h.left_word
    have hright := RawHistory.endpoint_of_append D H₂ h.rightPrefix h.rightLast h.right_word
    have hu := RawHistory.legal_last_of_append D H₁ h.leftPrefix h.leftLast h.left_word
    have hv := RawHistory.legal_last_of_append D H₂ h.rightPrefix h.rightLast h.right_word
    have hleft' : D.b (follow D H₁.start h.leftPrefix) =
        RawHistory.endpoint D H₁ := by simpa [step, hl] using hleft.symm
    have hright' : D.c (follow D H₂.start h.rightPrefix) =
        RawHistory.endpoint D H₁ := by simpa [step, hr, h.meet] using hright.symm
    have hu' : D.u (follow D H₁.start h.leftPrefix) = 0 := by
      simpa [LegalEdge, hl] using hu
    have hv' : D.v (follow D H₂.start h.rightPrefix) = 0 := by
      simpa [LegalEdge, hr] using hv
    exact mixedReverseBase_of_b_c D hleft' hright' hu' hv'
  · have hleft := RawHistory.endpoint_of_append D H₁ h.leftPrefix h.leftLast h.left_word
    have hright := RawHistory.endpoint_of_append D H₂ h.rightPrefix h.rightLast h.right_word
    have hv := RawHistory.legal_last_of_append D H₁ h.leftPrefix h.leftLast h.left_word
    have hu := RawHistory.legal_last_of_append D H₂ h.rightPrefix h.rightLast h.right_word
    have hright' : D.b (follow D H₂.start h.rightPrefix) =
        RawHistory.endpoint D H₁ := by simpa [step, hr, h.meet] using hright.symm
    have hleft' : D.c (follow D H₁.start h.leftPrefix) =
        RawHistory.endpoint D H₁ := by simpa [step, hl] using hleft.symm
    have hu' : D.u (follow D H₂.start h.rightPrefix) = 0 := by
      simpa [LegalEdge, hr] using hu
    have hv' : D.v (follow D H₁.start h.leftPrefix) = 0 := by
      simpa [LegalEdge, hl] using hv
    exact mixedReverseBase_of_b_c D hright' hleft' hu' hv'

theorem firstCoalescence_collision_dichotomy {H₁ H₂ : RawHistory D}
    (h : FirstCoalescence D H₁ H₂) :
    ∃ r, RawHistory.endpoint D H₁ = D.branchTarget r ∧
      ((L5A2C4I.ResidueData.ExactUnusedMergeReverseBase D r ∨
          L5A2C4J.ResidueData.PairedZeroDiamond D r) ∧
        ¬ (L5A2C4I.ResidueData.ExactUnusedMergeReverseBase D r ∧
          L5A2C4J.ResidueData.PairedZeroDiamond D r)) := by
  rcases firstCoalescence_mixedReverseBase D h with ⟨r, ht, hm⟩
  exact ⟨r, ht, L5A2C4J.ResidueData.mixedCoalescence_exact_dichotomy D hm⟩

/-! ### K3: one actual paired-zero displacement, without a termination claim -/

def OneStepArmDisplacement (H : RawHistory D) (r : R) (m : ℕ) : Prop :=
  m < RawHistory.length D H ∧
    (RawHistory.stateAt D H m = D.c r ∨ RawHistory.stateAt D H m = D.b r)

theorem pairedZero_oneStep_displacement {H : RawHistory D} {r : R}
    (hpaired : L5A2C4J.ResidueData.PairedZeroDiamond D r)
    (hend : RawHistory.endpoint D H = D.branchTarget r)
    (p : List RawDirection) (d : RawDirection) (hw : H.word = p ++ [d]) :
    OneStepArmDisplacement D H r p.length := by
  have hlt : p.length < RawHistory.length D H := by simp [RawHistory.length, hw]
  have hstate := RawHistory.stateAt_prefix_length D H p d hw
  have hlast := RawHistory.endpoint_of_append D H p d hw
  refine ⟨hlt, ?_⟩
  cases d with
  | b =>
      left
      rw [hstate]
      apply D.b.injective
      have hb : D.b (follow D H.start p) = RawHistory.endpoint D H := by
        simpa [step] using hlast.symm
      rw [hb, hend]
      exact (D.commute r).symm
  | c =>
      right
      rw [hstate]
      apply D.c.injective
      have hc : D.c (follow D H.start p) = RawHistory.endpoint D H := by
        simpa [step] using hlast.symm
      rw [hc, hend]
      rfl

/-! ### K4: first raw-word divergence -/

structure FirstDivergence (H₁ H₂ : RawHistory D) where
  commonStart : H₁.start = H₂.start
  commonPrefix : List RawDirection
  leftDirection : RawDirection
  rightDirection : RawDirection
  leftSuffix : List RawDirection
  rightSuffix : List RawDirection
  left_word : H₁.word = commonPrefix ++ leftDirection :: leftSuffix
  right_word : H₂.word = commonPrefix ++ rightDirection :: rightSuffix
  directions_ne : leftDirection ≠ rightDirection

private theorem legal_head_after_append (H : RawHistory D) (p : List RawDirection)
    (d : RawDirection) (s : List RawDirection)
    (hw : H.word = p ++ d :: s) : LegalEdge D d (follow D H.start p) := by
  have h := H.legal
  rw [hw] at h
  exact ((wordLegal_append D H.start p (d :: s)).1 h).2.1

theorem firstDivergence_isBranch {H₁ H₂ : RawHistory D}
    (h : FirstDivergence D H₁ H₂) :
    D.IsBranch (follow D H₁.start h.commonPrefix) := by
  have hl := legal_head_after_append D H₁ h.commonPrefix h.leftDirection
    h.leftSuffix h.left_word
  have hr := legal_head_after_append D H₂ h.commonPrefix h.rightDirection
    h.rightSuffix h.right_word
  rw [← h.commonStart] at hr
  cases hld : h.leftDirection <;> cases hrd : h.rightDirection
  · exact False.elim (h.directions_ne (by simp [hld, hrd]))
  · exact ⟨by simpa [LegalEdge, hld] using hl, by simpa [LegalEdge, hrd] using hr⟩
  · exact ⟨by simpa [LegalEdge, hrd] using hr, by simpa [LegalEdge, hld] using hl⟩
  · exact False.elim (h.directions_ne (by simp [hld, hrd]))

theorem firstDivergence_dichotomy {H₁ H₂ : RawHistory D}
    (h : FirstDivergence D H₁ H₂) :
    let X := follow D H₁.start h.commonPrefix
    (L5A2C4I.ResidueData.SourceTargetBranch D X ∨
        L5A2C4J.ResidueData.PairedZeroDiamond D X) ∧
      ¬ (L5A2C4I.ResidueData.SourceTargetBranch D X ∧
        L5A2C4J.ResidueData.PairedZeroDiamond D X) := by
  exact L5A2C4J.ResidueData.branch_exact_dichotomy D
    (firstDivergence_isBranch D h)

/-! ### K5: raw-only source hits and literal replay -/

def SourceHit (H₁ H₂ : RawHistory D) : Prop :=
  ∃ n, n ≤ RawHistory.length D H₁ ∧ RawHistory.stateAt D H₁ n = H₂.start

def LiteralRawReplay (H₁ H₂ : RawHistory D) : Prop :=
  H₁.start = H₂.start ∧ H₁.word = H₂.word

def RawSuffixReplayFrom (H₁ H₂ : RawHistory D) (i j : ℕ) : Prop :=
  RawHistory.stateAt D H₁ i = RawHistory.stateAt D H₂ j ∧
    H₁.word.drop i = H₂.word.drop j

theorem sourceHit_of_common_start {H₁ H₂ : RawHistory D}
    (h : H₁.start = H₂.start) : SourceHit D H₁ H₂ := by
  exact ⟨0, Nat.zero_le _, by simpa [RawHistory.stateAt, follow] using h⟩

theorem literalRawReplay_stateAt {H₁ H₂ : RawHistory D}
    (h : LiteralRawReplay D H₁ H₂) (n : ℕ) :
    RawHistory.stateAt D H₁ n = RawHistory.stateAt D H₂ n := by
  simp [RawHistory.stateAt, h.1, h.2]

theorem literalRawReplay_endpoint {H₁ H₂ : RawHistory D}
    (h : LiteralRawReplay D H₁ H₂) :
    RawHistory.endpoint D H₁ = RawHistory.endpoint D H₂ := by
  simp [RawHistory.endpoint, h.1, h.2]

theorem rawSuffixReplay_endpoint {H₁ H₂ : RawHistory D} {i j : ℕ}
    (h : RawSuffixReplayFrom D H₁ H₂ i j) :
    RawHistory.endpoint D H₁ = RawHistory.endpoint D H₂ := by
  rw [← RawHistory.endpoint_suffix D H₁ i, ← RawHistory.endpoint_suffix D H₂ j]
  simp [RawHistory.endpoint, RawHistory.suffix, h.1, h.2]

/-! ### K3 repaired: actual paired-zero contraction -/

def opposite : RawDirection → RawDirection
  | .b => .c
  | .c => .b

/-- The canonical arm from the paired-zero reverse base to the predecessor of
the selected incoming edge.  Its legality is supplied by the zero branch at
the reverse base, so the paired-zero hypothesis is load-bearing. -/
def pairedZeroCanonicalArm (r : R) (incoming : RawDirection)
    (hpaired : L5A2C4J.ResidueData.PairedZeroDiamond D r) : RawHistory D where
  start := r
  word := [opposite incoming]
  legal := by
    cases incoming <;>
      simp [opposite, WordLegal, LegalEdge, hpaired.1.1, hpaired.1.2]

@[simp] theorem pairedZeroCanonicalArm_start (r : R) (incoming : RawDirection)
    (hpaired : L5A2C4J.ResidueData.PairedZeroDiamond D r) :
    (pairedZeroCanonicalArm D r incoming hpaired).start = r := rfl

@[simp] theorem pairedZeroCanonicalArm_word (r : R) (incoming : RawDirection)
    (hpaired : L5A2C4J.ResidueData.PairedZeroDiamond D r) :
    (pairedZeroCanonicalArm D r incoming hpaired).word = [opposite incoming] := rfl

inductive PairedZeroContractionOutcome
    (original shortened arm : RawHistory D) : Type where
  | sourceReached (h : RawHistory.length D shortened = 0)
  | sourceHit (h : SourceHit D shortened arm)
  | firstCoalescence (h : FirstCoalescence D shortened arm)

/-- Kernel certificate for one source-side displacement at a paired zero
diamond.  The selected history is the left incoming side of the genuine first
coalescence; `shortened` is literally its last-edge prefix. -/
structure PairedZeroContraction {H₁ H₂ : RawHistory D}
    (h : FirstCoalescence D H₁ H₂) (r : R) where
  shortened : RawHistory D
  shortened_eq : shortened = RawHistory.prefixHistory D H₁ h.leftPrefix.length
  arm : RawHistory D
  arm_start : arm.start = r
  arm_word : arm.word = [opposite h.leftLast]
  arm_legal : WordLegal D r [opposite h.leftLast]
  endpoint_eq : RawHistory.endpoint D shortened = RawHistory.endpoint D arm
  length_succ : RawHistory.length D shortened + 1 = RawHistory.length D H₁
  length_lt : RawHistory.length D shortened < RawHistory.length D H₁
  outcome : PairedZeroContractionOutcome D H₁ shortened arm

noncomputable def pairedZero_contract_firstCoalescence {H₁ H₂ : RawHistory D}
    (h : FirstCoalescence D H₁ H₂) {r : R}
    (hend : RawHistory.endpoint D H₁ = D.branchTarget r)
    (hpaired : L5A2C4J.ResidueData.PairedZeroDiamond D r) :
    PairedZeroContraction D h r := by
  let Hshort := RawHistory.prefixHistory D H₁ h.leftPrefix.length
  let A := pairedZeroCanonicalArm D r h.leftLast hpaired
  have hshort_word : Hshort.word = h.leftPrefix := by
    simp [Hshort, h.left_word]
  have hshort_endpoint :
      RawHistory.endpoint D Hshort = follow D H₁.start h.leftPrefix := by
    simp [Hshort, RawHistory.endpoint, h.left_word]
  have hendpoint : RawHistory.endpoint D Hshort = RawHistory.endpoint D A := by
    rw [hshort_endpoint]
    have hlast := RawHistory.endpoint_of_append D H₁ h.leftPrefix h.leftLast h.left_word
    cases hd : h.leftLast with
    | b =>
        have hb : D.b (follow D H₁.start h.leftPrefix) = D.branchTarget r := by
          simpa [step, hd, hend] using hlast.symm
        have hpred : follow D H₁.start h.leftPrefix = D.c r := by
          apply D.b.injective
          rw [hb]
          exact (D.commute r).symm
        simp [A, pairedZeroCanonicalArm, opposite, RawHistory.endpoint, follow,
          step, hd, hpred]
    | c =>
        have hc : D.c (follow D H₁.start h.leftPrefix) = D.branchTarget r := by
          simpa [step, hd, hend] using hlast.symm
        have hpred : follow D H₁.start h.leftPrefix = D.b r := by
          apply D.c.injective
          simpa [CombinatorialCore.ResidueData.branchTarget] using hc
        simp [A, pairedZeroCanonicalArm, opposite, RawHistory.endpoint, follow,
          step, hd, hpred]
  have hlength_succ :
      RawHistory.length D Hshort + 1 = RawHistory.length D H₁ := by
    simp [Hshort, RawHistory.length, h.left_word]
  have hlength_lt :
      RawHistory.length D Hshort < RawHistory.length D H₁ := by omega
  have houtcome : PairedZeroContractionOutcome D H₁ Hshort A := by
    by_cases hz : RawHistory.length D Hshort = 0
    · exact .sourceReached hz
    by_cases hhit : SourceHit D Hshort A
    · exact .sourceHit hhit
    · have hword_ne : Hshort.word ≠ [] := by
        intro hw
        apply hz
        simp [RawHistory.length, hw]
      let last := Hshort.word.getLast hword_ne
      let initial := Hshort.word.dropLast
      have hword : Hshort.word = initial ++ [last] := by
        exact (List.dropLast_append_getLast hword_ne).symm
      have harm_word : A.word = [] ++ [opposite h.leftLast] := by
        simp [A]
      have hearlier : ∀ i j,
          i < RawHistory.length D Hshort → j < RawHistory.length D A →
            RawHistory.stateAt D Hshort i ≠ RawHistory.stateAt D A j := by
        intro i j hi hj heq
        have hj0 : j = 0 := by
          simpa [A, RawHistory.length] using hj
        apply hhit
        refine ⟨i, Nat.le_of_lt hi, ?_⟩
        simpa [hj0, A] using heq
      exact .firstCoalescence
        { leftPrefix := initial
          leftLast := last
          left_word := hword
          rightPrefix := []
          rightLast := opposite h.leftLast
          right_word := harm_word
          meet := hendpoint
          earlier_disjoint := hearlier }
  exact
    { shortened := Hshort
      shortened_eq := rfl
      arm := A
      arm_start := rfl
      arm_word := rfl
      arm_legal := A.legal
      endpoint_eq := hendpoint
      length_succ := hlength_succ
      length_lt := hlength_lt
      outcome := houtcome }

end ResidueData

/-! ### K6: unconditional specialization to the actual chosen-base routing data -/

variable {Gamma : NumericalSemigroup}

theorem actual_firstCoalescence_collision_dichotomy
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ H₁ H₂ : NS25Lean.L5A2C4K.ResidueData.RawHistory D,
      NS25Lean.L5A2C4K.ResidueData.FirstCoalescence D H₁ H₂ →
      ∃ r, NS25Lean.L5A2C4K.ResidueData.RawHistory.endpoint D H₁ =
          D.branchTarget r ∧
        ((L5A2C4I.ResidueData.ExactUnusedMergeReverseBase D r ∨
            L5A2C4J.ResidueData.PairedZeroDiamond D r) ∧
          ¬ (L5A2C4I.ResidueData.ExactUnusedMergeReverseBase D r ∧
            L5A2C4J.ResidueData.PairedZeroDiamond D r)) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro H₁ H₂ h
  exact NS25Lean.L5A2C4K.ResidueData.firstCoalescence_collision_dichotomy
    (routingData B e) h

theorem actual_pairedZero_oneStep_displacement
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ (H : NS25Lean.L5A2C4K.ResidueData.RawHistory D)
      (r : ZMod (routingA B e)),
      L5A2C4J.ResidueData.PairedZeroDiamond D r →
      NS25Lean.L5A2C4K.ResidueData.RawHistory.endpoint D H = D.branchTarget r →
      ∀ (p : List NS25Lean.L5A2C4K.ResidueData.RawDirection)
        (d : NS25Lean.L5A2C4K.ResidueData.RawDirection),
        H.word = p ++ [d] →
          NS25Lean.L5A2C4K.ResidueData.OneStepArmDisplacement D H r p.length := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro H r hp he p d hw
  exact NS25Lean.L5A2C4K.ResidueData.pairedZero_oneStep_displacement
    (routingData B e) hp he p d hw

theorem actual_firstDivergence_dichotomy
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ H₁ H₂ : NS25Lean.L5A2C4K.ResidueData.RawHistory D,
      (h : NS25Lean.L5A2C4K.ResidueData.FirstDivergence D H₁ H₂) →
      let X := NS25Lean.L5A2C4K.ResidueData.follow D H₁.start h.commonPrefix
      (L5A2C4I.ResidueData.SourceTargetBranch D X ∨
          L5A2C4J.ResidueData.PairedZeroDiamond D X) ∧
        ¬ (L5A2C4I.ResidueData.SourceTargetBranch D X ∧
          L5A2C4J.ResidueData.PairedZeroDiamond D X) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro H₁ H₂ h
  exact NS25Lean.L5A2C4K.ResidueData.firstDivergence_dichotomy
    (routingData B e) h

theorem actual_literalRawReplay_endpoint
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ H₁ H₂ : NS25Lean.L5A2C4K.ResidueData.RawHistory D,
      NS25Lean.L5A2C4K.ResidueData.LiteralRawReplay D H₁ H₂ →
      NS25Lean.L5A2C4K.ResidueData.RawHistory.endpoint D H₁ =
        NS25Lean.L5A2C4K.ResidueData.RawHistory.endpoint D H₂ := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro H₁ H₂ h
  exact NS25Lean.L5A2C4K.ResidueData.literalRawReplay_endpoint (routingData B e) h

noncomputable def actual_pairedZero_contract_firstCoalescence
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ (H₁ H₂ : NS25Lean.L5A2C4K.ResidueData.RawHistory D)
      (h : NS25Lean.L5A2C4K.ResidueData.FirstCoalescence D H₁ H₂)
      (r : ZMod (routingA B e)),
      NS25Lean.L5A2C4K.ResidueData.RawHistory.endpoint D H₁ = D.branchTarget r →
      L5A2C4J.ResidueData.PairedZeroDiamond D r →
      NS25Lean.L5A2C4K.ResidueData.PairedZeroContraction D h r := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro H₁ H₂ h r hend hpaired
  exact NS25Lean.L5A2C4K.ResidueData.pairedZero_contract_firstCoalescence
    (routingData B e) h hend hpaired

end NS25Lean.L5A2C4K
