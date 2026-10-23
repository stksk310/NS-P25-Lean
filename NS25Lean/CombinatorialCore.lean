/-
Copyright (c) 2026 Keisuke Sato. All rights reserved.
Authors: Keisuke Sato
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# The finite combinatorial core of NS25

This file isolates the graph-theoretic argument used in the relative-ideal
type bound.  The vertices form a finite type.  The permutations `b` and `c`
are the two residue shifts, while `u` and `v` record whether the corresponding
directed edge is present (value zero) or absent (nonzero value).

The main theorem `ResidueData.sinkCount_le_two_mul_sourceCount` proves the
abstract inequality `T ≤ 2S`.  The two degree counts
`E + T = |R| + B` and `E + S = |R| + M` are proved from the definitions, while
the branch estimate `B ≤ S + M` is proved from the diamond identity.
-/

namespace NS25Lean
namespace CombinatorialCore

/-- Finite residue data with two commuting shift directions and the diamond identity. -/
structure ResidueData (R : Type*) where
  u : R → ℕ
  v : R → ℕ
  b : Equiv.Perm R
  c : Equiv.Perm R
  commute : Function.Commute b c
  diamond : ∀ r, u r + v (b r) = v r + u (c r)

namespace ResidueData

variable {R : Type*} [Fintype R] (D : ResidueData R)

/-- No incoming edge in either residue direction. -/
def IsSource (r : R) : Prop :=
  D.u (D.b.symm r) ≠ 0 ∧ D.v (D.c.symm r) ≠ 0

/-- No outgoing edge in either residue direction. -/
def IsSink (r : R) : Prop :=
  D.u r ≠ 0 ∧ D.v r ≠ 0

/-- Both outgoing residue edges are present. -/
def IsBranch (r : R) : Prop :=
  D.u r = 0 ∧ D.v r = 0

/-- Both incoming residue edges are present. -/
def IsMerge (r : R) : Prop :=
  D.u (D.b.symm r) = 0 ∧ D.v (D.c.symm r) = 0

noncomputable def sourceCount : ℕ := Nat.card {r // D.IsSource r}

noncomputable def sinkCount : ℕ := Nat.card {r // D.IsSink r}

noncomputable def branchCount : ℕ := Nat.card {r // D.IsBranch r}

noncomputable def mergeCount : ℕ := Nat.card {r // D.IsMerge r}

/-- The number of directed edges, counting the two residue directions separately. -/
noncomputable def edgeCount : ℕ := by
  exact Nat.card {r // D.u r = 0} + Nat.card {r // D.v r = 0}

private lemma two_predicate_card_identity (p q : R → Prop) :
    Nat.card {r // p r} + Nat.card {r // q r} +
        Nat.card {r // ¬ p r ∧ ¬ q r} =
      Fintype.card R + Nat.card {r // p r ∧ q r} := by
  classical
  let E : Sum (Sum {r // p r} {r // q r}) {r // ¬ p r ∧ ¬ q r} ≃
      Sum R {r // p r ∧ q r} :=
    { toFun := fun x => match x with
        | Sum.inl (Sum.inl r) => Sum.inl r.1
        | Sum.inl (Sum.inr r) =>
            if hp : p r then Sum.inr ⟨r, hp, r.property⟩ else Sum.inl r.1
        | Sum.inr r => Sum.inl r.1
      invFun := fun x => match x with
        | Sum.inl r =>
            if hp : p r then Sum.inl (Sum.inl ⟨r, hp⟩)
            else if hq : q r then Sum.inl (Sum.inr ⟨r, hq⟩)
            else Sum.inr ⟨r, hp, hq⟩
        | Sum.inr r => Sum.inl (Sum.inr ⟨r, r.property.2⟩)
      left_inv := by
        intro x
        rcases x with (⟨r, hr⟩ | ⟨r, hr⟩) | ⟨r, hp, hq⟩
        · simp [hr]
        · by_cases hp : p r <;> simp [hp, hr]
        · simp [hp, hq]
      right_inv := by
        intro x
        rcases x with r | ⟨r, hp, hq⟩
        · by_cases hp : p r
          · simp [hp]
          · by_cases hq : q r <;> simp [hp, hq]
        · simp [hp] }
  simpa [Nat.card_sum, Nat.card_eq_fintype_card] using Nat.card_congr E

private lemma card_comp_symm (e : Equiv.Perm R) (p : R → Prop) :
    Nat.card {r // p (e.symm r)} = Nat.card {r // p r} := by
  classical
  let E : {r // p r} ≃ {r // p (e.symm r)} :=
    { toFun := fun r => ⟨e r, by simpa using r.property⟩
      invFun := fun r => ⟨e.symm r, r.property⟩
      left_inv := fun r => by simp
      right_inv := fun r => by simp }
  exact Nat.card_congr E.symm

/-- Counting outgoing edges by vertex type gives `E + T = |R| + B`. -/
theorem outgoing_edge_count :
    D.edgeCount + D.sinkCount = Fintype.card R + D.branchCount := by
  classical
  simpa [edgeCount, sinkCount, branchCount, IsSink, IsBranch] using
    (two_predicate_card_identity (R := R) (fun r => D.u r = 0) (fun r => D.v r = 0))

/-- Counting incoming edges by vertex type gives `E + S = |R| + M`. -/
theorem incoming_edge_count :
    D.edgeCount + D.sourceCount = Fintype.card R + D.mergeCount := by
  classical
  have h := two_predicate_card_identity (R := R)
    (fun r => D.u (D.b.symm r) = 0) (fun r => D.v (D.c.symm r) = 0)
  have hu := card_comp_symm (R := R) D.b (fun r => D.u r = 0)
  have hv := card_comp_symm (R := R) D.c (fun r => D.v r = 0)
  rw [hu, hv] at h
  simpa [edgeCount, sourceCount, mergeCount, IsSource, IsMerge] using h

/-- The residue reached by completing the `b`/`c` diamond. -/
def branchTarget (r : R) : R := D.c (D.b r)

omit [Fintype R] in
private lemma b_symm_branchTarget (r : R) :
    D.b.symm (D.branchTarget r) = D.c r := by
  apply D.b.injective
  simpa [branchTarget] using (D.commute r).symm

omit [Fintype R] in
private lemma c_symm_branchTarget (r : R) :
    D.c.symm (D.branchTarget r) = D.b r := by
  simp [branchTarget]

omit [Fintype R] in
/-- At a branch, the two edges entering the opposite corner agree. -/
lemma cross_eq_of_isBranch {r : R} (hr : D.IsBranch r) :
    D.v (D.b r) = D.u (D.c r) := by
  simpa [IsBranch, hr.1, hr.2] using D.diamond r

omit [Fintype R] in
/-- The opposite corner of a branch is either a source or a merge. -/
lemma branchTarget_isSource_or_isMerge {r : R} (hr : D.IsBranch r) :
    D.IsSource (D.branchTarget r) ∨ D.IsMerge (D.branchTarget r) := by
  have hcross := D.cross_eq_of_isBranch hr
  by_cases hu : D.u (D.c r) = 0
  · right
    constructor
    · simpa [IsMerge, D.b_symm_branchTarget r] using hu
    · simpa [IsMerge, D.c_symm_branchTarget r, hcross] using hu
  · left
    constructor
    · simpa [IsSource, D.b_symm_branchTarget r] using hu
    · have hv : D.v (D.b r) ≠ 0 := by
        simpa [hcross] using hu
      simpa [IsSource, D.c_symm_branchTarget r] using hv

omit [Fintype R] in
/-- Translation by `b+c` is injective on all vertices. -/
lemma branchTarget_injective : Function.Injective D.branchTarget := by
  intro r s hrs
  apply D.b.injective
  apply D.c.injective
  exact hrs

/-- The diamond identity injects branches into the disjoint choice of sources and merges. -/
theorem branchCount_le_sourceCount_add_mergeCount :
    D.branchCount ≤ D.sourceCount + D.mergeCount := by
  classical
  let target : {r // D.IsBranch r} →
      Sum {s // D.IsSource s} {s // D.IsMerge s} := fun r =>
    if hs : D.IsSource (D.branchTarget r) then
      Sum.inl ⟨D.branchTarget r, hs⟩
    else
      Sum.inr ⟨D.branchTarget r, (D.branchTarget_isSource_or_isMerge r.property).resolve_left hs⟩
  have htarget : Function.Injective target := by
    intro r s hrs
    apply Subtype.ext
    apply D.branchTarget_injective
    have hvals := congrArg
      (Sum.elim (fun x : {z // D.IsSource z} => x.1)
        (fun x : {z // D.IsMerge z} => x.1)) hrs
    calc
      D.branchTarget r = Sum.elim (fun x : {z // D.IsSource z} => x.1)
          (fun x : {z // D.IsMerge z} => x.1) (target r) := by
            simp only [target]
            split <;> rfl
      _ = Sum.elim (fun x : {z // D.IsSource z} => x.1)
          (fun x : {z // D.IsMerge z} => x.1) (target s) := hvals
      _ = D.branchTarget s := by
        simp only [target]
        split <;> rfl
  simpa [branchCount, sourceCount, mergeCount, Nat.card_eq_fintype_card] using
    (Fintype.card_le_of_injective target htarget)

/-- Eliminating the common edge count gives `T + M = S + B`. -/
lemma edge_count_balance {vertexCount edgeCount S T B M : ℕ}
    (outgoing : edgeCount + T = vertexCount + B)
    (incoming : edgeCount + S = vertexCount + M) :
    T + M = S + B := by
  omega

/--
The abstract NS25 combinatorial theorem: the diamond identity plus the two
degree-count equations imply that the number of sinks is at most twice the
number of sources.
-/
theorem sinkCount_le_two_mul_sourceCount_of_edge_counts {edgeCount : ℕ}
    (outgoing : edgeCount + D.sinkCount = Fintype.card R + D.branchCount)
    (incoming : edgeCount + D.sourceCount = Fintype.card R + D.mergeCount) :
    D.sinkCount ≤ 2 * D.sourceCount := by
  have hbalance : D.sinkCount + D.mergeCount =
      D.sourceCount + D.branchCount :=
    edge_count_balance outgoing incoming
  have hbranch := D.branchCount_le_sourceCount_add_mergeCount
  omega

/-- The self-contained finite combinatorial core theorem `T ≤ 2S`. -/
theorem sinkCount_le_two_mul_sourceCount :
    D.sinkCount ≤ 2 * D.sourceCount := by
  exact D.sinkCount_le_two_mul_sourceCount_of_edge_counts
    D.outgoing_edge_count D.incoming_edge_count

end ResidueData
end CombinatorialCore
end NS25Lean
