import NS25Lean.GenericFloorExceptional

set_option autoImplicit false
noncomputable section
namespace NS25Lean.FloorZeroChecks
open GenericFloorStaircase CombinatorialCore L5A2C4I
variable {H : NumericalSemigroup}

def floorPoints : Finset (ℕ × ℕ) := {(0,2),(1,0)}

theorem zero_floor_iff (i j : ℕ) :
    (1 ≤ i ∨ 2 ≤ j) ↔ ∃ p ∈ floorPoints, p.1 ≤ i ∧ p.2 ≤ j := by
  simp [floorPoints]
  omega

/-- This exact boundary pattern is realized by H=<6,7,8> and I=(7,16)+H.
The generic application must accept the ordinary floor point (1,0). -/
example (I : RelativeIdeal H) (a b c : ℕ) [NeZero a] (hb : b ∈ H) (hc : c ∈ H)
    (R : CanonicalRectangle I a b c 2 3)
    (hfloor : ∀ i j : ℕ, i < 2 → j < 3 →
      ((i : ℤ) * b + j * c ∈ I ↔ 1 ≤ i ∨ 2 ≤ j)) :
    1 ≤ Nat.card (ResidueData.ExactUnusedMergeBases (P3R60.idealData I a b c hb hc)) := by
  have h := sentinel_bound I a b c hb hc 2 3 R 2 {(1,0)} (by decide) (by decide)
    (by simp only [Finset.mem_singleton];intro p hp q hq _ _;simpa [hp,hq])
    (by simp)
    (by intro i j hi hj;rw [hfloor i j hi hj];simp <;> omega)
  simpa using h

/-- The actual first c-endpoint may be invoked at target coordinate j=0. -/
example (I : RelativeIdeal H) (a b c : ℕ) [NeZero a] (hb : b ∈ H) (hc : c ∈ H)
    (R : CanonicalRectangle I a b c 2 3)
    (hfloor : ∀ i j : ℕ, i < 2 → j < 3 →
      ((i : ℤ) * b + j * c ∈ I ↔ 1 ≤ i ∨ 2 ≤ j))
    (s : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val)=(b:ℤ)) :
    ResidueData.CFirstStageNonexceptional (P3R60.idealData I a b c hb hc) s := by
  apply c_nonexceptional_of_earlier_floor I a b c hb hc 2 3 R floorPoints
    (by intro i j hi hj;rw [hfloor i j hi hj];exact zero_floor_iff i j)
    s 1 0 0 2 (by decide) (by decide) (by simp [floorPoints]) (by decide) (by decide)
  simpa using ht

/-- The literal transpose also admits a target in the zero first column. -/
example (I : RelativeIdeal H) (a b c : ℕ) [NeZero a] (hb : b ∈ H) (hc : c ∈ H)
    (R : CanonicalRectangle I a b c 3 2)
    (hfloor : ∀ i j : ℕ, i < 3 → j < 2 →
      ((i : ℤ) * b + j * c ∈ I ↔ 2 ≤ i ∨ 1 ≤ j))
    (s : ResidueData.BSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val)=(c:ℤ)) :
    ResidueData.BFirstStageNonexceptional (P3R60.idealData I a b c hb hc) s := by
  apply b_nonexceptional_of_later_floor I a b c hb hc 3 2 R {(2,0),(0,1)}
    (by intro i j hi hj;rw [hfloor i j hi hj];simp <;> omega)
    s 0 1 2 0 (by decide) (by decide) (by simp) (by decide) (by decide)
  simpa using ht

/-- An empty ordinary family permits the sentinel itself to be (0,0). -/
example (I : RelativeIdeal H) (a b c : ℕ) [NeZero a] (hb : b ∈ H) (hc : c ∈ H)
    (R : CanonicalRectangle I a b c 1 1)
    (hfloor : ∀ i j : ℕ, i < 1 → j < 1 → (i:ℤ)*b+j*c∈I) :
    0 ≤ Nat.card (ResidueData.ExactUnusedMergeBases (P3R60.idealData I a b c hb hc)) := by
  have h := sentinel_bound I a b c hb hc 1 1 R 0 ∅ (by decide) (by decide)
    (by simp) (by simp) (by
      intro i j hi hj
      constructor
      · intro _
        exact ⟨(0,0),by simp,Nat.zero_le _,Nat.zero_le _⟩
      · intro _
        exact hfloor i j hi hj)
  simpa using h

#print axioms GenericFloorDirectional.c_nonexceptional_of_left_zero
#print axioms GenericFloorDirectional.b_nonexceptional_of_right_zero
#print axioms c_exceptional_has_least_first
#print axioms b_exceptional_has_greatest_first
end NS25Lean.FloorZeroChecks
