import NS25Lean.GenericFloorStaircase
import NS25Lean.GenericFloorDirectional

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericFloorStaircase
open CombinatorialCore L5A2C4I P3R67
variable {H : NumericalSemigroup}

/-- Actual canonical rectangle data. Its fields contain no merge, endpoint
or count conclusion. The same final relative ideal is used throughout. -/
structure CanonicalRectangle (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (Imax Jmax : ℕ) : Prop where
  subset : ∀ z : ℤ, z ∈ I → z ∈ H.asRelativeIdeal
  canonical : ∀ i j : ℕ, i < Imax → j < Jmax →
    H.asRelativeIdeal.aperyRepresentative a
      (((i : ℤ) * b + j * c : ℤ) : ZMod a) = (i : ℤ) * b + j * c
  injective : ∀ i j i' j' : ℕ, i < Imax → j < Jmax → i' < Imax → j' < Jmax →
    (((i : ℤ) * b + j * c : ℤ) : ZMod a) =
      (((i' : ℤ) * b + j' * c : ℤ) : ZMod a) → i = i' ∧ j = j'

theorem unused_bound (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) (Imax Jmax : ℕ)
    (R : CanonicalRectangle I a b c Imax Jmax)
    (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (hbounds : ∀ p ∈ S, p.1 < Imax ∧ p.2 < Jmax)
    (hfloor : ∀ i j : ℕ, i < Imax → j < Jmax →
      ((i : ℤ) * b + j * c ∈ I ↔ ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j)) :
    (coordinateMinima S).card - 1 ≤
      Nat.card (ResidueData.ExactUnusedMergeBases (P3R60.idealData I a b c hb hc)) := by
  obtain ⟨base,hinj,hmem,_⟩ := floor_staircase_family I a b c hb hc R.subset
    Imax Jmax S hS R.canonical R.injective hbounds hfloor
  simpa only [Nat.card_fin] using unused_count_of_injective_bases
    (P3R60.idealData I a b c hb hc) base hinj hmem

theorem minima_insert_sentinel (E : Finset (ℕ × ℕ)) (k : ℕ)
    (hanti : ∀ p ∈ E, ∀ q ∈ E, q.1 ≤ p.1 → q.2 ≤ p.2 → p = q)
    (hsep : ∀ p ∈ E, 0 < p.1 ∧ p.2 < k) :
    coordinateMinima (insert (0,k) E) = insert (0,k) E := by
  classical
  ext p
  rw [mem_coordinateMinima]
  constructor
  · exact fun h => h.1
  · intro hp
    refine ⟨hp,?_⟩
    intro q hq hq1 hq2
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · rfl
      · have := hsep q hq
        simp only [Prod.fst] at hq1
        omega
    · rcases Finset.mem_insert.mp hq with rfl | hq
      · have := hsep p hp
        simp only [Prod.snd] at hq2
        omega
      · exact hanti p hp q hq hq1 hq2

/-- k ordinary points and an incomparable zero-column sentinel give k
distinct total merges, also when the ordinary family is empty. -/
theorem sentinel_bound (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) (Imax Jmax : ℕ)
    (R : CanonicalRectangle I a b c Imax Jmax) (k : ℕ) (E : Finset (ℕ × ℕ))
    (hI0 : 0 < Imax) (hkJ : k < Jmax)
    (hanti : ∀ p ∈ E, ∀ q ∈ E, q.1 ≤ p.1 → q.2 ≤ p.2 → p = q)
    (hbounds : ∀ p ∈ E, 0 < p.1 ∧ p.1 < Imax ∧ p.2 < k)
    (hfloor : ∀ i j : ℕ, i < Imax → j < Jmax →
      ((i : ℤ) * b + j * c ∈ I ↔ ∃ p ∈ insert (0,k) E, p.1 ≤ i ∧ p.2 ≤ j)) :
    E.card ≤ Nat.card (ResidueData.ExactUnusedMergeBases (P3R60.idealData I a b c hb hc)) := by
  classical
  have hsep : ∀ p ∈ E, 0 < p.1 ∧ p.2 < k := by
    intro p hp
    exact ⟨(hbounds p hp).1,(hbounds p hp).2.2⟩
  have h := unused_bound I a b c hb hc Imax Jmax R (insert (0,k) E)
    (Finset.insert_nonempty _ _) (by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ⟨hI0,hkJ⟩
      · have hh := hbounds p hp
        exact ⟨hh.2.1,by omega⟩) hfloor
  rw [minima_insert_sentinel E k hanti hsep] at h
  have hn : (0,k) ∉ E := by
    intro hm
    have hh := hsep (0,k) hm
    omega
  simpa only [Finset.card_insert_of_notMem hn,Nat.add_sub_cancel] using h

/-- The actual first c-endpoint, derived through the first-zero corridor in
the same final ideal. An earlier antichain floor point supplies the zero. -/
theorem c_nonexceptional_of_earlier_floor (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) (Imax Jmax : ℕ)
    (R : CanonicalRectangle I a b c Imax Jmax) (S : Finset (ℕ × ℕ))
    (hfloor : ∀ i j : ℕ, i < Imax → j < Jmax →
      ((i : ℤ) * b + j * c ∈ I ↔ ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j))
    (s : ResidueData.CSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (i j x y : ℕ) (hiI : i < Imax) (hyJ : y < Jmax)
    (hp : (x,y) ∈ S) (hxi : x < i) (hjy : j < y)
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val) =
      ((i * b + j * c : ℕ) : ℤ)) :
    ResidueData.CFirstStageNonexceptional (P3R60.idealData I a b c hb hc) s := by
  apply GenericFloorDirectional.c_nonexceptional_of_left_zero I a b c hb hc R.subset Imax Jmax
    (by intro r t hr ht; simpa only [Nat.cast_add,Nat.cast_mul] using R.canonical r t hr ht)
    s i j x y hiI hyJ hxi hjy ht
  have hm := (hfloor x y (by omega) hyJ).mpr ⟨(x,y),hp,le_rfl,le_rfl⟩
  simpa only [Nat.cast_add,Nat.cast_mul] using hm

/-- Literal b/c transpose on the SAME final ideal and residue carrier.
The conclusion concerns the actual first b-endpoint of the supplied branch. -/
theorem b_nonexceptional_of_later_floor (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H) (Imax Jmax : ℕ)
    (R : CanonicalRectangle I a b c Imax Jmax) (S : Finset (ℕ × ℕ))
    (hfloor : ∀ i j : ℕ, i < Imax → j < Jmax →
      ((i : ℤ) * b + j * c ∈ I ↔ ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j))
    (s : ResidueData.BSourceTargetBranches (P3R60.idealData I a b c hb hc))
    (i j x y : ℕ) (hjJ : j < Jmax) (hxI : x < Imax)
    (hp : (x,y) ∈ S) (hix : i < x) (hyj : y < j)
    (ht : I.aperyRepresentative a ((P3R60.idealData I a b c hb hc).branchTarget s.val) =
      ((i * b + j * c : ℕ) : ℤ)) :
    ResidueData.BFirstStageNonexceptional (P3R60.idealData I a b c hb hc) s := by
  apply GenericFloorDirectional.b_nonexceptional_of_right_zero I a b c hb hc R.subset Imax Jmax
    (by intro r u hr hu;simpa only [Nat.cast_add,Nat.cast_mul] using R.canonical r u hr hu)
    s i j x y hjJ hxI hix hyj ht
  have hzero := (hfloor x y hxI (by omega)).mpr ⟨(x,y),hp,le_rfl,le_rfl⟩
  simpa only [Nat.cast_add,Nat.cast_mul] using hzero

end NS25Lean.GenericFloorStaircase

#print axioms NS25Lean.GenericFloorStaircase.floor_staircase_family
#print axioms NS25Lean.GenericFloorStaircase.sentinel_bound
#print axioms NS25Lean.GenericFloorStaircase.c_nonexceptional_of_earlier_floor
#print axioms NS25Lean.GenericFloorStaircase.b_nonexceptional_of_later_floor
