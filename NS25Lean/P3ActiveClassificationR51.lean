import NS25Lean.P2Sectors

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R51
open L2B L5A1
variable {Gamma : NumericalSemigroup}

/-- A three-component tail Betti degree forces defect at most two. -/
theorem defect_le_two_of_three_components (M : MultiplicityBase Gamma) (h : ℕ)
    (hh : 0 < h) (hc : componentCount M.base h = 3) :
    chosenDefect M.base ≤ 2 := by
  classical
  have ha : activeDegreeFinset M = {h} := by
    ext g
    simp only [Finset.mem_singleton]
    constructor
    · exact three_components_unique_active M h g hh hc
    · intro he
      subst g
      exact (mem_activeDegreeFinset M h).mpr ⟨hh, by omega⟩
  have hs := L2B2A2.chosenDefect_eq_contribution_sum M
  have hl := fiberContribution_le M h
  simp only [ha, Finset.sum_singleton] at hs
  omega

/-- No tail Betti degree, even one with zero contribution, has three components at p=3. -/
theorem active_componentCount_eq_two (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (h : ℕ) (hh : h ∈ activeDegreeFinset M) :
    componentCount M.base h = 2 := by
  have ha := (mem_activeDegreeFinset M h).mp hh
  have hu := componentCount_le_three M.base h ha.1
  have hn : componentCount M.base h ≠ 3 := by
    intro hc
    have := defect_le_two_of_three_components M h ha.1 hc
    omega
  omega

theorem positive_contribution_eq_one (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (h : ℕ) (hh : h ∈ positiveDegrees M) :
    fiberContribution M h = 1 := by
  have he := (mem_positiveDegrees M h).mp hh
  have ha := positive_contribution_active M h he
  have hc := active_componentCount_eq_two M hp h ((mem_activeDegreeFinset M h).mpr ha)
  have hl := fiberContribution_le M h
  omega

theorem positive_signature (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (h : ℕ) (hh : h ∈ positiveDegrees M) :
    LocalSignature M h 2 0 ∨ LocalSignature M h 2 1 := by
  have he := positive_contribution_eq_one M hp h hh
  have hs := (contribution_one_iff M h).mp he
  have hc := active_componentCount_eq_two M hp h
    ((mem_activeDegreeFinset M h).mpr (positive_contribution_active M h (by omega)))
  rcases hs with hs | hs | hs
  · exact Or.inl hs
  · exact Or.inr hs
  · have := hs.1; omega

theorem positive_sum (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) :
    ∑ h ∈ positiveDegrees M, fiberContribution M h = 3 := by
  classical
  have he := L2B2A2.chosenDefect_eq_contribution_sum M
  rw [hp] at he
  rw [he]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro h _ hn
  exact contribution_zero_outside_positive M h hn

theorem positiveDegrees_card (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) :
    (positiveDegrees M).card = 3 := by
  classical
  have hs := positive_sum M hp
  have he : ∑ h ∈ positiveDegrees M, fiberContribution M h =
      ∑ _h ∈ positiveDegrees M, 1 := by
    apply Finset.sum_congr rfl
    exact positive_contribution_eq_one M hp
  simpa only [he, Finset.sum_const, smul_eq_mul, mul_one] using hs

/-- Exactly three distinct actual degrees, their signatures, and vanishing everywhere else. -/
theorem active_three_degrees (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) :
    ∃ h₀ h₁ h₂ : ℕ, h₀ ≠ h₁ ∧ h₀ ≠ h₂ ∧ h₁ ≠ h₂ ∧
      positiveDegrees M = {h₀, h₁, h₂} ∧
      (∀ h ∈ ({h₀, h₁, h₂} : Finset ℕ), fiberContribution M h = 1 ∧
        (LocalSignature M h 2 0 ∨ LocalSignature M h 2 1)) ∧
      (∀ h, h ≠ h₀ → h ≠ h₁ → h ≠ h₂ → fiberContribution M h = 0) := by
  classical
  obtain ⟨h₀, h₁, h₂, h01, h02, h12, he⟩ :=
    Finset.card_eq_three.mp (positiveDegrees_card M hp)
  refine ⟨h₀, h₁, h₂, h01, h02, h12, he, ?_, ?_⟩
  · intro h hh
    rw [← he] at hh
    exact ⟨positive_contribution_eq_one M hp h hh, positive_signature M hp h hh⟩
  · intro h h0 h1 h2
    apply contribution_zero_outside_positive
    simp [he, h0, h1, h2]

open Classical in
def internalDegrees (M : MultiplicityBase Gamma) : Finset ℕ :=
  (positiveDegrees M).filter (fun h => killedCount M h = 0)

open Classical in
def boundaryDegrees (M : MultiplicityBase Gamma) : Finset ℕ :=
  (positiveDegrees M).filter (fun h => killedCount M h ≠ 0)

theorem signature_partition (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) :
    Disjoint (internalDegrees M) (boundaryDegrees M) ∧
      internalDegrees M ∪ boundaryDegrees M = positiveDegrees M ∧
      (internalDegrees M).card + (boundaryDegrees M).card = 3 := by
  classical
  refine ⟨Finset.disjoint_filter_filter_not _ _ _, ?_, ?_⟩
  · exact Finset.filter_union_filter_not_eq _ _
  · simpa only [internalDegrees, boundaryDegrees, positiveDegrees_card M hp] using
      (Finset.card_filter_add_card_filter_not (s := positiveDegrees M)
        (fun h => killedCount M h = 0))

theorem mem_internalDegrees_iff (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (h : ℕ) :
    h ∈ internalDegrees M ↔ LocalSignature M h 2 0 := by
  classical
  simp only [internalDegrees, Finset.mem_filter, mem_positiveDegrees]
  constructor
  · rintro ⟨hh, hd⟩
    exact ⟨active_componentCount_eq_two M hp h
      ((mem_activeDegreeFinset M h).mpr (positive_contribution_active M h hh)), hd⟩
  · rintro ⟨hc, hd⟩
    exact ⟨by simp [fiberContribution, hc, hd], hd⟩

theorem mem_boundaryDegrees_iff (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (h : ℕ) :
    h ∈ boundaryDegrees M ↔ LocalSignature M h 2 1 := by
  classical
  simp only [boundaryDegrees, Finset.mem_filter, mem_positiveDegrees]
  constructor
  · rintro ⟨hh, hd⟩
    have hs := positive_signature M hp h ((mem_positiveDegrees M h).mpr hh)
    rcases hs with hs | hs
    · exact False.elim (hd hs.2)
    · exact hs
  · rintro ⟨hc, hd⟩
    exact ⟨by simp [fiberContribution, hc, hd], by omega⟩

/-- The support budget is saturated; no zero-contribution tail Betti degrees remain. -/
theorem active_eq_positive (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) :
    activeDegreeFinset M = positiveDegrees M := by
  classical
  have hbound : (activeDegreeFinset M).card ≤ 3 := by
    calc
      _ = ∑ _h ∈ activeDegreeFinset M, 1 := by simp
      _ ≤ ∑ h ∈ activeDegreeFinset M, singletonComponentCount M h := by
        apply Finset.sum_le_sum
        intro h hh
        have ha := (mem_activeDegreeFinset M h).mp hh
        have hl := componentCount_sub_one_le_singletons M h ha.1
        omega
      _ ≤ 3 := singleton_sum_le_three M _ (fun h hh => (mem_activeDegreeFinset M h).mp hh)
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
  change (activeDegreeFinset M).card ≤ (positiveDegrees M).card
  rw [positiveDegrees_card M hp]
  exact hbound

/-- The four cases use the exact count of internal degrees, with no orientation choice. -/
theorem internal_count_cases (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) :
    (internalDegrees M).card = 0 ∨ (internalDegrees M).card = 1 ∨
      (internalDegrees M).card = 2 ∨ (internalDegrees M).card = 3 := by
  have hl : (internalDegrees M).card ≤ (positiveDegrees M).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hc := positiveDegrees_card M hp
  omega

/-- R0, R1, R2 and R3, in order, with both exact cardinalities. -/
theorem signature_count_pairs (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) :
    ((internalDegrees M).card = 0 ∧ (boundaryDegrees M).card = 3) ∨
    ((internalDegrees M).card = 1 ∧ (boundaryDegrees M).card = 2) ∨
    ((internalDegrees M).card = 2 ∧ (boundaryDegrees M).card = 1) ∨
    ((internalDegrees M).card = 3 ∧ (boundaryDegrees M).card = 0) := by
  have hsum := (signature_partition M hp).2.2
  have hcases := internal_count_cases M hp
  omega

/-- Original-binder classification on the entire actual tail Betti support. -/
theorem p3_active_classification (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) :
    (activeDegreeFinset M).card = 3 ∧
      (∀ h ∈ activeDegreeFinset M, fiberContribution M h = 1 ∧
        (LocalSignature M h 2 0 ∨ LocalSignature M h 2 1)) ∧
      ((internalDegrees M).card = 0 ∨ (internalDegrees M).card = 1 ∨
        (internalDegrees M).card = 2 ∨ (internalDegrees M).card = 3) := by
  rw [active_eq_positive M hp]
  exact ⟨positiveDegrees_card M hp, fun h hh =>
    ⟨positive_contribution_eq_one M hp h hh, positive_signature M hp h hh⟩,
    internal_count_cases M hp⟩

end NS25Lean.P3R51
