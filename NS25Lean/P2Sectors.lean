import NS25Lean.P2Signatures

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A1
open L2B
variable {Gamma : NumericalSemigroup}

open Classical in
/-- Positive contribution support, which can be smaller than the tail Betti support. -/
def positiveDegrees (M : MultiplicityBase Gamma) : Finset ℕ :=
  (activeDegreeFinset M).filter (fun h => 0 < fiberContribution M h)

@[simp] theorem mem_positiveDegrees (M : MultiplicityBase Gamma) (h : ℕ) :
    h ∈ positiveDegrees M ↔ 0 < fiberContribution M h := by
  classical
  simp only [positiveDegrees, Finset.mem_filter, mem_activeDegreeFinset]
  exact ⟨And.right, fun hp => ⟨positive_contribution_active M h hp, hp⟩⟩

theorem contribution_zero_outside_positive (M : MultiplicityBase Gamma) (h : ℕ)
    (hh : h ∉ positiveDegrees M) : fiberContribution M h = 0 := by
  simp only [mem_positiveDegrees, not_lt] at hh
  omega

theorem p2_positive_sum (P : P2Data Gamma) :
    ∑ h ∈ positiveDegrees P.M, fiberContribution P.M h = 2 := by
  classical
  have he := L2B2A2.chosenDefect_eq_contribution_sum P.M
  rw [P.hp] at he
  rw [he]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro h _ hn
  exact contribution_zero_outside_positive P.M h hn

/-- The two possible positive-support partitions, including vanishing everywhere else. -/
theorem p2_exact_partition (P : P2Data Gamma) :
    (∃ h, positiveDegrees P.M = {h} ∧ fiberContribution P.M h = 2 ∧
      ∀ g, g ≠ h → fiberContribution P.M g = 0) ∨
    (∃ h g, h ≠ g ∧ positiveDegrees P.M = {h, g} ∧
      fiberContribution P.M h = 1 ∧ fiberContribution P.M g = 1 ∧
      ∀ x, x ≠ h → x ≠ g → fiberContribution P.M x = 0) := by
  classical
  have hs := p2_positive_sum P
  have hc : (positiveDegrees P.M).card ≤ 2 := by
    calc
      _ = ∑ _h ∈ positiveDegrees P.M, 1 := by simp
      _ ≤ ∑ h ∈ positiveDegrees P.M, fiberContribution P.M h := by
        apply Finset.sum_le_sum
        intro h hh
        exact (mem_positiveDegrees P.M h).mp hh
      _ = 2 := hs
  have hn : (positiveDegrees P.M).Nonempty := by
    by_contra he
    have hz := Finset.not_nonempty_iff_eq_empty.mp he
    simp [hz] at hs
  have hcpos := Finset.card_pos.mpr hn
  have hcases : (positiveDegrees P.M).card = 1 ∨ (positiveDegrees P.M).card = 2 := by omega
  rcases hcases with h1 | h2
  · obtain ⟨h, hh⟩ := Finset.card_eq_one.mp h1
    left
    refine ⟨h, hh, ?_, ?_⟩
    · simpa [hh] using hs
    · intro g hg
      apply contribution_zero_outside_positive
      simpa [hh] using hg
  · obtain ⟨h, g, hne, hpair⟩ := Finset.card_eq_two.mp h2
    have hp : 0 < fiberContribution P.M h := (mem_positiveDegrees P.M h).mp (by simp [hpair])
    have gp : 0 < fiberContribution P.M g := (mem_positiveDegrees P.M g).mp (by simp [hpair])
    have he : fiberContribution P.M h + fiberContribution P.M g = 2 := by
      simpa [hpair, hne] using hs
    right
    refine ⟨h, g, hne, hpair, by omega, by omega, ?_⟩
    intro x hx hg
    apply contribution_zero_outside_positive
    simp [hpair, hx, hg]

theorem p2_three_components_contribution_two (P : P2Data Gamma) (h : ℕ)
    (hh : 0 < h) (hc : componentCount P.M.base h = 3) : fiberContribution P.M h = 2 := by
  classical
  have ha : activeDegreeFinset P.M = {h} := by
    ext g
    simp only [Finset.mem_singleton]
    constructor
    · exact three_components_unique_active P.M h g hh hc
    · intro he
      subst g
      exact (mem_activeDegreeFinset P.M h).mpr ⟨hh, by omega⟩
  have hs := L2B2A2.chosenDefect_eq_contribution_sum P.M
  simpa [P.hp, ha] using hs.symm

/-- The locally possible signature `(3,2)` is impossible in actual P2 data. -/
theorem p2_excludes_three_two (P : P2Data Gamma) (h : ℕ) : ¬ LocalSignature P.M h 3 2 := by
  intro hs
  have he : fiberContribution P.M h = 1 := (contribution_one_iff P.M h).mpr (Or.inr (Or.inr hs))
  have hh := (positive_contribution_active P.M h (by omega)).1
  have := p2_three_components_contribution_two P h hh hs.1
  omega

theorem p2_contribution_one_iff (P : P2Data Gamma) (h : ℕ) :
    fiberContribution P.M h = 1 ↔ LocalSignature P.M h 2 0 ∨ LocalSignature P.M h 2 1 := by
  rw [contribution_one_iff]
  have hn := p2_excludes_three_two P h
  tauto

def SectorY (M : MultiplicityBase Gamma) : Prop :=
  ∃ h, positiveDegrees M = {h} ∧ LocalSignature M h 3 0

def SectorA (M : MultiplicityBase Gamma) : Prop :=
  ∃ h, positiveDegrees M = {h} ∧ LocalSignature M h 3 1

def SectorB (M : MultiplicityBase Gamma) : Prop :=
  ∃ h g, h ≠ g ∧ positiveDegrees M = {h, g} ∧
    LocalSignature M h 2 0 ∧ LocalSignature M g 2 0

/-- Mixed sector, oriented with `(2,0)` first and `(2,1)` second. -/
def SectorC (M : MultiplicityBase Gamma) : Prop :=
  ∃ h g, h ≠ g ∧ positiveDegrees M = {h, g} ∧
    LocalSignature M h 2 0 ∧ LocalSignature M g 2 1

def SectorD (M : MultiplicityBase Gamma) : Prop :=
  ∃ h g, h ≠ g ∧ positiveDegrees M = {h, g} ∧
    LocalSignature M h 2 1 ∧ LocalSignature M g 2 1

/-- Unconditional exhaustive classification of actual P2 positive signatures. -/
theorem p2_five_sectors (P : P2Data Gamma) :
    SectorY P.M ∨ SectorA P.M ∨ SectorB P.M ∨ SectorC P.M ∨ SectorD P.M := by
  classical
  rcases p2_exact_partition P with ⟨h, hh, he, _⟩ | ⟨h, g, hne, hpair, he, ge, _⟩
  · rcases (contribution_two_iff P.M h).mp he with hY | hA
    · exact Or.inl ⟨h, hh, hY⟩
    · exact Or.inr (Or.inl ⟨h, hh, hA⟩)
  · rcases (p2_contribution_one_iff P h).mp he with h0 | h1 <;>
      rcases (p2_contribution_one_iff P g).mp ge with g0 | g1
    · exact Or.inr (Or.inr (Or.inl ⟨h, g, hne, hpair, h0, g0⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, g, hne, hpair, h0, g1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨g, h, Ne.symm hne,
        hpair.trans (Finset.pair_comm h g), g0, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, g, hne, hpair, h1, g1⟩)))

end NS25Lean.L5A1
