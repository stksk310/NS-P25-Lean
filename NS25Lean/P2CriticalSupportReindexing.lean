import NS25Lean.P2HerzogCore
import NS25Lean.P2SectorBActualRouting

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR4

open ChosenBase L2B L5A1 L5A2B3

variable {Gamma : NumericalSemigroup}

/-- Exact support-shape exhaustion for a positive two-component fiber in
three variables.  The alternatives are pure/pure and pure/mixed; two mixed
components are excluded by the global three-coordinate support budget. -/
theorem two_component_support_shape_exhaustion (B : Data Gamma)
    (h : ℕ) (hcard : Nat.card (FiberComponent B h) = 2) (hpos : 0 < h) :
    (∀ C : FiberComponent B h, (componentSupport B h C).card = 1) ∨
      ∃ C D : FiberComponent B h, C ≠ D ∧
        (((componentSupport B h C).card = 1 ∧
            (componentSupport B h D).card = 2) ∨
          ((componentSupport B h C).card = 2 ∧
            (componentSupport B h D).card = 1)) ∧
        ∀ E : FiberComponent B h, E = C ∨ E = D := by
  classical
  letI := Fintype.ofFinite (FiberComponent B h)
  obtain ⟨C, D, hne, hallSet⟩ := Nat.card_eq_two_iff.mp hcard
  have hall (E : FiberComponent B h) : E = C ∨ E = D := by
    have hmem : E ∈ ({C, D} : Set (FiberComponent B h)) :=
      hallSet.symm ▸ Set.mem_univ E
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hCpos : 0 < (componentSupport B h C).card :=
    Finset.card_pos.mpr (componentSupport_nonempty B h hpos C)
  have hDpos : 0 < (componentSupport B h D).card :=
    Finset.card_pos.mpr (componentSupport_nonempty B h hpos D)
  have hpair :
      (componentSupport B h C).card + (componentSupport B h D).card ≤
        ∑ E : FiberComponent B h, (componentSupport B h E).card := by
    have hs : ({C, D} : Finset (FiberComponent B h)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun E _ _ => Nat.zero_le (componentSupport B h E).card)
    simpa [hne] using hle
  have htotal :
      (componentSupport B h C).card + (componentSupport B h D).card ≤ 3 :=
    hpair.trans (sum_componentSupport_card_le_three B h)
  have hCshape : (componentSupport B h C).card = 1 ∨
      (componentSupport B h C).card = 2 := by omega
  have hDshape : (componentSupport B h D).card = 1 ∨
      (componentSupport B h D).card = 2 := by omega
  rcases hCshape with hCpure | hCmixed
  · rcases hDshape with hDpure | hDmixed
    · left
      intro E
      rcases hall E with rfl | rfl
      · exact hCpure
      · exact hDpure
    · exact Or.inr ⟨C, D, hne, Or.inl ⟨hCpure, hDmixed⟩, hall⟩
  · have hDpure : (componentSupport B h D).card = 1 := by omega
    exact Or.inr ⟨C, D, hne, Or.inr ⟨hCmixed, hDpure⟩, hall⟩

private theorem singletonCount_eq_componentCount_of_all
    (M : MultiplicityBase Gamma) (h : ℕ)
    (hall : ∀ C : FiberComponent M.base h,
      (componentSupport M.base h C).card = 1) :
    singletonComponentCount M h = componentCount M.base h := by
  let e : {C : FiberComponent M.base h //
      (componentSupport M.base h C).card = 1} ≃ FiberComponent M.base h := {
    toFun C := C.1
    invFun C := ⟨C, hall C⟩
    left_inv _ := rfl
    right_inv _ := rfl
  }
  exact Nat.card_congr e

/-- The two distinct actual Sector-B `(2,0)` fibers cannot both be
pure/pure.  This is forced by the three-variable active-singleton budget. -/
theorem sectorB_actual_fibers_not_both_pure
    (P : P2Data Gamma) (h g : ℕ) (hne : h ≠ g)
    (hhpos : 0 < h) (hgpos : 0 < g)
    (hhcard : componentCount P.M.base h = 2)
    (hgcard : componentCount P.M.base g = 2) :
    ¬ ((∀ C : FiberComponent P.M.base h,
          (componentSupport P.M.base h C).card = 1) ∧
        (∀ C : FiberComponent P.M.base g,
          (componentSupport P.M.base g C).card = 1)) := by
  rintro ⟨hhpure, hgpure⟩
  have hhs : singletonComponentCount P.M h = 2 :=
    (singletonCount_eq_componentCount_of_all P.M h hhpure).trans hhcard
  have hgs : singletonComponentCount P.M g = 2 :=
    (singletonCount_eq_componentCount_of_all P.M g hgpure).trans hgcard
  have hbudget := singleton_sum_le_three P.M {h, g} (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨hhpos, by omega⟩
    · exact ⟨hgpos, by omega⟩)
  simp [hne, hhs, hgs] at hbudget

/-- Strongest unconditional support statement presently derivable from the
thin frozen Sector-B signature: both actual fibers have the exact local
shape exhaustion, and at least one is pure/mixed. -/
theorem sectorB_actual_support_shape_checkpoint
    (P : P2Data Gamma) (hB : SectorB P.M) :
    ∃ h g, h ≠ g ∧ positiveDegrees P.M = {h, g} ∧
      componentCount P.M.base h = 2 ∧
      componentCount P.M.base g = 2 ∧
      0 < h ∧ 0 < g ∧
      ((∀ C : FiberComponent P.M.base h,
          (componentSupport P.M.base h C).card = 1) ∨
        ∃ C D : FiberComponent P.M.base h, C ≠ D ∧
          (((componentSupport P.M.base h C).card = 1 ∧
              (componentSupport P.M.base h D).card = 2) ∨
            ((componentSupport P.M.base h C).card = 2 ∧
              (componentSupport P.M.base h D).card = 1)) ∧
          ∀ E : FiberComponent P.M.base h, E = C ∨ E = D) ∧
      ((∀ C : FiberComponent P.M.base g,
          (componentSupport P.M.base g C).card = 1) ∨
        ∃ C D : FiberComponent P.M.base g, C ≠ D ∧
          (((componentSupport P.M.base g C).card = 1 ∧
              (componentSupport P.M.base g D).card = 2) ∨
            ((componentSupport P.M.base g C).card = 2 ∧
              (componentSupport P.M.base g D).card = 1)) ∧
          ∀ E : FiberComponent P.M.base g, E = C ∨ E = D) ∧
      ¬ ((∀ C : FiberComponent P.M.base h,
            (componentSupport P.M.base h C).card = 1) ∧
          (∀ C : FiberComponent P.M.base g,
            (componentSupport P.M.base g C).card = 1)) := by
  obtain ⟨h, g, hne, hdegrees, hhcard, hgcard, _⟩ :=
    sectorB_actualFiberData P hB
  have hhmem : h ∈ positiveDegrees P.M := by rw [hdegrees]; simp
  have hgmem : g ∈ positiveDegrees P.M := by rw [hdegrees]; simp
  have hhactive := positive_contribution_active P.M h
    ((mem_positiveDegrees P.M h).mp hhmem)
  have hgactive := positive_contribution_active P.M g
    ((mem_positiveDegrees P.M g).mp hgmem)
  have hhshape := two_component_support_shape_exhaustion P.M.base h hhcard hhactive.1
  have hgshape := two_component_support_shape_exhaustion P.M.base g hgcard hgactive.1
  exact ⟨h, g, hne, hdegrees, hhcard, hgcard, hhactive.1, hgactive.1,
    hhshape, hgshape,
    sectorB_actual_fibers_not_both_pure P h g hne hhactive.1 hgactive.1 hhcard hgcard⟩

end NS25Lean.L5A2B4AR4
