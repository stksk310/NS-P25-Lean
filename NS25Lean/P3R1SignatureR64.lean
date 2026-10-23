import NS25Lean.P3R2PhysicalDictionaryR57
import NS25Lean.P3CoherentHerzogR58

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R64
open ChosenBase L2B L5A1 L5A2B4AR4R1
variable {Gamma : NumericalSemigroup}

/-- Original R1 has one internal degree and two distinct boundary degrees of this M. -/
theorem r1_signature_degrees (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR1 : (P3R51.internalDegrees M).card = 1) :
    ∃ h₀ h₁ h₂ : ℕ, h₀ ≠ h₁ ∧ h₀ ≠ h₂ ∧ h₁ ≠ h₂ ∧
      P3R51.internalDegrees M = {h₀} ∧
      P3R51.boundaryDegrees M = {h₁, h₂} ∧
      positiveDegrees M = {h₀, h₁, h₂} ∧
      activeDegreeFinset M = {h₀, h₁, h₂} ∧
      LocalSignature M h₀ 2 0 ∧ LocalSignature M h₁ 2 1 ∧ LocalSignature M h₂ 2 1 ∧
      (∀ h ∈ ({h₀, h₁, h₂} : Finset ℕ), fiberContribution M h = 1) ∧
      (∀ h, h ≠ h₀ → h ≠ h₁ → h ≠ h₂ → fiberContribution M h = 0) := by
  classical
  obtain ⟨h₀, h0⟩ := Finset.card_eq_one.mp hR1
  have hpart := P3R51.signature_partition M hp
  have hb : (P3R51.boundaryDegrees M).card = 2 := by omega
  obtain ⟨h₁, h₂, h12, h12set⟩ := Finset.card_eq_two.mp hb
  have hi : h₀ ∈ P3R51.internalDegrees M := by simp [h0]
  have hb1 : h₁ ∈ P3R51.boundaryDegrees M := by simp [h12set]
  have hb2 : h₂ ∈ P3R51.boundaryDegrees M := by simp [h12set]
  have h01 : h₀ ≠ h₁ := by
    intro he; exact Finset.disjoint_left.mp hpart.1 hi (he.symm ▸ hb1)
  have h02 : h₀ ≠ h₂ := by
    intro he; exact Finset.disjoint_left.mp hpart.1 hi (he.symm ▸ hb2)
  have hs : positiveDegrees M = {h₀, h₁, h₂} := by
    rw [← hpart.2.1, h0, h12set]
    ext h
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨h₀, h₁, h₂, h01, h02, h12, h0, h12set, hs, ?_,
    (P3R51.mem_internalDegrees_iff M hp h₀).mp hi,
    (P3R51.mem_boundaryDegrees_iff M hp h₁).mp hb1,
    (P3R51.mem_boundaryDegrees_iff M hp h₂).mp hb2, ?_, ?_⟩
  · exact (P3R51.active_eq_positive M hp).trans hs
  · intro h hh
    exact P3R51.positive_contribution_eq_one M hp h (hs.symm ▸ hh)
  · intro h h0n h1n h2n
    apply contribution_zero_outside_positive
    simp [hs, h0n, h1n, h2n]

/-- The unique fully live axis is selected among the actual three Herzog axes. -/
theorem r1_unique_internal_axis (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR1 : (P3R51.internalDegrees M).card = 1) :
    ∃ j : Fin 3,
      (P3R55.axisIndex M hp j).val ∈ P3R51.internalDegrees M ∧
      (∀ k : Fin 3, (P3R55.axisIndex M hp j).val - weights M.base k ∈ M.base.apery) ∧
      (∀ i : Fin 3, i ≠ j → killedCount M (P3R55.axisIndex M hp i).val = 1) := by
  classical
  obtain ⟨h, hh⟩ := Finset.card_eq_one.mp hR1
  have hin : h ∈ P3R51.internalDegrees M := by simp [hh]
  have hpos : h ∈ positiveDegrees M := (Finset.mem_filter.mp hin).1
  have hact : h ∈ activeDegreeFinset M := by rwa [P3R51.active_eq_positive M hp]
  obtain ⟨j, hj⟩ := P3R55.axisIndex_exhausts_active M hp h hact
  have hjin : (P3R55.axisIndex M hp j).val ∈ P3R51.internalDegrees M := hj.symm ▸ hin
  refine ⟨j, hjin, ?_, ?_⟩
  · intro k
    let R := P3R55.axisRole M hp j
    by_cases hkj : k = j
    · obtain ⟨u, hu, he⟩ := P3R55.role_pure_representative R
      apply P3R57.internal_predecessor_apery M hjin u k
      simpa [he, R, hkj] using (criticalExponent_spec M.base j).1
    · apply P3R57.internal_predecessor_apery M hjin R.witness k
      apply P3R55.role_witness_positive R k
      simpa [R] using hkj
  · intro i hij
    have hipos : (P3R55.axisIndex M hp i).val ∈ positiveDegrees M := by
      rw [← P3R51.active_eq_positive M hp]
      exact (P3R55.axisIndex M hp i).property
    have hn : killedCount M (P3R55.axisIndex M hp i).val ≠ 0 := by
      intro hz
      have hiin : (P3R55.axisIndex M hp i).val ∈ P3R51.internalDegrees M :=
        Finset.mem_filter.mpr ⟨hipos, hz⟩
      have he : (P3R55.axisIndex M hp i).val = h := by simpa [hh] using hiin
      exact hij (P3R55.axisIndex_injective M hp (he.trans hj.symm))
    exact ((P3R51.mem_boundaryDegrees_iff M hp _).mp
      (Finset.mem_filter.mpr ⟨hipos, hn⟩)).2

/-- R1 admits a physical role with a fully live first axis and two one-killed axes. -/
theorem r1_legal_internal_role (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR1 : (P3R51.internalDegrees M).card = 1) :
    ∃ e : Fin 3 ≃ Fin 3,
      LocalSignature M (criticalExponent M.base (e 0) * weights M.base (e 0)) 2 0 ∧
      (∀ k : Fin 3, criticalExponent M.base (e 0) * weights M.base (e 0) -
        weights M.base k ∈ M.base.apery) ∧
      (∀ i : Fin 3, i ≠ 0 →
        LocalSignature M (criticalExponent M.base (e i) * weights M.base (e i)) 2 1 ∧
        ((BoundaryKilled M (P3R55.axisIndex M hp (e i)).val
            (P3R55.axisRole M hp (e i)).pureComponent ∧
          ¬ BoundaryKilled M (P3R55.axisIndex M hp (e i)).val
            (P3R55.axisRole M hp (e i)).mixedComponent) ∨
         (¬ BoundaryKilled M (P3R55.axisIndex M hp (e i)).val
            (P3R55.axisRole M hp (e i)).pureComponent ∧
          BoundaryKilled M (P3R55.axisIndex M hp (e i)).val
            (P3R55.axisRole M hp (e i)).mixedComponent))) := by
  obtain ⟨j, hj, hlive, hother⟩ := r1_unique_internal_axis M hp hR1
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 0 j
  have he : e 0 = j := Equiv.swap_apply_left 0 j
  refine ⟨e, ?_, ?_, ?_⟩
  · rw [he, ← P3R55.axisIndex_degree M hp j]
    exact (P3R51.mem_internalDegrees_iff M hp _).mp hj
  · intro k
    rw [he, ← P3R55.axisIndex_degree M hp j]
    exact hlive k
  · intro i hi
    have hij : e i ≠ j := fun h => hi (e.injective (h.trans he.symm))
    have hk := hother (e i) hij
    refine ⟨?_, P3R57.one_killed_role_dichotomy M (P3R55.axisRole M hp (e i)) hk⟩
    rw [← P3R55.axisIndex_degree M hp (e i)]
    exact ⟨P3R51.active_componentCount_eq_two M hp _
      (P3R55.axisIndex M hp (e i)).property, hk⟩

end NS25Lean.P3R64
