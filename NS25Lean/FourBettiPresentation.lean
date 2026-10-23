import NS25Lean.FourBettiFinite

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase Presentation
variable {Gamma : NumericalSemigroup}

theorem add_removed_variable (u : Fin 4 →₀ ℕ) (j : Fin 4) (hj : 0 < u j) :
    u - Finsupp.single j 1 + Finsupp.single j 1 = u := by
  apply tsub_add_cancel_of_le
  intro i
  by_cases he : i = j
  · subst i; simpa using (show 1 ≤ u j by omega)
  · simp [Finsupp.single_eq_of_ne he]

theorem connected_generated_lower (B : Data Gamma) (d : ℕ)
    (c : AddCon (Fin 4 →₀ ℕ))
    (hlower : ∀ e < d, ∀ u v : Fin 4 →₀ ℕ,
      weight B u = e → weight B v = e → c u v)
    (u v : FactorizationFiber B d)
    (hc : (fiberGraph B d).connectedComponentMk u = (fiberGraph B d).connectedComponentMk v) :
    c u.val v.val := by
  have hedge : ∀ a b : FactorizationFiber B d, (fiberGraph B d).Adj a b → c a.val b.val := by
    intro a b hab
    obtain ⟨_, j, ha, hb⟩ := hab
    have hea := remove_copies B a.val j 1 ha
    have heb := remove_copies B b.val j 1 hb
    rw [one_mul, a.property] at hea
    rw [one_mul, b.property] at heb
    have hp := weights_positive B j
    have hsmall := hlower (d - weights B j) (by omega)
      (a.val - Finsupp.single j 1) (b.val - Finsupp.single j 1) (by omega) (by omega)
    have h := c.add hsmall (c.refl (Finsupp.single j 1))
    simpa only [add_removed_variable a.val j ha, add_removed_variable b.val j hb] using h
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hc
  clear hc
  induction p with
  | nil => exact c.refl _
  | cons h _ ih => exact c.trans (hedge _ _ h) ih

open Classical in
def degreeRelations (B : Data Gamma) (d : ℕ) :
    Finset ((Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ)) :=
  letI := Fintype.ofFinite (FactorizationFiber B d)
  Finset.univ.image (fun p : FactorizationFiber B d × FactorizationFiber B d => (p.1.val, p.2.val))

@[simp] theorem mem_degreeRelations (B : Data Gamma) (d : ℕ) (u v : Fin 4 →₀ ℕ) :
    (u, v) ∈ degreeRelations B d ↔ weight B u = d ∧ weight B v = d := by
  classical
  letI := Fintype.ofFinite (FactorizationFiber B d)
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, _, he⟩ := Finset.mem_image.mp h
    cases he
    exact ⟨a.property, b.property⟩
  · rintro ⟨hu, hv⟩
    exact Finset.mem_image.mpr ⟨(⟨u, hu⟩, ⟨v, hv⟩), Finset.mem_univ _, rfl⟩

open Classical in
/-- A redundant ordinary finite presentation, built only after graph-defined Betti finiteness. -/
def bettiPresentation (B : Data Gamma) : Finset ((Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ)) :=
  (bettiDegrees B).biUnion (degreeRelations B)

@[simp] theorem mem_bettiPresentation (B : Data Gamma) (u v : Fin 4 →₀ ℕ) :
    (u, v) ∈ bettiPresentation B ↔ Betti B (weight B u) ∧ weight B u = weight B v := by
  classical
  simp only [bettiPresentation, Finset.mem_biUnion, mem_bettiDegrees, mem_degreeRelations]
  constructor
  · rintro ⟨d, hd, hu, hv⟩; exact ⟨hu ▸ hd, hu.trans hv.symm⟩
  · rintro ⟨hb, he⟩; exact ⟨_, hb, rfl, he.symm⟩

theorem bettiPresentation_generates (B : Data Gamma) (d : ℕ)
    (u v : Fin 4 →₀ ℕ) (hu : weight B u = d) (hv : weight B v = d) :
    generatedCongruence (bettiPresentation B : Set _) u v := by
  induction d using Nat.strong_induction_on generalizing u v with
  | h d ih =>
    by_cases hd : Betti B d
    · exact AddConGen.Rel.of _ _ ((mem_bettiPresentation B u v).mpr
        ⟨hu ▸ hd, hu.trans hv.symm⟩)
    · haveI : Subsingleton (FiberComponent B d) :=
        not_nontrivial_iff_subsingleton.mp (fun h => hd ((betti_iff_nontrivial B d).mpr h))
      exact connected_generated_lower B d _ ih ⟨u, hu⟩ ⟨v, hv⟩ (Subsingleton.elim _ _)

theorem bettiPresentation_isPresentation (B : Data Gamma) :
    IsPresentation B.family (bettiPresentation B) := by
  apply le_antisymm
  · apply AddCon.addConGen_le.mpr
    intro u v huv
    have he := ((mem_bettiPresentation B u v).mp huv).2
    apply Subtype.ext
    simpa only [← weight_eq_degree] using he
  · intro u v he
    apply bettiPresentation_generates B (weight B u) u v rfl
    have he' := congrArg Subtype.val he
    simpa only [← weight_eq_degree] using he'.symm

/-- An unconditional ordinary-presentation checkpoint; no cardinal equality is claimed. -/
theorem rho_le_bettiPresentation_card (B : Data Gamma) :
    Presentation.rho Gamma ≤ (bettiPresentation B).card := by
  rw [rho_eq_presentationNumber_of_minimal_degrees Gamma B.family B.generates B.positive B.minimal]
  exact presentationNumber_le_card _ _ (bettiPresentation_isPresentation B)

end NS25Lean.L2C
