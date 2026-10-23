import NS25Lean.HomogeneousQuotientCoordinates
import NS25Lean.BoundarySourceDimension

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A2
open NS25Lean.L2B NS25Lean.L2B2A ChosenBase ToricPresentation MvPolynomial PositivePresentation
variable {Gamma : NumericalSemigroup}

theorem exists_irredundant_subset {R : Type*} [CommRing R] [DecidableEq R] (s : Finset R) :
    ∃ t : Finset R, t ⊆ s ∧ Ideal.span (t : Set R) = Ideal.span (s : Set R) ∧
      ∀ f ∈ t, f ∉ Ideal.span ((t.erase f : Finset R) : Set R) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hirr : ∀ f ∈ s, f ∉ Ideal.span ((s.erase f : Finset R) : Set R)
    · exact ⟨s, le_rfl, rfl, hirr⟩
    · push Not at hirr
      obtain ⟨f, hf, hred⟩ := hirr
      obtain ⟨t, hts, htspan, htmin⟩ := ih (s.erase f) (Finset.erase_ssubset hf)
      refine ⟨t, hts.trans (Finset.erase_subset _ _), htspan.trans ?_, htmin⟩
      conv_rhs => rw [← Finset.insert_erase hf, Finset.coe_insert]
      exact (Submodule.span_insert_eq_span hred).symm

theorem J_eq_ideal_span_moves (k : Type*) [Field k] (B : Data Gamma) :
    B.J k = Ideal.span (toricMoves k B ∪ boundaryMonomials k B) := by
  apply le_antisymm
  · intro f hf
    have hh : f ∈ Submodule.span k (toricMoves k B ∪ boundaryMonomials k B) := by
      rw [← J_eq_span_moves]; exact hf
    have hle : Submodule.span k (toricMoves k B ∪ boundaryMonomials k B) ≤
        (Ideal.span (toricMoves k B ∪ boundaryMonomials k B)).restrictScalars k :=
      Submodule.span_le.mpr (fun _ hx => Ideal.subset_span hx)
    exact hle hh
  · apply Ideal.span_le.mpr
    intro f hf
    have hh := (Submodule.subset_span hf : f ∈ Submodule.span k
      (toricMoves k B ∪ boundaryMonomials k B))
    rw [← J_eq_span_moves] at hh
    exact hh

open Classical in
/-- Finite homogeneous generators are extracted from the actual toric/boundary
presentation of J; deleting redundant members supplies an irredundant family. -/
theorem exists_homogeneous_generators_J (k : Type*) [Field k] (B : Data Gamma) :
    ∃ t : Finset (Poly k 3), Ideal.span (t : Set (Poly k 3)) = B.J k ∧
      (∀ f ∈ t, ∃ d, f.IsWeightedHomogeneous (weights B) d) ∧
      ∀ f ∈ t, f ∉ Ideal.span ((t.erase f : Finset (Poly k 3)) : Set (Poly k 3)) := by
  classical
  let S := toricMoves k B ∪ boundaryMonomials k B
  have hs : (Ideal.span S).FG := by
    rw [← J_eq_ideal_span_moves]
    exact Ideal.fg_of_isNoetherianRing _
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp hs
  obtain ⟨t, hts, ht, hmin⟩ := exists_irredundant_subset s
  refine ⟨t, ht.trans (hs.symm.trans (J_eq_ideal_span_moves k B).symm), ?_, hmin⟩
  intro f hf
  rcases hsS (hts hf) with ⟨u, v, he, rfl⟩ | ⟨u, _, rfl⟩
  · exact ⟨weight B u,
      (isWeightedHomogeneous_monomial (weights B) u (1 : k) rfl).sub
        (isWeightedHomogeneous_monomial (weights B) v (1 : k) he.symm)⟩
  · exact ⟨weight B u, isWeightedHomogeneous_monomial (weights B) u (1 : k) rfl⟩

/-- Positive homogeneous coordinates identify actual ideal generator number and
actual J/nJ dimension, independently of MUJ and presentation cardinality. -/
theorem generatorQuotient_finrank_eq_spanFinrank (k : Type*) [Field k] (B : Data Gamma) :
    Module.finrank k (GeneratorQuotient k B) = (B.J k).spanFinrank := by
  classical
  obtain ⟨t, ht, hh, hm⟩ := exists_homogeneous_generators_J k B
  let g : t → Poly k 3 := Subtype.val
  have hrange : Set.range g = (t : Set (Poly k 3)) := by ext f; simp [g]
  have hspan : Ideal.span (Set.range g) = B.J k := by rw [hrange, ht]
  choose d hd using (fun i : t => hh i.val i.property)
  have hmin : ∀ i : t, g i ∉ Ideal.span (g '' {j | j ≠ i}) := by
    intro i hi
    apply hm i.val i.property
    apply Ideal.span_mono (s := g '' {j | j ≠ i}) _ hi
    rintro f ⟨j, hj, rfl⟩
    exact Finset.mem_erase.mpr ⟨fun he => hj (Subtype.ext he), j.property⟩
  have hdim := homogeneousQuotient_finrank (weights B) (weights_positive B) g d hd hmin
  rw [hspan] at hdim
  change Module.finrank k (GeneratorQuotient k B) = Fintype.card t at hdim
  rw [hdim, Fintype.card_coe]
  apply le_antisymm
  · obtain ⟨s, hc, hs⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (show (B.J k).FG from Ideal.fg_of_isNoetherianRing _)
    have hl := homogeneous_card_le_generators (weights B) (weights_positive B) g d hd hmin
      s (hs.trans hspan.symm)
    simpa only [Fintype.card_coe, hc] using hl
  · rw [← ht]
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite t.finite_toSet

end NS25Lean.L2B2A2
