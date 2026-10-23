import NS25Lean.ChosenBaseData
import NS25Lean.RegularSpecialization

set_option linter.style.header false

noncomputable section
namespace NS25Lean.ChosenBase
open MvPolynomial ToricPresentation Presentation

/-- Exact preservation of the arbitrary ideal generator number, over every field. -/
theorem JGamma_generatorNumber_eq (k : Type*) [Field k]
    (H : AddSubmonoid ℕ) (w : Fin 4 → H) (hw : ∀ i, 0 < (w i).val) :
    (JGamma k H w).spanFinrank = toricGeneratorNumber k H w := by
  classical
  apply le_antisymm (JGamma_generatorNumber_le k H w)
  obtain ⟨s, hs, _⟩ := exists_minimalPresentation w
  let g : s → Poly k 4 := fun p => relationBinomial k p.val
  let d : s → ℕ := fun p => (factorizationMap w p.val.1).val
  have hg : ∀ p : s, (g p).IsWeightedHomogeneous (fun i => (w i).val) (d p) := by
    intro p
    apply relationBinomial_homogeneous k H w p.val
    have he : generatedCongruence (s : Set _) = factorizationCongruence w := hs.1
    rw [← he]
    exact AddConGen.Rel.of _ _ p.property
  have hm : ∀ p : s, g p ∉ Ideal.span (g '' {q | q ≠ p}) := by
    intro p hp
    apply binomial_not_mem_erase_of_minimal k w s hs p.val p.property
    have hsub : g '' {q | q ≠ p} ⊆
        relationBinomial k '' (s.erase p.val : Set ((Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ))) := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨q.val, Finset.mem_erase.mpr ⟨fun h => hq (Subtype.ext h), q.property⟩, rfl⟩
    simpa only [relationIdeal, g, Finset.coe_erase] using (Ideal.span_mono hsub hp)
  have hrange : Set.range g = relationBinomial k '' (s : Set ((Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ))) := by
    ext f
    constructor
    · rintro ⟨p, rfl⟩; exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩
  have he : Ideal.span (Set.range g) = toricIdeal k H w := by
    rw [hrange]
    have he := (isPresentation_iff_relationIdeal_eq_ker k w s).mp hs.1
    rw [factorizationAlgebraMap_eq_toricMap] at he
    exact he
  obtain ⟨t, hc, ht⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (show (JGamma k H w).FG from Ideal.fg_of_isNoetherianRing _)
  have hreg : ∀ f : Poly k 4, X 0 * f ∈ Ideal.span (Set.range g) →
      f ∈ Ideal.span (Set.range g) := by
    intro f hf
    rw [he] at hf ⊢
    exact (X_mul_mem_toricIdeal_iff k H w 0 f).mp hf
  have ht' : Ideal.span (t : Set _) = Ideal.map (specialization k) (Ideal.span (Set.range g)) := by
    rw [he]
    exact ht
  have hb := PositivePresentation.card_le_specialized_generators
    (fun i => (w i).val) hw g d hg hm hreg t ht'
  rw [Fintype.card_coe, minimalPresentation_card_eq_toricGeneratorNumber k H w hw s hs, hc] at hb
  exact hb

/-- Source Proposition MUJ for every chosen pivot, with the frozen intrinsic rho. -/
theorem Data.specialized_muj (k : Type*) [Field k] {Gamma : NumericalSemigroup}
    (B : Data Gamma) :
    (JGamma k Gamma.toAddSubmonoid B.degrees).spanFinrank = Presentation.rho Gamma :=
  (JGamma_generatorNumber_eq k _ _ B.degrees_positive).trans
    (B.rho_eq_toricGeneratorNumber k).symm

end NS25Lean.ChosenBase
