import NS25Lean.StandardRho

set_option linter.style.header false

/-! Positive homogeneous residue coordinates survive specialization by a regular variable.
This proves the reverse generator inequality without a free-resolution interface. -/

noncomputable section
namespace NS25Lean.PositivePresentation
open MvPolynomial ToricPresentation
variable {k ι : Type*} [Field k] [Fintype ι]
variable (w : Fin 4 → ℕ) (hw : ∀ i, 0 < w i)
  (g : ι → Poly k 4) (d : ι → ℕ)
  (hg : ∀ i, (g i).IsWeightedHomogeneous w (d i))
  (hmin : ∀ i, g i ∉ Ideal.span (g '' {j | j ≠ i}))

include hw hg hmin

theorem coordinates_mem_span_of_mem_span {τ : Type*} (v : τ → Poly k 4)
    (hv : ∀ j, v j ∈ Ideal.span (Set.range g)) (f : Poly k 4)
    (hf : f ∈ Ideal.span (Set.range v)) :
    generatorCoordinates g f ∈ Submodule.span k (Set.range (generatorCoordinates g ∘ v)) := by
  have hle : Ideal.span (Set.range v) ≤ Ideal.span (Set.range g) :=
    Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hv j)
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨j, rfl⟩ := hf
      exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [generatorCoordinates_zero w hw g d hg hmin]; exact Submodule.zero_mem _
  | add f h hf hh ihf ihh =>
      rw [generatorCoordinates_add w hw g d hg hmin f h (hle hf) (hle hh)]
      exact Submodule.add_mem _ ihf ihh
  | smul a f hf ih =>
      change generatorCoordinates g (a * f) ∈ _
      rw [generatorCoordinates_mul w hw g d hg hmin a f (hle hf)]
      exact Submodule.smul_mem _ _ ih

/-- Specialization loses no minimal generators when the killed variable is regular modulo I. -/
theorem card_le_specialized_generators
    (hreg : ∀ f : Poly k 4, X 0 * f ∈ Ideal.span (Set.range g) →
      f ∈ Ideal.span (Set.range g))
    (t : Finset (Poly k 3))
    (ht : Ideal.span (t : Set _) = Ideal.map (specialization k) (Ideal.span (Set.range g))) :
    Fintype.card ι ≤ t.card := by
  classical
  have hex : ∀ j : t, ∃ f : Poly k 4, f ∈ Ideal.span (Set.range g) ∧
      specialization k f = j.val := by
    intro j
    apply (Ideal.mem_map_iff_of_surjective _ (specialization_surjective k)).mp
    rw [← ht]
    exact Ideal.subset_span j.property
  choose v hv he using hex
  have hspan : Submodule.span k (Set.range (generatorCoordinates g ∘ v)) = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun k ι).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply, ← generatorCoordinates_generator w hw g d hg hmin i]
    have hs : specialization k (g i) ∈ Ideal.span (Set.range (fun j : t => j.val)) := by
      have hr : Set.range (fun j : t => j.val) = (t : Set (Poly k 3)) := by
        ext f; simp
      rw [hr, ht]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    obtain ⟨a, ha⟩ := exists_generatorRepresentation (fun j : t => j.val) hs
    let b : Poly k 4 := ∑ j, tailInclusion k (a j) * v j
    have hb : b ∈ Ideal.span (Set.range v) := by
      apply Ideal.sum_mem
      intro j _
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have hbg : b ∈ Ideal.span (Set.range g) := by
      exact (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hv j)) hb
    have hspec : specialization k (g i - b) = 0 := by
      simp only [map_sub, b, map_sum, map_mul, specialization_tailInclusion, he]
      exact sub_eq_zero.mpr ha.symm
    have hker : g i - b ∈ Ideal.span {X (0 : Fin 4)} := by
      rw [← ker_specialization k]
      exact hspec
    obtain ⟨f, hf⟩ := Ideal.mem_span_singleton.mp hker
    have hfg : f ∈ Ideal.span (Set.range g) := by
      apply hreg
      rw [← hf]
      exact Ideal.sub_mem _ (Ideal.subset_span ⟨i, rfl⟩) hbg
    have hgi : g i = b + X 0 * f := by rw [← hf]; ring
    rw [hgi, generatorCoordinates_add w hw g d hg hmin b (X 0 * f) hbg
      (Ideal.mul_mem_left _ _ hfg), generatorCoordinates_mul w hw g d hg hmin _ f hfg]
    simp only [constantCoeff_X, zero_smul, add_zero]
    exact coordinates_mem_span_of_mem_span w hw g d hg hmin v hv b hb
  let u := Finset.univ.image (generatorCoordinates g ∘ v)
  have hu : Submodule.span k (u : Set (ι → k)) = ⊤ := by
    simpa only [u, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hspan
  have hc := linearIndependent_le_span_finset (Pi.basisFun k ι)
    (Pi.basisFun k ι).linearIndependent u hu
  have hc' : Fintype.card ι ≤ u.card := by
    simpa only [Cardinal.mk_fintype, Nat.cast_le] using hc
  exact hc'.trans (Finset.card_image_le.trans (by simp))

end NS25Lean.PositivePresentation
