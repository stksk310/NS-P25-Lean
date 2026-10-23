import NS25Lean.BoundarySourceCoordinates
import NS25Lean.HomogeneousGeneratorNumber

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A2
open NS25Lean.L2B ChosenBase ToricPresentation MvPolynomial PositivePresentation

theorem mem_variableIdeal_iff_constantCoeff_zero (k : Type*) [Field k] (f : Poly k 3) :
    f ∈ variableIdeal k ↔ constantCoeff f = 0 := by
  classical
  constructor
  · intro hf
    have hle : variableIdeal k ≤ RingHom.ker (constantCoeff : Poly k 3 →+* k) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      simp
    exact hle hf
  · intro hf
    rw [← support_sum_monomial_coeff f]
    apply Ideal.sum_mem
    intro u hu
    have hn : u ≠ 0 := by
      intro he
      subst u
      exact (mem_support_iff.mp hu) hf
    obtain ⟨j, hj⟩ : ∃ j, 0 < u j := by
      by_contra hh
      push Not at hh
      exact hn (by ext j; exact Nat.eq_zero_of_le_zero (hh j))
    have hm : monomial u (1 : k) ∈ variableIdeal k := by
      rw [← variable_mul_removed k u j hj]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
    change monomial u (coeff u f) ∈ (variableIdeal k).restrictScalars k
    simpa only [smul_monomial, smul_eq_mul, mul_one] using
      ((variableIdeal k).restrictScalars k).smul_mem (coeff u f) hm

def idealGeneratorRelations (k : Type*) [Field k] (I : Ideal (Poly k 3)) : Submodule k I :=
  ((variableIdeal k * I).restrictScalars k).comap (I.subtype.restrictScalars k)

section Coordinates
variable {k ι : Type*} [Field k] [Fintype ι]
variable (w : Fin 3 → ℕ) (hw : ∀ j, 0 < w j)
  (g : ι → Poly k 3) (d : ι → ℕ)
  (hg : ∀ i, (g i).IsWeightedHomogeneous w (d i))
  (hmin : ∀ i, g i ∉ Ideal.span (g '' {j | j ≠ i}))

include hw hg hmin

def homogeneousCoordinateMap : Ideal.span (Set.range g) →ₗ[k] (ι → k) where
  toFun f := generatorCoordinates g f.val
  map_add' f h := generatorCoordinates_add w hw g d hg hmin _ _ f.property h.property
  map_smul' c f := by
    change generatorCoordinates g (c • f.val) = c • generatorCoordinates g f.val
    rw [show c • f.val = C c * f.val from C_mul'.symm,
      generatorCoordinates_mul w hw g d hg hmin _ _ f.property, constantCoeff_C]

theorem homogeneousCoordinates_nI (f : Poly k 3)
    (hf : f ∈ variableIdeal k * Ideal.span (Set.range g)) : generatorCoordinates g f = 0 := by
  have hh : f ∈ Ideal.span (Set.range g) ∧ generatorCoordinates g f = 0 := by
    refine Submodule.mul_induction_on
      (C := fun f : Poly k 3 => f ∈ Ideal.span (Set.range g) ∧ generatorCoordinates g f = 0)
      hf ?_ ?_
    · intro a ha b hb
      refine ⟨Ideal.mul_mem_left _ _ hb, ?_⟩
      rw [generatorCoordinates_mul w hw g d hg hmin _ _ hb,
        (mem_variableIdeal_iff_constantCoeff_zero k a).mp ha, zero_smul]
    · intro a b ha hb
      refine ⟨Ideal.add_mem _ ha.1 hb.1, ?_⟩
      rw [generatorCoordinates_add w hw g d hg hmin _ _ ha.1 hb.1, ha.2, hb.2, add_zero]
  exact hh.2

theorem homogeneousCoordinates_zero_iff (f : Ideal.span (Set.range g)) :
    homogeneousCoordinateMap w hw g d hg hmin f = 0 ↔
      f.val ∈ variableIdeal k * Ideal.span (Set.range g) := by
  constructor
  · intro hf
    obtain ⟨a, ha⟩ := exists_generatorRepresentation g f.property
    have hc := generatorCoordinates_of_representation w hw g d hg hmin a f.val ha
    change generatorCoordinates g f.val = 0 at hf
    rw [hf] at hc
    rw [← ha]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_mul
      ((mem_variableIdeal_iff_constantCoeff_zero k (a i)).mpr (congrFun hc i).symm)
      (Ideal.subset_span ⟨i, rfl⟩)
  · exact homogeneousCoordinates_nI w hw g d hg hmin f.val

theorem homogeneousCoordinateMap_surjective :
    Function.Surjective (homogeneousCoordinateMap w hw g d hg hmin) := by
  classical
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← (Pi.basisFun k ι).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨⟨g i, Ideal.subset_span ⟨i, rfl⟩⟩, ?_⟩
  change generatorCoordinates g (g i) = (Pi.basisFun k ι) i
  rw [Pi.basisFun_apply]
  exact generatorCoordinates_generator w hw g d hg hmin i

/-- The usual positive homogeneous residue-coordinate map has exactly nI as its
kernel, not merely a bound on dimensions. -/
theorem homogeneousCoordinateMap_ker :
    LinearMap.ker (homogeneousCoordinateMap w hw g d hg hmin) =
      idealGeneratorRelations k (Ideal.span (Set.range g)) := by
  ext f
  exact homogeneousCoordinates_zero_iff w hw g d hg hmin f

theorem homogeneousQuotient_finrank :
    Module.finrank k (Ideal.span (Set.range g) ⧸
      idealGeneratorRelations k (Ideal.span (Set.range g))) = Fintype.card ι := by
  have he := (homogeneousCoordinateMap w hw g d hg hmin).quotKerEquivOfSurjective
    (homogeneousCoordinateMap_surjective w hw g d hg hmin)
  have hh := he.finrank_eq
  rw [homogeneousCoordinateMap_ker, Module.finrank_fintype_fun_eq_card] at hh
  exact hh

end Coordinates
end NS25Lean.L2B2A2
