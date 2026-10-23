import NS25Lean.PositiveGrading

set_option linter.style.header false

/-!
# Counting irredundant positive homogeneous generators

Coordinates are the constant coefficients of an ideal representation. The
syzygy theorem proves independence of the chosen representation. On the ideal,
they form the residue-coordinate space normally expressed as `I / (X_i) I`.
Only the coordinate properties needed for the generator bound are used here.
-/

noncomputable section
namespace NS25Lean.PositivePresentation
open MvPolynomial
variable {k σ ι : Type*} [Field k] [Fintype ι]

open Classical in
def generatorCoordinates (g : ι → MvPolynomial σ k) (f : MvPolynomial σ k) : ι → k :=
  if h : ∃ a : ι → MvPolynomial σ k, ∑ i, a i * g i = f then
    fun i => constantCoeff (Classical.choose h i)
  else 0

theorem exists_generatorRepresentation (g : ι → MvPolynomial σ k)
    {f : MvPolynomial σ k} (hf : f ∈ Ideal.span (Set.range g)) :
    ∃ a : ι → MvPolynomial σ k, ∑ i, a i * g i = f := by
  simpa only [smul_eq_mul] using
    (Submodule.mem_span_range_iff_exists_fun (R := MvPolynomial σ k)).mp hf

variable (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (g : ι → MvPolynomial σ k) (d : ι → ℕ)
  (hg : ∀ i, (g i).IsWeightedHomogeneous w (d i))
  (hmin : ∀ i, g i ∉ Ideal.span (g '' {j | j ≠ i}))

include hw hg hmin

/-- Any ideal representation computes the same residue coordinates. -/
theorem generatorCoordinates_of_representation (a : ι → MvPolynomial σ k)
    (f : MvPolynomial σ k) (ha : ∑ i, a i * g i = f) :
    generatorCoordinates g f = fun i => constantCoeff (a i) := by
  classical
  have hex : ∃ a : ι → MvPolynomial σ k, ∑ i, a i * g i = f := ⟨a, ha⟩
  unfold generatorCoordinates
  rw [dite_eq_left hex]
  have hz : ∑ i, (Classical.choose hex i - a i) * g i = 0 := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [Classical.choose_spec hex, ha, sub_self]
  have hc := syzygy_constantCoeff_eq_zero w hw g d hg hmin _ hz
  funext i
  exact sub_eq_zero.mp (by simpa only [map_sub] using hc i)

theorem generatorCoordinates_zero : generatorCoordinates g 0 = 0 := by
  have he := generatorCoordinates_of_representation w hw g d hg hmin (fun _ => 0) 0 (by simp)
  funext i
  simpa using congrFun he i

theorem generatorCoordinates_add (f h : MvPolynomial σ k)
    (hf : f ∈ Ideal.span (Set.range g)) (hh : h ∈ Ideal.span (Set.range g)) :
    generatorCoordinates g (f + h) = generatorCoordinates g f + generatorCoordinates g h := by
  obtain ⟨a, ha⟩ := exists_generatorRepresentation g hf
  obtain ⟨b, hb⟩ := exists_generatorRepresentation g hh
  have hab : ∑ i, (a i + b i) * g i = f + h := by
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [ha, hb]
  rw [generatorCoordinates_of_representation w hw g d hg hmin _ _ hab,
    generatorCoordinates_of_representation w hw g d hg hmin _ _ ha,
    generatorCoordinates_of_representation w hw g d hg hmin _ _ hb]
  funext i
  exact map_add _ _ _

theorem generatorCoordinates_mul (a f : MvPolynomial σ k)
    (hf : f ∈ Ideal.span (Set.range g)) :
    generatorCoordinates g (a * f) = constantCoeff a • generatorCoordinates g f := by
  obtain ⟨b, hb⟩ := exists_generatorRepresentation g hf
  have hab : ∑ i, (a * b i) * g i = a * f := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hb]
  rw [generatorCoordinates_of_representation w hw g d hg hmin _ _ hab,
    generatorCoordinates_of_representation w hw g d hg hmin _ _ hb]
  funext i
  exact map_mul _ _ _

open Classical in
theorem generatorCoordinates_generator (i : ι) :
    generatorCoordinates g (g i) = Pi.single i 1 := by
  classical
  have he : ∑ j, (Pi.single i (1 : MvPolynomial σ k) : ι → MvPolynomial σ k) j * g j = g i := by
    simp [Pi.single_apply]
  rw [generatorCoordinates_of_representation w hw g d hg hmin _ _ he]
  funext j
  by_cases hij : j = i <;> simp [hij]

theorem generatorCoordinates_mem_span (t : Finset (MvPolynomial σ k))
    (ht : Ideal.span (t : Set _) = Ideal.span (Set.range g))
    (f : MvPolynomial σ k) (hf : f ∈ Ideal.span (Set.range g)) :
    generatorCoordinates g f ∈ Submodule.span k (generatorCoordinates g '' (t : Set _)) := by
  rw [← ht] at hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact Submodule.subset_span ⟨f, hf, rfl⟩
  | zero => rw [generatorCoordinates_zero w hw g d hg hmin]; exact Submodule.zero_mem _
  | add f h hf hh ihf ihh =>
      rw [generatorCoordinates_add w hw g d hg hmin f h (ht ▸ hf) (ht ▸ hh)]
      exact Submodule.add_mem _ ihf ihh
  | smul a f hf ih =>
      change generatorCoordinates g (a * f) ∈ _
      rw [generatorCoordinates_mul w hw g d hg hmin a f (ht ▸ hf)]
      exact Submodule.smul_mem _ _ ih

/-- Every arbitrary polynomial generating family spans the residue-coordinate space. -/
theorem span_generatorCoordinates_eq_top (t : Finset (MvPolynomial σ k))
    (ht : Ideal.span (t : Set _) = Ideal.span (Set.range g)) :
    Submodule.span k (generatorCoordinates g '' (t : Set _)) = ⊤ := by
  classical
  apply top_unique
  rw [← (Pi.basisFun k ι).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply, ← generatorCoordinates_generator w hw g d hg hmin i]
  exact generatorCoordinates_mem_span w hw g d hg hmin t ht _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Irredundant homogeneous generators have at most the size of any generating family. -/
theorem homogeneous_card_le_generators (t : Finset (MvPolynomial σ k))
    (ht : Ideal.span (t : Set _) = Ideal.span (Set.range g)) :
    Fintype.card ι ≤ t.card := by
  classical
  let u := t.image (generatorCoordinates g)
  have hu : Submodule.span k (u : Set (ι → k)) = ⊤ := by
    simpa only [u, Finset.coe_image] using span_generatorCoordinates_eq_top w hw g d hg hmin t ht
  have hb := linearIndependent_le_span_finset (Pi.basisFun k ι)
    (Pi.basisFun k ι).linearIndependent u hu
  have hc : Fintype.card ι ≤ u.card := by
    simpa only [Cardinal.mk_fintype, Nat.cast_le] using hb
  exact hc.trans Finset.card_image_le

end NS25Lean.PositivePresentation
