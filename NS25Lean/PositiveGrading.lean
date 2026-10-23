import NS25Lean.IntrinsicPresentation
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

set_option linter.style.header false

/-! Positive weighted projection and constant coefficients of homogeneous syzygies. -/

noncomputable section
namespace NS25Lean.PositivePresentation
open MvPolynomial

variable {k σ : Type*} [Field k]

/-- Projecting a multiple of a homogeneous element stays in every ideal containing it. -/
theorem component_mul_mem (w : σ → ℕ) (J : Ideal (MvPolynomial σ k))
    {f : MvPolynomial σ k} {d : ℕ} (hf : f.IsWeightedHomogeneous w d) (hJ : f ∈ J)
    (a : MvPolynomial σ k) (n : ℕ) : weightedHomogeneousComponent w n (a * f) ∈ J := by
  induction a using MvPolynomial.induction_on' with
  | monomial u c =>
      have hh := (isWeightedHomogeneous_monomial w u c rfl).mul hf
      by_cases hn : n = Finsupp.weight w u + d
      · rw [hn, hh.weightedHomogeneousComponent_same]
        exact J.mul_mem_left _ hJ
      · rw [hh.weightedHomogeneousComponent_ne n hn]
        exact J.zero_mem
  | add a b ha hb =>
      rw [add_mul, map_add]
      exact J.add_mem ha hb

/-- Ideals spanned by weighted homogeneous elements are closed under weighted projection. -/
theorem component_mem_span (w : σ → ℕ) (S : Set (MvPolynomial σ k))
    (hS : ∀ f ∈ S, ∃ d, f.IsWeightedHomogeneous w d)
    (f : MvPolynomial σ k) (hf : f ∈ Ideal.span S) (n : ℕ) :
    weightedHomogeneousComponent w n f ∈ Ideal.span S := by
  have aux : ∀ f ∈ Ideal.span S, ∀ a : MvPolynomial σ k, ∀ n : ℕ,
      weightedHomogeneousComponent w n (a * f) ∈ Ideal.span S := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨d, hd⟩ := hS f hf
        exact component_mul_mem w _ hd (Ideal.subset_span hf)
    | zero => intro a n; simp
    | add f g hf hg ihf ihg =>
        intro a n
        rw [mul_add, map_add]
        exact (Ideal.span S).add_mem (ihf a n) (ihg a n)
    | smul c f hf ih =>
        intro a n
        simpa only [smul_eq_mul, mul_assoc] using ih (a * c) n
  simpa only [one_mul] using aux f hf 1 n

/-- Positivity eliminates every nonconstant multiplier at the degree of the element itself. -/
theorem component_self_mul (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    {f : MvPolynomial σ k} {d : ℕ} (hf : f.IsWeightedHomogeneous w d)
    (a : MvPolynomial σ k) :
    weightedHomogeneousComponent w d (a * f) = C (constantCoeff a) * f := by
  classical
  induction a using MvPolynomial.induction_on' with
  | monomial u c =>
      by_cases hu : u = 0
      · subst u
        change weightedHomogeneousComponent w d (C c * f) = C (constantCoeff (C c)) * f
        rw [constantCoeff_C, weightedHomogeneousComponent_C_mul,
          hf.weightedHomogeneousComponent_same]
      · have hweight : Finsupp.weight w u ≠ 0 := by
          intro hz
          apply hu
          ext i
          exact (weightedDegree_eq_zero_iff (nonTorsionWeight_of (fun i => (hw i).ne'))).mp hz i
        have hh := (isWeightedHomogeneous_monomial w u c rfl).mul hf
        rw [hh.weightedHomogeneousComponent_ne d (by omega)]
        simp [constantCoeff_monomial, hu]
  | add a b ha hb =>
      simp only [add_mul, map_add, ha, hb]

/-- In an irredundant homogeneous ideal generating family, every syzygy has zero
constant coefficients. This is the positive-graded step behind the generator count. -/
theorem syzygy_constantCoeff_eq_zero {ι : Type*} [Fintype ι]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (g : ι → MvPolynomial σ k) (d : ι → ℕ)
    (hg : ∀ i, (g i).IsWeightedHomogeneous w (d i))
    (hmin : ∀ i, g i ∉ Ideal.span (g '' {j | j ≠ i}))
    (a : ι → MvPolynomial σ k) (ha : ∑ i, a i * g i = 0) :
    ∀ i, constantCoeff (a i) = 0 := by
  classical
  intro i
  let J := Ideal.span (g '' {j | j ≠ i})
  have hrest : ∑ j ∈ Finset.univ.erase i, a j * g j ∈ J := by
    apply J.sum_mem
    intro j hj
    exact J.mul_mem_left _ (Ideal.subset_span ⟨j, (Finset.mem_erase.mp hj).1, rfl⟩)
  have he : (∑ j ∈ Finset.univ.erase i, a j * g j) + a i * g i = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    exact ha
  have hai : a i * g i ∈ J := by
    have he' : a i * g i = -(∑ j ∈ Finset.univ.erase i, a j * g j) := by
      linear_combination he
    rw [he']
    exact J.neg_mem hrest
  have hhom : ∀ f ∈ g '' {j | j ≠ i}, ∃ d, f.IsWeightedHomogeneous w d := by
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨d j, hg j⟩
  have hc := component_mem_span w _ hhom _ hai (d i)
  rw [component_self_mul w hw (hg i)] at hc
  by_contra hz
  apply hmin i
  have hh := J.mul_mem_left (C ((constantCoeff (a i))⁻¹)) hc
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hz, map_one, one_mul] using hh

end NS25Lean.PositivePresentation
