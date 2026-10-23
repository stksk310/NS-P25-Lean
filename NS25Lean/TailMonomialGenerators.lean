import NS25Lean.FourGeneratedToric
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.NumberTheory.FrobeniusNumber
import Mathlib.RingTheory.FiniteType

set_option linter.style.header false

/-!
# Minimal tail degrees and arbitrary polynomial generators

Phase L1-A. At a minimal tail degree, multiplication by a semigroup polynomial
acts on coefficients through its constant coefficient. Thus arbitrary ideal
generators must span the coordinate space of minimal tail degrees over the field.
No identification with the standard presentation invariant is made here.
-/

noncomputable section
namespace NS25Lean.ToricPresentation
open FourGeneratedBridge
variable (k : Type*) [Field k]

/-- Coefficient collapse at a minimal tail degree. -/
theorem minimalTailGenerator_coefficient_mul
    (Gamma H : AddSubmonoid ℕ) (m : ℕ) (hHGamma : H ≤ Gamma)
    (x : H) (hx : IsMinimalTailGenerator H (aperyTail Gamma H m) x.val)
    (a f : SemigroupAlgebra k H) (hf : f ∈ tailMonomialIdeal k Gamma H m) :
    (a * f).coeff x = a.coeff 0 * f.coeff x := by
  classical
  have hu : UniqueAdd a.coeff.support f.coeff.support 0 x := by
    intro u v _hu hv he
    have hvK := (mem_tailMonomialIdeal_iff k Gamma H m hHGamma f).mp hf v hv
    have hval : u.val + v.val = x.val := by
      simpa using congrArg Subtype.val he
    have hu0 : u.val = 0 := by
      by_contra hn
      rcases hx.2 u.val u.property hn with hlt | hnot
      · omega
      · apply hnot
        have hs : x.val - u.val = v.val := by omega
        simpa [hs] using hvK
    exact ⟨Subtype.ext hu0, Subtype.ext (by omega)⟩
  simpa using AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hu

/-- The index type uses exactly the frozen natural-number predicate. -/
abbrev MinimalTailDegrees (Gamma H : AddSubmonoid ℕ) (m : ℕ) :=
  {x : ℕ // IsMinimalTailGenerator H (aperyTail Gamma H m) x}

/-- Coefficient vectors on minimal degrees, defined on the ambient algebra.
Its restriction to the tail ideal is the coefficient-vector map of the proof. -/
def minimalTailCoefficientMap (Gamma H : AddSubmonoid ℕ) (m : ℕ) :
    SemigroupAlgebra k H →ₗ[k] (MinimalTailDegrees Gamma H m → k) where
  toFun f x := f.coeff ⟨x.val, x.property.1.1⟩
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

theorem minimalTailCoefficientMap_mul
    (Gamma H : AddSubmonoid ℕ) (m : ℕ) (hHGamma : H ≤ Gamma)
    (a f : SemigroupAlgebra k H) (hf : f ∈ tailMonomialIdeal k Gamma H m) :
    minimalTailCoefficientMap k Gamma H m (a * f) =
      a.coeff 0 • minimalTailCoefficientMap k Gamma H m f := by
  ext x
  exact minimalTailGenerator_coefficient_mul k Gamma H m hHGamma
    ⟨x.val, x.property.1.1⟩ x.property a f hf

/-- Every ideal combination becomes a field-linear combination of coefficient vectors. -/
theorem minimalTailCoefficientMap_mem_span
    (Gamma H : AddSubmonoid ℕ) (m : ℕ) (hHGamma : H ≤ Gamma)
    (s : Finset (SemigroupAlgebra k H))
    (hs : Ideal.span (s : Set (SemigroupAlgebra k H)) = tailMonomialIdeal k Gamma H m)
    (f : SemigroupAlgebra k H) (hf : f ∈ tailMonomialIdeal k Gamma H m) :
    minimalTailCoefficientMap k Gamma H m f ∈
      Submodule.span k (minimalTailCoefficientMap k Gamma H m '' (s : Set _)) := by
  rw [← hs] at hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact Submodule.subset_span ⟨f, hf, rfl⟩
  | zero => simp
  | add f g hf hg ihf ihg =>
      simpa using Submodule.add_mem _ ihf ihg
  | smul a f hf ih =>
      have hfI : f ∈ tailMonomialIdeal k Gamma H m := hs ▸ hf
      change minimalTailCoefficientMap k Gamma H m (a * f) ∈ _
      rw [minimalTailCoefficientMap_mul k Gamma H m hHGamma a f hfI]
      exact Submodule.smul_mem _ _ ih

/-- Minimal degrees occur in the supports of every finite ideal generating family. -/
theorem minimalTailGenerators_subset_supports
    (Gamma H : AddSubmonoid ℕ) (m : ℕ) (hHGamma : H ≤ Gamma)
    (s : Finset (SemigroupAlgebra k H))
    (hs : Ideal.span (s : Set (SemigroupAlgebra k H)) = tailMonomialIdeal k Gamma H m) :
    ∀ x : MinimalTailDegrees Gamma H m,
      ∃ f ∈ s, f.coeff ⟨x.val, x.property.1.1⟩ ≠ 0 := by
  classical
  intro x
  by_contra! hz
  let d : H := ⟨x.val, x.property.1.1⟩
  have vanish : ∀ f ∈ tailMonomialIdeal k Gamma H m, f.coeff d = 0 := by
    intro f hf
    rw [← hs] at hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact hz f hf
    | zero => rfl
    | add f g hf hg ihf ihg => simp [ihf, ihg]
    | smul a f hf ih =>
        change (a * f).coeff d = 0
        rw [minimalTailGenerator_coefficient_mul k Gamma H m hHGamma d x.property
          a f (hs ▸ hf), ih, mul_zero]
  have hm : AddMonoidAlgebra.single d (1 : k) ∈ tailMonomialIdeal k Gamma H m :=
    (single_mem_tailMonomialIdeal_iff k Gamma H m hHGamma d).mpr x.property.1
  have hc := vanish _ hm
  simp at hc

/-- Finiteness is derived from a generating family, rather than assumed. -/
theorem minimalTailGenerators_finite_of_fg
    (Gamma H : AddSubmonoid ℕ) (m : ℕ) (hHGamma : H ≤ Gamma)
    (hfg : (tailMonomialIdeal k Gamma H m).FG) :
    Finite (MinimalTailDegrees Gamma H m) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  let t : Finset ℕ := s.biUnion fun f => f.coeff.support.image Subtype.val
  have hsub : {x | IsMinimalTailGenerator H (aperyTail Gamma H m) x} ⊆ (t : Set ℕ) := by
    intro x hx
    obtain ⟨f, hf, hfx⟩ := minimalTailGenerators_subset_supports k Gamma H m hHGamma s hs ⟨x, hx⟩
    exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_image.mpr
      ⟨⟨x, hx.1.1⟩, Finsupp.mem_support_iff.mpr hfx, rfl⟩⟩
  exact (t.finite_toSet.subset hsub).to_subtype

/-- Minimal monomials map to the coordinate basis. -/
theorem minimalTailCoefficientMap_single
    (Gamma H : AddSubmonoid ℕ) (m : ℕ) (x : MinimalTailDegrees Gamma H m) :
    minimalTailCoefficientMap k Gamma H m
      (AddMonoidAlgebra.single ⟨x.val, x.property.1.1⟩ 1) = Pi.single x 1 := by
  classical
  ext y
  by_cases he : x = y
  · subst y
    simp [minimalTailCoefficientMap]
  · have hd : (⟨x.val, x.property.1.1⟩ : H) ≠ ⟨y.val, y.property.1.1⟩ := by
      intro h
      exact he (Subtype.ext (congrArg (fun z : H => z.val) h))
    simp [minimalTailCoefficientMap, hd, Ne.symm he]

/-- Images of arbitrary ideal generators span the whole minimal-degree coordinate space. -/
theorem span_minimalTailCoefficientMap_eq_top
    (Gamma H : AddSubmonoid ℕ) (m : ℕ) (hHGamma : H ≤ Gamma)
    (s : Finset (SemigroupAlgebra k H))
    (hs : Ideal.span (s : Set (SemigroupAlgebra k H)) = tailMonomialIdeal k Gamma H m) :
    Submodule.span k (minimalTailCoefficientMap k Gamma H m '' (s : Set _)) = ⊤ := by
  classical
  let := minimalTailGenerators_finite_of_fg k Gamma H m hHGamma ⟨s, hs⟩
  apply top_unique
  rw [← (Pi.basisFun k (MinimalTailDegrees Gamma H m)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  rw [Pi.basisFun_apply, ← minimalTailCoefficientMap_single k Gamma H m x]
  exact minimalTailCoefficientMap_mem_span k Gamma H m hHGamma s hs _
    ((single_mem_tailMonomialIdeal_iff k Gamma H m hHGamma _).mpr x.property.1)

private theorem coordinate_card_le_of_span {ι : Type*} [Finite ι]
    (s : Finset (ι → k)) (hs : Submodule.span k (s : Set (ι → k)) = ⊤) :
    Nat.card ι ≤ s.card := by
  classical
  let := Fintype.ofFinite ι
  have hb := linearIndependent_le_span_finset (Pi.basisFun k ι)
    (Pi.basisFun k ι).linearIndependent s hs
  rw [Nat.card_eq_fintype_card]
  simpa only [Cardinal.mk_fintype, Nat.cast_le] using hb

/-- Lower bound against every finite family of arbitrary polynomials generating the ideal. -/
theorem tailGeneratorCount_le_card_of_generates
    (Gamma H : AddSubmonoid ℕ) (m : ℕ) (hHGamma : H ≤ Gamma)
    (s : Finset (SemigroupAlgebra k H))
    (hs : Ideal.span (s : Set (SemigroupAlgebra k H)) = tailMonomialIdeal k Gamma H m) :
    tailGeneratorCount H (aperyTail Gamma H m) ≤ s.card := by
  classical
  let := minimalTailGenerators_finite_of_fg k Gamma H m hHGamma ⟨s, hs⟩
  let t := s.image (minimalTailCoefficientMap k Gamma H m)
  have hspan : Submodule.span k (t : Set (MinimalTailDegrees Gamma H m → k)) = ⊤ := by
    simpa only [t, Finset.coe_image] using
      span_minimalTailCoefficientMap_eq_top k Gamma H m hHGamma s hs
  change Nat.card (MinimalTailDegrees Gamma H m) ≤ s.card
  exact (coordinate_card_le_of_span k t hspan).trans (Finset.card_image_le (f :=
    minimalTailCoefficientMap k Gamma H m) (s := s))

/-- Every tail ideal here is finitely generated: every additive submonoid of
the natural numbers is finitely generated, so its semigroup algebra is Noetherian. -/
theorem tailMonomialIdeal_fg (Gamma H : AddSubmonoid ℕ) (m : ℕ) :
    (tailMonomialIdeal k Gamma H m).FG := by
  let : AddMonoid.FG H := (AddMonoid.fg_iff_addSubmonoid_fg H).mpr (Nat.addSubmonoid_fg H)
  let : IsNoetherianRing (SemigroupAlgebra k H) :=
    Algebra.FiniteType.isNoetherianRing k (SemigroupAlgebra k H)
  exact Ideal.fg_of_isNoetherianRing _

/-- The L1-A generic bridge, with no finite-generation assumption. -/
theorem tailGeneratorCount_le_spanFinrank
    (Gamma H : AddSubmonoid ℕ) (m : ℕ) (hHGamma : H ≤ Gamma) :
    tailGeneratorCount H (aperyTail Gamma H m) ≤
      (tailMonomialIdeal k Gamma H m).spanFinrank := by
  obtain ⟨s, hcard, hs⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (tailMonomialIdeal_fg k Gamma H m)
  exact hcard ▸ tailGeneratorCount_le_card_of_generates k Gamma H m hHGamma s hs

/-- The L1-A four-generated bridge to the baseline algebraic toric generator number. -/
theorem fourGenerated_tailGeneratorCount_le_toricGeneratorNumber
    (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    tailGeneratorCount (generatedThree n₁ n₂ n₃)
      (aperyTail Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m) ≤
        toricGeneratorNumber k Gamma.toAddSubmonoid (fourDegrees Gamma m n₁ n₂ n₃ h) := by
  have hle : generatedThree n₁ n₂ n₃ ≤ Gamma.toAddSubmonoid := by
    rw [h.generated]
    exact generatedThree_le_generatedFour m n₁ n₂ n₃
  exact (tailGeneratorCount_le_spanFinrank k Gamma.toAddSubmonoid
    (generatedThree n₁ n₂ n₃) m hle).trans
      (fourGenerated_tailMonomial_generatorNumber_le k Gamma m n₁ n₂ n₃ h)

end NS25Lean.ToricPresentation
