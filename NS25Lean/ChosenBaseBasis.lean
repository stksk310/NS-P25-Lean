import NS25Lean.ChosenBaseQuotient
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module

set_option linter.style.header false

noncomputable section
namespace NS25Lean.ChosenBase
open ToricPresentation FourGeneratedBridge
variable (k : Type*) [Field k] {Gamma : NumericalSemigroup}

def Data.aperyDegree (B : Data Gamma) (w : B.apery) : Gamma.toAddSubmonoid :=
  ⟨w.val, w.property.1⟩

theorem Data.aperyDegree_injective (B : Data Gamma) : Function.Injective B.aperyDegree := by
  intro a b he
  exact Subtype.ext (congrArg (fun h : Gamma.toAddSubmonoid => h.val) he)

def Data.monomialClass (B : Data Gamma) (h : Gamma.toAddSubmonoid) : B.A k :=
  B.quotientMap k (AddMonoidAlgebra.single h 1)

theorem Data.monomialClass_eq_zero_iff (B : Data Gamma) (h : Gamma.toAddSubmonoid) :
    B.monomialClass k h = 0 ↔ h.val ∉ B.apery := by
  change Ideal.Quotient.mk (B.principal k) (AddMonoidAlgebra.single h 1) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Data.principal, mem_principal_monomial_iff]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.support_single _ one_ne_zero,
    Finset.mem_singleton, forall_eq]
  change (B.q.val ≤ h.val ∧ h.val - B.q.val ∈ Gamma.toAddSubmonoid) ↔
    ¬(h.val ∈ Gamma.toAddSubmonoid ∧ (h.val < B.q.val ∨ h.val - B.q.val ∉ Gamma.toAddSubmonoid))
  simp only [h.property, true_and, not_or, not_lt, not_not]

/-- Membership in (t^q) forces every surviving coefficient to vanish. -/
theorem Data.principal_coeff_eq_zero (B : Data Gamma)
    (f : SemigroupAlgebra k Gamma.toAddSubmonoid) (hf : f ∈ B.principal k)
    (w : B.apery) : f.coeff (B.aperyDegree w) = 0 := by
  by_contra hn
  have ht := (mem_principal_monomial_iff k Gamma.toAddSubmonoid B.q f).mp hf
    (B.aperyDegree w) (Finsupp.mem_support_iff.mpr hn)
  rcases w.property.2 with hlt | hnot
  · exact (Nat.not_lt.mpr ht.1) hlt
  · exact hnot ht.2

theorem Data.apery_linearIndependent (B : Data Gamma) :
    LinearIndependent k (fun w : B.apery => B.monomialClass k (B.aperyDegree w)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s a ha i hi
  let f : SemigroupAlgebra k Gamma.toAddSubmonoid :=
    ∑ j ∈ s, a j • AddMonoidAlgebra.single (B.aperyDegree j) 1
  have hf : f ∈ B.principal k := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change B.quotientMap k f = 0
    simpa only [f, map_sum, map_smul, Data.monomialClass] using ha
  have hc := B.principal_coeff_eq_zero k f hf i
  have he : f.coeff (B.aperyDegree i) = a i := by
    simp [f, Finsupp.single_apply, B.aperyDegree_injective.eq_iff, hi]
  exact he.symm.trans hc

theorem Data.apery_span (B : Data Gamma) :
    Submodule.span k (Set.range (fun w : B.apery => B.monomialClass k (B.aperyDegree w))) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change B.quotientMap k f ∈ _
  induction f using AddMonoidAlgebra.induction_on with
  | of h =>
      by_cases hh : h.val ∈ B.apery
      · exact Submodule.subset_span ⟨⟨h.val, hh⟩, rfl⟩
      · change B.monomialClass k h ∈ _
        rw [(B.monomialClass_eq_zero_iff k h).mpr hh]
        exact Submodule.zero_mem _
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul a f hf => rw [map_smul]; exact Submodule.smul_mem _ a hf

/-- A3: a genuine basis of surviving monomial classes indexed by Apéry degrees. -/
def Data.aperyBasis (B : Data Gamma) : Module.Basis B.apery k (B.A k) :=
  Module.Basis.mk (B.apery_linearIndependent k) (by rw [B.apery_span k])

@[simp] theorem Data.aperyBasis_apply (B : Data Gamma) (w : B.apery) :
    B.aperyBasis k w = B.monomialClass k (B.aperyDegree w) :=
  Module.Basis.mk_apply _ _ w

/-- A4: finite dimensionality follows from the actual monomial basis. -/
instance Data.finiteDimensionalA (B : Data Gamma) : FiniteDimensional k (B.A k) :=
  FiniteDimensional.of_finite_basis (B.aperyBasis k) B.apery_finite

def Data.polynomialQuotientBasis (B : Data Gamma) :
    Module.Basis B.apery k (MvPolynomial (Fin 3) k ⧸ B.J k) :=
  (B.aperyBasis k).map (B.quotientEquiv k).symm.toLinearEquiv

instance Data.finiteDimensionalPolynomialQuotient (B : Data Gamma) :
    FiniteDimensional k (MvPolynomial (Fin 3) k ⧸ B.J k) :=
  FiniteDimensional.of_finite_basis (B.polynomialQuotientBasis k) B.apery_finite

instance Data.artinianA (B : Data Gamma) : IsArtinianRing (B.A k) :=
  IsArtinianRing.of_finite k (B.A k)

instance Data.artinianPolynomialQuotient (B : Data Gamma) :
    IsArtinianRing (MvPolynomial (Fin 3) k ⧸ B.J k) :=
  IsArtinianRing.of_finite k (MvPolynomial (Fin 3) k ⧸ B.J k)

end NS25Lean.ChosenBase
