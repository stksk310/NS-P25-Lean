import NS25Lean.ActiveFiberBoundarySources

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A2
open NS25Lean.L2B NS25Lean.L2B2A ChosenBase Presentation ToricPresentation
  FourGeneratedBridge MvPolynomial
variable {Gamma : NumericalSemigroup}

abbrev Source (B : Data Gamma) := {h : ℕ // IsMinimalTailGenerator B.H B.K h}

instance finiteSource (B : Data Gamma) : Finite (Source B) :=
  minimalTailGenerators_finite_of_fg ℚ _ _ _ B.H_le (tailMonomialIdeal_fg ℚ _ _ _)

/-- Actual coefficients after the tail toric map, at precisely the minimal sources. -/
def sourceCoordinates (k : Type*) [Field k] (B : Data Gamma) :
    Poly k 3 →ₗ[k] (Source B → k) :=
  (minimalTailCoefficientMap k Gamma.toAddSubmonoid B.H B.q.val).comp
    (toricMap k B.H B.tailDegrees).toLinearMap

theorem sourceCoordinates_monomial (k : Type*) [Field k] (B : Data Gamma)
    (u : Fin 3 →₀ ℕ) (x : Source B) :
    sourceCoordinates k B (monomial u 1) x = if weight B u = x.val then 1 else 0 := by
  classical
  change (toricMap k B.H B.tailDegrees (monomial u 1)).coeff
    ⟨x.val, x.property.1.1⟩ = _
  rw [B.tailMap_monomial k]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  congr 1
  exact propext (Subtype.ext_iff.trans (by rw [← weight_eq_degree B u]))

theorem sourceCoordinates_IH (k : Type*) [Field k] (B : Data Gamma)
    (f : Poly k 3) (hf : f ∈ B.IH k) : sourceCoordinates k B f = 0 := by
  have hz : toricMap k B.H B.tailDegrees f = 0 := hf
  change minimalTailCoefficientMap k _ _ _ (toricMap k B.H B.tailDegrees f) = 0
  rw [hz, map_zero]

theorem sourceCoordinates_boundaryMove (k : Type*) [Field k] (B : Data Gamma)
    (j : Fin 3) (v : Fin 3 →₀ ℕ) (hv : weight B v ∈ B.K) :
    sourceCoordinates k B (monomial (Finsupp.single j 1 + v) 1) = 0 := by
  classical
  ext x
  rw [sourceCoordinates_monomial]
  have hn : weight B (Finsupp.single j 1 + v) ≠ x.val := by
    intro he
    have he' : weights B j + weight B v = x.val := by
      simpa only [map_add, weight, Finsupp.weight_single, one_nsmul] using he
    rcases x.property.2 (weights B j) (B.tailDegrees j).property
      (weights_positive B j).ne' with hlt | hnot
    · omega
    · apply hnot
      simpa only [← he', Nat.add_sub_cancel_left] using hv
  exact ite_eq_right hn

theorem sourceCoordinates_nJ (k : Type*) [Field k] (B : Data Gamma)
    (f : Poly k 3) (hf : f ∈ variableIdeal k * B.J k) :
    sourceCoordinates k B f = 0 := by
  change f ∈ (variableIdeal k * B.J k).restrictScalars k at hf
  rw [nJ_eq_span_moves] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with ⟨u, v, he, _, rfl⟩ | ⟨j, v, hv, rfl⟩
      · exact sourceCoordinates_IH k B _ (binomial_mem_IH k B u v he)
      · exact sourceCoordinates_boundaryMove k B j v hv
  | zero => exact map_zero _
  | add f g hf hg ihf ihg => simp only [map_add, ihf, ihg, add_zero]
  | smul c f hf ih => simp only [map_smul, ih, smul_zero]

def generatorSourceCoordinates (k : Type*) [Field k] (B : Data Gamma) :
    GeneratorQuotient k B →ₗ[k] (Source B → k) :=
  (generatorRelations k B).liftQ
    ((sourceCoordinates k B).comp ((B.J k).subtype.restrictScalars k))
    (by intro f hf; exact sourceCoordinates_nJ k B f.val hf)

/-- Source coordinates descend through both actual quotients. -/
def boundarySourceCoordinates (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    BoundaryGeneratorQuotient k M →ₗ[k] (Source M.base → k) :=
  (tailGeneratorImage k M.base).liftQ (generatorSourceCoordinates k M.base)
    (by
      rintro x ⟨f, rfl⟩
      exact sourceCoordinates_IH k M.base f.val f.property)

def boundaryClass (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    M.base.J k →ₗ[k] BoundaryGeneratorQuotient k M :=
  (tailGeneratorImage k M.base).mkQ.comp (generatorRelations k M.base).mkQ

theorem boundaryClass_surjective (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    Function.Surjective (boundaryClass k M) :=
  (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)

theorem boundarySourceCoordinates_class (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (f : M.base.J k) :
    boundarySourceCoordinates k M (boundaryClass k M f) = sourceCoordinates k M.base f.val := rfl

theorem boundaryClass_IH (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (f : M.base.J k) (hf : f.val ∈ M.base.IH k) : boundaryClass k M f = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨⟨f.val, hf⟩, rfl⟩

theorem boundaryClass_nJ (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (f : M.base.J k) (hf : f.val ∈ variableIdeal k * M.base.J k) :
    boundaryClass k M f = 0 := by
  have hz : (generatorRelations k M.base).mkQ f = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hf
  simp only [boundaryClass, LinearMap.comp_apply, hz, map_zero]

end NS25Lean.L2B2A2
