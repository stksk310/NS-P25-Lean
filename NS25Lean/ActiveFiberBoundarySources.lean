import NS25Lean.ActiveFiberDimension

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A
open NS25Lean.L2B ChosenBase FourGeneratedBridge ToricPresentation MvPolynomial
variable {Gamma : NumericalSemigroup}

/-- The boundary part still to be counted globally:
the actual generator quotient modulo its tail image. -/
abbrev BoundaryGeneratorQuotient (k : Type*) [Field k] (M : MultiplicityBase Gamma) :=
  GeneratorQuotient k M.base ⧸ tailGeneratorImage k M.base

/-- At a minimal H-source, none of the component coordinates is boundary-killed. -/
theorem minimalSource_not_boundaryKilled (M : MultiplicityBase Gamma) (h : ℕ)
    (hs : IsMinimalTailGenerator M.base.H M.base.K h)
    (C : FiberComponent M.base h) : ¬BoundaryKilled M h C := by
  rintro ⟨u, _, j, huj, hk⟩
  have he := congrArg (weight M.base) (remove_variable_add u.val j huj)
  simp only [map_add, weight, Finsupp.weight_single, one_nsmul] at he
  change weights M.base j + weight M.base (u.val - Finsupp.single j 1) =
    weight M.base u.val at he
  have hu := u.property
  rcases hs.2 (weights M.base j) (M.base.tailDegrees j).property
    (weights_positive M.base j).ne' with hlt | hn
  · omega
  · exact hn hk

theorem minimalSource_killedCount_zero (M : MultiplicityBase Gamma) (h : ℕ)
    (hs : IsMinimalTailGenerator M.base.H M.base.K h) : killedCount M h = 0 := by
  have : IsEmpty {C : FiberComponent M.base h // BoundaryKilled M h C} :=
    ⟨fun C => minimalSource_not_boundaryKilled M h hs C.val C.property⟩
  exact Nat.card_eq_zero.mpr (Or.inl this)

/-- A minimal-source monomial survives in the actual J/nJ.
This does not yet identify the global quotient by the tail image. -/
theorem minimalSource_monomial_not_mem_nJ (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ)
    (hs : IsMinimalTailGenerator M.base.H M.base.K h)
    (u : FactorizationFiber M.base h) :
    monomial u.val (1 : k) ∉ variableIdeal k * M.base.J k := by
  rw [monomial_mem_nJ_iff_boundaryKilled k M h u]
  exact minimalSource_not_boundaryKilled M h hs _

end NS25Lean.L2B2A
