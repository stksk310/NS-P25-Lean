import NS25Lean.ActiveFiberAssembly
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.LinearAlgebra.Dimension.DivisionRing

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A2
open NS25Lean.L2B NS25Lean.L2B2A ChosenBase
variable {Gamma : NumericalSemigroup}

instance finiteBoundaryGeneratorQuotient (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    Module.Finite k (BoundaryGeneratorQuotient k M) :=
  Module.Finite.equiv (boundarySourceEquiv k M)

instance finiteGeneratorQuotient (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    Module.Finite k (GeneratorQuotient k M.base) :=
  Module.Finite.of_submodule_quotient (tailGeneratorImage k M.base)

/-- Exact addition in the actual short quotient sequence, after the boundary and
tail coordinate calculations. No presentation cardinality enters this identity. -/
theorem generatorQuotient_finrank_eq_source_add_contributions (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) :
    Module.finrank k (GeneratorQuotient k M.base) = sourceCount M.base +
      ∑ h ∈ activeDegreeFinset M, fiberContribution M h := by
  have he := (tailGeneratorImage k M.base).finrank_quotient_add_finrank
  rw [boundaryGeneratorQuotient_finrank_eq_sourceCount,
    tailGeneratorImage_finrank_eq_contribution_sum] at he
  exact he.symm

end NS25Lean.L2B2A2
