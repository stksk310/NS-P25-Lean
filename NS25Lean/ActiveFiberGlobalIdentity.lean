import NS25Lean.HomogeneousGeneratorBridge
import NS25Lean.GeneratorQuotientDimension

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A2
open NS25Lean.L2B ChosenBase
variable {Gamma : NumericalSemigroup}

/-- The manuscript's active-fiber identity for the actual ideal generator number.
This proof uses only the boundary, graded tail, and homogeneous residue coordinates. -/
theorem active_fiber_mu_identity (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    (M.base.J k).spanFinrank = sourceCount M.base +
      ∑ h ∈ activeDegreeFinset M, fiberContribution M h :=
  (generatorQuotient_finrank_eq_spanFinrank k M.base).symm.trans
    (generatorQuotient_finrank_eq_source_add_contributions k M)

end NS25Lean.L2B2A2
