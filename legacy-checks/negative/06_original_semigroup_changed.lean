import NS25Lean
set_option autoImplicit false
noncomputable section
open NS25Lean

example (Gamma Delta : NumericalSemigroup) (M : L2B.MultiplicityBase Gamma) :
    Delta.asRelativeIdeal.idealType = Presentation.rho Delta - 1 ↔
      EC.R75.FiniteEqualityCertificate M :=
  EC.R75.finite_intrinsic_equality_iff Gamma M
