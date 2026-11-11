import NS25Lean
set_option autoImplicit false
noncomputable section
open NS25Lean

example (Gamma : NumericalSemigroup) (M : L2B.MultiplicityBase Gamma) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔ True :=
  EC.R75.finite_intrinsic_equality_iff Gamma M
