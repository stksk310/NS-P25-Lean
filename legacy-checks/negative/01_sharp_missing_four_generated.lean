import NS25Lean
set_option autoImplicit false
noncomputable section
open NS25Lean

example (Gamma : NumericalSemigroup) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 1 :=
  L4B.ns_sharp Gamma
