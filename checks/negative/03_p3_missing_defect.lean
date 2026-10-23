import NS25Lean
set_option autoImplicit false
noncomputable section
open NS25Lean

example {Gamma : NumericalSemigroup} (M : L2B.MultiplicityBase Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 :=
  P3R68.p3_strong_of_chosenDefect_three M
