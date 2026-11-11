import NS25Lean
set_option autoImplicit false
noncomputable section
open NS25Lean

example {Gamma : NumericalSemigroup} (B : ChosenBase.Data Gamma) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      ∃ i : Fin 4, EC.R75.PivotFiniteCertificate (L2C.atPivot B i) :=
  EC.R75.equality_iff_all_original_pivots B
