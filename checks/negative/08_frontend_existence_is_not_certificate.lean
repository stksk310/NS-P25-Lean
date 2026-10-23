import NS25Lean
set_option autoImplicit false
noncomputable section
open NS25Lean

example {Gamma : NumericalSemigroup} {M : L2B.MultiplicityBase Gamma}
    {d : ℕ} (F : L3B.InternalFrontend ℚ M d) (G : L3C.NormalizedSources F) :
    EC.R74.PCRCountCertificate F G :=
  G
