import NS25Lean
set_option autoImplicit false
noncomputable section
open NS25Lean

example {Gamma : NumericalSemigroup} {M : L2B.MultiplicityBase Gamma}
    {d : ℕ} (F : L3B.InternalFrontend ℚ M d) : L3A.q_fs F.initial.ideal = 1 :=
  F.q_fs_le_one
