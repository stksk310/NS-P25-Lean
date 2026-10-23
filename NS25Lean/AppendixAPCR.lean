import NS25Lean.AppendixATypeII

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- Appendix-A PCR for the sole frozen formal entry, with no extra branch assumptions. -/
theorem pcr (F : InternalFrontend k M h) :
    F.delta1 + (L3A.q_fs F.initial.ideal : ℤ) - 1 ≤ F.delta3 := by
  by_cases hq : L3A.q_fs F.initial.ideal = 0
  · simpa [hq] using qfs_zero_compensation F hq
  have hq1 : L3A.q_fs F.initial.ideal = 1 := by have := F.q_fs_le_one; omega
  by_cases hc : F.normal.c = 0
  · have hh := typeI_endpoint_survival F hq1 hc
    simpa [hq1] using hh
  · have hh := typeII_endpoint_pincer F hq1 (Nat.pos_of_ne_zero hc)
    simpa [hq1] using hh

end NS25Lean.L3C
