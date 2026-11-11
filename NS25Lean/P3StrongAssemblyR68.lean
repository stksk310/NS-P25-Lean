import NS25Lean.P3ActiveClassificationR51
import NS25Lean.P3R0TypeR56
import NS25Lean.P3R1TypeR65
import NS25Lean.P3R1SentinelAlignment
import NS25Lean.P3R2DirectTypeR63
import NS25Lean.P3R2StaircaseAlignment
import NS25Lean.P3R3OriginalR67

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean
open ChosenBase L2B L5A1

namespace P3R67
/-- R68 naming forwarder: the accepted R1 proof is in the frozen P3R65
namespace. This theorem supplies the exact name advertised by the R68 DAG,
without changing that proof or its original Gamma/M assumptions. -/
theorem r1_original_type_le_rho_sub_two {Gamma : NumericalSemigroup}
    (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (hR1 : (P3R51.internalDegrees M).card = 1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  exact P3R65.r1_original_type_le_rho_sub_two M hp hR1
end P3R67

namespace P3R68
/-- Original P3-STRONG on every original multiplicity base with chosen defect
three. The actual internal count is exhaustively classified, never assumed. -/
theorem p3_strong_of_chosenDefect_three {Gamma : NumericalSemigroup}
    (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  rcases P3R51.internal_count_cases M hp with h0 | h1 | h2 | h3
  · exact P3R56.r0_type_bound M hp h0
  · exact P3R65.r1_original_type_via_final_sentinel M hp h1
  · exact P3R63.r2_original_type_via_final_staircase M hp h2
  · exact P3R67.r3_original_type_le_rho_sub_two M hp h3
end P3R68
end NS25Lean
