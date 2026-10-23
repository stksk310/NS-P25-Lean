import NS25Lean.P2SectorAClosureR49
import NS25Lean.P2SectorDClosureR49
import NS25Lean.P2FiveSectorAssemblyCheckpointR48

set_option linter.style.header false
namespace NS25Lean.L5A2R49

/-- The five actual sectors close on the original chosen P2 data. -/
theorem p2_type_le_sourceCount {Gamma : NumericalSemigroup} (P : L5A1.P2Data Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  rcases L5A2R48.p2_type_bound_or_sectorA_or_sectorD P with h | hA | hD
  · exact h
  · exact sectorA_type_le_sourceCount P hA
  · exact L5A2R49D.sectorD_type_le_sourceCount P hD

/-- Intrinsic rho-minus-two bound at the chosen P2Data binder. -/
theorem p2_type_le_rho_sub_two {Gamma : NumericalSemigroup} (P : L5A1.P2Data Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  have := p2_type_le_sourceCount P
  have := L5A1.p2_rho_eq_sourceCount_add_two P
  omega

end NS25Lean.L5A2R49
