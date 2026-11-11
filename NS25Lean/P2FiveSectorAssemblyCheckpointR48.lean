import NS25Lean.P2SectorYFinalClosure
import NS25Lean.P2SectorBFinalRepairClosure
import NS25Lean.P2SectorCSharedClosure

set_option linter.style.header false

namespace NS25Lean.L5A2R48

open L5A1

/-- Eliminate the three certified sectors on the original chosen P2 data.
The actual Sector A and Sector D alternatives remain explicit. -/
theorem p2_type_bound_or_sectorA_or_sectorD
    {Gamma : NumericalSemigroup} (P : P2Data Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount ∨ SectorA P.M ∨ SectorD P.M := by
  rcases p2_five_sectors P with hY | hA | hB | hC | hD
  · exact Or.inl (sectorY_type_le_sourceCount P hY)
  · exact Or.inr (Or.inl hA)
  · exact Or.inl (L5A2BFinalRepair.sectorB_actual_type_le_sourceCount P hB)
  · exact Or.inl (SectorCSharedClosure.sectorC_type_bound P hC)
  · exact Or.inr (Or.inr hD)

end NS25Lean.L5A2R48
