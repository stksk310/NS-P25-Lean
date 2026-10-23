import NS25Lean.P2ReindexInvariants

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A1R

open L2B L5A1
variable {Gamma : NumericalSemigroup}

theorem localSignature_reindex_iff (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (h c d : ℕ) :
    LocalSignature (reindexMultiplicityBase M e) h c d ↔ LocalSignature M h c d := by
  simp [LocalSignature, componentCount_reindex, killedCount_reindex]

theorem positiveDegrees_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    positiveDegrees (reindexMultiplicityBase M e) = positiveDegrees M := by
  ext h
  simp [mem_positiveDegrees, fiberContribution_reindex]

theorem sectorY_reindex_iff (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    SectorY (reindexMultiplicityBase M e) ↔ SectorY M := by
  simp [SectorY, positiveDegrees_reindex, localSignature_reindex_iff]

theorem sectorA_reindex_iff (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    SectorA (reindexMultiplicityBase M e) ↔ SectorA M := by
  simp [SectorA, positiveDegrees_reindex, localSignature_reindex_iff]

theorem sectorB_reindex_iff (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    SectorB (reindexMultiplicityBase M e) ↔ SectorB M := by
  simp [SectorB, positiveDegrees_reindex, localSignature_reindex_iff]

theorem sectorC_reindex_iff (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    SectorC (reindexMultiplicityBase M e) ↔ SectorC M := by
  simp [SectorC, positiveDegrees_reindex, localSignature_reindex_iff]

theorem sectorD_reindex_iff (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    SectorD (reindexMultiplicityBase M e) ↔ SectorD M := by
  simp [SectorD, positiveDegrees_reindex, localSignature_reindex_iff]

/-- Reindex actual P2 data; the defect proof is transported from the actual base. -/
def reindexP2Data (P : P2Data Gamma) (e : Fin 3 ≃ Fin 3) : P2Data Gamma where
  M := reindexMultiplicityBase P.M e
  hp := (chosenDefect_reindex P.M e).trans P.hp

@[simp] theorem reindexP2Data_sourceCount (P : P2Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (reindexP2Data P e).sourceCount = P.sourceCount :=
  sourceCount_reindex P.M e

@[simp] theorem reindexP2Data_positiveDegrees (P : P2Data Gamma) (e : Fin 3 ≃ Fin 3) :
    positiveDegrees (reindexP2Data P e).M = positiveDegrees P.M :=
  positiveDegrees_reindex P.M e

end NS25Lean.L5A1R
