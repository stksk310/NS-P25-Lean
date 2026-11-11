import NS25Lean.P2CriticalReturnCapAdapter
import NS25Lean.P2PurePairCapAdapter

set_option autoImplicit false
set_option linter.style.header false
namespace NS25Lean.SectorCSharedClosure
open L5A1 L5A2C3G L5A2C4C
variable {Gamma : NumericalSemigroup}

/-- The original pure-pair source budget uses the shared attained-cap
compensation, after the exact coordinate and cardinality dictionaries. -/
theorem boundary_all_pure_type_bound (P : P2Data Gamma) (G : SectorCActualFibers P)
    (h : ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount := by
  obtain ⟨A,_,hm,hk,hl,_,_,_,hb⟩ :=
    L5A2C4OR46.boundary_all_pure_checkpoint P G h
  have hc := PurePairCapAdapter.boundary_compensation G A hm hk hl
  omega

/-- The actual C dispatcher sends both positive and pure-pair remaining
branches through the common cap theorem. The pure internal branch retains
its transverse-minimum endpoint. All hypotheses are original P2 data. -/
theorem sectorC_type_bound (P : P2Data Gamma) (hC : SectorC P.M) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount := by
  rcases L5A2C4G.sectorC_actual_nonsymmetric_exhaustion P hC with hB | hI | hNS
  · obtain ⟨G,h⟩ := hB
    exact boundary_all_pure_type_bound P G h
  · obtain ⟨G,bp,bm,hne,hp,hm,hi⟩ := hI
    exact L5A2C4OR45.internal_all_pure_type_bound P G bp bm hne hp hm hi
  · exact CriticalReturnCapAdapter.actual_nonsymmetric_type_bound_shared P hNS
end NS25Lean.SectorCSharedClosure
