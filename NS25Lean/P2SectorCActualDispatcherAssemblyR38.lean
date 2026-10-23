import NS25Lean.P2SectorCPureCCapsR37

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR38

open L2B L5A1 L5A2C3G L5A2C4G L5A2C4OR19

variable {Gamma : NumericalSemigroup}

/-- The actual bound for any supplied role packet, without a DirectPF premise. -/
theorem actual_role_packet_type_bound {P : P2Data Gamma} (R : ActualRolePacket P) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have hcomp := L5A2C4OR37.actual_role_packet_compensation R
  have hbound := L5A2C4OR35.actual_M6_M7_bound R
  omega

/-- Construct the frozen packet for the same physical Gamma and P from the
actual nonsymmetric gate. All fields are literal gate outputs, not new
numerical or accounting hypotheses. -/
theorem actual_nonsymmetric_role_packet_exists (P : P2Data Gamma)
    (hNS : NonsymmetricSectorC P) : Nonempty (ActualRolePacket P) := by
  obtain ⟨G, bp, bm, ip, im, e, HD, hbne, hine, hpc, hmab, hpb, hmac,
    hinactive, _⟩ := actual_nonsymmetric_gate_interface P hNS
  exact ⟨{
    G := G
    boundaryPure := bp
    boundaryMixed := bm
    internalPure := ip
    internalMixed := im
    e := e
    HD := HD
    boundary_ne := hbne
    internal_ne := hine
    pureC := hpc
    mixedAB := hmab
    pureB := hpb
    mixedAC := hmac
    inactive := hinactive }⟩

/-- Nonsymmetric Sector C, including both notch orientations and DirectPF,
closes without a caller-supplied role packet or branch predicate. -/
theorem actual_nonsymmetric_type_bound (P : P2Data Gamma)
    (hNS : NonsymmetricSectorC P) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  obtain ⟨R⟩ := actual_nonsymmetric_role_packet_exists P hNS
  exact actual_role_packet_type_bound R

/-- The live dispatcher with its genuinely nonsymmetric branch discharged.
The two pure geometry cases are retained literally, not relabeled as CI. -/
theorem sectorC_type_bound_or_pure_geometry (P : P2Data Gamma)
    (hC : SectorC P.M) :
    (∃ G : SectorCActualFibers P,
      ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) ∨
    (∃ (G : SectorCActualFibers P)
      (bp bm : boundaryComponents G),
      bp ≠ bm ∧ IsPureBoundaryComponent G bp ∧ IsMixedBoundaryComponent G bm ∧
        ∀ C : internalComponents G,
          (componentSupport P.M.base G.internalDegree C).card = 1) ∨
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  rcases sectorC_actual_nonsymmetric_exhaustion P hC with hA | hB | hNS
  · exact Or.inl hA
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr (actual_nonsymmetric_type_bound P hNS))

end NS25Lean.L5A2C4OR38
