import NS25Lean.P2SectorCActualSourceHitLocalReductionR10

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR11

open L5A2C4H
open L5A2C4D
open L5A2C4OR5

variable {Gamma : NumericalSemigroup}

/-- The actual eta/grid-lift measurement of the `b`-carry on the upper edge
of the local square based at `(i,j)`.  This is a definition from the frozen
physical-offset dictionary, not an assumed carry value. -/
def coherentCMLocalCarry (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j : ℕ) : ℕ :=
  L5A2C4C.eta B e i (j + 1) + gridLift B e (i + 1) (j + 1) -
    (L5A2C4C.eta B e (i + 1) (j + 1) + gridLift B e i (j + 1))

/-- The only central critical seam of the coherent Herzog L-shape. -/
def IsCriticalC1Seam (HD : CoherentHerzogData B e) (i j : ℕ) : Prop :=
  cr12 HD ≤ i + 1 ∧ cr13 HD ≤ j + 1

/-- The source-exact height correction attached to the central seam. -/
noncomputable def criticalC1SeamCorrection (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ) : ℕ :=
  by
    classical
    exact if IsCriticalC1Seam HD i j then L5A2C4A.c1 B e else 0

theorem criticalC1SeamCorrection_eq_zero_of_not_seam
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (h : ¬ IsCriticalC1Seam HD i j) :
    criticalC1SeamCorrection B e HD i j = 0 := by
  simp [criticalC1SeamCorrection, h]

theorem criticalC1SeamCorrection_eq_c1_of_seam
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (h : IsCriticalC1Seam HD i j) :
    criticalC1SeamCorrection B e HD i j = L5A2C4A.c1 B e := by
  simp [criticalC1SeamCorrection, h]

theorem criticalC1SeamCorrection_cases
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (i j : ℕ) :
    criticalC1SeamCorrection B e HD i j = 0 ∨
      criticalC1SeamCorrection B e HD i j = L5A2C4A.c1 B e := by
  by_cases h : IsCriticalC1Seam HD i j
  · exact Or.inr (criticalC1SeamCorrection_eq_c1_of_seam B e HD h)
  · exact Or.inl (criticalC1SeamCorrection_eq_zero_of_not_seam B e HD h)

/-- At the central seam the raw upper-right corner differs from the reduced
origin by exactly the critical relation `c1*a`. -/
theorem criticalC1Seam_normalizedGrid_correction
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (h : IsCriticalC1Seam HD i j) :
    normalizedGrid B e 0 (i + 1) (j + 1) =
      normalizedGrid B e (L5A2C4A.c1 B e)
        (i + 1 - cr12 HD) (j + 1 - cr13 HD) := by
  have hr := (L5A2C4OR5.coherent_normalized_relations B e HD).1
  simp only [normalizedGrid, zero_mul, zero_add, mul_zero, add_zero]
  have hi := Nat.sub_add_cancel h.1
  have hj := Nat.sub_add_cancel h.2
  calc
    (i + 1) * routingB B e + (j + 1) * routingC B e =
        ((i + 1 - cr12 HD) + cr12 HD) * routingB B e +
          ((j + 1 - cr13 HD) + cr13 HD) * routingC B e := by rw [hi, hj]
    _ = L5A2C4A.c1 B e * routingA B e +
          (i + 1 - cr12 HD) * routingB B e +
          (j + 1 - cr13 HD) * routingC B e := by rw [hr]; ring

/-- Every finite coherent L-shape index gives its actual natural grid
coordinate, in the actual Herzog domain, with the same residue. -/
theorem lShapeIndex_actual_coordinate
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e)
    (x : GenericLShape.Index (cr12 HD) (cr13 HD) (cr32 HD) (cr23 HD)) :
    ∃ i j : ℕ,
      HerzogLShapeDomain HD i j ∧
      GenericLShape.residue (routingA B e) (routingB B e) (routingC B e)
          (cr12 HD) (cr13 HD) (cr32 HD) (cr23 HD) x =
        gridResidue B e i j := by
  have hs := coherent_coefficients B e HD
  rcases x with ij | sj
  · refine ⟨ij.1, ij.2, ?_, ?_⟩
    · exact ⟨by omega, by omega, Or.inl ij.1.isLt⟩
    · simp only [GenericLShape.residue, GenericLShape.pair, gridResidue]
      norm_cast
  · refine ⟨cr12 HD + sj.1, sj.2, ?_, ?_⟩
    · exact ⟨by omega, by omega, Or.inr sj.2.isLt⟩
    · simp only [GenericLShape.residue, GenericLShape.pair, gridResidue]
      norm_cast

/-- The exact still-missing geometric location assertion: the source-hit
square must stay inside the two outer critical bounds.  Once this is known,
the only possible failure of upper-right L-shape membership is the central
`c1` seam. -/
def SourceHitSquareInterior
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit
      (routingData B e) incoming target.raw) : Prop :=
  let Q := L5A2C4OR9.actualSourceHitState B e incoming target hit
  ∃ i j : ℕ,
    HerzogLShapeDomain HD i j ∧ gridResidue B e i j = Q ∧
      i + 1 < L5A2C4A.c2 B e ∧ j + 1 < L5A2C4A.c3 B e

theorem upperRight_domain_or_criticalC1Seam
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (hbase : HerzogLShapeDomain HD i j)
    (hi : i + 1 < L5A2C4A.c2 B e)
    (hj : j + 1 < L5A2C4A.c3 B e) :
    HerzogLShapeDomain HD (i + 1) (j + 1) ∨
      IsCriticalC1Seam HD i j := by
  rcases hbase with ⟨-, -, hcorner⟩
  by_cases hleft : i + 1 < cr12 HD
  · exact Or.inl ⟨hi, hj, Or.inl hleft⟩
  by_cases hbottom : j + 1 < cr13 HD
  · exact Or.inl ⟨hi, hj, Or.inr hbottom⟩
  right
  exact ⟨le_of_not_gt hleft, le_of_not_gt hbottom⟩

/-- The raw routing cross on the upper edge is definitionally the coherent
eta/grid-lift local carry at the same actual coordinate. -/
theorem raw_upper_cross_eq_coherentCMLocalCarry
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    (routingData B e).u ((routingData B e).c (gridResidue B e i j)) =
      coherentCMLocalCarry B e i j := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hc : (routingData B e).c (gridResidue B e i j) =
      gridResidue B e i (j + 1) := by
    simpa [routingData, AperyStepData.toResidueData,
      RelativeIdeal.toAperyStepData] using (gridResidue_add_c B e i j).symm
  rw [hc]
  have ht := eta_b_carry_transition B e i (j + 1)
  unfold coherentCMLocalCarry
  omega

/-- Non-seam specialization: the raw cross and coherent local carry agree and
the correction is zero. -/
theorem nonseam_local_square_carry
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (h : ¬ IsCriticalC1Seam HD i j) :
    (routingData B e).u ((routingData B e).c (gridResidue B e i j)) =
        coherentCMLocalCarry B e i j ∧
      criticalC1SeamCorrection B e HD i j = 0 :=
  ⟨raw_upper_cross_eq_coherentCMLocalCarry B e i j,
    criticalC1SeamCorrection_eq_zero_of_not_seam B e HD h⟩

/-- Seam specialization: the raw cross still equals the coherent local carry,
while the raw upper-right grid corner carries exactly one `c1*a` correction. -/
theorem seam_local_square_carry_corrected
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (h : IsCriticalC1Seam HD i j) :
    (routingData B e).u ((routingData B e).c (gridResidue B e i j)) =
        coherentCMLocalCarry B e i j ∧
      criticalC1SeamCorrection B e HD i j = L5A2C4A.c1 B e ∧
      normalizedGrid B e 0 (i + 1) (j + 1) =
        normalizedGrid B e (L5A2C4A.c1 B e)
          (i + 1 - cr12 HD) (j + 1 - cr13 HD) :=
  ⟨raw_upper_cross_eq_coherentCMLocalCarry B e i j,
    criticalC1SeamCorrection_eq_c1_of_seam B e HD h,
    criticalC1Seam_normalizedGrid_correction B e HD h⟩

/-- Strongest unconditional C4O-R11 dictionary checkpoint.  The coordinate,
raw cross, coherent local carry, positivity/opposite-arm identity, and the
central seam correction are all recovered from the accepted R10 source-hit
objects.  The outer-square interior bridge is intentionally not claimed here. -/
theorem actual_sourceHit_raw_eta_gridLift_dictionary
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit
      (routingData B e) incoming target.raw) :
    let D := routingData B e
    let Q := L5A2C4OR9.actualSourceHitState B e incoming target hit
    let w := D.u (D.c Q)
    ∃ i j : ℕ,
      HerzogLShapeDomain HD i j ∧
      gridResidue B e i j = Q ∧
      w = coherentCMLocalCarry B e i j ∧
      0 < w ∧ w = D.v (D.b Q) ∧
      (criticalC1SeamCorrection B e HD i j = 0 ∨
        criticalC1SeamCorrection B e HD i j = L5A2C4A.c1 B e) ∧
      (IsCriticalC1Seam HD i j →
        normalizedGrid B e 0 (i + 1) (j + 1) =
          normalizedGrid B e (L5A2C4A.c1 B e)
            (i + 1 - cr12 HD) (j + 1 - cr13 HD)) := by
  dsimp only
  obtain ⟨x, hx, -⟩ :=
    L5A2C4OR10.actual_sourceHit_unique_lShape_index B e HD incoming target hit
  obtain ⟨i, j, hdomain, hres⟩ := lShapeIndex_actual_coordinate B e HD x
  have hQ : gridResidue B e i j =
      L5A2C4OR9.actualSourceHitState B e incoming target hit :=
    hres.symm.trans hx
  have hcross := L5A2C4OR10.actual_sourceHit_cross_value_spec
    B e incoming target hit
  refine ⟨i, j, hdomain, hQ, ?_, hcross.1, hcross.2,
    criticalC1SeamCorrection_cases B e HD i j, ?_⟩
  · rw [← hQ]
    exact raw_upper_cross_eq_coherentCMLocalCarry B e i j
  · intro hseam
    exact criticalC1Seam_normalizedGrid_correction B e HD hseam

end NS25Lean.L5A2C4OR11
