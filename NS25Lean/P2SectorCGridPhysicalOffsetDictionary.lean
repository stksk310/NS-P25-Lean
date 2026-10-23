import NS25Lean.P2SectorCPhysicalHeightBridge

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR4

open FourGeneratedBridge L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR3

variable {Gamma : NumericalSemigroup}

/-- The raw `(i,j)` grid bottom is an actual element of the normalized tail
semigroup. -/
theorem normalizedGrid_zero_mem_routingH
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    (normalizedGrid B e 0 i j : ℤ) ∈ (routingH B e).asRelativeIdeal := by
  refine ⟨normalizedGrid B e 0 i j, ?_, rfl⟩
  have hi := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e) i
  have hj := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e) j
  simpa [normalizedGrid, nsmul_eq_mul] using
    (routingH B e).toAddSubmonoid.add_mem hi hj

private theorem existsUnique_tailGridLift
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ∃! l : ℕ, (normalizedGrid B e 0 i j : ℤ) =
      physicalAlpha B e (gridResidue B e i j) + routingA B e * l := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let beta : ℤ := normalizedGrid B e 0 i j
  let s := gridResidue B e i j
  let alpha := physicalAlpha B e s
  have hmem : beta ∈ (routingH B e).asRelativeIdeal := by
    simpa [beta] using normalizedGrid_zero_mem_routingH B e i j
  have hmodBeta : (beta : ZMod (routingA B e)) = s := by
    simpa [beta, s] using normalizedGrid_mod B e 0 i j
  have hmodAlpha : (alpha : ZMod (routingA B e)) = s := by
    simpa [alpha, physicalAlpha] using
      (routingH B e).asRelativeIdeal.aperyRepresentative_mod
        (routingA B e) s
  have hle : alpha ≤ beta := by
    apply (routingH B e).asRelativeIdeal.aperyRepresentative_le
      (routingA B e) s hmem hmodBeta
  obtain ⟨l, hl⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
    (routingA B e) hle (hmodBeta.trans hmodAlpha.symm)
  refine ⟨l, by simpa [beta, alpha, s] using hl, ?_⟩
  intro k hk
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hl' : beta = alpha + (routingA B e : ℤ) * l := hl
  have hk' : beta = alpha + (routingA B e : ℤ) * k := by
    simpa [beta, alpha, s] using hk
  have : (l : ℤ) = k := by nlinarith
  exact_mod_cast this.symm

/-- The exact nonnegative offset between a raw grid bottom and the actual
normalized-tail semigroup Apéry representative in the same residue. -/
noncomputable def tailGridLift
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) : ℕ := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact Classical.choose (existsUnique_tailGridLift B e i j)

/-- Defining equation for the independently constructed tail-grid lift. -/
theorem tailGridLift_spec
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (normalizedGrid B e 0 i j : ℤ) =
      physicalAlpha B e (gridResidue B e i j) +
        routingA B e * tailGridLift B e i j :=
  (Classical.choose_spec (existsUnique_tailGridLift B e i j)).1

/-- Every point in a raw grid column is the canonical tail Apéry
representative plus the exact bottom offset and its `a`-height. -/
theorem normalizedGrid_eq_physicalAlpha_add
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (n i j : ℕ) :
    (normalizedGrid B e n i j : ℤ) =
      physicalAlpha B e (gridResidue B e i j) +
        routingA B e * (tailGridLift B e i j + n) := by
  have hspec := tailGridLift_spec B e i j
  simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul] at hspec ⊢
  push_cast at hspec ⊢
  nlinarith

/-- The C4C eta threshold equals the actual physical threshold translated by
the independently measured raw-grid offset. -/
theorem eta_le_iff_physicalHeight_le_add
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j n : ℕ) :
    eta B e i j ≤ n ↔
      physicalHeight B e (gridResidue B e i j) ≤
        tailGridLift B e i j + n := by
  have hgrid := normalizedGrid_mem_iff_eta_le B e n i j
  have hdecomp := normalizedGrid_eq_physicalAlpha_add B e n i j
  have hraw := rawMinimum_threshold B e (gridResidue B e i j)
    (tailGridLift B e i j + n)
  have hraw' :
      physicalAlpha B e (gridResidue B e i j) +
          (routingA B e : ℤ) *
            ((tailGridLift B e i j : ℤ) + n) ∈ routingI B e ↔
        rawMinimum B e (gridResidue B e i j) ≤
          (tailGridLift B e i j : ℤ) + n := by
    simpa only [Nat.cast_add] using hraw
  have hheight := physicalHeight_eq_max_rawMinimum B e
    (gridResidue B e i j)
  rw [hdecomp] at hgrid
  rw [hraw'] at hgrid
  constructor <;> intro h
  · have hmu := hgrid.mpr h
    have hhcast : (physicalHeight B e (gridResidue B e i j) : ℤ) ≤
        tailGridLift B e i j + n := by
      rw [hheight]
      omega
    exact_mod_cast hhcast
  · apply hgrid.mp
    have hhcast : (physicalHeight B e (gridResidue B e i j) : ℤ) ≤
        tailGridLift B e i j + n := by exact_mod_cast h
    rw [hheight] at hhcast
    omega

/-- Global exact dictionary: eta is physical height minus the raw bottom
offset, using natural saturated subtraction. -/
theorem eta_eq_physicalHeight_sub_tailGridLift
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    eta B e i j =
      physicalHeight B e (gridResidue B e i j) - tailGridLift B e i j := by
  apply le_antisymm
  · apply (eta_le_iff_physicalHeight_le_add B e i j _).mpr
    omega
  · have h := (eta_le_iff_physicalHeight_le_add B e i j
      (eta B e i j)).mp (le_refl _)
    omega

/-- Conservation identity comparing the semigroup-bottom lift with C4H's
ideal-Apéry lift at the eta threshold. -/
theorem tailGridLift_add_eta_eq_physicalHeight_add_gridLift
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    tailGridLift B e i j + eta B e i j =
      physicalHeight B e (gridResidue B e i j) + gridLift B e i j := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hgrid := normalizedGrid_eq_physicalAlpha_add B e (eta B e i j) i j
  have hlift := gridLift_spec B e i j
  have hheight := physicalHeight_spec B e (gridResidue B e i j)
  change (routingI B e).aperyRepresentative (routingA B e)
      (gridResidue B e i j) =
    physicalAlpha B e (gridResidue B e i j) +
      (routingA B e : ℤ) *
        physicalHeight B e (gridResidue B e i j) at hheight
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hcast : (tailGridLift B e i j + eta B e i j : ℕ) =
      physicalHeight B e (gridResidue B e i j) + gridLift B e i j := by
    exact_mod_cast (show
      (tailGridLift B e i j : ℤ) + eta B e i j =
        physicalHeight B e (gridResidue B e i j) + gridLift B e i j by
          nlinarith)
  exact hcast

/-- Closed saturated form of the existing C4H ideal-Apéry grid lift. -/
theorem gridLift_eq_tailGridLift_sub_physicalHeight
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    gridLift B e i j = tailGridLift B e i j -
      physicalHeight B e (gridResidue B e i j) := by
  have heta := eta_eq_physicalHeight_sub_tailGridLift B e i j
  have hcons := tailGridLift_add_eta_eq_physicalHeight_add_gridLift B e i j
  omega

/-- An actual canonical tail-grid point is one whose raw bottom literally is
the normalized-tail semigroup Apéry representative in its residue. -/
def IsCanonicalTailGridPoint
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) : Prop :=
  (normalizedGrid B e 0 i j : ℤ) =
    physicalAlpha B e (gridResidue B e i j)

theorem isCanonicalTailGridPoint_iff_tailGridLift_eq_zero
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    IsCanonicalTailGridPoint B e i j ↔ tailGridLift B e i j = 0 := by
  have hspec := tailGridLift_spec B e i j
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  constructor
  · intro hcanonical
    change (normalizedGrid B e 0 i j : ℤ) =
      physicalAlpha B e (gridResidue B e i j) at hcanonical
    have hcast : (tailGridLift B e i j : ℤ) = 0 := by nlinarith
    exact_mod_cast hcast
  · intro hlift
    change (normalizedGrid B e 0 i j : ℤ) =
      physicalAlpha B e (gridResidue B e i j)
    simpa [hlift] using hspec

/-- Eta agrees with physical height only under actual tail-grid
canonicality. -/
theorem eta_eq_physicalHeight_of_isCanonical
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ)
    (h : IsCanonicalTailGridPoint B e i j) :
    eta B e i j = physicalHeight B e (gridResidue B e i j) := by
  rw [eta_eq_physicalHeight_sub_tailGridLift,
    (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e i j).mp h]
  simp

/-- The existing ideal-Apéry lift vanishes at an actual canonical tail-grid
point. -/
theorem gridLift_eq_zero_of_isCanonical
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ)
    (h : IsCanonicalTailGridPoint B e i j) :
    gridLift B e i j = 0 := by
  rw [gridLift_eq_tailGridLift_sub_physicalHeight,
    (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e i j).mp h]
  simp

end NS25Lean.L5A2C4OR4
