import NS25Lean.OneDefectTransfer
import NS25Lean.P2StrongOriginalR50
import NS25Lean.P3StrongAssemblyR68

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.EC.R70
open ChosenBase L2B L2C L3B
variable {Gamma : NumericalSemigroup}

/-- P2 transported through the actual dilation, retaining the original Gamma. -/
theorem arbitrary_pivot_p2_strong (B : Data Gamma) (hp : chosenDefect B = 2) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  have ht := dilation_transfer B (transferScale B) (transferScale_gt B)
    (transferScale_coprime B)
  have hd : chosenDefect (transferBase B).base = 2 := ht.2.2.2.2.trans hp
  have hb := P2Strong.p2_strong (transferBase B) hd
  dsimp only [transferSemigroup] at hb
  rw [ht.2.1, ht.2.2.1] at hb
  exact hb

/-- P3 uses the accepted R68 four-case theorem on the dilated multiplicity base. -/
theorem arbitrary_pivot_p3_strong (B : Data Gamma) (hp : chosenDefect B = 3) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  have ht := dilation_transfer B (transferScale B) (transferScale_gt B)
    (transferScale_coprime B)
  have hd : chosenDefect (transferBase B).base = 3 := ht.2.2.2.2.trans hp
  have hb := P3R68.p3_strong_of_chosenDefect_three (transferBase B) hd
  dsimp only [transferSemigroup] at hb
  rw [ht.2.1, ht.2.2.1] at hb
  exact hb

/-- Defect range for every actual chosen generator, via a different semigroup. -/
theorem arbitrary_pivot_defect_le_three (B : Data Gamma) : chosenDefect B ≤ 3 := by
  have ht := dilation_transfer B (transferScale B) (transferScale_gt B)
    (transferScale_coprime B)
  have hb := L2B2A2.multiplicity_chosenDefect_le_three (transferBase B)
  have hd : chosenDefect (transferBase B).base = chosenDefect B := ht.2.2.2.2
  omega

/-- The numerical part of ALL-PIVOTS; no equality mechanism is asserted here. -/
theorem equality_pivot_defect_zero_or_one (B : Data Gamma)
    (he : Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1) :
    chosenDefect B = 0 ∨ chosenDefect B = 1 := by
  have hr := arbitrary_pivot_defect_le_three B
  have hn2 : chosenDefect B ≠ 2 := by
    intro h2
    have hb := arbitrary_pivot_p2_strong B h2
    have hsource := sourceCount_add_defect B
    omega
  have hn3 : chosenDefect B ≠ 3 := by
    intro h3
    have hb := arbitrary_pivot_p3_strong B h3
    have hsource := sourceCount_add_defect B
    omega
  omega

/-- Quantifiers are all four original generator indices, not only the multiplicity. -/
theorem equality_every_pivot_defect_zero_or_one (B : Data Gamma)
    (he : Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1) :
    ∀ i : Fin 4, chosenDefect (atPivot B i) = 0 ∨ chosenDefect (atPivot B i) = 1 :=
  fun i => equality_pivot_defect_zero_or_one (atPivot B i) he

end NS25Lean.EC.R70
