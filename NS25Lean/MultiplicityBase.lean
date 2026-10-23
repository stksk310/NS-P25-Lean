import NS25Lean.ChosenBaseInterface

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase FourGeneratedBridge ToricPresentation
variable {Gamma : NumericalSemigroup}

def sourceCount (B : Data Gamma) : ℕ := tailGeneratorCount B.H B.K
def chosenDefect (B : Data Gamma) : ℕ := Presentation.rho Gamma - sourceCount B

theorem sourceCount_le_rho (B : Data Gamma) : sourceCount B ≤ Presentation.rho Gamma := by
  rw [B.rho_eq_toricGeneratorNumber ℚ]
  exact (tailGeneratorCount_le_spanFinrank ℚ _ _ _ B.H_le).trans
    (tailMonomialIdeal_generatorNumber_le ℚ _ _ B.H_le B.degrees B.tailDegrees
      (fun _ => rfl) B.degrees_generate B.tailDegrees_generate)

theorem sourceCount_add_defect (B : Data Gamma) :
    sourceCount B + chosenDefect B = Presentation.rho Gamma :=
  Nat.add_sub_of_le (sourceCount_le_rho B)

/-- Actual least positive element, independent of the displayed index order. -/
def IsMultiplicity (B : Data Gamma) : Prop :=
  ∀ n : ℕ, n ∈ Gamma.toAddSubmonoid → n ≠ 0 → B.q.val ≤ n

def multiplicityPivot (B : Data Gamma) : Fin 4 :=
  Classical.choose (Finset.exists_min_image Finset.univ (fun i => (B.family i).val)
    Finset.univ_nonempty)

theorem multiplicityPivot_le (B : Data Gamma) (i : Fin 4) :
    (B.family (multiplicityPivot B)).val ≤ (B.family i).val :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ (fun i => (B.family i).val)
    Finset.univ_nonempty)).2 i (Finset.mem_univ i)

def multiplicityData (B : Data Gamma) : Data Gamma := { B with pivot := multiplicityPivot B }

theorem multiplicityData_isMultiplicity (B : Data Gamma) : IsMultiplicity (multiplicityData B) := by
  intro n hn hne
  rw [← B.generates] at hn
  induction hn using AddSubmonoid.closure_induction with
  | mem n hn =>
      obtain ⟨i, rfl⟩ := hn
      exact multiplicityPivot_le B i
  | zero => exact (hne rfl).elim
  | add a b ha hb iha ihb =>
      by_cases haz : a = 0
      · subst a
        simpa using ihb (by simpa using hne)
      · exact (iha haz).trans (Nat.le_add_right a b)

theorem exists_multiplicity_base (B : Data Gamma) : ∃ B' : Data Gamma, IsMultiplicity B' :=
  ⟨multiplicityData B, multiplicityData_isMultiplicity B⟩

end NS25Lean.L2B
