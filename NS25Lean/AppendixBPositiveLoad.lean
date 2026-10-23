import NS25Lean.FourBasePreparation

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L4A

open ChosenBase L2C

variable {Gamma : NumericalSemigroup}

/-- Appendix B, positive-load equality: the four positive integral loads exhaust
the frozen four-base budget. -/
theorem positive_load_sum_eq_four (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) :
    (∑ i : Fin 4, internalLoad B i) = 4 := by
  apply Nat.le_antisymm (four_base_budget B)
  calc
    4 = ∑ _i : Fin 4, (1 : ℕ) := by simp
    _ ≤ ∑ i : Fin 4, internalLoad B i :=
      Finset.sum_le_sum (fun i _ => hpos i)

/-- Every actual internal Betti load is one; no chosen-base defect is identified
with an internal load in this result. -/
theorem positive_load_eq_one (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (i : Fin 4) :
    internalLoad B i = 1 := by
  have hsum : (∑ _j : Fin 4, (1 : ℕ)) = ∑ j : Fin 4, internalLoad B j := by
    rw [positive_load_sum_eq_four B hpos]
    simp
  exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => hpos j)).mp hsum i
    (Finset.mem_univ i)).symm

/-- Equality tracing through the actual degree contributions in the frozen
four-base proof. -/
theorem positive_load_degree_sum_eq_four (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) :
    (∑ d ∈ bettiDegrees B,
      (4 - (fiberVariables B d).card) * (componentCount B d - 1)) = 4 := by
  have hsum := positive_load_sum_eq_four B hpos
  simp_rw [internalLoad_eq_sum] at hsum
  rw [Finset.sum_comm] at hsum
  simp_rw [degree_contribution_identity] at hsum
  exact hsum

/-- Appendix B's total singleton budget is attained under positive loads. -/
theorem singleton_budget_equality (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) :
    (∑ d ∈ bettiDegrees B, singletonComponentCount B d) = 4 := by
  apply Nat.le_antisymm
  · exact singleton_sum_le_four B _ (by
      intro d hd
      have hb := (mem_bettiDegrees B d).mp hd
      exact ⟨betti_positive B d hb, hb⟩)
  · calc
      4 = ∑ d ∈ bettiDegrees B,
          (4 - (fiberVariables B d).card) * (componentCount B d - 1) :=
        (positive_load_degree_sum_eq_four B hpos).symm
      _ ≤ ∑ d ∈ bettiDegrees B, singletonComponentCount B d := by
        apply Finset.sum_le_sum
        intro d hd
        exact local_support_partition_bound B d ((mem_bettiDegrees B d).mp hd)

/-- Equality of the summed budget forces equality at each actual Betti degree. -/
theorem local_budget_equality (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d) :
    (4 - (fiberVariables B d).card) * (componentCount B d - 1) =
      singletonComponentCount B d := by
  have hsum : (∑ e ∈ bettiDegrees B,
      (4 - (fiberVariables B e).card) * (componentCount B e - 1)) =
      ∑ e ∈ bettiDegrees B, singletonComponentCount B e := by
    rw [positive_load_degree_sum_eq_four B hpos, singleton_budget_equality B hpos]
  exact (Finset.sum_eq_sum_iff_of_le (fun e he =>
    local_support_partition_bound B e ((mem_bettiDegrees B e).mp he))).mp hsum d
      ((mem_bettiDegrees B d).mpr hd)

end NS25Lean.L4A
