import NS25Lean.FourCriticalSingleton
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase
variable {Gamma : NumericalSemigroup}

theorem componentSupport_union (B : Data Gamma) (d : ℕ) :
    letI := Fintype.ofFinite (FiberComponent B d)
    Finset.univ.biUnion (componentSupport B d) = fiberVariables B d := by
  classical
  letI := Fintype.ofFinite (FiberComponent B d)
  ext j
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    mem_componentSupport, mem_variables]
  constructor
  · rintro ⟨C, u, _, hu⟩; exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩; exact ⟨_, u, rfl, hu⟩

theorem sum_componentSupport_card (B : Data Gamma) (d : ℕ) :
    letI := Fintype.ofFinite (FiberComponent B d)
    ∑ C : FiberComponent B d, (componentSupport B d C).card =
      (fiberVariables B d).card := by
  classical
  letI := Fintype.ofFinite (FiberComponent B d)
  have hp : (↑(Finset.univ : Finset (FiberComponent B d)) : Set _).PairwiseDisjoint
      (componentSupport B d) := by
    intro C _ E _ hne
    exact componentSupports_disjoint B d C E hne
  rw [← Finset.card_biUnion hp, componentSupport_union]

/-- A numerical consequence of the actual disjoint, nonempty component supports. -/
theorem local_support_partition_bound (B : Data Gamma) (d : ℕ) (hd : Betti B d) :
    (4 - (fiberVariables B d).card) * (componentCount B d - 1) ≤
      singletonComponentCount B d := by
  classical
  letI := Fintype.ofFinite (FiberComponent B d)
  have hpos (C : FiberComponent B d) : 0 < (componentSupport B d C).card :=
    Finset.card_pos.mpr (componentSupport_nonempty B d (betti_positive B d hd) C)
  have hcount : componentCount B d ≤ (fiberVariables B d).card := by
    rw [← sum_componentSupport_card]
    calc
      componentCount B d = ∑ _C : FiberComponent B d, 1 := by
        simp [componentCount, Nat.card_eq_fintype_card]
      _ ≤ _ := Finset.sum_le_sum (fun C _ => hpos C)
  have hdouble : 2 * componentCount B d ≤
      (fiberVariables B d).card + singletonComponentCount B d := by
    have he : singletonComponentCount B d =
        ∑ C : FiberComponent B d, if (componentSupport B d C).card = 1 then 1 else 0 := by
      simp only [singletonComponentCount, Nat.card_eq_fintype_card, Fintype.card_subtype,
        Finset.card_filter]
    rw [he, ← sum_componentSupport_card, ← Finset.sum_add_distrib]
    calc
      2 * componentCount B d = ∑ _C : FiberComponent B d, 2 := by
        simp [componentCount, Nat.card_eq_fintype_card, Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro C _
        have hp := hpos C
        split_ifs <;> omega
  have hs : (fiberVariables B d).card ≤ 4 :=
    (Finset.card_le_univ _).trans_eq (by simp)
  have hc : 2 ≤ componentCount B d := hd
  generalize (fiberVariables B d).card = s at *
  interval_cases s <;> simp only [Nat.reduceSub, zero_mul, one_mul] <;> omega

theorem degree_contribution_identity (B : Data Gamma) (d : ℕ) :
    (∑ i : Fin 4, if i ∉ fiberVariables B d then componentCount B d - 1 else 0) =
      (4 - (fiberVariables B d).card) * (componentCount B d - 1) := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, smul_eq_mul]
  congr 1
  have he : (Finset.univ.filter (fun i => i ∉ fiberVariables B d)) =
      (Finset.univ : Finset (Fin 4)) \ fiberVariables B d := by ext i; simp
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

theorem four_base_budget (B : Data Gamma) : ∑ i : Fin 4, internalLoad B i ≤ 4 := by
  classical
  simp_rw [internalLoad_eq_sum]
  rw [Finset.sum_comm]
  simp_rw [degree_contribution_identity]
  calc
    _ ≤ ∑ d ∈ bettiDegrees B, singletonComponentCount B d := by
      apply Finset.sum_le_sum
      intro d hd
      exact local_support_partition_bound B d ((mem_bettiDegrees B d).mp hd)
    _ ≤ 4 := singleton_sum_le_four B _ (by
      intro d hd
      have hb := (mem_bettiDegrees B d).mp hd
      exact ⟨betti_positive B d hb, hb⟩)

end NS25Lean.L2C
