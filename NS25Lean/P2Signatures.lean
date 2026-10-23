import NS25Lean.P2Foundation
import NS25Lean.MultiplicityDefectClosure

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A1
open L2B
variable {Gamma : NumericalSemigroup}

/-- A signature records the actual component and boundary-killed counts. -/
def LocalSignature (M : MultiplicityBase Gamma) (h c d : ℕ) : Prop :=
  componentCount M.base h = c ∧ killedCount M h = d

theorem componentCount_le_three (B : ChosenBase.Data Gamma) (h : ℕ) (hh : 0 < h) :
    componentCount B h ≤ 3 := by
  classical
  letI := Fintype.ofFinite (FiberComponent B h)
  have hl : ∑ C : FiberComponent B h, 1 ≤
      ∑ C : FiberComponent B h, (componentSupport B h C).card := by
    apply Finset.sum_le_sum
    intro C _
    exact Finset.card_pos.mpr (componentSupport_nonempty B h hh C)
  have hu := sum_componentSupport_card_le_three B h
  simpa [componentCount, Nat.card_eq_fintype_card] using hl.trans hu

theorem positive_contribution_active (M : MultiplicityBase Gamma) (h : ℕ)
    (hp : 0 < fiberContribution M h) : 0 < h ∧ 1 < componentCount M.base h := by
  by_contra hn
  have hout : h ∉ activeDegreeFinset M := by simpa using hn
  have := contribution_zero_outside_active M h hout
  omega

theorem positive_contribution_le_two (M : MultiplicityBase Gamma) (h : ℕ)
    (hp : 0 < fiberContribution M h) : fiberContribution M h ≤ 2 := by
  have hc := componentCount_le_three M.base h (positive_contribution_active M h hp).1
  have hl := fiberContribution_le M h
  omega

theorem contribution_two_iff (M : MultiplicityBase Gamma) (h : ℕ) :
    fiberContribution M h = 2 ↔ LocalSignature M h 3 0 ∨ LocalSignature M h 3 1 := by
  constructor
  · intro he
    have hc := componentCount_le_three M.base h (positive_contribution_active M h (by omega)).1
    have hd := killedCount_le_componentCount M h
    unfold fiberContribution at he
    unfold LocalSignature
    split_ifs at he <;> omega
  · intro hs
    rcases hs with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;> simp [fiberContribution, hc, hd]

theorem contribution_one_iff (M : MultiplicityBase Gamma) (h : ℕ) :
    fiberContribution M h = 1 ↔
      LocalSignature M h 2 0 ∨ LocalSignature M h 2 1 ∨ LocalSignature M h 3 2 := by
  constructor
  · intro he
    have hc := componentCount_le_three M.base h (positive_contribution_active M h (by omega)).1
    have hd := killedCount_le_componentCount M h
    unfold fiberContribution at he
    unfold LocalSignature
    split_ifs at he <;> omega
  · intro hs
    rcases hs with ⟨hc, hd⟩ | ⟨hc, hd⟩ | ⟨hc, hd⟩ <;> simp [fiberContribution, hc, hd]

/-- Three nonempty disjoint supports in three variables must all be singletons. -/
theorem componentSupport_card_eq_one_of_three (M : MultiplicityBase Gamma) (h : ℕ)
    (hh : 0 < h) (hc : componentCount M.base h = 3) (C : FiberComponent M.base h) :
    (componentSupport M.base h C).card = 1 := by
  classical
  letI := Fintype.ofFinite (FiberComponent M.base h)
  have hp (E : FiberComponent M.base h) : 1 ≤ (componentSupport M.base h E).card :=
    Finset.card_pos.mpr (componentSupport_nonempty M.base h hh E)
  have hs := sum_componentSupport_card_le_three M.base h
  have hn : Fintype.card (FiberComponent M.base h) = 3 := by
    simpa [componentCount, Nat.card_eq_fintype_card] using hc
  have hz : ∑ E : FiberComponent M.base h, ((componentSupport M.base h E).card - 1) = 0 := by
    rw [Finset.sum_tsub_distrib _ (fun E _ => hp E)]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hn]
    omega
  have he := (Finset.sum_eq_zero_iff.mp hz) C (Finset.mem_univ C)
  have := hp C
  omega

theorem singletonComponentCount_eq_three (M : MultiplicityBase Gamma) (h : ℕ)
    (hh : 0 < h) (hc : componentCount M.base h = 3) : singletonComponentCount M h = 3 := by
  classical
  letI := Fintype.ofFinite (FiberComponent M.base h)
  have hall := componentSupport_card_eq_one_of_three M h hh hc
  simpa [singletonComponentCount, componentCount, Nat.card_eq_fintype_card,
    Fintype.card_subtype, hall] using hc

/-- A three-component active degree is the unique tail Betti degree. -/
theorem three_components_unique_active (M : MultiplicityBase Gamma) (h g : ℕ)
    (hh : 0 < h) (hc : componentCount M.base h = 3)
    (hg : g ∈ activeDegreeFinset M) : g = h := by
  classical
  by_contra hne
  have hg' := (mem_activeDegreeFinset M g).mp hg
  have hs := singleton_sum_le_three M {h, g} (by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨hh, by omega⟩
    · exact hg')
  have hh3 := singletonComponentCount_eq_three M h hh hc
  have hg1 := componentCount_sub_one_le_singletons M g hg'.1
  have hne' : h ≠ g := Ne.symm hne
  simp [hne'] at hs
  omega

end NS25Lean.L5A1
