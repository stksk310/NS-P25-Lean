import NS25Lean.P3ActiveClassificationR51
import NS25Lean.P2CriticalRoleDichotomy

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R54
open ChosenBase L2B L5A1 L5A2B4AR4 L5A2B4AR4R1
variable {Gamma : NumericalSemigroup}

/-- At defect three the global singleton-support budget is saturated at every active degree. -/
theorem p3_singletonComponentCount_eq_one (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (h : ℕ) (hh : h ∈ activeDegreeFinset M) :
    singletonComponentCount M h = 1 := by
  classical
  have hcard := (P3R51.p3_active_classification M hp).1
  have hbound := singleton_sum_le_three M (activeDegreeFinset M)
    (fun d hd => (mem_activeDegreeFinset M d).mp hd)
  have hone (d : ℕ) (hd : d ∈ activeDegreeFinset M) :
      1 ≤ singletonComponentCount M d := by
    have hl := componentCount_sub_one_le_singletons M d
      ((mem_activeDegreeFinset M d).mp hd).1
    have hc := P3R51.active_componentCount_eq_two M hp d hd
    omega
  have herase : ((activeDegreeFinset M).erase h).card = 2 := by
    rw [Finset.card_erase_of_mem hh, hcard]
  have hlower : 2 ≤ ∑ d ∈ (activeDegreeFinset M).erase h, singletonComponentCount M d := by
    calc
      2 = ∑ _d ∈ (activeDegreeFinset M).erase h, 1 := by simp [herase]
      _ ≤ _ := Finset.sum_le_sum (fun d hd => hone d (Finset.mem_of_mem_erase hd))
  have hsplit := Finset.sum_erase_add (activeDegreeFinset M) (singletonComponentCount M) hh
  have hl := hone h hh
  omega

/-- Actual defect-three critical fibers are pure/mixed. The mixed witness is
constructed in the actual component and has both complementary coordinates positive. -/
theorem p3_actual_pureMixedCriticalRole (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (h : ℕ) (hh : h ∈ activeDegreeFinset M) :
    Nonempty (PureMixedCriticalRole M.base h) := by
  have ha := (mem_activeDegreeFinset M h).mp hh
  have hc := P3R51.active_componentCount_eq_two M hp h hh
  have hs := p3_singletonComponentCount_eq_one M hp h hh
  rcases two_component_support_shape_exhaustion M.base h hc ha.1 with hall | hpair
  · let E : {C : FiberComponent M.base h //
        (componentSupport M.base h C).card = 1} ≃ FiberComponent M.base h :=
      { toFun := fun C => C.val
        invFun := fun C => ⟨C, hall C⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have he : singletonComponentCount M h = componentCount M.base h := Nat.card_congr E
    omega
  · obtain ⟨C, D, hne, hshape, _⟩ := hpair
    rcases hshape with ⟨hC, hD⟩ | ⟨hC, hD⟩
    · exact pureMixedCriticalRole_of_components M.base h ha.1 hc C D hne hC hD
    · exact pureMixedCriticalRole_of_components M.base h ha.1 hc D C hne.symm hD hC

end NS25Lean.P3R54
