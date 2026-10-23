import NS25Lean.AppendixBRigidity

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C
variable {Gamma : NumericalSemigroup}

/-- A component containing a variable outside every pure pair has only one
actual factorization: two-variable nontriviality would invoke rigidity. -/
theorem outside_purePairs_component_unique (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (i : Fin 4)
    (hout : ∀ e ∈ purePairDegrees B, i ∉ fiberVariables B e)
    (d : ℕ) (hd : Betti B d) (C : FiberComponent B d)
    (hiC : i ∈ componentSupport B d C) (u v : FactorizationFiber B d)
    (hu : (fiberGraph B d).connectedComponentMk u = C)
    (hv : (fiberGraph B d).connectedComponentMk v = C) : u = v := by
  classical
  have hcard := componentSupport_card_le_two B hpos d hd C
  have hnonempty : 0 < (componentSupport B d C).card :=
    Finset.card_pos.mpr ⟨i, hiC⟩
  by_cases hone : (componentSupport B d C).card = 1
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hone
    exact singleton_component_unique_rep B d C j hj u v hu hv
  · have htwo : (componentSupport B d C).card = 2 := by omega
    obtain ⟨j, k, hjk, hC⟩ := Finset.card_eq_two.mp htwo
    by_contra hne
    obtain ⟨hpure, hvars, _⟩ := two_variable_component_rigidity B d C j k hjk hC u v hu hv hne
    apply hout _ hpure
    rw [hvars, ← hC]
    exact hiC

/-- Every occurrence of a variable outside all pure pairs is source-essential. -/
theorem outside_purePairs_essential (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (i : Fin 4)
    (hout : ∀ e ∈ purePairDegrees B, i ∉ fiberVariables B e)
    (d : ℕ) (hd : Betti B d) (hi : i ∈ fiberVariables B d) :
    i ∈ essentialVariables B d := by
  obtain ⟨u, hui⟩ := (mem_variables B d i).mp hi
  let C := (fiberGraph B d).connectedComponentMk u
  have hiC : i ∈ componentSupport B d C :=
    (mem_componentSupport B d C i).mpr ⟨u, rfl, hui⟩
  apply (mem_essentialVariables B d i).mpr
  refine ⟨C, (mem_componentEssential B d C i).mpr ?_⟩
  intro v hv
  have he := outside_purePairs_component_unique B hpos i hout d hd C hiC u v rfl hv
  simpa [← he] using hui

/-- The actual frozen source-essential formula equals internal load
when the chosen variable is essential at every Betti degree where it occurs. -/
theorem chosenDefect_eq_internalLoad_of_essential (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (i : Fin 4)
    (hess : ∀ d, Betti B d → i ∈ fiberVariables B d → i ∈ essentialVariables B d) :
    L2B.chosenDefect (atPivot B i) = internalLoad B i := by
  classical
  rw [every_pivot_defect_formula, internalLoad_eq_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hb := (mem_bettiDegrees B d).mp hd
  rw [equality_componentCount_two B hpos d hb]
  by_cases hi : i ∈ fiberVariables B d
  · have he := hess d hb hi
    simp [hi, he]
  · have he : i ∉ essentialVariables B d := fun he =>
      hi (essential_subset_variables B d he)
    simp [hi, he]

/-- Essentiality plus the positive-load equality gives actual chosen-base defect one. -/
theorem chosenDefect_eq_one_of_essential (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (i : Fin 4)
    (hess : ∀ d, Betti B d → i ∈ fiberVariables B d → i ∈ essentialVariables B d) :
    L2B.chosenDefect (atPivot B i) = 1 := by
  rw [chosenDefect_eq_internalLoad_of_essential B hpos i hess, positive_load_eq_one B hpos i]

/-- Every variable outside all pure pairs is an actual protected pivot. -/
theorem outside_purePairs_chosenDefect_one (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (i : Fin 4)
    (hout : ∀ e ∈ purePairDegrees B, i ∉ fiberVariables B e) :
    L2B.chosenDefect (atPivot B i) = 1 :=
  chosenDefect_eq_one_of_essential B hpos i (outside_purePairs_essential B hpos i hout)

/-- The union of actual pair supports has precisely two variables per degree. -/
theorem purePair_support_union_card (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) :
    ((purePairDegrees B).biUnion (fiberVariables B)).card = 2 * (purePairDegrees B).card := by
  classical
  have hp : (↑(purePairDegrees B) : Set ℕ).PairwiseDisjoint (fiberVariables B) := by
    intro d hd e he hne
    exact purePair_supports_disjoint B hpos d e hd he hne
  rw [Finset.card_biUnion hp]
  calc
    _ = ∑ _d ∈ purePairDegrees B, 2 := Finset.sum_congr rfl
      (fun d hd => ((mem_purePairDegrees B d).mp hd).2)
    _ = _ := by simp [Nat.mul_comm]

/-- Zero or one pure pair leaves an actual variable outside every pair support. -/
theorem exists_outside_purePairs_of_card_le_one (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (hcard : (purePairDegrees B).card ≤ 1) :
    ∃ i : Fin 4, ∀ e ∈ purePairDegrees B, i ∉ fiberVariables B e := by
  classical
  have hu := purePair_support_union_card B hpos
  have hlt : ((purePairDegrees B).biUnion (fiberVariables B)).card <
      (Finset.univ : Finset (Fin 4)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨i, ?_⟩
  intro e he hie
  exact hi (Finset.mem_biUnion.mpr ⟨e, he, hie⟩)

/-- Appendix B, Proposition one-pure-pair: an actual pivot with defect one. -/
theorem zero_or_one_purePair_protected (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (hcard : (purePairDegrees B).card ≤ 1) :
    ∃ i : Fin 4, L2B.chosenDefect (atPivot B i) = 1 := by
  obtain ⟨i, hi⟩ := exists_outside_purePairs_of_card_le_one B hpos hcard
  exact ⟨i, outside_purePairs_chosenDefect_one B hpos i hi⟩

end NS25Lean.L4A

