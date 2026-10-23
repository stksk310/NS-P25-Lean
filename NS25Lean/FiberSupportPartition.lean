import NS25Lean.ActiveFiberObjects

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase
variable {Gamma : NumericalSemigroup}

open Classical in
def componentSupport (B : Data Gamma) (h : ℕ) (C : FiberComponent B h) : Finset (Fin 3) :=
  Finset.univ.filter (fun j => ∃ u : FactorizationFiber B h,
    (fiberGraph B h).connectedComponentMk u = C ∧ 0 < u.val j)

theorem mem_componentSupport (B : Data Gamma) (h : ℕ) (C : FiberComponent B h) (j : Fin 3) :
    j ∈ componentSupport B h C ↔ ∃ u : FactorizationFiber B h,
      (fiberGraph B h).connectedComponentMk u = C ∧ 0 < u.val j := by
  classical
  simp [componentSupport]

theorem components_eq_of_shared_support (B : Data Gamma) (h : ℕ)
    (C E : FiberComponent B h) (j : Fin 3)
    (hjC : j ∈ componentSupport B h C) (hjE : j ∈ componentSupport B h E) : C = E := by
  obtain ⟨u, hu, hju⟩ := (mem_componentSupport B h C j).mp hjC
  obtain ⟨v, hv, hjv⟩ := (mem_componentSupport B h E j).mp hjE
  by_cases he : u = v
  · exact hu.symm.trans (he ▸ hv)
  · have ha : (fiberGraph B h).Adj u v := ⟨he, j, hju, hjv⟩
    exact hu.symm.trans ((SimpleGraph.ConnectedComponent.sound ha.reachable).trans hv)

theorem componentSupports_disjoint (B : Data Gamma) (h : ℕ)
    (C E : FiberComponent B h) (hne : C ≠ E) :
    Disjoint (componentSupport B h C) (componentSupport B h E) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hjC hjE
  exact hne (components_eq_of_shared_support B h C E j hjC hjE)

theorem componentSupport_nonempty (B : Data Gamma) (h : ℕ) (hh : 0 < h)
    (C : FiberComponent B h) : (componentSupport B h C).Nonempty := by
  classical
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h u =>
    have hex : ∃ j : Fin 3, 0 < u.val j := by
      by_contra hn
      push Not at hn
      have hu : u.val = 0 := by
        ext j
        change u.val j = 0
        have := hn j
        omega
      have hw := u.property
      rw [hu, map_zero] at hw
      omega
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, (mem_componentSupport B h _ j).mpr ⟨u, rfl, hj⟩⟩

theorem sum_componentSupport_card_le_three (B : Data Gamma) (h : ℕ) :
    letI := Fintype.ofFinite (FiberComponent B h)
    ∑ C : FiberComponent B h, (componentSupport B h C).card ≤ 3 := by
  classical
  letI := Fintype.ofFinite (FiberComponent B h)
  have hp : (↑(Finset.univ : Finset (FiberComponent B h)) : Set _).PairwiseDisjoint
      (componentSupport B h) := by
    intro C _ E _ hne
    exact componentSupports_disjoint B h C E hne
  rw [← Finset.card_biUnion hp]
  exact (Finset.card_le_univ _).trans_eq (by simp)

def singletonComponentCount (M : MultiplicityBase Gamma) (h : ℕ) : ℕ :=
  Nat.card {C : FiberComponent M.base h // (componentSupport M.base h C).card = 1}

/-- The paper's support-partition inequality at each positive degree. -/
theorem componentCount_sub_one_le_singletons (M : MultiplicityBase Gamma)
    (h : ℕ) (hh : 0 < h) :
    componentCount M.base h - 1 ≤ singletonComponentCount M h := by
  classical
  letI := Fintype.ofFinite (FiberComponent M.base h)
  let s := (Finset.univ : Finset (FiberComponent M.base h)).filter
    (fun C => (componentSupport M.base h C).card = 1)
  let t := (Finset.univ : Finset (FiberComponent M.base h)) \ s
  have hpos (C : FiberComponent M.base h) : 0 < (componentSupport M.base h C).card :=
    Finset.card_pos.mpr (componentSupport_nonempty M.base h hh C)
  have htcard : t.card ≤ 1 := by
    by_contra hn
    obtain ⟨C, hC, E, hE, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < t.card)
    have htwo (C : FiberComponent M.base h) (hC : C ∈ t) :
        2 ≤ (componentSupport M.base h C).card := by
      have hn : (componentSupport M.base h C).card ≠ 1 := by
        simpa [t, s] using (Finset.mem_sdiff.mp hC).2
      have := hpos C
      omega
    have hsum := sum_componentSupport_card_le_three M.base h
    have hle : (componentSupport M.base h C).card + (componentSupport M.base h E).card ≤
        ∑ F : FiberComponent M.base h, (componentSupport M.base h F).card := by
      have hs : ({C, E} : Finset (FiberComponent M.base h)) ⊆ Finset.univ := Finset.subset_univ _
      have hb := Finset.sum_le_sum_of_subset_of_nonneg hs
        (fun F _ _ => Nat.zero_le (componentSupport M.base h F).card)
      simpa [hne] using hb
    have hC2 := htwo C hC
    have hE2 := htwo E hE
    omega
  have hc : componentCount M.base h = s.card + t.card := by
    have he := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
    simpa [componentCount, Nat.card_eq_fintype_card, t, Nat.add_comm] using he.symm
  have hs : singletonComponentCount M h = s.card := by
    simp [singletonComponentCount, Nat.card_eq_fintype_card, s, Fintype.card_subtype]
  omega

end NS25Lean.L2B
