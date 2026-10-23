import NS25Lean.OneDefectSplit

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3B
open ChosenBase L2B L2B2A L2B2A2 MvPolynomial
variable {Gamma : NumericalSemigroup}

/-- Betti degrees in the paper's tail factorization graph, restricted to Apéry. -/
def AperyBetti (B : Data Gamma) (d : ℕ) : Prop :=
  d ∈ B.apery ∧ 1 < componentCount B d

theorem unique_apery_betti (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h) :
    ∀ d, AperyBetti M.base d ↔ d = h := by
  intro d
  constructor
  · rintro ⟨ha, hc⟩
    by_contra hn
    have := apery_component_le_one M d (hz d hn) ha
    omega
  · rintro rfl
    exact ⟨ht.1, by rw [ht.2.2]; omega⟩

/-- Removing a shared variable would create a smaller Apéry Betti degree. -/
theorem internal_tie_graph_bot (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h) :
    fiberGraph M.base h = ⊥ := by
  apply graph_bot_of_lower_unique M.base h ht.1
  intro d hd ha
  exact apery_fiber_unique_below M.base h
    (fun e he hae => apery_component_le_one M e (hz e (by omega)) hae) d hd ha

theorem internal_tie_components_singleton (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h)
    (u v : FactorizationFiber M.base h)
    (he : (fiberGraph M.base h).connectedComponentMk u =
      (fiberGraph M.base h).connectedComponentMk v) : u = v := by
  have hr := SimpleGraph.ConnectedComponent.exact he
  simpa only [internal_tie_graph_bot M h hz ht, SimpleGraph.reachable_bot] using hr

theorem internal_tie_fiber_card (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h) :
    Nat.card (FactorizationFiber M.base h) = 2 := by
  have hi : Function.Bijective (fiberGraph M.base h).connectedComponentMk :=
    ⟨fun u v he => internal_tie_components_singleton M h hz ht u v he, Quot.mk_surjective⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hi)).trans ht.2.2

theorem internal_tie_two_factorizations (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h) :
    ∃ α β : FactorizationFiber M.base h, α ≠ β ∧
      ∀ u : FactorizationFiber M.base h, u = α ∨ u = β := by
  obtain ⟨α, β, hne, he⟩ := Nat.card_eq_two_iff.mp (internal_tie_fiber_card M h hz ht)
  refine ⟨α, β, hne, fun u => ?_⟩
  have hu : u ∈ ({α, β} : Set _) := he.symm ▸ Set.mem_univ u
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hu

theorem internal_tie_disjoint_exponents (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h)
    (α β : FactorizationFiber M.base h) (hne : α ≠ β) :
    ∀ j, α.val j = 0 ∨ β.val j = 0 := by
  intro j
  by_contra hn
  push Not at hn
  have ha : (fiberGraph M.base h).Adj α β :=
    ⟨hne, j, Nat.pos_of_ne_zero hn.1, Nat.pos_of_ne_zero hn.2⟩
  simpa only [internal_tie_graph_bot M h hz ht, SimpleGraph.bot_adj] using ha

/-- Polynomial coprimality means every common divisor is a unit (not comaximality). -/
theorem monomials_relPrime_of_disjoint (k : Type*) [Field k]
    (α β : Fin 3 →₀ ℕ) (hd : ∀ j, α j = 0 ∨ β j = 0) :
    IsRelPrime (monomial α (1 : k)) (monomial β 1) := by
  intro f hf hg
  obtain ⟨u, a, hua, hau, rfl⟩ := dvd_monomial_one_iff_exists.mp hf
  have hub : u ≤ β := (monomial_dvd_monomial.mp hg).1.resolve_left one_ne_zero
  have hu : u = 0 := by
    ext j
    rcases hd j with hj | hj
    · have := hua j; simp only [hj] at this; exact Nat.eq_zero_of_le_zero this
    · have := hub j; simp only [hj] at this; exact Nat.eq_zero_of_le_zero this
  rw [hu]
  change IsUnit (C a)
  exact hau.map C

theorem internal_tie_coprime (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h)
    (α β : FactorizationFiber M.base h) (hne : α ≠ β) :
    IsRelPrime (monomial α.val (1 : k)) (monomial β.val 1) :=
  monomials_relPrime_of_disjoint k α.val β.val (internal_tie_disjoint_exponents M h hz ht α β hne)

end NS25Lean.L3B

