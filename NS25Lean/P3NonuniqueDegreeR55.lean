import NS25Lean.P3R0AperyStructureR54

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R55
open ChosenBase L2B L5A1
variable {Gamma : NumericalSemigroup}

/-- The minimal-nonunique-degree graph argument does not require Apéry membership. -/
theorem graph_bot_of_all_lower_unique (B : Data Gamma) (h : ℕ)
    (hl : ∀ d, d < h → Subsingleton (FactorizationFiber B d)) : fiberGraph B h = ⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  rintro ⟨hne, j, hu, hv⟩
  have heu := L3B.removed_weight B h u j hu
  have hev := L3B.removed_weight B h v j hv
  have hp := weights_positive B j
  let u' : FactorizationFiber B (h - weights B j) :=
    ⟨u.val - Finsupp.single j 1, by omega⟩
  let v' : FactorizationFiber B (h - weights B j) :=
    ⟨v.val - Finsupp.single j 1, by omega⟩
  have he := congrArg Subtype.val ((hl _ (by omega)).elim u' v')
  apply hne
  apply Subtype.ext
  have he' := congrArg (fun w => Finsupp.single j 1 + w) he
  simpa only [u', v', remove_variable_add u.val j hu, remove_variable_add v.val j hv] using he'

theorem fiber_unique_below_component_bound (B : Data Gamma) (N : ℕ)
    (hc : ∀ d, d < N → componentCount B d ≤ 1)
    (d : ℕ) (hd : d < N) : Subsingleton (FactorizationFiber B d) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    exact L3B.fiber_unique_of_graph_bot_count B d
      (graph_bot_of_all_lower_unique B d (fun e he => ih e he (by omega))) (hc d hd)

/-- A genuine nonunique tail degree lies above an actual active degree.
This supplies M02 §3's minimum-degree obstruction without a presentation assumption. -/
theorem nonunique_has_active_below (M : MultiplicityBase Gamma) (h : ℕ)
    (u v : FactorizationFiber M.base h) (hne : u ≠ v) :
    ∃ d ∈ activeDegreeFinset M, d ≤ h := by
  classical
  by_contra hn
  push_neg at hn
  have hc (d : ℕ) (hd : d < h + 1) : componentCount M.base d ≤ 1 := by
    by_cases hz : d = 0
    · subst d; exact componentCount_zero_le_one M.base
    · by_contra hh
      have ha := (mem_activeDegreeFinset M d).mpr ⟨by omega, by omega⟩
      have := hn d ha
      omega
  exact hne ((fiber_unique_below_component_bound M.base (h + 1) hc h (by omega)).elim u v)

end NS25Lean.P3R55
