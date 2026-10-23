import NS25Lean.PureSingletonBudget

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase Classical
variable {Gamma : NumericalSemigroup}

def OutsideExponent (B : Data Gamma) (j : Fin 3) (r : ℕ) : Prop :=
  0 < r ∧ ∃ v : Fin 3 →₀ ℕ, v j = 0 ∧ weight B v = r * weights B j

theorem exists_outsideExponent (B : Data Gamma) (j : Fin 3) : ∃ r, OutsideExponent B j r := by
  classical
  obtain ⟨i, hi⟩ := exists_ne j
  refine ⟨weights B i, weights_positive B i, Finsupp.single i (weights B j), ?_, ?_⟩
  · simp [Ne.symm hi]
  · rw [weight_single, Nat.mul_comm]

def criticalExponent (B : Data Gamma) (j : Fin 3) : ℕ := Nat.find (exists_outsideExponent B j)

theorem criticalExponent_spec (B : Data Gamma) (j : Fin 3) :
    OutsideExponent B j (criticalExponent B j) := Nat.find_spec (exists_outsideExponent B j)

theorem criticalExponent_min (B : Data Gamma) (j : Fin 3) (r : ℕ) (hr : OutsideExponent B j r) :
    criticalExponent B j ≤ r := Nat.find_min' (exists_outsideExponent B j) hr

theorem pure_exponent_le_outside (B : Data Gamma) (g : ℕ) (E : FiberComponent B g)
    (j : Fin 3) (hE : componentSupport B g E = {j})
    (w : FactorizationFiber B g) (hw : (fiberGraph B g).connectedComponentMk w = E)
    (r : ℕ) (hr : OutsideExponent B j r) : w.val j ≤ r := by
  classical
  obtain ⟨hrpos, v, hvj, hvdeg⟩ := hr
  by_contra hn
  have hlt : r < w.val j := by omega
  have hw' := fiber_eq_single_of_componentSupport B g E j hE w hw
  have gdeg : g = w.val j * weights B j :=
    w.property.symm.trans ((congrArg (weight B) hw').trans (weight_single B j _))
  have hex : ∃ i : Fin 3, 0 < v i := by
    by_contra hh
    push Not at hh
    have hz : v = 0 := by ext i; change v i = 0; exact Nat.eq_zero_of_le_zero (hh i)
    have hp := weights_positive B j
    rw [hz, map_zero] at hvdeg
    nlinarith
  obtain ⟨i, hi⟩ := hex
  have hij : i ≠ j := by intro he; subst i; omega
  let z : FactorizationFiber B g := ⟨v + Finsupp.single j (w.val j - r), by
    rw [map_add, weight_single, hvdeg]
    have hs := Nat.sub_add_cancel (le_of_lt hlt)
    nlinarith⟩
  have hzj : 0 < z.val j := by simp only [z, Finsupp.add_apply, Finsupp.single_eq_same]; omega
  have hwj : 0 < w.val j := by omega
  have hzE : (fiberGraph B g).connectedComponentMk z = E := by
    by_cases he : z = w
    · exact he ▸ hw
    · have ha : (fiberGraph B g).Adj z w := ⟨he, j, hzj, hwj⟩
      exact (SimpleGraph.ConnectedComponent.sound ha.reachable).trans hw
  have hzi : 0 < z.val i := by
    simp only [z, Finsupp.add_apply, Finsupp.single_eq_of_ne hij, add_zero]
    exact hi
  have hiE := (mem_componentSupport B g E i).mpr ⟨z, hzE, hzi⟩
  rw [hE, Finset.mem_singleton] at hiE
  exact hij hiE

/-- A pure singleton at an active degree occurs exactly at its critical exponent degree. -/
theorem singleton_active_degree_eq_critical (B : Data Gamma) (h : ℕ)
    (hh : 0 < h) (hc : 1 < componentCount B h) (C : FiberComponent B h)
    (j : Fin 3) (hC : componentSupport B h C = {j}) :
    h = criticalExponent B j * weights B j := by
  classical
  obtain ⟨u, hu⟩ := C.exists_rep
  have hu' := fiber_eq_single_of_componentSupport B h C j hC u hu
  have hdeg : h = u.val j * weights B j :=
    u.property.symm.trans ((congrArg (weight B) hu').trans (weight_single B j _))
  have hpos : 0 < u.val j := by nlinarith
  haveI : Nontrivial (FiberComponent B h) := by
    by_contra hn
    haveI : Subsingleton (FiberComponent B h) := not_nontrivial_iff_subsingleton.mp hn
    have hz : Nat.card (FiberComponent B h) ≤ 1 := by
      simpa using Nat.card_le_card_of_injective (fun _ : FiberComponent B h => ())
        (fun x y _ => Subsingleton.elim x y)
    change 1 < Nat.card (FiberComponent B h) at hc
    omega
  obtain ⟨F, hF⟩ := exists_ne C
  obtain ⟨v, hv⟩ := F.exists_rep
  have hvj : v.val j = 0 := by
    by_contra hn
    have hjF := (mem_componentSupport B h F j).mpr ⟨v, hv, Nat.pos_of_ne_zero hn⟩
    have hjC : j ∈ componentSupport B h C := by simp [hC]
    exact hF (components_eq_of_shared_support B h F C j hjF hjC)
  have hmin := criticalExponent_min B j (u.val j) ⟨hpos, v.val, hvj, v.property.trans hdeg⟩
  have hmax := pure_exponent_le_outside B h C j hC u hu _ (criticalExponent_spec B j)
  have he : u.val j = criticalExponent B j := by omega
  exact hdeg.trans (congrArg (fun r => r * weights B j) he)

end NS25Lean.L2B
