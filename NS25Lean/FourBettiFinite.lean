import NS25Lean.FourFactorizationGraph

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase
variable {Gamma : NumericalSemigroup}

theorem remove_copies (B : Data Gamma) (u : Fin 4 →₀ ℕ) (j : Fin 4)
    (r : ℕ) (hr : r ≤ u j) :
    weight B (u - Finsupp.single j r) + r * weights B j = weight B u := by
  have hle : Finsupp.single j r ≤ u := by
    intro i
    by_cases he : i = j
    · subst i; simpa using hr
    · simp [Finsupp.single_eq_of_ne he]
  have he := congrArg (weight B) (tsub_add_cancel_of_le hle)
  simpa only [map_add, weight_single] using he

/-- If a coordinate is too large, a two-variable exchange crosses any purported
component separation. This gives an elementary finite bound without presentations. -/
theorem coordinate_le_other_weight (B : Data Gamma) (d : ℕ)
    (u v : FactorizationFiber B d)
    (hne : (fiberGraph B d).connectedComponentMk u ≠
      (fiberGraph B d).connectedComponentMk v)
    (i j : Fin 4) (hvj : 0 < v.val j) : u.val i ≤ weights B j := by
  by_contra hn
  have hlt : weights B j < u.val i := by omega
  have hij : i ≠ j := by
    intro he; subst j
    exact hne (same_component_of_shared B d u v i (by omega) hvj)
  let z : FactorizationFiber B d :=
    ⟨u.val - Finsupp.single i (weights B j) + Finsupp.single j (weights B i), by
      rw [map_add, weight_single]
      have he := remove_copies B u.val i (weights B j) (by omega)
      rw [u.property] at he
      nlinarith⟩
  have hzi : 0 < z.val i := by
    simp only [z, Finsupp.add_apply, Finsupp.tsub_apply,
      Finsupp.single_eq_same, Finsupp.single_eq_of_ne hij, add_zero]
    omega
  have hzj : 0 < z.val j := by
    have hp := weights_positive B j
    have hi := weights_positive B i
    simp only [z, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  exact hne ((same_component_of_shared B d u z i (by omega) hzi).trans
    (same_component_of_shared B d z v j hzj hvj))

def degreeBound (B : Data Gamma) : ℕ := (∑ j, weights B j) ^ 2

theorem betti_le_degreeBound (B : Data Gamma) (d : ℕ) (hd : Betti B d) :
    d ≤ degreeBound B := by
  classical
  letI := (betti_iff_nontrivial B d).mp hd
  obtain ⟨C, E, hCE⟩ := exists_pair_ne (FiberComponent B d)
  obtain ⟨u, hu⟩ := C.exists_rep
  obtain ⟨v, hv⟩ := E.exists_rep
  have hn : (fiberGraph B d).connectedComponentMk u ≠
      (fiberGraph B d).connectedComponentMk v := fun h => hCE (hu.symm.trans (h.trans hv))
  obtain ⟨j, hj⟩ := componentSupport_nonempty B d (betti_positive B d hd) E
  obtain ⟨w, hw, hwj⟩ := (mem_componentSupport B d E j).mp hj
  have hn' : (fiberGraph B d).connectedComponentMk u ≠
      (fiberGraph B d).connectedComponentMk w := fun h => hCE (hu.symm.trans (h.trans hw))
  have hc (i : Fin 4) : u.val i ≤ ∑ j, weights B j :=
    (coordinate_le_other_weight B d u w hn' i j hwj).trans
      (Finset.single_le_sum (fun a _ => Nat.zero_le (weights B a)) (Finset.mem_univ j))
  calc
    d = ∑ i, u.val i * weights B i := u.property.symm.trans (weight_eq_sum B u.val)
    _ ≤ ∑ i, (∑ j, weights B j) * weights B i :=
      Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (hc i))
    _ = degreeBound B := by simp [degreeBound, ← Finset.mul_sum, pow_two]

theorem betti_finite (B : Data Gamma) : Set.Finite {d | Betti B d} := by
  apply (Set.finite_le_nat (degreeBound B)).subset
  exact fun d hd => betti_le_degreeBound B d hd

open Classical in
def bettiDegrees (B : Data Gamma) : Finset ℕ := (betti_finite B).toFinset

@[simp] theorem mem_bettiDegrees (B : Data Gamma) (d : ℕ) :
    d ∈ bettiDegrees B ↔ Betti B d := by
  classical
  exact Set.Finite.mem_toFinset _

open Classical in
/-- The manuscript's internal load. It is independent of chosenDefect. -/
def internalLoad (B : Data Gamma) (i : Fin 4) : ℕ :=
  ∑ d ∈ (bettiDegrees B).filter (fun d => i ∉ fiberVariables B d),
    (componentCount B d - 1)

theorem internalLoad_eq_sum (B : Data Gamma) (i : Fin 4) :
    internalLoad B i = ∑ d ∈ bettiDegrees B,
      if i ∉ fiberVariables B d then componentCount B d - 1 else 0 := by
  classical
  exact Finset.sum_filter _ _

theorem internalLoad_nonneg (B : Data Gamma) (i : Fin 4) : 0 ≤ internalLoad B i :=
  Nat.zero_le _

theorem contribution_le_internalLoad (B : Data Gamma) (i : Fin 4) (d : ℕ)
    (hd : Betti B d) (hi : i ∉ fiberVariables B d) :
    componentCount B d - 1 ≤ internalLoad B i := by
  classical
  exact Finset.single_le_sum (fun a _ => Nat.zero_le (componentCount B a - 1))
    (Finset.mem_filter.mpr ⟨(mem_bettiDegrees B d).mpr hd, hi⟩)

theorem not_betti_of_internalLoad_zero (B : Data Gamma) (i : Fin 4)
    (hz : internalLoad B i = 0) (d : ℕ) (hi : i ∉ fiberVariables B d) : ¬ Betti B d := by
  intro hd
  have hle := contribution_le_internalLoad B i d hd hi
  unfold Betti at hd
  omega

end NS25Lean.L2C
