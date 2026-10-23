import NS25Lean.AppendixBPositiveLoad

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C
variable {Gamma : NumericalSemigroup}

theorem componentCount_le_support_card (B : Data Gamma) (d : ℕ) (hd : Betti B d) :
    componentCount B d ≤ (fiberVariables B d).card := by
  classical
  let := Fintype.ofFinite (FiberComponent B d)
  rw [← sum_componentSupport_card]
  calc
    componentCount B d = ∑ _C : FiberComponent B d, 1 := by
      simp [componentCount, Nat.card_eq_fintype_card]
    _ ≤ _ := Finset.sum_le_sum (fun C _ => Finset.card_pos.mpr
      (componentSupport_nonempty B d (betti_positive B d hd) C))

theorem singletonCount_eq_sum (B : Data Gamma) (d : ℕ) :
    let := Fintype.ofFinite (FiberComponent B d)
    singletonComponentCount B d = ∑ C : FiberComponent B d,
      if (componentSupport B d C).card = 1 then 1 else 0 := by
  classical
  let := Fintype.ofFinite (FiberComponent B d)
  simp only [singletonComponentCount, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_filter]

theorem double_componentCount_le (B : Data Gamma) (d : ℕ) (hd : Betti B d) :
    2 * componentCount B d ≤ (fiberVariables B d).card + singletonComponentCount B d := by
  classical
  let := Fintype.ofFinite (FiberComponent B d)
  rw [singletonCount_eq_sum, ← sum_componentSupport_card, ← Finset.sum_add_distrib]
  calc
    2 * componentCount B d = ∑ _C : FiberComponent B d, 2 := by
      simp [componentCount, Nat.card_eq_fintype_card, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (by
      intro C _
      have := Finset.card_pos.mpr (componentSupport_nonempty B d (betti_positive B d hd) C)
      split_ifs <;> omega)

theorem singletonCount_eq_of_count_eq_support (B : Data Gamma) (d : ℕ) (hd : Betti B d)
    (he : componentCount B d = (fiberVariables B d).card) :
    singletonComponentCount B d = componentCount B d := by
  classical
  let := Fintype.ofFinite (FiberComponent B d)
  have hsum : (∑ _C : FiberComponent B d, 1) =
      ∑ C : FiberComponent B d, (componentSupport B d C).card := by
    rw [sum_componentSupport_card, ← he]
    simp [componentCount, Nat.card_eq_fintype_card]
  have hsing (C : FiberComponent B d) : (componentSupport B d C).card = 1 :=
    ((Finset.sum_eq_sum_iff_of_le (fun C _ => Finset.card_pos.mpr
      (componentSupport_nonempty B d (betti_positive B d hd) C))).mp hsum C
      (Finset.mem_univ C)).symm
  rw [singletonCount_eq_sum]
  simp [hsing, componentCount, Nat.card_eq_fintype_card]

theorem equality_componentCount_two (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d) :
    componentCount B d = 2 := by
  have hc := componentCount_le_support_card B d hd
  have hdbl := double_componentCount_le B d hd
  have he := local_budget_equality B hpos d hd
  have hs : (fiberVariables B d).card ≤ 4 := (Finset.card_le_univ _).trans_eq (by simp)
  have hb : 2 ≤ componentCount B d := hd
  have hall := singletonCount_eq_of_count_eq_support B d hd
  generalize (fiberVariables B d).card = s at *
  interval_cases s <;> simp only [Nat.reduceSub, zero_mul, one_mul] at he <;> omega

theorem equality_singletonCount (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d) :
    singletonComponentCount B d = 4 - (fiberVariables B d).card := by
  have := local_budget_equality B hpos d hd
  simpa [equality_componentCount_two B hpos d hd] using this.symm

theorem equality_two_components (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d) :
    ∃ C E : FiberComponent B d, C ≠ E ∧
      (∀ F : FiberComponent B d, F = C ∨ F = E) ∧
      (componentSupport B d C).Nonempty ∧ (componentSupport B d E).Nonempty ∧
      Disjoint (componentSupport B d C) (componentSupport B d E) ∧
      componentSupport B d C ∪ componentSupport B d E = fiberVariables B d := by
  classical
  let := Fintype.ofFinite (FiberComponent B d)
  have hc : (Finset.univ : Finset (FiberComponent B d)).card = 2 := by
    simpa [componentCount, Nat.card_eq_fintype_card] using equality_componentCount_two B hpos d hd
  obtain ⟨C, E, hne, hCE⟩ := Finset.card_eq_two.mp hc
  refine ⟨C, E, hne, ?_, componentSupport_nonempty B d (betti_positive B d hd) C,
    componentSupport_nonempty B d (betti_positive B d hd) E,
    componentSupports_disjoint B d C E hne, ?_⟩
  · intro F
    have := Finset.mem_univ F
    simpa [hCE] using this
  · have := componentSupport_union B d
    simpa [hCE] using this

theorem singletonCount_pos_of_component (B : Data Gamma) (d : ℕ)
    (C : FiberComponent B d) (hC : (componentSupport B d C).card = 1) :
    0 < singletonComponentCount B d := by
  classical
  let := Fintype.ofFinite (FiberComponent B d)
  rw [singletonCount_eq_sum]
  have h := Finset.single_le_sum (f := fun E : FiberComponent B d =>
    if (componentSupport B d E).card = 1 then 1 else 0)
    (fun E _ => Nat.zero_le _) (Finset.mem_univ C)
  simpa [hC] using h

theorem componentSupport_card_le_two (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d)
    (C : FiberComponent B d) : (componentSupport B d C).card ≤ 2 := by
  classical
  obtain ⟨E, F, hne, hall, hE, hF, hdis, hun⟩ := equality_two_components B hpos d hd
  have hsum : (componentSupport B d E).card + (componentSupport B d F).card =
      (fiberVariables B d).card := by rw [← hun, Finset.card_union_of_disjoint hdis]
  have hpE := Finset.card_pos.mpr hE
  have hpF := Finset.card_pos.mpr hF
  have hs : (fiberVariables B d).card ≤ 4 := (Finset.card_le_univ _).trans_eq (by simp)
  have hzero := equality_singletonCount B hpos d hd
  have he := singletonCount_pos_of_component B d E
  have hf := singletonCount_pos_of_component B d F
  rcases hall C with rfl | rfl <;> omega



/-- The actual two components have exactly the source partitions 1+1, 1+2, or 2+2. -/
theorem equality_support_classification (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d) :
    ∃ C E : FiberComponent B d, C ≠ E ∧
      (∀ F : FiberComponent B d, F = C ∨ F = E) ∧
      (componentSupport B d C).Nonempty ∧ (componentSupport B d E).Nonempty ∧
      Disjoint (componentSupport B d C) (componentSupport B d E) ∧
      componentSupport B d C ∪ componentSupport B d E = fiberVariables B d ∧
      (((fiberVariables B d).card = 2 ∧ singletonComponentCount B d = 2 ∧
        (componentSupport B d C).card = 1 ∧ (componentSupport B d E).card = 1) ∨
       ((fiberVariables B d).card = 3 ∧ singletonComponentCount B d = 1 ∧
        ((componentSupport B d C).card = 1 ∧ (componentSupport B d E).card = 2 ∨
         (componentSupport B d C).card = 2 ∧ (componentSupport B d E).card = 1)) ∨
       ((fiberVariables B d).card = 4 ∧ singletonComponentCount B d = 0 ∧
        (componentSupport B d C).card = 2 ∧ (componentSupport B d E).card = 2)) := by
  classical
  obtain ⟨C, E, hne, hall, hC, hE, hdis, hun⟩ := equality_two_components B hpos d hd
  refine ⟨C, E, hne, hall, hC, hE, hdis, hun, ?_⟩
  have hsum : (componentSupport B d C).card + (componentSupport B d E).card =
      (fiberVariables B d).card := by rw [← hun, Finset.card_union_of_disjoint hdis]
  have hpC := Finset.card_pos.mpr hC
  have hpE := Finset.card_pos.mpr hE
  have hbC := componentSupport_card_le_two B hpos d hd C
  have hbE := componentSupport_card_le_two B hpos d hd E
  have hs := equality_singletonCount B hpos d hd
  omega

theorem support_three_not_three_components (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d) :
    componentCount B d ≠ 3 := by rw [equality_componentCount_two B hpos d hd]; omega

theorem support_four_no_singleton (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d)
    (hs : (fiberVariables B d).card = 4) (C : FiberComponent B d) :
    (componentSupport B d C).card ≠ 1 := by
  have he := equality_singletonCount B hpos d hd
  intro hC
  have := singletonCount_pos_of_component B d C hC
  omega

open Classical in
def purePairDegrees (B : Data Gamma) : Finset ℕ :=
  (bettiDegrees B).filter (fun d => (fiberVariables B d).card = 2)

@[simp] theorem mem_purePairDegrees (B : Data Gamma) (d : ℕ) :
    d ∈ purePairDegrees B ↔ Betti B d ∧ (fiberVariables B d).card = 2 := by
  classical
  simp [purePairDegrees, mem_bettiDegrees]

theorem purePair_component_singleton (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : d ∈ purePairDegrees B)
    (C : FiberComponent B d) : (componentSupport B d C).card = 1 := by
  obtain ⟨hb, hs⟩ := (mem_purePairDegrees B d).mp hd
  obtain ⟨E, F, hne, hall, hE, hF, hdis, hun⟩ := equality_two_components B hpos d hb
  have hsum : (componentSupport B d E).card + (componentSupport B d F).card = 2 := by
    rw [← Finset.card_union_of_disjoint hdis, hun, hs]
  have hpE := Finset.card_pos.mpr hE
  have hpF := Finset.card_pos.mpr hF
  rcases hall C with rfl | rfl <;> omega

theorem purePair_variable_singleton (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : d ∈ purePairDegrees B)
    (j : Fin 4) (hj : j ∈ fiberVariables B d) :
    ∃ C : FiberComponent B d, componentSupport B d C = {j} := by
  obtain ⟨u, hu⟩ := (mem_variables B d j).mp hj
  let C := (fiberGraph B d).connectedComponentMk u
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp (purePair_component_singleton B hpos d hd C)
  have hjC := (mem_componentSupport B d C j).mpr ⟨u, rfl, hu⟩
  have hjk : j = k := by simpa [hk] using hjC
  exact ⟨C, hjk ▸ hk⟩

theorem purePair_variable_degree_unique (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d e : ℕ)
    (hd : d ∈ purePairDegrees B) (he : e ∈ purePairDegrees B) (j : Fin 4)
    (hjd : j ∈ fiberVariables B d) (hje : j ∈ fiberVariables B e) : d = e := by
  obtain ⟨C, hC⟩ := purePair_variable_singleton B hpos d hd j hjd
  obtain ⟨E, hE⟩ := purePair_variable_singleton B hpos e he j hje
  have hdB := ((mem_purePairDegrees B d).mp hd).1
  have heB := ((mem_purePairDegrees B e).mp he).1
  exact singleton_active_degree_unique B d e (betti_positive B d hdB)
    (betti_positive B e heB) hdB heB C E j hC hE

theorem purePair_supports_disjoint (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d e : ℕ)
    (hd : d ∈ purePairDegrees B) (he : e ∈ purePairDegrees B) (hne : d ≠ e) :
    Disjoint (fiberVariables B d) (fiberVariables B e) := by
  apply Finset.disjoint_left.mpr
  intro j hjd hje
  exact hne (purePair_variable_degree_unique B hpos d e hd he j hjd hje)

theorem purePairDegrees_card_le_two (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) : (purePairDegrees B).card ≤ 2 := by
  classical
  have hp : (↑(purePairDegrees B) : Set ℕ).PairwiseDisjoint (fiberVariables B) := by
    intro d hd e he hne
    exact purePair_supports_disjoint B hpos d e hd he hne
  have hsum : ∑ d ∈ purePairDegrees B, (fiberVariables B d).card =
      (purePairDegrees B).card * 2 := by
    calc
      _ = ∑ _d ∈ purePairDegrees B, 2 := Finset.sum_congr rfl
        (fun d hd => ((mem_purePairDegrees B d).mp hd).2)
      _ = _ := by simp [Nat.mul_comm]
  have hb : ((purePairDegrees B).biUnion (fiberVariables B)).card ≤ 4 :=
    (Finset.card_le_univ _).trans_eq (by simp)
  rw [Finset.card_biUnion hp, hsum] at hb
  omega



/-- A singleton-support component contains a unique actual factorization. -/
theorem singleton_component_unique_rep (B : Data Gamma) (d : ℕ)
    (C : FiberComponent B d) (j : Fin 4) (hC : componentSupport B d C = {j})
    (u v : FactorizationFiber B d)
    (hu : (fiberGraph B d).connectedComponentMk u = C)
    (hv : (fiberGraph B d).connectedComponentMk v = C) : u = v := by
  have hu' := fiber_eq_single_of_componentSupport B d C j hC u hu
  have hv' := fiber_eq_single_of_componentSupport B d C j hC v hv
  have heu : u.val j * weights B j = d := by
    rw [← weight_single, ← hu']; exact u.property
  have hev : v.val j * weights B j = d := by
    rw [← weight_single, ← hv']; exact v.property
  have he : u.val j = v.val j := Nat.eq_of_mul_eq_mul_right (weights_positive B j)
    (heu.trans hev.symm)
  apply Subtype.ext
  rw [hu', hv', he]

/-- Complete pure-pair payload: the actual variables, positive exponents,
actual weighted degree equalities, and both directions of the full-fiber description. -/
theorem purePair_fiber_exactly_two_pure_powers (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : d ∈ purePairDegrees B) :
    ∃ (i j : Fin 4) (a b : ℕ), i ≠ j ∧ 0 < a ∧ 0 < b ∧
      d = a * weights B i ∧ d = b * weights B j ∧
      fiberVariables B d = {i, j} ∧
      (∀ u : Fin 4 →₀ ℕ, weight B u = d ↔
        u = Finsupp.single i a ∨ u = Finsupp.single j b) := by
  classical
  have hb := ((mem_purePairDegrees B d).mp hd).1
  obtain ⟨C, E, hne, hall, hCpos, hEpos, hdis, hun⟩ := equality_two_components B hpos d hb
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (purePair_component_singleton B hpos d hd C)
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp (purePair_component_singleton B hpos d hd E)
  have hij : i ≠ j := by
    intro he
    apply hne
    apply components_eq_of_shared_support B d C E i
    · simp [hi]
    · simp [hj, he]
  obtain ⟨u, hu⟩ := C.exists_rep
  obtain ⟨v, hv⟩ := E.exists_rep
  have hu' := fiber_eq_single_of_componentSupport B d C i hi u hu
  have hv' := fiber_eq_single_of_componentSupport B d E j hj v hv
  have hdu : d = u.val i * weights B i :=
    u.property.symm.trans ((congrArg (weight B) hu').trans (weight_single B i _))
  have hdv : d = v.val j * weights B j :=
    v.property.symm.trans ((congrArg (weight B) hv').trans (weight_single B j _))
  have hdpos := betti_positive B d hb
  have hau : 0 < u.val i := by nlinarith
  have hav : 0 < v.val j := by nlinarith
  refine ⟨i, j, u.val i, v.val j, hij, hau, hav, hdu, hdv, ?_, ?_⟩
  · simpa [hi, hj] using hun.symm
  · intro w
    constructor
    · intro hw
      let z : FactorizationFiber B d := ⟨w, hw⟩
      rcases hall ((fiberGraph B d).connectedComponentMk z) with hz | hz
      · left
        have he := singleton_component_unique_rep B d C i hi z u hz hu
        exact (congrArg Subtype.val he).trans hu'
      · right
        have he := singleton_component_unique_rep B d E j hj z v hz hv
        exact (congrArg Subtype.val he).trans hv'
    · rintro (rfl | rfl)
      · exact (weight_single B i _).trans hdu.symm
      · exact (weight_single B j _).trans hdv.symm

end NS25Lean.L4A
