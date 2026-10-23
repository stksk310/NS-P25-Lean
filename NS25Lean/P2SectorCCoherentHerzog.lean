import NS25Lean.P2SectorCEtaKappaStencil

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4D

open L2B L5A1 L5A2C3G L5A2C4A L5A2C4B L5A2C4C ChosenBase Classical

variable {Gamma : NumericalSemigroup}

/-- The component containing C4A's arbitrary outside witness.  Only its
actual component is used here; its coordinates are not declared coherent. -/
private def arbitraryOutsideComponent (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i : Fin 3) : FiberComponent B (herzogC B e i * weights B (e i)) :=
  (fiberGraph B _).connectedComponentMk
    ⟨herzogWitness B e i, herzogWitness_weight B e i⟩

private theorem arbitraryOutsideComponent_ne_pure (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    arbitraryOutsideComponent B e i ≠ critical_pure_component B (e i) := by
  intro heq
  let v : FactorizationFiber B (herzogC B e i * weights B (e i)) :=
    ⟨herzogWitness B e i, herzogWitness_weight B e i⟩
  have hvzero : v.val (e i) = 0 := herzogWitness_zero B e i
  have hs : componentSupport B (herzogC B e i * weights B (e i))
      (arbitraryOutsideComponent B e i) = {e i} := by
    rw [heq]
    simpa [herzogC] using critical_component_support_eq_singleton B (e i)
  have hvpos : 0 < weight B v.val := by
    rw [v.property]
    have hc := herzogC_positive B e i
    have hw := weights_positive B (e i)
    nlinarith
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, 0 < v.val j := by
    by_contra hn
    push Not at hn
    have hz : v.val = 0 := by
      ext j
      exact Nat.eq_zero_of_le_zero (hn j)
    rw [hz, map_zero] at hvpos
    omega
  have hjs : j ∈ componentSupport B (herzogC B e i * weights B (e i))
      (arbitraryOutsideComponent B e i) :=
    (mem_componentSupport B _ _ j).mpr ⟨v, rfl, hj⟩
  rw [hs, Finset.mem_singleton] at hjs
  subst j
  omega

/-- D1 for the inactive critical degree: the component opposite the actual
pure `a` component has exactly the two other reindexed variables as support. -/
theorem exists_h1_nonpure_component_support {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (internalPure internalMixed : internalComponents G)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (hine : internalPure ≠ internalMixed) (hbne : boundaryPure ≠ boundaryMixed)
    (hiPure : componentSupport P.M.base G.internalDegree internalPure = {e 1})
    (hiMixed : componentSupport P.M.base G.internalDegree internalMixed = {e 0, e 2})
    (hbPure : componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2})
    (hbMixed : componentSupport P.M.base G.boundaryDegree boundaryMixed = {e 0, e 1}) :
    ∃ C : FiberComponent P.M.base (c1 P.M.base e * weights P.M.base (e 0)),
      C ≠ critical_pure_component P.M.base (e 0) ∧
        componentSupport P.M.base (c1 P.M.base e * weights P.M.base (e 0)) C =
          {e 1, e 2} := by
  classical
  let B := P.M.base
  let h1 := c1 B e * weights B (e 0)
  let C : FiberComponent B h1 := arbitraryOutsideComponent B e 0
  have hCne : C ≠ critical_pure_component B (e 0) :=
    arbitraryOutsideComponent_ne_pure B e 0
  have hdegne := actual_h1_distinct_degrees G e internalPure internalMixed
    boundaryPure boundaryMixed hine hbne hiPure hiMixed hbPure hbMixed
  have hdegneB : h1 ≠ G.internalDegree ∧ h1 ≠ G.boundaryDegree := by
    simpa [h1, B] using hdegne
  have hc1 : componentCount B h1 = 2 := actual_h1_componentCount G e hdegne.1
  have hh1 : 0 < h1 := by
    have hc := herzogC_positive B e 0
    have hw := weights_positive B (e 0)
    dsimp [h1, B]
    nlinarith
  have h0not : e 0 ∉ componentSupport B h1 C := by
    intro h0
    have hp : e 0 ∈ componentSupport B h1 (critical_pure_component B (e 0)) := by
      change e 0 ∈ componentSupport B
        (criticalExponent B (e 0) * weights B (e 0))
        (critical_pure_component B (e 0))
      rw [critical_component_support_eq_singleton]
      simp
    exact hCne (components_eq_of_shared_support B h1 C
      (critical_pure_component B (e 0)) (e 0) h0 hp)
  have hnonempty : (componentSupport B h1 C).Nonempty :=
    componentSupport_nonempty B h1 hh1 C
  have hcard_ne_one : (componentSupport B h1 C).card ≠ 1 := by
    intro hcard
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
    obtain ⟨i, rfl⟩ := e.surjective j
    fin_cases i
    · exact h0not (by simp [hj])
    · have heq := singleton_active_degree_unique B h1 G.internalDegree
        hh1
        (positive_contribution_active P.M G.internalDegree (by
          rw [G.internalContribution]
          omega)).1
        (by rw [hc1]; omega)
        (by
          have hc : componentCount B G.internalDegree = 2 := by
            simpa [B] using G.internalSignature.1
          omega)
        C internalPure (e 1) (by simpa [hj]) hiPure
      exact hdegneB.1 heq
    · have heq := singleton_active_degree_unique B h1 G.boundaryDegree
        hh1
        (positive_contribution_active P.M G.boundaryDegree (by
          rw [G.boundaryContribution]
          omega)).1
        (by rw [hc1]; omega)
        (by
          have hc : componentCount B G.boundaryDegree = 2 := by
            simpa [B] using G.boundarySignature.1
          omega)
        C boundaryPure (e 2) (by simpa [hj]) hbPure
      exact hdegneB.2 heq
  have hsubset : componentSupport B h1 C ⊆ ({e 1, e 2} : Finset (Fin 3)) := by
    intro j hj
    obtain ⟨i, rfl⟩ := e.surjective j
    fin_cases i
    · exact (h0not hj).elim
    · simp
    · simp
  have hcard_le : (componentSupport B h1 C).card ≤ 2 := by
    have := Finset.card_le_card hsubset
    simpa [e.injective.eq_iff] using this
  have hcard_pos := Finset.card_pos.mpr hnonempty
  have hcard : (componentSupport B h1 C).card = 2 := by omega
  refine ⟨C, hCne, ?_⟩
  apply Finset.eq_of_subset_of_card_le hsubset
  simpa [hcard, e.injective.eq_iff]

/-- A connected component whose support is exactly two coordinates contains
an actual factorization in which both coordinates occur. -/
theorem exists_mixed_factorization_of_componentSupport_pair
    (B : Data Gamma) (h : ℕ) (C : FiberComponent B h) (j k : Fin 3)
    (hjk : j ≠ k) (hC : componentSupport B h C = {j, k}) :
    ∃ u : FactorizationFiber B h,
      (fiberGraph B h).connectedComponentMk u = C ∧
        0 < u.val j ∧ 0 < u.val k := by
  classical
  obtain ⟨uj, hujC, hujj⟩ :=
    (mem_componentSupport B h C j).mp (by simp [hC])
  obtain ⟨uk, hukC, hukk⟩ :=
    (mem_componentSupport B h C k).mp (by simp [hC])
  by_contra hnone
  push Not at hnone
  have hedge : ∀ {x y : FactorizationFiber B h},
      (fiberGraph B h).Adj x y →
      (fiberGraph B h).connectedComponentMk x = C →
      0 < x.val j → 0 < y.val j := by
    intro x y hxy hxC hxj
    obtain ⟨_, q, hxq, hyq⟩ := hxy
    by_cases hqj : q = j
    · simpa [hqj] using hyq
    have hqmem : q ∈ componentSupport B h C :=
      (mem_componentSupport B h C q).mpr ⟨x, hxC, hxq⟩
    have hqk : q = k := by
      rw [hC] at hqmem
      simpa [hqj] using hqmem
    subst q
    exact (Nat.not_lt_of_ge (hnone x hxC hxj) hxq).elim
  have hprop : ∀ {x y : FactorizationFiber B h},
      (fiberGraph B h).Reachable x y →
      (fiberGraph B h).connectedComponentMk x = C →
      0 < x.val j → 0 < y.val j := by
    intro x y hxy hxC hxj
    obtain ⟨p⟩ := hxy
    induction p with
    | nil => exact hxj
    | @cons x y z hxy p ih =>
        have hyj := hedge hxy hxC hxj
        have hyC : (fiberGraph B h).connectedComponentMk y = C :=
          (SimpleGraph.ConnectedComponent.sound hxy.reachable).symm.trans hxC
        exact ih hyC hyj
  have hreach := SimpleGraph.ConnectedComponent.exact (hujC.trans hukC.symm)
  have hukj := hprop hreach hujC hujj
  exact (Nat.not_lt_of_ge (hnone uk hukC hukj) hukk).elim

private theorem coordinate_eq_zero_of_not_mem_componentSupport
    (B : Data Gamma) (h : ℕ) (C : FiberComponent B h)
    (u : FactorizationFiber B h)
    (huC : (fiberGraph B h).connectedComponentMk u = C) (j : Fin 3)
    (hj : j ∉ componentSupport B h C) : u.val j = 0 := by
  apply Nat.eq_zero_of_not_pos
  intro huj
  exact hj ((mem_componentSupport B h C j).mpr ⟨u, huC, huj⟩)

private theorem cast_factorization_val_eq (B : Data Gamma) {h k : ℕ}
    (p : h = k) (u : FactorizationFiber B h) :
    (p ▸ u : FactorizationFiber B k).val = u.val := by
  subst k
  rfl

/-- A simultaneous coherent choice of the three actual mixed critical-fiber
representatives.  No relation, bound, or coefficient-sum identity is a field. -/
structure CoherentHerzogData (B : Data Gamma) (e : Fin 3 ≃ Fin 3) where
  witness1 : FactorizationFiber B (c1 B e * weights B (e 0))
  witness2 : FactorizationFiber B (c2 B e * weights B (e 1))
  witness3 : FactorizationFiber B (c3 B e * weights B (e 2))
  witness1_self_zero : witness1.val (e 0) = 0
  witness2_self_zero : witness2.val (e 1) = 0
  witness3_self_zero : witness3.val (e 2) = 0
  witness1_left_pos : 0 < witness1.val (e 1)
  witness1_right_pos : 0 < witness1.val (e 2)
  witness2_left_pos : 0 < witness2.val (e 0)
  witness2_right_pos : 0 < witness2.val (e 2)
  witness3_left_pos : 0 < witness3.val (e 0)
  witness3_right_pos : 0 < witness3.val (e 1)

abbrev cr12 {B : Data Gamma} {e : Fin 3 ≃ Fin 3} (D : CoherentHerzogData B e) :=
  D.witness1.val (e 1)
abbrev cr13 {B : Data Gamma} {e : Fin 3 ≃ Fin 3} (D : CoherentHerzogData B e) :=
  D.witness1.val (e 2)
abbrev cr21 {B : Data Gamma} {e : Fin 3 ≃ Fin 3} (D : CoherentHerzogData B e) :=
  D.witness2.val (e 0)
abbrev cr23 {B : Data Gamma} {e : Fin 3 ≃ Fin 3} (D : CoherentHerzogData B e) :=
  D.witness2.val (e 2)
abbrev cr31 {B : Data Gamma} {e : Fin 3 ≃ Fin 3} (D : CoherentHerzogData B e) :=
  D.witness3.val (e 0)
abbrev cr32 {B : Data Gamma} {e : Fin 3 ≃ Fin 3} (D : CoherentHerzogData B e) :=
  D.witness3.val (e 1)

/-- D2/D3 construction: all witness and positivity fields are discharged from
the actual three non-pure components. -/
theorem exists_coherentHerzogData {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (internalPure internalMixed : internalComponents G)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (hine : internalPure ≠ internalMixed) (hbne : boundaryPure ≠ boundaryMixed)
    (hiPure : componentSupport P.M.base G.internalDegree internalPure = {e 1})
    (hiMixed : componentSupport P.M.base G.internalDegree internalMixed = {e 0, e 2})
    (hbPure : componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2})
    (hbMixed : componentSupport P.M.base G.boundaryDegree boundaryMixed = {e 0, e 1}) :
    Nonempty (CoherentHerzogData P.M.base e) := by
  classical
  obtain ⟨C1, _, hC1⟩ := exists_h1_nonpure_component_support G e
    internalPure internalMixed boundaryPure boundaryMixed hine hbne
    hiPure hiMixed hbPure hbMixed
  obtain ⟨w1, hw1C, hw12, hw13⟩ :=
    exists_mixed_factorization_of_componentSupport_pair P.M.base _ C1
      (e 1) (e 2) (by intro he; have := e.injective he; omega) hC1
  have hw10 : w1.val (e 0) = 0 :=
    coordinate_eq_zero_of_not_mem_componentSupport P.M.base _ C1 w1 hw1C (e 0)
      (by rw [hC1]; simp [e.injective.eq_iff])
  have hdegrees := actual_internal_boundary_critical_degrees G e internalPure boundaryPure
    hiPure hbPure
  obtain ⟨w2raw, hw2C, hw21raw, hw23raw⟩ :=
    exists_mixed_factorization_of_componentSupport_pair P.M.base G.internalDegree
      internalMixed (e 0) (e 2) (by intro he; have := e.injective he; omega) hiMixed
  have hw20raw : w2raw.val (e 1) = 0 :=
    coordinate_eq_zero_of_not_mem_componentSupport P.M.base _ internalMixed
      w2raw hw2C (e 1) (by rw [hiMixed]; simp [e.injective.eq_iff])
  let w2 : FactorizationFiber P.M.base
      (c2 P.M.base e * weights P.M.base (e 1)) := hdegrees.1 ▸ w2raw
  have hw21 : 0 < w2.val (e 0) := by
    rw [show w2.val = w2raw.val by
      exact cast_factorization_val_eq P.M.base hdegrees.1 w2raw]
    exact hw21raw
  have hw23 : 0 < w2.val (e 2) := by
    rw [show w2.val = w2raw.val by
      exact cast_factorization_val_eq P.M.base hdegrees.1 w2raw]
    exact hw23raw
  have hw20 : w2.val (e 1) = 0 :=
    by
      rw [show w2.val = w2raw.val by
        exact cast_factorization_val_eq P.M.base hdegrees.1 w2raw]
      exact hw20raw
  obtain ⟨w3raw, hw3C, hw31raw, hw32raw⟩ :=
    exists_mixed_factorization_of_componentSupport_pair P.M.base G.boundaryDegree
      boundaryMixed (e 0) (e 1) (by intro he; have := e.injective he; omega) hbMixed
  have hw30raw : w3raw.val (e 2) = 0 :=
    coordinate_eq_zero_of_not_mem_componentSupport P.M.base _ boundaryMixed
      w3raw hw3C (e 2) (by rw [hbMixed]; simp [e.injective.eq_iff])
  let w3 : FactorizationFiber P.M.base
      (c3 P.M.base e * weights P.M.base (e 2)) := hdegrees.2 ▸ w3raw
  have hw31 : 0 < w3.val (e 0) := by
    rw [show w3.val = w3raw.val by
      exact cast_factorization_val_eq P.M.base hdegrees.2 w3raw]
    exact hw31raw
  have hw32 : 0 < w3.val (e 1) := by
    rw [show w3.val = w3raw.val by
      exact cast_factorization_val_eq P.M.base hdegrees.2 w3raw]
    exact hw32raw
  have hw30 : w3.val (e 2) = 0 :=
    by
      rw [show w3.val = w3raw.val by
        exact cast_factorization_val_eq P.M.base hdegrees.2 w3raw]
      exact hw30raw
  exact ⟨⟨w1, w2, w3, hw10, hw20, hw30, hw12, hw13, hw21, hw23, hw31, hw32⟩⟩

/-- The three weighted Herzog relations are consequences of actual fiber
membership and the self-coordinate exclusions. -/
theorem coherent_relations (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    c1 B e * weights B (e 0) =
        cr12 D * weights B (e 1) + cr13 D * weights B (e 2) ∧
      c2 B e * weights B (e 1) =
        cr21 D * weights B (e 0) + cr23 D * weights B (e 2) ∧
      c3 B e * weights B (e 2) =
        cr31 D * weights B (e 0) + cr32 D * weights B (e 1) := by
  have h1 := D.witness1.property
  have h2 := D.witness2.property
  have h3 := D.witness3.property
  rw [weight_three_coordinates B e] at h1 h2 h3
  simp only [D.witness1_self_zero, D.witness2_self_zero, D.witness3_self_zero,
    zero_mul, zero_add, add_zero] at h1 h2 h3
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- All six coherent cross coefficients are positive by construction from
genuinely mixed actual component vertices. -/
theorem coherent_coefficients_positive (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    0 < cr12 D ∧ 0 < cr13 D ∧ 0 < cr21 D ∧
      0 < cr23 D ∧ 0 < cr31 D ∧ 0 < cr32 D :=
  ⟨D.witness1_left_pos, D.witness1_right_pos,
    D.witness2_left_pos, D.witness2_right_pos,
    D.witness3_left_pos, D.witness3_right_pos⟩

private def coordinateVector (e : Fin 3 ≃ Fin 3) (x y z : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single (e 0) x + Finsupp.single (e 1) y + Finsupp.single (e 2) z

@[simp] private theorem coordinateVector_apply_zero (e : Fin 3 ≃ Fin 3) (x y z : ℕ) :
    coordinateVector e x y z (e 0) = x := by
  simp [coordinateVector, e.injective.eq_iff]

@[simp] private theorem coordinateVector_apply_one (e : Fin 3 ≃ Fin 3) (x y z : ℕ) :
    coordinateVector e x y z (e 1) = y := by
  simp [coordinateVector, e.injective.eq_iff]

@[simp] private theorem coordinateVector_apply_two (e : Fin 3 ≃ Fin 3) (x y z : ℕ) :
    coordinateVector e x y z (e 2) = z := by
  simp [coordinateVector, e.injective.eq_iff]

private theorem weight_coordinateVector (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x y z : ℕ) : weight B (coordinateVector e x y z) =
      x * weights B (e 0) + y * weights B (e 1) + z * weights B (e 2) := by
  rw [weight_three_coordinates B e]
  simp

private theorem coherent_r12_lt_c2 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : cr12 D < c2 B e := by
  have hr := coherent_relations B e D
  have hp := coherent_coefficients_positive B e D
  by_contra hn
  have hle : c2 B e ≤ cr12 D := by omega
  let u : FactorizationFiber B (c1 B e * weights B (e 0)) :=
    ⟨coordinateVector e (cr21 D) (cr12 D - c2 B e) (cr13 D + cr23 D), by
      rw [weight_coordinateVector]
      have hs := Nat.sub_add_cancel hle
      nlinarith [hr.1, hr.2.1]⟩
  have hu := factorization_eq_criticalPure_of_coord_pos B (e 0) u (by
    simpa [u] using hp.2.2.1)
  have hc := congrArg (fun v : FactorizationFiber B _ ↦ v.val (e 2)) hu
  simp [u, criticalPureFactorization, e.injective.eq_iff] at hc
  omega

private theorem coherent_r13_lt_c3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : cr13 D < c3 B e := by
  have hr := coherent_relations B e D
  have hp := coherent_coefficients_positive B e D
  by_contra hn
  have hle : c3 B e ≤ cr13 D := by omega
  let u : FactorizationFiber B (c1 B e * weights B (e 0)) :=
    ⟨coordinateVector e (cr31 D) (cr12 D + cr32 D) (cr13 D - c3 B e), by
      rw [weight_coordinateVector]
      have hs := Nat.sub_add_cancel hle
      nlinarith [hr.1, hr.2.2]⟩
  have hu := factorization_eq_criticalPure_of_coord_pos B (e 0) u (by
    simpa [u] using hp.2.2.2.2.1)
  have hc := congrArg (fun v : FactorizationFiber B _ ↦ v.val (e 1)) hu
  simp [u, criticalPureFactorization, e.injective.eq_iff] at hc
  omega

private theorem coherent_r21_lt_c1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : cr21 D < c1 B e := by
  have hr := coherent_relations B e D
  have hp := coherent_coefficients_positive B e D
  by_contra hn
  have hle : c1 B e ≤ cr21 D := by omega
  let u : FactorizationFiber B (c2 B e * weights B (e 1)) :=
    ⟨coordinateVector e (cr21 D - c1 B e) (cr12 D) (cr23 D + cr13 D), by
      rw [weight_coordinateVector]
      have hs := Nat.sub_add_cancel hle
      nlinarith [hr.1, hr.2.1]⟩
  have hu := factorization_eq_criticalPure_of_coord_pos B (e 1) u (by
    simpa [u] using hp.1)
  have hc := congrArg (fun v : FactorizationFiber B _ ↦ v.val (e 2)) hu
  simp [u, criticalPureFactorization, e.injective.eq_iff] at hc
  omega

private theorem coherent_r23_lt_c3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : cr23 D < c3 B e := by
  have hr := coherent_relations B e D
  have hp := coherent_coefficients_positive B e D
  by_contra hn
  have hle : c3 B e ≤ cr23 D := by omega
  let u : FactorizationFiber B (c2 B e * weights B (e 1)) :=
    ⟨coordinateVector e (cr21 D + cr31 D) (cr32 D) (cr23 D - c3 B e), by
      rw [weight_coordinateVector]
      have hs := Nat.sub_add_cancel hle
      nlinarith [hr.2.1, hr.2.2]⟩
  have hu := factorization_eq_criticalPure_of_coord_pos B (e 1) u (by
    simpa [u] using hp.2.2.2.2.2)
  have hc := congrArg (fun v : FactorizationFiber B _ ↦ v.val (e 0)) hu
  simp [u, criticalPureFactorization, e.injective.eq_iff] at hc
  omega

private theorem coherent_r31_lt_c1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : cr31 D < c1 B e := by
  have hr := coherent_relations B e D
  have hp := coherent_coefficients_positive B e D
  by_contra hn
  have hle : c1 B e ≤ cr31 D := by omega
  let u : FactorizationFiber B (c3 B e * weights B (e 2)) :=
    ⟨coordinateVector e (cr31 D - c1 B e) (cr32 D + cr12 D) (cr13 D), by
      rw [weight_coordinateVector]
      have hs := Nat.sub_add_cancel hle
      nlinarith [hr.1, hr.2.2]⟩
  have hu := factorization_eq_criticalPure_of_coord_pos B (e 2) u (by
    simpa [u] using hp.2.1)
  have hc := congrArg (fun v : FactorizationFiber B _ ↦ v.val (e 1)) hu
  simp [u, criticalPureFactorization, e.injective.eq_iff] at hc
  omega

private theorem coherent_r32_lt_c2 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : cr32 D < c2 B e := by
  have hr := coherent_relations B e D
  have hp := coherent_coefficients_positive B e D
  by_contra hn
  have hle : c2 B e ≤ cr32 D := by omega
  let u : FactorizationFiber B (c3 B e * weights B (e 2)) :=
    ⟨coordinateVector e (cr31 D + cr21 D) (cr32 D - c2 B e) (cr23 D), by
      rw [weight_coordinateVector]
      have hs := Nat.sub_add_cancel hle
      nlinarith [hr.2.1, hr.2.2]⟩
  have hu := factorization_eq_criticalPure_of_coord_pos B (e 2) u (by
    simpa [u] using hp.2.2.2.1)
  have hc := congrArg (fun v : FactorizationFiber B _ ↦ v.val (e 0)) hu
  simp [u, criticalPureFactorization, e.injective.eq_iff] at hc
  omega

/-- D4: each coherent cross coefficient is strictly below the critical
exponent of its target coordinate.  Each clause is proved by one actual
substitution factorization and pure-critical rigidity. -/
theorem coherent_strict_bounds (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    cr12 D < c2 B e ∧ cr13 D < c3 B e ∧
      cr21 D < c1 B e ∧ cr23 D < c3 B e ∧
      cr31 D < c1 B e ∧ cr32 D < c2 B e :=
  ⟨coherent_r12_lt_c2 B e D, coherent_r13_lt_c3 B e D,
    coherent_r21_lt_c1 B e D, coherent_r23_lt_c3 B e D,
    coherent_r31_lt_c1 B e D, coherent_r32_lt_c2 B e D⟩

private theorem coherent_c1_le (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : c1 B e ≤ cr21 D + cr31 D := by
  have hr := coherent_relations B e D
  have hb := coherent_strict_bounds B e D
  apply criticalExponent_min B (e 0) (cr21 D + cr31 D)
  refine ⟨by have hp := coherent_coefficients_positive B e D; omega,
    coordinateVector e 0 (c2 B e - cr32 D) (c3 B e - cr23 D), ?_, ?_⟩
  · simp
  · rw [weight_coordinateVector]
    have hs32 := Nat.sub_add_cancel (Nat.le_of_lt hb.2.2.2.2.2)
    have hs23 := Nat.sub_add_cancel (Nat.le_of_lt hb.2.2.2.1)
    nlinarith [hr.2.1, hr.2.2]

private theorem coherent_c2_le (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : c2 B e ≤ cr12 D + cr32 D := by
  have hr := coherent_relations B e D
  have hb := coherent_strict_bounds B e D
  apply criticalExponent_min B (e 1) (cr12 D + cr32 D)
  refine ⟨by have hp := coherent_coefficients_positive B e D; omega,
    coordinateVector e (c1 B e - cr31 D) 0 (c3 B e - cr13 D), ?_, ?_⟩
  · simp
  · rw [weight_coordinateVector]
    have hs31 := Nat.sub_add_cancel (Nat.le_of_lt hb.2.2.2.2.1)
    have hs13 := Nat.sub_add_cancel (Nat.le_of_lt hb.2.1)
    nlinarith [hr.1, hr.2.2]

private theorem coherent_c3_le (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : c3 B e ≤ cr13 D + cr23 D := by
  have hr := coherent_relations B e D
  have hb := coherent_strict_bounds B e D
  apply criticalExponent_min B (e 2) (cr13 D + cr23 D)
  refine ⟨by have hp := coherent_coefficients_positive B e D; omega,
    coordinateVector e (c1 B e - cr21 D) (c2 B e - cr12 D) 0, ?_, ?_⟩
  · simp
  · rw [weight_coordinateVector]
    have hs21 := Nat.sub_add_cancel (Nat.le_of_lt hb.2.2.1)
    have hs12 := Nat.sub_add_cancel (Nat.le_of_lt hb.1)
    nlinarith [hr.1, hr.2.1]

/-- D5: the coherent coefficients satisfy the three paper Herzog sums.
The forward inequalities come from three actual outside factorizations and
critical-exponent minimality; summing the three actual fiber relations forces
all three nonnegative defects to vanish. -/
theorem coherent_coefficients (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    c1 B e = cr21 D + cr31 D ∧
      c2 B e = cr12 D + cr32 D ∧
      c3 B e = cr13 D + cr23 D := by
  have hr := coherent_relations B e D
  have h1 := coherent_c1_le B e D
  have h2 := coherent_c2_le B e D
  have h3 := coherent_c3_le B e D
  have hw0 := weights_positive B (e 0)
  have hw1 := weights_positive B (e 1)
  have hw2 := weights_positive B (e 2)
  constructor
  · nlinarith [hr.1, hr.2.1, hr.2.2]
  constructor
  · nlinarith [hr.1, hr.2.1, hr.2.2]
  · nlinarith [hr.1, hr.2.1, hr.2.2]

/-- D6: paper-facing coordinates rebuilt from the coherent coefficients.
These are additive names; the frozen C4C abbreviations remain untouched. -/
abbrev coherentH0 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := eta B e 0 0

abbrev coherentP1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) := eta B e (cr12 D - 1) (cr13 D)

abbrev coherentQ1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) := eta B e (cr12 D) (cr13 D - 1)

abbrev coherentY3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) := eta B e 0 (c3 B e - 1)

abbrev coherentZ3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) := eta B e (cr32 D) 0

abbrev coherentZ3minus (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) := eta B e (cr32 D - 1) 0

def coherentKappa1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : ℕ × ℕ :=
  (c2 B e - 1, cr13 D - 1)

end NS25Lean.L5A2C4D
