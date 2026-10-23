import NS25Lean.P2SectorCCoherentKappaStencil

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4F

open L2B L5A1 L5A2C3G L5A2C4A L5A2C4C L5A2C4D L5A2C4E ChosenBase

variable {Gamma : NumericalSemigroup}

private theorem actual_boundary_degree_eq_h3 {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2}) :
    G.boundaryDegree = c3 P.M.base e * weights P.M.base (e 2) := by
  apply singleton_active_degree_eq_critical P.M.base G.boundaryDegree
    (positive_contribution_active P.M G.boundaryDegree (by
      rw [G.boundaryContribution]
      omega)).1
    (by
      have hc := G.boundarySignature.1
      unfold componentCount at hc ⊢
      omega)
    pure (e 2) hpure

private theorem boundary_sub_c_eq_grid {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2}) :
    G.boundaryDegree - weights P.M.base (e 2) =
      gridDegree P.M.base e 0 0 (c3 P.M.base e - 1) := by
  have hdeg := actual_boundary_degree_eq_h3 G e pure hpure
  have hc3 : 0 < c3 P.M.base e := herzogC_positive P.M.base e 2
  have hs : c3 P.M.base e - 1 + 1 = c3 P.M.base e := Nat.sub_add_cancel hc3
  rw [hdeg]
  simp only [gridDegree, zero_mul, zero_add]
  conv_lhs => rw [← hs, Nat.add_mul, one_mul]
  omega

private theorem boundary_sub_a_eq_grid {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (D : CoherentHerzogData P.M.base e) :
    G.boundaryDegree - weights P.M.base (e 0) =
      gridDegree P.M.base e (cr31 D - 1) (cr32 D) 0 := by
  have hdeg := actual_boundary_degree_eq_h3 G e pure hpure
  have hr := (coherent_relations P.M.base e D).2.2
  have hp := (coherent_coefficients_positive P.M.base e D).2.2.2.2.1
  have hs : cr31 D - 1 + 1 = cr31 D := Nat.sub_add_cancel hp
  rw [hdeg, hr]
  simp only [gridDegree]
  conv_lhs => rw [← hs, Nat.add_mul, one_mul]
  omega

private theorem boundary_sub_b_eq_grid {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (D : CoherentHerzogData P.M.base e) :
    G.boundaryDegree - weights P.M.base (e 1) =
      gridDegree P.M.base e (cr31 D) (cr32 D - 1) 0 := by
  have hdeg := actual_boundary_degree_eq_h3 G e pure hpure
  have hr := (coherent_relations P.M.base e D).2.2
  have hp := (coherent_coefficients_positive P.M.base e D).2.2.2.2.2
  have hs : cr32 D - 1 + 1 = cr32 D := Nat.sub_add_cancel hp
  rw [hdeg, hr]
  simp only [gridDegree]
  conv_lhs => rw [← hs, Nat.add_mul, one_mul]
  omega

/-- Actual pure-component killing is exactly the `Y3=0` threshold event. -/
theorem pure_boundaryKilled_iff_Y3_zero {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (D : CoherentHerzogData P.M.base e) :
    BoundaryKilled P.M G.boundaryDegree pure ↔
      coherentY3 P.M.base e D = 0 := by
  constructor
  · rintro ⟨u, huC, j, huj, hk⟩
    have hjmem : j ∈ componentSupport P.M.base G.boundaryDegree pure :=
      (mem_componentSupport P.M.base G.boundaryDegree pure j).mpr ⟨u, huC, huj⟩
    rw [hpure, Finset.mem_singleton] at hjmem
    subst j
    rw [boundary_sub_c_eq_grid G e pure hpure] at hk
    exact (eta_eq_zero_iff P.M.base e 0 (c3 P.M.base e - 1)).mpr hk
  · intro hY
    have he2 : e 2 ∈ componentSupport P.M.base G.boundaryDegree pure := by
      rw [hpure]
      simp
    obtain ⟨u, huC, hu2⟩ :=
      (mem_componentSupport P.M.base G.boundaryDegree pure (e 2)).mp he2
    refine ⟨u, huC, e 2, hu2, ?_⟩
    rw [boundary_sub_c_eq_grid G e pure hpure]
    exact (eta_eq_zero_iff P.M.base e 0 (c3 P.M.base e - 1)).mp hY

/-- Actual mixed-component killing is exactly the repaired numerical
disjunction.  The disjunction is proved here, not stored in an orientation. -/
theorem mixed_boundaryKilled_iff_threshold {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure mixed : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (hmixed : componentSupport P.M.base G.boundaryDegree mixed = {e 0, e 1})
    (D : CoherentHerzogData P.M.base e) :
    BoundaryKilled P.M G.boundaryDegree mixed ↔
      coherentZ3 P.M.base e D < cr31 D ∨
        coherentZ3minus P.M.base e D < cr31 D + 1 := by
  constructor
  · rintro ⟨u, huC, j, huj, hk⟩
    have hjmem : j ∈ componentSupport P.M.base G.boundaryDegree mixed :=
      (mem_componentSupport P.M.base G.boundaryDegree mixed j).mpr ⟨u, huC, huj⟩
    rw [hmixed] at hjmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
    rcases hjmem with rfl | rfl
    · left
      rw [boundary_sub_a_eq_grid G e pure hpure D] at hk
      have hle := eta_le_of_mem P.M.base e (cr32 D) 0 (cr31 D - 1) hk
      have hle' : coherentZ3 P.M.base e D ≤ cr31 D - 1 := by
        simpa [coherentZ3] using hle
      have hp31 : 0 < cr31 D :=
        (coherent_coefficients_positive P.M.base e D).2.2.2.2.1
      exact hle'.trans_lt (by omega)
    · right
      rw [boundary_sub_b_eq_grid G e pure hpure D] at hk
      have hle := eta_le_of_mem P.M.base e (cr32 D - 1) 0 (cr31 D) hk
      have hle' : coherentZ3minus P.M.base e D ≤ cr31 D := by
        simpa [coherentZ3minus] using hle
      exact Nat.lt_succ_of_le hle'
  · intro hthreshold
    rcases hthreshold with hZ | hZm
    · have he0 : e 0 ∈ componentSupport P.M.base G.boundaryDegree mixed := by
        rw [hmixed]
        simp
      obtain ⟨u, huC, hu0⟩ :=
        (mem_componentSupport P.M.base G.boundaryDegree mixed (e 0)).mp he0
      refine ⟨u, huC, e 0, hu0, ?_⟩
      rw [boundary_sub_a_eq_grid G e pure hpure D]
      apply (gridDegree_mem_K_iff_eta_le P.M.base e (cr32 D) 0 (cr31 D - 1)).2
      change coherentZ3 P.M.base e D ≤ cr31 D - 1
      omega
    · have he1 : e 1 ∈ componentSupport P.M.base G.boundaryDegree mixed := by
        rw [hmixed]
        simp
      obtain ⟨u, huC, hu1⟩ :=
        (mem_componentSupport P.M.base G.boundaryDegree mixed (e 1)).mp he1
      refine ⟨u, huC, e 1, hu1, ?_⟩
      rw [boundary_sub_b_eq_grid G e pure hpure D]
      apply (gridDegree_mem_K_iff_eta_le P.M.base e (cr32 D - 1) 0 (cr31 D)).2
      change coherentZ3minus P.M.base e D ≤ cr31 D
      omega

/-- F1 pure orientation numerical consequences. -/
theorem pure_orientation_numerical {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure mixed : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (hmixed : componentSupport P.M.base G.boundaryDegree mixed = {e 0, e 1})
    (D : CoherentHerzogData P.M.base e)
    (hO : PureOrientation G pure mixed) :
    coherentY3 P.M.base e D = 0 ∧
      coherentZ3 P.M.base e D = cr31 D ∧
      cr31 D + 1 ≤ coherentZ3minus P.M.base e D := by
  have hY := (pure_boundaryKilled_iff_Y3_zero G e pure hpure D).mp hO.1
  have hnot := not_congr (mixed_boundaryKilled_iff_threshold G e pure mixed hpure hmixed D)
  have hnumerical := hnot.mp hO.2
  have hR2 := coherent_Z3_le_cr31_add_Y3 P.M.base e D
  constructor
  · exact hY
  constructor <;> omega

/-- F1 mixed orientation numerical consequences. -/
theorem mixed_orientation_numerical {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure mixed : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (hmixed : componentSupport P.M.base G.boundaryDegree mixed = {e 0, e 1})
    (D : CoherentHerzogData P.M.base e)
    (hO : MixedOrientation G pure mixed) :
    1 ≤ coherentY3 P.M.base e D ∧
      (coherentZ3 P.M.base e D < cr31 D ∨
        coherentZ3minus P.M.base e D < cr31 D + 1) := by
  have hYnot := not_congr (pure_boundaryKilled_iff_Y3_zero G e pure hpure D)
  have hY := hYnot.mp hO.1
  have hm := (mixed_boundaryKilled_iff_threshold G e pure mixed hpure hmixed D).mp hO.2
  exact ⟨by omega, hm⟩

/-- F2: the genuine surviving-notch gate, with the coherent paper names,
is definitionally the pair of actual eta-zero events. -/
theorem coherent_notch_gate (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    (coherentP1 B e D = 0 ∧ coherentQ1 B e D = 0) ↔
      (eta B e (cr12 D - 1) (cr13 D) = 0 ∧
        eta B e (cr12 D) (cr13 D - 1) = 0) :=
  Iff.rfl

/-- F3 / C-R1: the surviving mixed notch has width at least two. -/
theorem mixed_orientation_width {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure mixed : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (hmixed : componentSupport P.M.base G.boundaryDegree mixed = {e 0, e 1})
    (D : CoherentHerzogData P.M.base e)
    (hO : MixedOrientation G pure mixed)
    (hP1 : coherentP1 P.M.base e D = 0) :
    2 ≤ cr12 D := by
  have hY := (mixed_orientation_numerical G e pure mixed hpure hmixed D hO).1
  have hc := coherent_coefficients P.M.base e D
  have hp := coherent_coefficients_positive P.M.base e D
  by_contra hn
  have hr12 : cr12 D = 1 := by omega
  have hP : eta P.M.base e 0 (cr13 D) = 0 := by
    simpa [coherentP1, hr12] using hP1
  have hindex : cr13 D + (c3 P.M.base e - 1 - cr13 D) = c3 P.M.base e - 1 := by
    omega
  have hm := eta_antitone_right P.M.base e 0 (cr13 D)
    (c3 P.M.base e - 1 - cr13 D)
  rw [hindex] at hm
  change coherentY3 P.M.base e D ≤ eta P.M.base e 0 (cr13 D) at hm
  omega

/-- Width one plus the genuine surviving-notch gate is routed to the pure
orientation; the structural two-way orientation is the only exhaustion used. -/
theorem width_one_surviving_notch_pure {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure mixed : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (hmixed : componentSupport P.M.base G.boundaryDegree mixed = {e 0, e 1})
    (D : CoherentHerzogData P.M.base e)
    (hOrient : PureOrientation G pure mixed ∨ MixedOrientation G pure mixed)
    (hr12 : cr12 D = 1)
    (hP1 : coherentP1 P.M.base e D = 0)
    (_hQ1 : coherentQ1 P.M.base e D = 0) :
    PureOrientation G pure mixed := by
  rcases hOrient with hPure | hMixed
  · exact hPure
  · have hw := mixed_orientation_width G e pure mixed hpure hmixed D hMixed hP1
    omega

/-- F4 / C-R4: the mixed orientation has exactly the two repaired chambers. -/
theorem mixed_orientation_chambers {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure mixed : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (hmixed : componentSupport P.M.base G.boundaryDegree mixed = {e 0, e 1})
    (D : CoherentHerzogData P.M.base e)
    (hO : MixedOrientation G pure mixed) :
    coherentZ3 P.M.base e D < cr31 D ∨
      (coherentZ3 P.M.base e D = cr31 D ∧
        coherentZ3minus P.M.base e D = cr31 D) := by
  rcases (mixed_orientation_numerical G e pure mixed hpure hmixed D hO).2 with hZ | hZm
  · exact Or.inl hZ
  · by_cases hZ : coherentZ3 P.M.base e D < cr31 D
    · exact Or.inl hZ
    · right
      have hR2 := coherent_Z3minus_ge_Z3 P.M.base e D
      omega

/-- F5 paper-facing endpoint.  Every numerical branch fact is an output;
the inputs are only actual supports, coherent actual data, and structural
orientation. -/
theorem repaired_orientation_interface {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (pure mixed : boundaryComponents G)
    (hpure : componentSupport P.M.base G.boundaryDegree pure = {e 2})
    (hmixed : componentSupport P.M.base G.boundaryDegree mixed = {e 0, e 1})
    (D : CoherentHerzogData P.M.base e)
    (hOrient : PureOrientation G pure mixed ∨ MixedOrientation G pure mixed) :
    (PureOrientation G pure mixed →
      coherentY3 P.M.base e D = 0 ∧
        coherentZ3 P.M.base e D = cr31 D ∧
        cr31 D + 1 ≤ coherentZ3minus P.M.base e D) ∧
    (MixedOrientation G pure mixed →
      (1 ≤ coherentY3 P.M.base e D ∧
        (coherentZ3 P.M.base e D < cr31 D ∨
          coherentZ3minus P.M.base e D < cr31 D + 1)) ∧
      (coherentP1 P.M.base e D = 0 → 2 ≤ cr12 D) ∧
      (coherentZ3 P.M.base e D < cr31 D ∨
        (coherentZ3 P.M.base e D = cr31 D ∧
          coherentZ3minus P.M.base e D = cr31 D))) ∧
    (cr12 D = 1 → coherentP1 P.M.base e D = 0 →
      coherentQ1 P.M.base e D = 0 → PureOrientation G pure mixed) := by
  refine ⟨pure_orientation_numerical G e pure mixed hpure hmixed D, ?_, ?_⟩
  · intro hMixed
    exact ⟨mixed_orientation_numerical G e pure mixed hpure hmixed D hMixed,
      mixed_orientation_width G e pure mixed hpure hmixed D hMixed,
      mixed_orientation_chambers G e pure mixed hpure hmixed D hMixed⟩
  · intro hr hP hQ
    exact width_one_surviving_notch_pure G e pure mixed hpure hmixed D
      hOrient hr hP hQ

end NS25Lean.L5A2C4F
