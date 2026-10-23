import NS25Lean.P2SectorCHerzogDictionary

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4B

open L2B L5A1 L5A2C3G L5A2C4A ChosenBase Classical

variable {Gamma : NumericalSemigroup}

/-- The actual pure factorization at a coordinate's critical degree. -/
def criticalPureFactorization (B : Data Gamma) (j : Fin 3) :
    FactorizationFiber B (criticalExponent B j * weights B j) :=
  ⟨Finsupp.single j (criticalExponent B j), weight_single B j _⟩

/-- The connected component containing the actual pure critical factorization. -/
def critical_pure_component (B : Data Gamma) (j : Fin 3) :
    FiberComponent B (criticalExponent B j * weights B j) :=
  (fiberGraph B _).connectedComponentMk (criticalPureFactorization B j)

private theorem weight_eq_zero_iff (B : Data Gamma) (u : Fin 3 →₀ ℕ) :
    weight B u = 0 ↔ u = 0 := by
  constructor
  · intro hu
    ext i
    have hterm : u i * weights B i ≤ ∑ k, u k * weights B k :=
      Finset.single_le_sum (fun k _ ↦ Nat.zero_le (u k * weights B k))
        (Finset.mem_univ i)
    rw [← weight_eq_sum, hu] at hterm
    have hp := weights_positive B i
    simp only [Finsupp.zero_apply]
    nlinarith
  · rintro rfl
    simp

/-- Critical minimality forces every factorization having positive critical
coordinate to be the pure factorization itself. -/
theorem factorization_eq_criticalPure_of_coord_pos (B : Data Gamma) (j : Fin 3)
    (u : FactorizationFiber B (criticalExponent B j * weights B j))
    (huj : 0 < u.val j) : u = criticalPureFactorization B j := by
  classical
  have hterm : u.val j * weights B j ≤ ∑ i, u.val i * weights B i :=
    Finset.single_le_sum (fun i _ ↦ Nat.zero_le (u.val i * weights B i))
      (Finset.mem_univ j)
  rw [← weight_eq_sum, u.property] at hterm
  have hwpos := weights_positive B j
  have hjle : u.val j ≤ criticalExponent B j := by nlinarith
  by_cases hjlt : u.val j < criticalExponent B j
  · have hdecomp := congrArg (weight B) (Finsupp.single_add_erase j u.val)
    rw [map_add, weight_single, u.property] at hdecomp
    have herase : weight B (u.val.erase j) =
        (criticalExponent B j - u.val j) * weights B j := by
      have hsub := Nat.sub_add_cancel hjle
      nlinarith
    have hout : OutsideExponent B j (criticalExponent B j - u.val j) :=
      ⟨by omega, u.val.erase j, by simp, herase⟩
    have hmin := criticalExponent_min B j _ hout
    omega
  · have hj : u.val j = criticalExponent B j := by omega
    have hdecomp := congrArg (weight B) (Finsupp.single_add_erase j u.val)
    rw [map_add, weight_single, u.property, hj] at hdecomp
    have herase : u.val.erase j = 0 :=
      (weight_eq_zero_iff B _).mp (by omega)
    apply Subtype.ext
    calc
      u.val = Finsupp.single j (u.val j) + u.val.erase j :=
        (Finsupp.single_add_erase j u.val).symm
      _ = Finsupp.single j (criticalExponent B j) := by rw [hj, herase, add_zero]

private theorem criticalPure_neighborSet_eq_empty (B : Data Gamma) (j : Fin 3) :
    (fiberGraph B _).neighborSet (criticalPureFactorization B j) = ∅ := by
  ext u
  simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hne, i, hpi, hui⟩
  have hij : i = j := by
    by_contra hij
    simpa [criticalPureFactorization, Finsupp.single_eq_of_ne hij] using hpi
  subst i
  have hu := factorization_eq_criticalPure_of_coord_pos B j u hui
  exact hne hu.symm

/-- Forward critical-component rigidity: the actual pure critical component
has exactly the singleton coordinate support. -/
theorem critical_component_support_eq_singleton (B : Data Gamma) (j : Fin 3) :
    componentSupport B (criticalExponent B j * weights B j)
      (critical_pure_component B j) = {j} := by
  classical
  apply Finset.ext
  intro i
  constructor
  · intro hi
    obtain ⟨u, hu, hui⟩ := (mem_componentSupport B _ _ i).mp hi
    change (fiberGraph B _).connectedComponentMk u =
      (fiberGraph B _).connectedComponentMk (criticalPureFactorization B j) at hu
    by_cases hup : u = criticalPureFactorization B j
    · subst u
      have hij : i = j := by
        by_contra hij
        simp [criticalPureFactorization, hij] at hui
      simpa [hij]
    · have hreach := SimpleGraph.ConnectedComponent.exact hu
      exact (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hup
        (criticalPure_neighborSet_eq_empty B j) hreach).elim
  · intro hi
    have hij : i = j := by simpa using hi
    subst i
    apply (mem_componentSupport B _ _ j).mpr
    refine ⟨criticalPureFactorization B j, rfl, ?_⟩
    simpa [criticalPureFactorization] using (criticalExponent_spec B j).1

/-- The outside witness is in a component distinct from the isolated pure
critical component, so the critical fiber has at least two components. -/
theorem critical_fiber_componentCount_ge_two (B : Data Gamma) (j : Fin 3) :
    2 ≤ componentCount B (criticalExponent B j * weights B j) := by
  classical
  let v : FactorizationFiber B (criticalExponent B j * weights B j) :=
    ⟨Classical.choose (criticalExponent_spec B j).2,
      (Classical.choose_spec (criticalExponent_spec B j).2).2⟩
  let C := critical_pure_component B j
  let D := (fiberGraph B _).connectedComponentMk v
  have hvj : v.val j = 0 :=
    (Classical.choose_spec (criticalExponent_spec B j).2).1
  have hCD : C ≠ D := by
    intro he
    change (fiberGraph B _).connectedComponentMk (criticalPureFactorization B j) =
      (fiberGraph B _).connectedComponentMk v at he
    have hreach := SimpleGraph.ConnectedComponent.exact he.symm
    by_cases hvp : v = criticalPureFactorization B j
    · have hc := congrArg (fun w ↦ w.val j) hvp
      simp [criticalPureFactorization, hvj] at hc
      have hr := (criticalExponent_spec B j).1
      omega
    · exact (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty hvp
        (criticalPure_neighborSet_eq_empty B j) hreach).elim
  let f : Fin 2 → FiberComponent B (criticalExponent B j * weights B j) := ![C, D]
  have hf : Function.Injective f := by
    intro a b
    fin_cases a <;> fin_cases b <;> simp [f, hCD, Ne.symm hCD]
  have hcard := Nat.card_le_card_of_injective f hf
  simpa [componentCount] using hcard

private theorem two_components_exhaust (B : Data Gamma) (h : ℕ)
    (C D : FiberComponent B h) (hne : C ≠ D) (hc : componentCount B h = 2)
    (E : FiberComponent B h) : E = C ∨ E = D := by
  classical
  letI := Fintype.ofFinite (FiberComponent B h)
  have hcard : Fintype.card (FiberComponent B h) = 2 := by
    simpa [componentCount, Nat.card_eq_fintype_card] using hc
  have hall : ({C, D} : Finset (FiberComponent B h)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simp [hne, hcard])
  have hmem : E ∈ ({C, D} : Finset (FiberComponent B h)) := by rw [hall]; simp
  simpa using hmem

private theorem critical_degree_ne_of_two_supports (B : Data Gamma) (j : Fin 3)
    (h : ℕ) (C D : FiberComponent B h) (hne : C ≠ D)
    (hc : componentCount B h = 2)
    (hCne : ({j} : Finset (Fin 3)) ≠ componentSupport B h C)
    (hDne : ({j} : Finset (Fin 3)) ≠ componentSupport B h D) :
    criticalExponent B j * weights B j ≠ h := by
  intro heq
  cases heq
  have hcrit := critical_component_support_eq_singleton B j
  rcases two_components_exhaust B _ C D hne hc (critical_pure_component B j) with hE | hE
  · subst hE
    exact hCne hcrit.symm
  · subst hE
    exact hDne hcrit.symm

/-- The critical degree `h1` cannot coincide with either actual positive
Sector-C degree, because its singleton support is the third reindexed
coordinate and each positive fiber is already exhausted by its frozen two
support components. -/
theorem actual_h1_distinct_degrees {P : P2Data Gamma} (G : SectorCActualFibers P)
    (e : Fin 3 ≃ Fin 3)
    (internalPure internalMixed : internalComponents G)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (hine : internalPure ≠ internalMixed) (hbne : boundaryPure ≠ boundaryMixed)
    (hiPure : componentSupport P.M.base G.internalDegree internalPure = {e 1})
    (hiMixed : componentSupport P.M.base G.internalDegree internalMixed = {e 0, e 2})
    (hbPure : componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2})
    (hbMixed : componentSupport P.M.base G.boundaryDegree boundaryMixed = {e 0, e 1}) :
    c1 P.M.base e * weights P.M.base (e 0) ≠ G.internalDegree ∧
      c1 P.M.base e * weights P.M.base (e 0) ≠ G.boundaryDegree := by
  constructor
  · apply critical_degree_ne_of_two_supports P.M.base (e 0) G.internalDegree
      internalPure internalMixed hine G.internalSignature.1
    · rw [hiPure]
      intro hs
      have he01 : e 0 = e 1 := Finset.singleton_inj.mp hs
      have : (0 : Fin 3) = 1 := e.injective he01
      omega
    · rw [hiMixed]
      intro hs
      have hcard := congrArg Finset.card hs
      simpa [e.injective.eq_iff] using hcard
  · apply critical_degree_ne_of_two_supports P.M.base (e 0) G.boundaryDegree
      boundaryPure boundaryMixed hbne G.boundarySignature.1
    · rw [hbPure]
      intro hs
      have he02 : e 0 = e 2 := Finset.singleton_inj.mp hs
      have : (0 : Fin 3) = 2 := e.injective he02
      omega
    · rw [hbMixed]
      intro hs
      have hcard := congrArg Finset.card hs
      simpa [e.injective.eq_iff] using hcard

theorem actual_h1_componentCount {P : P2Data Gamma} (G : SectorCActualFibers P)
    (e : Fin 3 ≃ Fin 3)
    (h1ne : c1 P.M.base e * weights P.M.base (e 0) ≠ G.internalDegree) :
    componentCount P.M.base (c1 P.M.base e * weights P.M.base (e 0)) = 2 := by
  have hlow : 2 ≤ componentCount P.M.base
      (c1 P.M.base e * weights P.M.base (e 0)) := by
    simpa [c1, herzogC] using critical_fiber_componentCount_ge_two P.M.base (e 0)
  have hpos : 0 < c1 P.M.base e * weights P.M.base (e 0) := by
    have hc := herzogC_positive P.M.base e 0
    have hw := weights_positive P.M.base (e 0)
    nlinarith
  have hupp := componentCount_le_three P.M.base _ hpos
  by_cases hthree : componentCount P.M.base
      (c1 P.M.base e * weights P.M.base (e 0)) = 3
  · have hactive : G.internalDegree ∈ activeDegreeFinset P.M :=
      (mem_activeDegreeFinset P.M G.internalDegree).mpr
        (positive_contribution_active P.M G.internalDegree (by
          rw [G.internalContribution]
          omega))
    have heq := three_components_unique_active P.M
      (c1 P.M.base e * weights P.M.base (e 0)) G.internalDegree hpos hthree hactive
    exact (h1ne heq.symm).elim
  · omega

theorem actual_h1_contribution_zero {P : P2Data Gamma} (G : SectorCActualFibers P)
    (e : Fin 3 ≃ Fin 3)
    (hne : c1 P.M.base e * weights P.M.base (e 0) ≠ G.internalDegree ∧
      c1 P.M.base e * weights P.M.base (e 0) ≠ G.boundaryDegree) :
    fiberContribution P.M (c1 P.M.base e * weights P.M.base (e 0)) = 0 :=
  G.contribution_zero_elsewhere _ hne.1 hne.2

theorem actual_h1_killedCount {P : P2Data Gamma} (G : SectorCActualFibers P)
    (e : Fin 3 ≃ Fin 3)
    (hc : componentCount P.M.base (c1 P.M.base e * weights P.M.base (e 0)) = 2)
    (hz : fiberContribution P.M (c1 P.M.base e * weights P.M.base (e 0)) = 0) :
    killedCount P.M (c1 P.M.base e * weights P.M.base (e 0)) = 2 := by
  have hle := killedCount_le_componentCount P.M
    (c1 P.M.base e * weights P.M.base (e 0))
  unfold fiberContribution at hz
  split_ifs at hz <;> omega

/-- Exact paper interface for the actual nonsymmetric Sector-C inactive gate
`h1 = c1*a`: two components, both boundary-killed. -/
theorem actual_h1_inactive_gate {P : P2Data Gamma} (G : SectorCActualFibers P)
    (e : Fin 3 ≃ Fin 3)
    (internalPure internalMixed : internalComponents G)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (hine : internalPure ≠ internalMixed) (hbne : boundaryPure ≠ boundaryMixed)
    (hiPure : componentSupport P.M.base G.internalDegree internalPure = {e 1})
    (hiMixed : componentSupport P.M.base G.internalDegree internalMixed = {e 0, e 2})
    (hbPure : componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2})
    (hbMixed : componentSupport P.M.base G.boundaryDegree boundaryMixed = {e 0, e 1}) :
    LocalSignature P.M (c1 P.M.base e * weights P.M.base (e 0)) 2 2 := by
  have hne := actual_h1_distinct_degrees G e internalPure internalMixed
    boundaryPure boundaryMixed hine hbne hiPure hiMixed hbPure hbMixed
  have hc := actual_h1_componentCount G e hne.1
  have hz := actual_h1_contribution_zero G e hne
  exact ⟨hc, actual_h1_killedCount G e hc hz⟩

end NS25Lean.L5A2C4B
