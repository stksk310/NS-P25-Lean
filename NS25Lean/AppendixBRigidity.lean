import NS25Lean.AppendixBSupport
import NS25Lean.AppendixBTwoGenerator

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C
variable {Gamma : NumericalSemigroup}

/-- Coordinates outside an actual component's support vanish. -/
theorem component_coordinate_zero (B : Data Gamma) (d : ℕ) (C : FiberComponent B d)
    (u : FactorizationFiber B d) (hu : (fiberGraph B d).connectedComponentMk u = C)
    (k : Fin 4) (hk : k ∉ componentSupport B d C) : u.val k = 0 := by
  by_contra hn
  exact hk ((mem_componentSupport B d C k).mpr ⟨u, hu, Nat.pos_of_ne_zero hn⟩)

/-- A factorization on an actual two-variable component is the displayed sum. -/
theorem component_pair_decomposition (B : Data Gamma) (d : ℕ) (C : FiberComponent B d)
    (i j : Fin 4) (hij : i ≠ j) (hC : componentSupport B d C = {i,j})
    (u : FactorizationFiber B d) (hu : (fiberGraph B d).connectedComponentMk u = C) :
    u.val = Finsupp.single i (u.val i) + Finsupp.single j (u.val j) := by
  classical
  ext k
  by_cases hki : k = i
  · subst k; simp [hij]
  by_cases hkj : k = j
  · subst k; simp [hij.symm]
  have hz := component_coordinate_zero B d C u hu k (by simp [hC, hki, hkj])
  simp [Finsupp.single_eq_of_ne hki, Finsupp.single_eq_of_ne hkj, hz]

/-- A connected component with two distinct vertices supplies an actual edge. -/
theorem component_exists_adjacent (B : Data Gamma) (d : ℕ) (C : FiberComponent B d)
    (u v : FactorizationFiber B d) (hu : (fiberGraph B d).connectedComponentMk u = C)
    (hv : (fiberGraph B d).connectedComponentMk v = C) (hne : u ≠ v) :
    ∃ w : FactorizationFiber B d, (fiberGraph B d).Adj u w ∧
      (fiberGraph B d).connectedComponentMk w = C := by
  have hr := SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)
  obtain ⟨w, hw⟩ := hr.nonempty_neighborSet_left hne
  exact ⟨w, hw, (SimpleGraph.ConnectedComponent.sound hw.reachable).symm.trans hu⟩

/-- Positive gcd reduction, with the actual lcm degree retained. -/
theorem pair_weight_normalization (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    ∃ g A D : ℕ, 0 < g ∧ 0 < A ∧ 0 < D ∧ A.Coprime D ∧
      m = g * A ∧ n = g * D ∧ Nat.lcm m n = g * (A * D) := by
  let g := Nat.gcd m n
  have hg : 0 < g := Nat.gcd_pos_of_pos_left n hm
  have hA : g * (m/g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hD : g * (n/g) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  refine ⟨g, m/g, n/g, hg, ?_, ?_, Nat.coprime_div_gcd_div_gcd hg,
    hA.symm, hD.symm, ?_⟩
  · nlinarith
  · nlinarith
  · have hl := Nat.gcd_mul_lcm m n
    change g * Nat.lcm m n = m*n at hl
    nlinarith [hA, hD]

/-- An edge in the two-variable component has a primitive pure-power divisor
with a nonzero residual monomial. -/
theorem adjacent_pair_residual (B : Data Gamma) (d : ℕ) (C : FiberComponent B d)
    (i j : Fin 4) (hij : i ≠ j) (hC : componentSupport B d C = {i,j})
    (g A D : ℕ) (hg : 0 < g) (_hA : 0 < A) (hD : 0 < D) (hcop : A.Coprime D)
    (hi : weights B i = g * A) (hj : weights B j = g * D)
    (u v : FactorizationFiber B d) (hu : (fiberGraph B d).connectedComponentMk u = C)
    (hv : (fiberGraph B d).connectedComponentMk v = C) (hadj : (fiberGraph B d).Adj u v)
    (hlt : v.val i < u.val i) :
    ∃ r : Fin 4 →₀ ℕ, r ≠ 0 ∧ u.val = Finsupp.single i D + r := by
  classical
  have hu' := component_pair_decomposition B d C i j hij hC u hu
  have hv' := component_pair_decomposition B d C i j hij hC v hv
  have hwu : u.val i * weights B i + u.val j * weights B j = d := by
    rw [← weight_single, ← weight_single, ← map_add, ← hu']; exact u.property
  have hwv : v.val i * weights B i + v.val j * weights B j = d := by
    rw [← weight_single, ← weight_single, ← map_add, ← hv']; exact v.property
  have heq : A * v.val i + D * v.val j = A * u.val i + D * u.val j := by
    rw [hi, hj] at hwu hwv
    nlinarith
  obtain ⟨t, hti, htj⟩ := two_generator_difference A D (v.val i) (v.val j)
    (u.val i) (u.val j) hD hcop heq
  have hD' : (0 : ℤ) < D := by exact_mod_cast hD
  have hlt' : (v.val i : ℤ) < u.val i := by exact_mod_cast hlt
  have htpos : 1 ≤ t := by nlinarith [hti]
  have hstep : v.val i + D ≤ u.val i := by
    have hmul := mul_le_mul_of_nonneg_left htpos (le_of_lt hD')
    have hc : (v.val i : ℤ) + D ≤ u.val i := by nlinarith [hti]
    exact_mod_cast hc
  let r := Finsupp.single i (u.val i - D) + Finsupp.single j (u.val j)
  have hur : u.val = Finsupp.single i D + r := by
    rw [hu']
    dsimp [r]
    rw [← add_assoc, ← Finsupp.single_add, Nat.add_sub_of_le (by omega : D ≤ u.val i)]
  refine ⟨r, ?_, hur⟩
  obtain ⟨hne, k, hku, hkv⟩ := hadj
  have hk : k = i ∨ k = j := by
    have := (mem_componentSupport B d C k).mpr ⟨u, hu, hku⟩
    simpa [hC] using this
  intro hr
  rcases hk with hki | hkj
  · subst k
    have hz := congrArg (fun f : Fin 4 →₀ ℕ => f i) hr
    simp [r, hij] at hz
    omega
  · subst k
    have hz := congrArg (fun f : Fin 4 →₀ ℕ => f j) hr
    simp [r, hij.symm] at hz
    omega



/-- Connectedness and the primitive relation provide a translation seed. -/
theorem component_pair_residual (B : Data Gamma) (d : ℕ) (C : FiberComponent B d)
    (i j : Fin 4) (hij : i ≠ j) (hC : componentSupport B d C = {i,j})
    (g A D : ℕ) (hg : 0 < g) (hA : 0 < A) (hD : 0 < D) (hcop : A.Coprime D)
    (hi : weights B i = g * A) (hj : weights B j = g * D)
    (u v : FactorizationFiber B d) (hu : (fiberGraph B d).connectedComponentMk u = C)
    (hv : (fiberGraph B d).connectedComponentMk v = C) (hne : u ≠ v) :
    ∃ (w : FactorizationFiber B d) (r : Fin 4 →₀ ℕ),
      (fiberGraph B d).connectedComponentMk w = C ∧ r ≠ 0 ∧
      w.val = Finsupp.single i D + r := by
  obtain ⟨w, hw, hwC⟩ := component_exists_adjacent B d C u v hu hv hne
  have hni : u.val i ≠ w.val i := by
    intro he
    have hu' := component_pair_decomposition B d C i j hij hC u hu
    have hw' := component_pair_decomposition B d C i j hij hC w hwC
    have hd1 := u.property
    have hd2 := w.property
    rw [hu', map_add, weight_single, weight_single] at hd1
    rw [hw', map_add, weight_single, weight_single] at hd2
    have hej : u.val j = w.val j := by
      apply Nat.eq_of_mul_eq_mul_right (weights_positive B j)
      rw [he] at hd1
      omega
    apply hw.1
    apply Subtype.ext
    rw [hu', hw', he, hej]
  rcases lt_or_gt_of_ne hni with hlt | hlt
  · obtain ⟨r, hr, hwr⟩ := adjacent_pair_residual B d C i j hij hC g A D hg hA hD hcop
      hi hj w u hwC hu hw.symm hlt
    exact ⟨w, r, hwC, hr, hwr⟩
  · obtain ⟨r, hr, hur⟩ := adjacent_pair_residual B d C i j hij hC g A D hg hA hD hcop
      hi hj u w hu hwC hw hlt
    exact ⟨u, r, hu, hr, hur⟩

/-- Translation by a nonzero residual forces every small-degree factorization
inside the support of the original actual component. -/
theorem residual_forces_fiber_support (B : Data Gamma) (d L : ℕ) (C : FiberComponent B d)
    (i : Fin 4) (a : ℕ) (hL : L = a * weights B i)
    (u : FactorizationFiber B d) (hu : (fiberGraph B d).connectedComponentMk u = C)
    (r : Fin 4 →₀ ℕ) (hr : r ≠ 0) (hur : u.val = Finsupp.single i a + r)
    (v : FactorizationFiber B L) : v.val.support ⊆ componentSupport B d C := by
  classical
  have hdeg : L + weight B r = d := by
    have := u.property
    rw [hur, map_add, weight_single, ← hL] at this
    exact this
  let z : FactorizationFiber B d := ⟨v.val + r, by rw [map_add, v.property, hdeg]⟩
  obtain ⟨k, hk⟩ : ∃ k : Fin 4, 0 < r k := by
    by_contra hn
    push Not at hn
    apply hr
    ext k
    exact Nat.eq_zero_of_le_zero (hn k)
  have hzk : 0 < z.val k := by simp only [z, Finsupp.add_apply]; omega
  have huk : 0 < u.val k := by rw [hur, Finsupp.add_apply]; omega
  have hzC : (fiberGraph B d).connectedComponentMk z = C :=
    (same_component_of_shared B d z u k hzk huk).trans hu
  intro q hq
  have hqv : 0 < v.val q := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hq)
  apply (mem_componentSupport B d C q).mpr
  exact ⟨z, hzC, by simp only [z, Finsupp.add_apply]; omega⟩

/-- Gcd reduction plus two-generator arithmetic identifies a fiber already
known to use only the pair. -/
theorem pair_supported_lcm_fiber (B : Data Gamma) (i j : Fin 4) (hij : i ≠ j)
    (g A D : ℕ) (hg : 0 < g) (hA : 0 < A) (hD : 0 < D) (hcop : A.Coprime D)
    (hi : weights B i = g * A) (hj : weights B j = g * D)
    (hL : Nat.lcm (weights B i) (weights B j) = g * (A * D))
    (hs : ∀ v : FactorizationFiber B (Nat.lcm (weights B i) (weights B j)),
      v.val.support ⊆ {i,j}) :
    ∀ w : Fin 4 →₀ ℕ, weight B w = Nat.lcm (weights B i) (weights B j) ↔
      w = Finsupp.single i D ∨ w = Finsupp.single j A := by
  classical
  intro w
  constructor
  · intro hw
    have hsw := hs ⟨w, hw⟩
    have hdecomp : w = Finsupp.single i (w i) + Finsupp.single j (w j) := by
      ext k
      by_cases hki : k = i
      · subst k; simp [hij]
      by_cases hkj : k = j
      · subst k; simp [hij.symm]
      have hz : w k = 0 := by
        by_contra hn
        have := hsw (Finsupp.mem_support_iff.mpr hn)
        simp [hki, hkj] at this
      simp [Finsupp.single_eq_of_ne hki, Finsupp.single_eq_of_ne hkj, hz]
    have heq : A * w i + D * w j = A * D := by
      rw [hdecomp, map_add, weight_single, weight_single, hL, hi, hj] at hw
      nlinarith
    rcases two_generator_product_solutions A D (w i) (w j) hA hD hcop heq with h | h
    · left; simpa [h.1, h.2] using hdecomp
    · right; simpa [h.1, h.2] using hdecomp
  · rintro (rfl | rfl)
    · rw [weight_single, hL, hi]; ring
    · rw [weight_single, hL, hj]; ring



/-- The source rigidity conclusion for the full actual lcm fiber. The proof
needs only the stated component data, so no positive-load hypothesis is required. -/
theorem two_variable_component_lcm_fiber (B : Data Gamma) (d : ℕ)
    (C : FiberComponent B d) (i j : Fin 4) (hij : i ≠ j)
    (hC : componentSupport B d C = {i,j})
    (u v : FactorizationFiber B d) (hu : (fiberGraph B d).connectedComponentMk u = C)
    (hv : (fiberGraph B d).connectedComponentMk v = C) (hne : u ≠ v) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      Nat.lcm (weights B i) (weights B j) = a * weights B i ∧
      Nat.lcm (weights B i) (weights B j) = b * weights B j ∧
      (∀ w : Fin 4 →₀ ℕ, weight B w = Nat.lcm (weights B i) (weights B j) ↔
        w = Finsupp.single i a ∨ w = Finsupp.single j b) := by
  obtain ⟨g, A, D, hg, hA, hD, hcop, hi, hj, hL⟩ :=
    pair_weight_normalization (weights B i) (weights B j)
      (weights_positive B i) (weights_positive B j)
  obtain ⟨w, r, hw, hr, hwr⟩ := component_pair_residual B d C i j hij hC
    g A D hg hA hD hcop hi hj u v hu hv hne
  have hLi : Nat.lcm (weights B i) (weights B j) = D * weights B i := by
    rw [hL, hi]; ring
  have hLj : Nat.lcm (weights B i) (weights B j) = A * weights B j := by
    rw [hL, hj]; ring
  refine ⟨D, A, hD, hA, hLi, hLj, ?_⟩
  apply pair_supported_lcm_fiber B i j hij g A D hg hA hD hcop hi hj hL
  intro z
  simpa [hC] using residual_forces_fiber_support B d _ C i D hLi w hw r hr hwr z

/-- A full fiber with precisely two positive pure powers has a disconnected actual
graph and exactly the indicated variable pair. -/
theorem two_pure_power_fiber_is_pair (B : Data Gamma) (L : ℕ) (i j : Fin 4)
    (hij : i ≠ j) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hfull : ∀ w : Fin 4 →₀ ℕ, weight B w = L ↔
      w = Finsupp.single i a ∨ w = Finsupp.single j b) :
    Betti B L ∧ fiberVariables B L = {i,j} := by
  classical
  let u : FactorizationFiber B L := ⟨Finsupp.single i a, (hfull _).mpr (Or.inl rfl)⟩
  let v : FactorizationFiber B L := ⟨Finsupp.single j b, (hfull _).mpr (Or.inr rfl)⟩
  have huv : u ≠ v := by
    intro he
    have := congrArg (fun z : FactorizationFiber B L => z.val i) he
    simp [u, v, hij] at this
    omega
  have hcomp : (fiberGraph B L).connectedComponentMk u ≠
      (fiberGraph B L).connectedComponentMk v := by
    intro he
    have hr := SimpleGraph.ConnectedComponent.exact he
    obtain ⟨w, hw⟩ := hr.nonempty_neighborSet_left huv
    rcases (hfull w.val).mp w.property with hwval | hwval
    · apply hw.1
      apply Subtype.ext
      exact hwval.symm
    · obtain ⟨_, k, hku, hkw⟩ := hw
      have hki : k = i := by
        by_contra hn
        simp [u, Finsupp.single_eq_of_ne hn] at hku
      subst k
      rw [hwval, Finsupp.single_eq_of_ne hij] at hkw
      omega
  constructor
  · apply (betti_iff_nontrivial B L).mpr
    exact ⟨⟨_, _, hcomp⟩⟩
  · ext k
    constructor
    · intro hk
      obtain ⟨z, hz⟩ := (mem_variables B L k).mp hk
      rcases (hfull z.val).mp z.property with hzval | hzval
      · have hki : k = i := by
          by_contra hn
          rw [hzval, Finsupp.single_eq_of_ne hn] at hz
          omega
        simp [hki]
      · have hkj : k = j := by
          by_contra hn
          rw [hzval, Finsupp.single_eq_of_ne hn] at hz
          omega
        simp [hkj]
    · intro hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with hki | hkj
      · subst k
        exact (mem_variables B L i).mpr ⟨u, by simpa [u] using ha⟩
      · subst k
        exact (mem_variables B L j).mpr ⟨v, by simpa [v] using hb⟩

/-- Appendix B two-variable component rigidity, including actual pure-pair
membership. This holds in particular under the Appendix B positive-load assumptions. -/
theorem two_variable_component_rigidity (B : Data Gamma) (d : ℕ)
    (C : FiberComponent B d) (i j : Fin 4) (hij : i ≠ j)
    (hC : componentSupport B d C = {i,j})
    (u v : FactorizationFiber B d) (hu : (fiberGraph B d).connectedComponentMk u = C)
    (hv : (fiberGraph B d).connectedComponentMk v = C) (hne : u ≠ v) :
    Nat.lcm (weights B i) (weights B j) ∈ purePairDegrees B ∧
      fiberVariables B (Nat.lcm (weights B i) (weights B j)) = {i,j} ∧
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
        Nat.lcm (weights B i) (weights B j) = a * weights B i ∧
        Nat.lcm (weights B i) (weights B j) = b * weights B j ∧
        (∀ w : Fin 4 →₀ ℕ, weight B w = Nat.lcm (weights B i) (weights B j) ↔
          w = Finsupp.single i a ∨ w = Finsupp.single j b) := by
  obtain ⟨a, b, ha, hb, hLi, hLj, hfull⟩ :=
    two_variable_component_lcm_fiber B d C i j hij hC u v hu hv hne
  obtain ⟨hbetti, hvars⟩ := two_pure_power_fiber_is_pair B _ i j hij a b ha hb hfull
  refine ⟨(mem_purePairDegrees B _).mpr ⟨hbetti, ?_⟩, hvars,
    a, b, ha, hb, hLi, hLj, hfull⟩
  simp [hvars, hij]



/-- A full two-pure-power fiber occurs at the least common multiple, not at a
higher common multiple. This auxiliary fact supports the later pair normalization. -/
theorem two_pure_power_degree_eq_lcm (B : Data Gamma) (d : ℕ) (i j : Fin 4)
    (hij : i ≠ j) (a b : ℕ) (ha : 0 < a) (_hb : 0 < b)
    (hdi : d = a * weights B i) (hdj : d = b * weights B j)
    (hfull : ∀ w : Fin 4 →₀ ℕ, weight B w = d ↔
      w = Finsupp.single i a ∨ w = Finsupp.single j b) :
    d = Nat.lcm (weights B i) (weights B j) := by
  classical
  obtain ⟨g, A, D, hg, hA, hD, hcop, hi, hj, hL⟩ :=
    pair_weight_normalization (weights B i) (weights B j)
      (weights_positive B i) (weights_positive B j)
  have hLi : Nat.lcm (weights B i) (weights B j) = D * weights B i := by
    rw [hL, hi]; ring
  have hLj : Nat.lcm (weights B i) (weights B j) = A * weights B j := by
    rw [hL, hj]; ring
  have haD : a ≤ D := by
    by_contra hn
    have hDa : D < a := by omega
    let w := Finsupp.single i (a-D) + Finsupp.single j A
    have hw : weight B w = d := by
      dsimp [w]
      rw [map_add, weight_single, weight_single, ← hLj, hLi]
      rw [hdi]
      have := Nat.sub_add_cancel (le_of_lt hDa)
      nlinarith
    rcases (hfull w).mp hw with hwi | hwj
    · have he := congrArg (fun z : Fin 4 →₀ ℕ => z j) hwi
      simp [w, hij.symm] at he
      omega
    · have he := congrArg (fun z : Fin 4 →₀ ℕ => z i) hwj
      simp [w, hij] at he
      omega
  apply Nat.le_antisymm
  · rw [hdi, hLi]
    exact Nat.mul_le_mul_right _ haD
  · have hdp : 0 < d := by rw [hdi]; exact Nat.mul_pos ha (weights_positive B i)
    apply Nat.le_of_dvd hdp
    apply Nat.lcm_dvd
    · exact ⟨a, by simpa [Nat.mul_comm] using hdi⟩
    · exact ⟨b, by simpa [Nat.mul_comm] using hdj⟩

/-- Convenient pure-pair normalization using its actual variable support. -/
theorem purePair_degree_eq_lcm (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (d : ℕ) (hd : d ∈ purePairDegrees B) :
    ∃ i j : Fin 4, i ≠ j ∧ fiberVariables B d = {i,j} ∧
      d = Nat.lcm (weights B i) (weights B j) := by
  obtain ⟨i, j, a, b, hij, ha, hb, hdi, hdj, hvars, hfull⟩ :=
    purePair_fiber_exactly_two_pure_powers B hpos d hd
  exact ⟨i, j, hij, hvars, two_pure_power_degree_eq_lcm B d i j hij a b ha hb hdi hdj hfull⟩

end NS25Lean.L4A


