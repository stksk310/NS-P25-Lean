import NS25Lean.P2DAResidueR49

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2R49
open ChosenBase L2B L5A1 MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem three_components_pure_at (M : MultiplicityBase Gamma) (h : ℕ)
    (hh : 0 < h) (hc : componentCount M.base h = 3) (j : Fin 3) : TailPureAt M.base h j := by
  classical
  let role : FiberComponent M.base h → Fin 3 := fun C =>
    Classical.choose (Finset.card_eq_one.mp (componentSupport_card_eq_one_of_three M h hh hc C))
  have hs (C : FiberComponent M.base h) : componentSupport M.base h C = {role C} :=
    Classical.choose_spec (Finset.card_eq_one.mp (componentSupport_card_eq_one_of_three M h hh hc C))
  have hi : Function.Injective role := by
    intro C E he
    apply components_eq_of_shared_support M.base h C E (role C)
    · simp [hs C]
    · rw [he]; simp [hs E]
  have hcard : Nat.card (FiberComponent M.base h) = Nat.card (Fin 3) := by
    simpa [componentCount] using hc
  obtain ⟨C, hC⟩ := ((Nat.bijective_iff_injective_and_card role).mpr ⟨hi, hcard⟩).2 j
  obtain ⟨u, hu⟩ := C.exists_rep
  have hp := tail_fiber_eq_single_of_componentSupport M.base h C j
    (by simpa only [hC] using hs C) u hu
  refine ⟨u, hp, ?_⟩
  have he := u.property
  rw [hp, weight_single] at he
  have := weights_positive M.base j
  nlinarith

/-- The actual killed pure axis and both actual live predecessors. -/
theorem sectorA_actual_endpoints (P : P2Data Gamma) (hA : SectorA P.M) :
    ∃ h : ℕ, ∃ x : Fin 3, ∃ A : ℕ,
      0 < A ∧ h = A * weights P.M.base x ∧
      h - weights P.M.base x ∈ P.M.base.K ∧
      (∀ j, TailPureAt P.M.base h j) ∧
      ∀ j, j ≠ x → h - weights P.M.base j ∈ P.M.base.apery := by
  classical
  rcases hA with ⟨h, hs, hc, hk⟩
  have hh := (positive_contribution_active P.M h
    ((mem_positiveDegrees P.M h).mp (by simp [hs]))).1
  obtain ⟨C, hall⟩ := Nat.card_eq_one_iff_exists.mp hk
  obtain ⟨u, huC, x, hux, hpred⟩ := C.property
  obtain ⟨z, hpure, hz⟩ := tail_factorization_is_pure_of_three_components P.M h hh hc u
  have hxz : x = z := by
    by_contra hn
    have he := congrArg (fun v : Fin 3 →₀ ℕ => v x) hpure
    simp only [Finsupp.single_eq_of_ne hn] at he
    omega
  subst z
  have he : h = u.val x * weights P.M.base x := by
    calc
      h = weight P.M.base u.val := u.property.symm
      _ = weight P.M.base (Finsupp.single x (u.val x)) := congrArg _ hpure
      _ = u.val x * weights P.M.base x := weight_single _ _ _
  refine ⟨h, x, u.val x, hux, he, hpred, three_components_pure_at P.M h hh hc, ?_⟩
  intro j hjx
  obtain ⟨v, hvpure, hvj⟩ := three_components_pure_at P.M h hh hc j
  have hjH : h - weights P.M.base j ∈ P.M.base.H := by
    have hvw := L3B.removed_weight P.M.base h v j hvj
    have hw : weight P.M.base (v.val - Finsupp.single j 1) = h - weights P.M.base j := by omega
    rw [← hw]
    exact L3C.weight_mem_H _ _
  rw [P.M.base.apery_eq_compl]
  refine ⟨hjH, ?_⟩
  intro hjK
  let E : {D : FiberComponent P.M.base h // BoundaryKilled P.M h D} :=
    ⟨(fiberGraph P.M.base h).connectedComponentMk v, v, rfl, j, hvj, hjK⟩
  have hec : (fiberGraph P.M.base h).connectedComponentMk v =
      (fiberGraph P.M.base h).connectedComponentMk u := by
    exact (congrArg Subtype.val (hall E)).trans huC.symm
  let D := (fiberGraph P.M.base h).connectedComponentMk u
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (componentSupport_card_eq_one_of_three P.M h hh hc D)
  have hxr : x = r := by
    have hx := (mem_componentSupport P.M.base h D x).mpr ⟨u, rfl, hux⟩
    simpa only [hr, Finset.mem_singleton] using hx
  have hjr : j = r := by
    have hj := (mem_componentSupport P.M.base h D j).mpr ⟨v, hec, hvj⟩
    simpa only [hr, Finset.mem_singleton] using hj
  exact hjx (hjr.trans hxr.symm)

/-- A minimal pure boundary below the killed predecessor. -/
theorem sectorA_minimal_killed_axis (k : Type*) [Field k] (P : P2Data Gamma)
    (h : ℕ) (x : Fin 3) (A : ℕ) (hA : 0 < A)
    (he : h = A * weights P.M.base x)
    (hk : h - weights P.M.base x ∈ P.M.base.K) :
    ∃ a : ℕ, 0 < a ∧ a ≤ A - 1 ∧
      Finsupp.single x a ∈ L3A.minimalExponents (P.J k) := by
  have hpw : weight P.M.base (Finsupp.single x (A - 1)) = h - weights P.M.base x := by
    rw [weight_single, he, Nat.sub_mul]; simp
  have hm : monomial (Finsupp.single x (A - 1)) (1 : k) ∈ P.J k :=
    (monomial_mem_chosen_iff_boundary k _ _).mpr (hpw.symm ▸ hk)
  obtain ⟨u, hule, humin⟩ := L3A.exists_minimal_le (P.J k) _ hm
  have hupure : u = Finsupp.single x (u x) := by
    ext j
    by_cases hj : j = x
    · subst j; simp
    · have := hule j
      simpa only [Finsupp.single_eq_of_ne hj, Nat.le_zero] using this
  have hupos : 0 < u x := by
    by_contra hn
    have huz : u = 0 := by rw [hupure]; simp [show u x = 0 by omega]
    have huk := (monomial_mem_chosen_iff_boundary k _ _).mp humin.1
    rw [huz, map_zero] at huk
    have := huk.2.1
    have := P.M.base.q_positive
    omega
  exact ⟨u x, hupos, by have := hule x; simpa using this, hupure ▸ humin⟩

/-- Both transverse coefficients vanish, using the two distinct live predecessors. -/
theorem sectorA_killed_axis_residue_zero (k : Type*) [Field k] (P : P2Data Gamma)
    (h : ℕ) (x : Fin 3) (A a : ℕ) (ha : a ≤ A - 1)
    (he : h = A * weights P.M.base x)
    (hmin : Finsupp.single x a ∈ L3A.minimalExponents (P.J k))
    (hlive : ∀ j, j ≠ x → h - weights P.M.base j ∈ P.M.base.apery) :
    Nat.ModEq P.M.base.q.val (weight P.M.base (Finsupp.single x a)) 0 := by
  obtain ⟨v, ell, hv, hell, hrep⟩ := minimal_boundary_decomposition k _ _ hmin
  have hapos : 0 < a := by
    by_contra hn
    have hak := (monomial_mem_chosen_iff_boundary k _ _).mp hmin.1
    have haz : a = 0 := by omega
    simp only [haz, Finsupp.single_zero, map_zero] at hak
    have := hak.2.1
    have := P.M.base.q_positive
    omega
  have hvzero : v = 0 := by
    ext j
    by_cases hj : j = x
    · subst j
      exact minimal_boundary_support_complement k _ _ v hmin ell hell hrep x
        (by simpa using hapos)
    · by_contra hn
      have hvj : 0 < v j := Nat.pos_of_ne_zero hn
      let w := Finsupp.single x (A - a) + (v - Finsupp.single j 1)
      have hvr := L3B.removed_weight P.M.base _
        (⟨v, rfl⟩ : FactorizationFiber P.M.base (weight P.M.base v)) j hvj
      have hww : weight P.M.base w = (A - a) * weights P.M.base x +
          weight P.M.base (v - Finsupp.single j 1) := by simp only [w, map_add, weight_single]
      rw [weight_single] at hrep
      have hAle : a ≤ A := by omega
      have hsplit : A * weights P.M.base x =
          (A - a) * weights P.M.base x + a * weights P.M.base x := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hAle]
      have hdecomp : h - weights P.M.base j = weight P.M.base w + ell * P.M.base.q.val := by
        dsimp at hvr
        omega
      have hl := hlive j hj
      exact (P.M.base.apery_eq_compl ▸ hl).2
        (boundary_of_positive_shift _ w _ ell hell hdecomp (P.M.base.apery_eq_compl ▸ hl).1)
  rw [hvzero, map_zero, zero_add] at hrep
  rw [hrep]
  simp [Nat.ModEq]

theorem sectorA_q_fs_zero (k : Type*) [Field k] (P : P2Data Gamma) (hA : SectorA P.M) :
    L3A.q_fs (P.J k) = 0 := by
  obtain ⟨h, x, A, hApos, he, hk, _, hlive⟩ := sectorA_actual_endpoints P hA
  obtain ⟨a, ha, hab, hmin⟩ := sectorA_minimal_killed_axis k P h x A hApos he hk
  have hr := sectorA_killed_axis_residue_zero k P h x A a hab he hmin hlive
  change (L3A.fullSupportGenerators (P.J k)).ncard = 0
  rw [Set.ncard_eq_zero (hs := L3A.fullSupportGenerators_finite _)]
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hg
  exact pure_residue_zero_excludes_full_support k _ (sectorA_apery_unique P hA) x a ha hmin hr g hg

theorem sectorA_type_le_sourceCount (P : P2Data Gamma) (hA : SectorA P.M) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have hbound := L3A.support_refined_monomial_type_bound
    (L3A.chosenArtinianMonomial P.M.base MonomialOrder.degLex (sectorA_monomial P hA ℚ))
  change L3A.quotientType (P.J ℚ) ≤ L3A.mu (P.J ℚ) + L3A.q_fs (P.J ℚ) - 2 at hbound
  rw [L3A.chosen_type_eq (k := ℚ), L3A.chosen_mu_eq (k := ℚ), sectorA_q_fs_zero ℚ P hA] at hbound
  have := p2_rho_eq_sourceCount_add_two P
  omega

end NS25Lean.L5A2R49
