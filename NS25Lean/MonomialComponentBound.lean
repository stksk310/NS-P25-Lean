import NS25Lean.MonomialComponentRigidity
set_option linter.style.header false
noncomputable section
namespace NS25Lean.MonomialPivotStrictness
open ChosenBase L2B L2B2A L2B2A2 L3A L3B L3C L5A1 L5A2R49 L5A2R49First
open MvPolynomial
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

theorem three_components_one_killed_endpoints (M : MultiplicityBase Gamma)
    (h : ℕ) (hh : 0<h) (hc : componentCount M.base h=3) (hk : killedCount M h=1) :
    ∃ (x : Fin 3) (A : ℕ), 0<A ∧ h=A*weights M.base x ∧
      (∀ j, TailPureAt M.base h j) ∧
      ∀ j, j≠x → h-weights M.base j∈M.base.apery := by
  classical
  obtain ⟨C, hall⟩ := Nat.card_eq_one_iff_exists.mp hk
  obtain ⟨u, huC, x, hux, hpred⟩ := C.property
  obtain ⟨z, hpure, hz⟩ := tail_factorization_is_pure_of_three_components M h hh hc u
  have hxz : x = z := by
    by_contra hn
    have he := congrArg (fun v : Fin 3 →₀ ℕ => v x) hpure
    simp only [Finsupp.single_eq_of_ne hn] at he
    omega
  subst z
  have he : h = u.val x * weights M.base x := by
    calc
      h = weight M.base u.val := u.property.symm
      _ = weight M.base (Finsupp.single x (u.val x)) := congrArg _ hpure
      _ = u.val x * weights M.base x := weight_single _ _ _
  refine ⟨x,u.val x,hux,he,three_components_pure_at M h hh hc,?_⟩
  intro j hjx
  obtain ⟨v, hvpure, hvj⟩ := three_components_pure_at M h hh hc j
  have hjH : h - weights M.base j ∈ M.base.H := by
    have hvw := L3B.removed_weight M.base h v j hvj
    have hw : weight M.base (v.val - Finsupp.single j 1) = h - weights M.base j := by omega
    rw [← hw]
    exact L3C.weight_mem_H _ _
  rw [M.base.apery_eq_compl]
  refine ⟨hjH, ?_⟩
  intro hjK
  let E : {D : FiberComponent M.base h // BoundaryKilled M h D} :=
    ⟨(fiberGraph M.base h).connectedComponentMk v, v, rfl, j, hvj, hjK⟩
  have hec : (fiberGraph M.base h).connectedComponentMk v =
      (fiberGraph M.base h).connectedComponentMk u := by
    exact (congrArg Subtype.val (hall E)).trans huC.symm
  let D := (fiberGraph M.base h).connectedComponentMk u
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp (componentSupport_card_eq_one_of_three M h hh hc D)
  have hxr : x = r := by
    have hx := (mem_componentSupport M.base h D x).mpr ⟨u, rfl, hux⟩
    simpa only [hr, Finset.mem_singleton] using hx
  have hjr : j = r := by
    have hj := (mem_componentSupport M.base h D j).mpr ⟨v, hec, hvj⟩
    simpa only [hr, Finset.mem_singleton] using hj
  exact hjx (hjr.trans hxr.symm)

theorem border_axis_residue_zero (k : Type*) [Field k] (D : Data Gamma)
    (h : ℕ) (x : Fin 3) (A a : ℕ) (ha : a ≤ A)
    (he : h = A * weights D x)
    (hmin : Finsupp.single x a ∈ L3A.minimalExponents (D.J k))
    (hlive : ∀ j, j ≠ x → h - weights D j ∈ D.apery) :
    Nat.ModEq D.q.val (weight D (Finsupp.single x a)) 0 := by
  obtain ⟨v, ell, hv, hell, hrep⟩ := minimal_boundary_decomposition k _ _ hmin
  have hapos : 0 < a := by
    by_contra hn
    have hak := (monomial_mem_chosen_iff_boundary k _ _).mp hmin.1
    have haz : a = 0 := by omega
    simp only [haz, Finsupp.single_zero, map_zero] at hak
    have := hak.2.1
    have := D.q_positive
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
      have hvr := L3B.removed_weight D _
        (⟨v, rfl⟩ : FactorizationFiber D (weight D v)) j hvj
      have hww : weight D w = (A - a) * weights D x +
          weight D (v - Finsupp.single j 1) := by simp only [w, map_add, weight_single]
      rw [weight_single] at hrep
      have hAle : a ≤ A := by omega
      have hsplit : A * weights D x =
          (A - a) * weights D x + a * weights D x := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hAle]
      have hdecomp : h - weights D j = weight D w + ell * D.q.val := by
        dsimp at hvr
        omega
      have hl := hlive j hj
      exact (D.apery_eq_compl ▸ hl).2
        (boundary_of_positive_shift _ w _ ell hell hdecomp (D.apery_eq_compl ▸ hl).1)
  rw [hvzero, map_zero, zero_add] at hrep
  rw [hrep]
  simp [Nat.ModEq]


/-- Each excluded pure power contains its genuine minimal pure boundary. -/
theorem pure_minimal_below (k : Type*) [Field k] (D : Data Gamma)
    (x : Fin 3) (A : ℕ) (hK : A*weights D x∈D.K) :
    ∃ a : ℕ, 0<a ∧ a≤A ∧ Finsupp.single x a∈minimalExponents (D.J k) := by
  have hm : monomial (Finsupp.single x A) (1:k)∈D.J k :=
    (monomial_mem_chosen_iff_boundary k D _).mpr (by simpa [weight_single] using hK)
  obtain ⟨u,hle,hmin⟩ := exists_minimal_le (D.J k) _ hm
  have he : u=Finsupp.single x (u x) := by
    ext j
    by_cases hj : j=x
    · subst j; simp
    · have hz := hle j
      simpa only [Finsupp.single_eq_of_ne hj,Nat.le_zero] using hz
  have hp : 0<u x := by
    by_contra hn
    have hu0 : u=0 := by rw [he]; simp [show u x=0 by omega]
    have hk := (monomial_mem_chosen_iff_boundary k D _).mp hmin.1
    rw [hu0,map_zero] at hk
    have := hk.2.1
    have := D.q_positive
    omega
  exact ⟨u x,hp,by simpa using hle x,he ▸ hmin⟩

theorem three_components_zero_killed_endpoints (M : MultiplicityBase Gamma)
    (h : ℕ) (hh : 0<h) (hc : componentCount M.base h=3) (hk : killedCount M h=0) :
    ∃ (x : Fin 3) (A : ℕ), 0<A ∧ h=A*weights M.base x ∧
      ∀ j, j≠x → h-weights M.base j∈M.base.apery := by
  classical
  obtain ⟨u,hu,hupos⟩ := three_components_pure_at M h hh hc 0
  refine ⟨0,u.val 0,hupos,?_,?_⟩
  · calc
      h=weight M.base u.val := u.property.symm
      _=weight M.base (Finsupp.single 0 (u.val 0)) := congrArg _ hu
      _=u.val 0*weights M.base 0 := weight_single _ _ _
  · intro j _
    obtain ⟨v,hv,hvj⟩ := three_components_pure_at M h hh hc j
    have hr := removed_weight M.base h v j hvj
    have hw : weight M.base (v.val-Finsupp.single j 1)=h-weights M.base j := by omega
    rw [M.base.apery_eq_compl]
    refine ⟨hw ▸ weight_mem_H M.base _,?_⟩
    intro hjK
    have hpos : 0<killedCount M h := Nat.card_pos_iff.mpr
      ⟨⟨⟨(fiberGraph M.base h).connectedComponentMk v,v,rfl,j,hvj,hjK⟩⟩,inferInstance⟩
    omega

/-- The actual local contribution is at most one: the only possible larger
signatures (3,0) and (3,1) force a pure residue-zero minimal boundary,
contradicting the fully supported minimal boundary. -/
theorem monomial_contribution_le_one (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (hJ : IsMonomialIdeal k (M.base.J k))
    (g : Exponent) (hg : g∈fullSupportGenerators (M.base.J k)) (h : ℕ) :
    fiberContribution M h≤1 := by
  by_contra hn
  have hp : 0<fiberContribution M h := by omega
  have hle := positive_contribution_le_two M h hp
  have he : fiberContribution M h=2 := by omega
  have hh := (positive_contribution_active M h hp).1
  have hK := positive_degree_boundary k M hJ h hp
  obtain ⟨x,A,hA,hdeg,hlive⟩ : ∃ (x : Fin 3) (A : ℕ), 0<A ∧
      h=A*weights M.base x ∧ ∀ j, j≠x → h-weights M.base j∈M.base.apery := by
    rcases (contribution_two_iff M h).mp he with ⟨hc,hk⟩ | ⟨hc,hk⟩
    · exact three_components_zero_killed_endpoints M h hh hc hk
    · obtain ⟨x,A,hA,hdeg,_,hlive⟩ := three_components_one_killed_endpoints M h hh hc hk
      exact ⟨x,A,hA,hdeg,hlive⟩
  obtain ⟨a,ha,haA,hmin⟩ := pure_minimal_below k M.base x A (hdeg ▸ hK)
  have hr := border_axis_residue_zero k M.base h x A a haA hdeg hmin hlive
  exact pure_residue_zero_excludes_full_support k M.base
    (monomial_apery_unique k M.base hJ) x a ha hmin hr g hg

end NS25Lean.MonomialPivotStrictness
