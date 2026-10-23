import NS25Lean.AppendixALayers
import NS25Lean.AppendixASourceOrder

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

theorem boundary_mem_initial (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ)
    (hu : weight M.base u ∈ M.base.K) : monomial u (1 : k) ∈ F.initial.ideal :=
  Ideal.subset_span ⟨monomial u 1, boundary_monomial_mem_J k M.base u hu,
    (permutationOrder F.normal.perm).leadingTerm_monomial u 1⟩

/-- The actual initial standard monomials are exactly the slab representatives of Apéry. -/
theorem standard_iff_slab_apery (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : Fin 3 →₀ ℕ) :
    u ∈ L3A.standardExponents F.initial.ideal ↔
      u (F.normal.perm 0) < F.normal.a ∧ weight M.base u ∈ M.base.apery := by
  constructor
  · intro hu
    refine ⟨standard_slab F ⟨u, hu⟩, ?_⟩
    rw [M.base.apery_eq_compl]
    exact ⟨weight_mem_H M.base u, fun hk => hu (boundary_mem_initial F u hk)⟩
  · rintro ⟨hs, ha⟩ hm
    rw [initial_eq_oneWrapIdeal F G, oneWrapIdeal, L3A.monomial_mem_span_iff] at hm
    obtain ⟨v, (hv | ⟨s, rfl⟩) | ⟨s, _, rfl⟩, hvu⟩ := hm
    · have he := Set.mem_singleton_iff.mp hv
      subst v
      have hh := hvu (F.normal.perm 0)
      rw [F.normal.alpha_eq, Finsupp.single_eq_same] at hh
      omega
    · exact boundary_not_below_apery M.base _ u ((G.degree s).symm ▸ s.property.1) ha hvu
    · apply boundary_not_below_apery M.base _ u ?_ ha hvu
      rw [wrap_weight F G]
      exact aperyTail_add_mem M.base.H_le s.property.1
        (M.base.H.nsmul_mem (M.base.tailDegrees (F.normal.perm 0)).property _)

theorem slab_initial_iff_boundary (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : Fin 3 →₀ ℕ) (hu : u (F.normal.perm 0) < F.normal.a) :
    monomial u (1 : k) ∈ F.initial.ideal ↔ weight M.base u ∈ M.base.K := by
  constructor
  · intro hm
    by_contra hn
    have ha : weight M.base u ∈ M.base.apery :=
      M.base.apery_eq_compl.symm ▸ ⟨weight_mem_H M.base u, hn⟩
    exact ((standard_iff_slab_apery F G u).mpr ⟨hu, ha⟩) hm
  · exact boundary_mem_initial F u

theorem slab_factorization_unique (F : InternalFrontend k M h)
    {d : ℕ} (hd : d ∈ M.base.apery) (u v : FactorizationFiber M.base d)
    (hu : u.val (F.normal.perm 0) < F.normal.a)
    (hv : v.val (F.normal.perm 0) < F.normal.a) : u = v := by
  obtain ⟨j, hj⟩ := apery_factorization_difference F d hd u v
  have hp : 0 ≤ j := tieAdmissible_nonneg_of_slab F.normal u.val hu (by
    intro i; rw [← hj i]; exact Int.natCast_nonneg _)
  have hn : 0 ≤ -j := tieAdmissible_nonneg_of_slab F.normal v.val hv (by
    intro i
    have he : (v.val i : ℤ) + -j * tieDelta F.normal i = u.val i := by rw [hj]; ring
    rw [he]; exact Int.natCast_nonneg _)
  have hz : j = 0 := by omega
  apply Subtype.ext
  ext i
  have he := hj i
  simp only [hz, zero_mul, add_zero] at he
  exact_mod_cast he.symm

theorem standard_weight_injective (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Function.Injective (fun u : L3A.standardExponents F.initial.ideal => weight M.base u.val) := by
  intro u v he
  have hu := (standard_iff_slab_apery F G u.val).mp u.property
  have hv := (standard_iff_slab_apery F G v.val).mp v.property
  have hh := slab_factorization_unique F hu.2
    (⟨u.val, rfl⟩ : FactorizationFiber M.base (weight M.base u.val))
    ⟨v.val, he.symm⟩ hu.1 hv.1
  exact Subtype.ext (congrArg
    (fun w : FactorizationFiber M.base (weight M.base u.val) => w.val) hh)

theorem standard_weight_surjective (F : InternalFrontend k M h) (G : NormalizedSources F)
    (d : ℕ) (hd : d ∈ M.base.apery) :
    ∃ u : L3A.standardExponents F.initial.ideal, weight M.base u.val = d := by
  obtain ⟨u, hu, _⟩ := apery_normalized_factorization_chain F d hd
  exact ⟨⟨u.val, (standard_iff_slab_apery F G u.val).mpr
    ⟨hu, u.property.symm ▸ hd⟩⟩, u.property⟩

theorem socle_iff_tail_successors (B : Data Gamma) (d : ℕ) :
    IsSocle Gamma.toAddSubmonoid B.H B.q.val d ↔
      d ∈ B.apery ∧ ∀ i : Fin 3, d + weights B i ∈ B.K := by
  constructor
  · rintro ⟨hH, hK, hs⟩
    refine ⟨B.apery_eq_compl.symm ▸ ⟨hH, hK⟩, fun i => ?_⟩
    exact hs _ (B.tailDegrees i).property (Nat.ne_of_gt (weights_positive B i))
  · rintro ⟨ha, hs⟩
    have hh := B.apery_eq_compl ▸ ha
    refine ⟨hh.1, hh.2, fun e he hn => ?_⟩
    obtain ⟨v⟩ := fiber_nonempty B ⟨e, he⟩
    have hv : v.val ≠ 0 := by
      intro hz
      have hd := v.property
      rw [hz, map_zero] at hd
      exact hn hd.symm
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hv
    have hp : 0 < v.val i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    have hw := removed_weight B e v i hp
    have hm := aperyTail_add_mem B.H_le (hs i)
      (weight_mem_H B (v.val - Finsupp.single i 1))
    have heq : d + weights B i + weight B (v.val - Finsupp.single i 1) = d + e := by omega
    rwa [heq] at hm

def genuineSocleExponents (F : InternalFrontend k M h) : Set (Fin 3 →₀ ℕ) :=
  {u | u ∈ L3A.standardExponents F.initial.ideal ∧
    ∀ i : Fin 3, weight M.base (u + Finsupp.single i 1) ∈ M.base.K}

theorem genuineSocle_subset (F : InternalFrontend k M h) :
    genuineSocleExponents F ⊆ L3A.socleExponents F.initial.ideal := by
  rintro u ⟨hu, hs⟩
  exact ⟨hu, fun i => boundary_mem_initial F _ (hs i)⟩

theorem genuineSocle_weight (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : genuineSocleExponents F) :
    IsSocle Gamma.toAddSubmonoid M.base.H M.base.q.val (weight M.base u.val) := by
  rw [socle_iff_tail_successors]
  refine ⟨((standard_iff_slab_apery F G u.val).mp u.property.1).2, fun i => ?_⟩
  simpa only [map_add, weight_single, one_mul] using u.property.2 i

def genuineSocleEquiv (F : InternalFrontend k M h) (G : NormalizedSources F) :
    genuineSocleExponents F ≃
      {d // IsSocle Gamma.toAddSubmonoid M.base.H M.base.q.val d} := by
  let f := fun u : genuineSocleExponents F =>
    (⟨weight M.base u.val, genuineSocle_weight F G u⟩ :
      {d // IsSocle Gamma.toAddSubmonoid M.base.H M.base.q.val d})
  apply Equiv.ofBijective f
  constructor
  · intro u v he
    have hh : (⟨u.val, u.property.1⟩ : L3A.standardExponents F.initial.ideal) =
        ⟨v.val, v.property.1⟩ := standard_weight_injective F G (congrArg Subtype.val he)
    exact Subtype.ext (congrArg
      (fun w : L3A.standardExponents F.initial.ideal => w.val) hh)
  · intro d
    have hd := (socle_iff_tail_successors M.base d.val).mp d.property
    obtain ⟨u, hu⟩ := standard_weight_surjective F G d.val hd.1
    refine ⟨⟨u.val, u.property, fun i => ?_⟩, Subtype.ext hu⟩
    simpa only [map_add, weight_single, one_mul, hu] using hd.2 i

/-- Genuine normal socles have exactly the original semigroup type. -/
theorem genuineSocle_card (F : InternalFrontend k M h) (G : NormalizedSources F) :
    (genuineSocleExponents F).ncard = Gamma.asRelativeIdeal.idealType := by
  change Nat.card (genuineSocleExponents F) = _
  rw [Nat.card_congr (genuineSocleEquiv F G)]
  exact (natCard_socle_eq_pseudoFrobeniusInt M.base.q_positive M.base.q.property M.base.H_le
    M.base.generatedOver).trans (natCard_pseudoFrobeniusInt_eq_idealType Gamma)

theorem socle_successor_boundary_away_x (F : InternalFrontend k M h)
    (G : NormalizedSources F) (u : L3A.socleExponents F.initial.ideal)
    (i : Fin 3) (hi : i ≠ F.normal.perm 0) :
    weight M.base (u.val + Finsupp.single i 1) ∈ M.base.K := by
  apply (slab_initial_iff_boundary F G _ ?_).mp (u.property.2 i)
  simpa [Finsupp.single_apply, hi, Ne.symm hi] using
    ((standard_iff_slab_apery F G u.val).mp u.property.1).1

theorem socle_genuine_iff_x (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : L3A.socleExponents F.initial.ideal) :
    u.val ∈ genuineSocleExponents F ↔
      weight M.base (u.val + Finsupp.single (F.normal.perm 0) 1) ∈ M.base.K := by
  constructor
  · exact fun hu => hu.2 _
  · intro hx
    refine ⟨u.property.1, fun i => ?_⟩
    by_cases hi : i = F.normal.perm 0
    · simpa [hi] using hx
    · exact socle_successor_boundary_away_x F G u i hi

def artificialSocleExponents (F : InternalFrontend k M h) : Set (Fin 3 →₀ ℕ) :=
  L3A.socleExponents F.initial.ideal \ genuineSocleExponents F

theorem artificial_at_top (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : artificialSocleExponents F) : u.val (F.normal.perm 0) = F.normal.a - 1 := by
  have hs := ((standard_iff_slab_apery F G u.val).mp u.property.1.1).1
  have hn : weight M.base (u.val + Finsupp.single (F.normal.perm 0) 1) ∉ M.base.K :=
    fun hh => u.property.2 ((socle_genuine_iff_x F G ⟨u.val, u.property.1⟩).mpr hh)
  by_contra he
  have hl : (u.val + Finsupp.single (F.normal.perm 0) 1 : Fin 3 →₀ ℕ) (F.normal.perm 0) <
      F.normal.a := by simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega
  exact hn ((slab_initial_iff_boundary F G _ hl).mp (u.property.1.2 _))

theorem weight_top_wrap (F : InternalFrontend k M h) (u : PlanarExponent) :
    weight M.base (layerExponent F F.normal.a u) =
      weight M.base (layerExponent F 0 (u + planarTie F)) := by
  classical
  have he : layerExponent F F.normal.a u =
      F.normal.alpha.val + layerExponent F 0 u := by
    ext j
    obtain ⟨l, rfl⟩ := F.normal.perm.surjective j
    fin_cases l <;> simp [layerExponent, F.normal.alpha_eq, F.normal.perm.injective.eq_iff]
  have hf : layerExponent F 0 (u + planarTie F) =
      F.normal.beta.val + layerExponent F 0 u := by
    ext j
    obtain ⟨l, rfl⟩ := F.normal.perm.surjective j
    fin_cases l <;>
      simp [layerExponent, planarTie, F.normal.beta_eq, F.normal.perm.injective.eq_iff, add_comm]
  rw [he, hf, map_add, map_add, F.normal.alpha.property, F.normal.beta.property]

theorem top_x_boundary_iff_colon (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) :
    weight M.base (layerExponent F (F.normal.a - 1) u +
      Finsupp.single (F.normal.perm 0) 1) ∈ M.base.K ↔
      monomial u (1 : k) ∈ planarJ F G := by
  have ha : F.normal.a - 1 + 1 = F.normal.a := by have := F.normal.a_ge_two; omega
  have hapos : 0 < F.normal.a := by have := F.normal.a_ge_two; omega
  rw [layerExponent_add_x, ha, weight_top_wrap,
    ← slab_initial_iff_boundary F G _ (by simpa using hapos),
    actual_layer_monomial F G 0 hapos, layer_zero_eq_B, ← planar_colon_monomial]

/-- The source's artificial socles are exactly the surviving planar maximal corners. -/
theorem top_artificial_iff (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) :
    layerExponent F (F.normal.a - 1) u ∈ artificialSocleExponents F ↔
      u ∈ planarMaxD F G ∩ planarE F G := by
  constructor
  · rintro ⟨hs, hg⟩
    refine ⟨(top_socle_iff F G u).mp hs, ?_⟩
    intro hj
    apply hg
    exact (socle_genuine_iff_x F G ⟨_, hs⟩).mpr ((top_x_boundary_iff_colon F G u).mpr hj)
  · rintro ⟨hm, he⟩
    have hs := (top_socle_iff F G u).mpr hm
    refine ⟨hs, fun hg => ?_⟩
    exact he ((top_x_boundary_iff_colon F G u).mp
      ((socle_genuine_iff_x F G ⟨_, hs⟩).mp hg))

def artificialSocleEquiv (F : InternalFrontend k M h) (G : NormalizedSources F) :
    {u : PlanarExponent // u ∈ planarMaxD F G ∩ planarE F G} ≃
      artificialSocleExponents F := by
  let f := fun u : {u : PlanarExponent // u ∈ planarMaxD F G ∩ planarE F G} =>
    (⟨layerExponent F (F.normal.a - 1) u.val, (top_artificial_iff F G u.val).mpr u.property⟩ :
      artificialSocleExponents F)
  apply Equiv.ofBijective f
  constructor
  · intro u v he
    exact Subtype.ext (layerExponent_injective F _
      (congrArg (fun w : artificialSocleExponents F => w.val) he))
  · intro u
    have hu : layerExponent F (F.normal.a - 1) (planarProjection F u.val) = u.val := by
      rw [← artificial_at_top F G u, layerExponent_projection]
    refine ⟨⟨planarProjection F u.val, (top_artificial_iff F G _).mp ?_⟩, Subtype.ext hu⟩
    rw [hu]
    exact u.property

/-- Exact formula for the frozen raw integer socle loss, using the actual type. -/
theorem artificial_socle_formula (F : InternalFrontend k M h) (G : NormalizedSources F) :
    F.delta3 = ((planarMaxD F G ∩ planarE F G).ncard : ℤ) := by
  let := F.initial.artinian
  have hfin := L3A.socleExponents_finite F.initial.ideal F.initial.monomial
  have hc := Set.ncard_sdiff_add_ncard_of_subset (genuineSocle_subset F) hfin
  have he : (artificialSocleExponents F).ncard = (planarMaxD F G ∩ planarE F G).ncard :=
    Nat.card_congr (artificialSocleEquiv F G).symm
  change (artificialSocleExponents F).ncard + (genuineSocleExponents F).ncard =
    (L3A.socleExponents F.initial.ideal).ncard at hc
  rw [he, genuineSocle_card F G,
    ← L3A.quotientType_eq_socle_count F.initial.ideal F.initial.monomial] at hc
  unfold InternalFrontend.delta3
  omega

theorem delta3_nonneg (F : InternalFrontend k M h) (G : NormalizedSources F) :
    0 ≤ F.delta3 := by
  rw [artificial_socle_formula F G]
  exact Int.natCast_nonneg _

/-- Literal maximal-element version of the Appendix A formula. -/
theorem artificial_socle_formula_maximal (F : InternalFrontend k M h)
    (G : NormalizedSources F) :
    F.delta3 = (({u : PlanarExponent | Maximal (fun v => v ∈ planarD F G) u} ∩
      planarE F G).ncard : ℤ) := by
  rw [artificial_socle_formula F G]
  congr 2
  ext u
  exact and_congr_left (fun _ => planarMaxD_iff_maximal F G u)

end NS25Lean.L3C
