import NS25Lean.AppendixAColon

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- Actual source cuts selected by minimality of their actual wrap in M. -/
def cuts (F : InternalFrontend k M h) (G : NormalizedSources F) : Set PlanarExponent :=
  {u | ∃ s, 0 < G.exponents s (F.normal.perm 0) ∧
    u = planarSource F G s ∧ wrap F (G.exponents s) ∈ L3A.minimalExponents F.initial.ideal}

def cutWrap (F : InternalFrontend k M h) (u : PlanarExponent) : Fin 3 →₀ ℕ :=
  layerExponent F 0 (planarTie F + u)

theorem cutWrap_source (F : InternalFrontend k M h) (G : NormalizedSources F) (s : Source M.base) :
    cutWrap F (planarSource F G s) = wrap F (G.exponents s) := by
  have he := layerExponent_projection F (wrap F (G.exponents s))
  simpa only [wrap_x_zero, planarProjection_wrap, planarSource, cutWrap] using he

theorem cutWrap_injective (F : InternalFrontend k M h) : Function.Injective (cutWrap F) := by
  intro u v he
  exact add_left_cancel (layerExponent_injective F 0 he)

theorem cutWrap_image (F : InternalFrontend k M h) (G : NormalizedSources F) :
    cutWrap F '' cuts F G = survivingWraps F G := by
  ext w
  constructor
  · rintro ⟨u, ⟨s, hs, rfl, hm⟩, rfl⟩
    rw [cutWrap_source]
    exact ⟨⟨s, hs, rfl⟩, hm⟩
  · rintro ⟨⟨s, hs, rfl⟩, hm⟩
    exact ⟨planarSource F G s, ⟨s, hs, rfl, hm⟩, cutWrap_source F G s⟩

theorem cuts_card_eq_delta1 (F : InternalFrontend k M h) (G : NormalizedSources F) :
    ((cuts F G).ncard : ℤ) = F.delta1 := by
  rw [← Set.ncard_image_of_injective (cuts F G) (cutWrap_injective F), cutWrap_image]
  exact survivingWraps_card_eq_delta1 F G

theorem cuts_finite (F : InternalFrontend k M h) (G : NormalizedSources F) :
    (cuts F G).Finite := by
  apply Set.Finite.of_finite_image (f := cutWrap F) _ (cutWrap_injective F).injOn
  rw [cutWrap_image]
  exact survivingWraps_finite F G

theorem planarProjection_layerExponent (F : InternalFrontend k M h) (r : ℕ) (u : PlanarExponent) :
    planarProjection F (layerExponent F r u) = u := by
  ext i
  exact layerExponent_planar F r u i

theorem cutWrap_le_iff (F : InternalFrontend k M h) (u v : PlanarExponent) :
    cutWrap F u ≤ cutWrap F v ↔ u ≤ v := by
  rw [cutWrap, cutWrap, le_layerExponent_iff, layerExponent_x, planarProjection_layerExponent]
  simp only [le_refl, true_and, add_le_add_iff_left]
theorem cuts_antichain (F : InternalFrontend k M h) (G : NormalizedSources F)
    {u v : PlanarExponent} (hu : u ∈ cuts F G) (hv : v ∈ cuts F G) (hle : u ≤ v) : u = v := by
  obtain ⟨s, hs, rfl, hm⟩ := hu
  obtain ⟨t, ht, rfl, hn⟩ := hv
  have hh : wrap F (G.exponents s) ≤ wrap F (G.exponents t) := by
    rw [← cutWrap_source, ← cutWrap_source]
    exact (cutWrap_le_iff F _ _).mpr hle
  have he := le_antisymm hh (hn.2 hm.1 hh)
  apply cutWrap_injective F
  simpa only [cutWrap_source] using he

theorem cutWrap_mem_actual_iff (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) : monomial (cutWrap F u) (1 : k) ∈ F.initial.ideal ↔
      monomial u (1 : k) ∈ planarJ F G := by
  rw [cutWrap, actual_layer_monomial F G 0 (by have := F.normal.a_ge_two; omega),
    layer_zero_eq_B, planar_colon_monomial, add_comm]

theorem cuts_common_minimal (F : InternalFrontend k M h) (G : NormalizedSources F)
    {u : PlanarExponent} (hu : u ∈ cuts F G) :
    Minimal (fun w => monomial w (1 : k) ∈ planarA F G) u ∧
    Minimal (fun w => monomial w (1 : k) ∈ planarJ F G) u := by
  obtain ⟨s, hs, rfl, hm⟩ := hu
  have hA : monomial (planarSource F G s) (1 : k) ∈ planarA F G :=
    Ideal.subset_span ⟨_, ⟨s, rfl⟩, rfl⟩
  have hJ : Minimal (fun w => monomial w (1 : k) ∈ planarJ F G) (planarSource F G s) := by
    refine ⟨planarA_le_planarJ F G hA, ?_⟩
    intro w hw hle
    have hwM := (cutWrap_mem_actual_iff F G w).mpr hw
    have hh := (cutWrap_le_iff F w (planarSource F G s)).mpr hle
    rw [cutWrap_source] at hh
    have hback := hm.2 hwM hh
    rw [← cutWrap_source F G s] at hback
    exact (cutWrap_le_iff F _ _).mp hback
  exact ⟨⟨hA, fun w hw hle => hJ.2 (planarA_le_planarJ F G hw) hle⟩, hJ⟩

theorem source_full_support_iff (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) : L3A.FullSupport (G.exponents s) ↔
    0 < G.exponents s (F.normal.perm 0) ∧ 0 < planarSource F G s 0 ∧ 0 < planarSource F G s 1 := by
  constructor
  · intro hs
    exact ⟨hs _, hs _, hs _⟩
  · rintro ⟨hx, hy, hz⟩ i
    obtain ⟨j, rfl⟩ := F.normal.perm.surjective i
    fin_cases j
    · exact hx
    · exact hy
    · exact hz

def mixedCuts (F : InternalFrontend k M h) (G : NormalizedSources F) : Set PlanarExponent :=
  {u | u ∈ cuts F G ∧ 0 < u 0 ∧ 0 < u 1}

theorem mixedCuts_card_le_qfs (F : InternalFrontend k M h) (G : NormalizedSources F) :
    (mixedCuts F G).ncard ≤ L3A.q_fs F.initial.ideal := by
  classical
  let chosen (u : mixedCuts F G) : Source M.base := Classical.choose u.property.1
  have chosen_spec (u : mixedCuts F G) := Classical.choose_spec u.property.1
  let f : mixedCuts F G → L3A.fullSupportGenerators F.initial.ideal := fun u =>
    ⟨G.exponents (chosen u), old_minimal_actual F G (Sum.inl (chosen u)),
      (source_full_support_iff F G (chosen u)).mpr
        ⟨(chosen_spec u).1, (chosen_spec u).2.1 ▸ u.property.2.1,
          (chosen_spec u).2.1 ▸ u.property.2.2⟩⟩
  have hf : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    have hu : planarProjection F (f u).val = u.val := (chosen_spec u).2.1.symm
    have hv : planarProjection F (f v).val = v.val := (chosen_spec v).2.1.symm
    rw [← hu, ← hv, he]
  haveI := (L3A.fullSupportGenerators_finite F.initial.ideal).to_subtype
  exact Nat.card_le_card_of_injective f hf
theorem cuts_axis_card_le_one (F : InternalFrontend k M h) (G : NormalizedSources F)
    (i : Fin 2) : {u ∈ cuts F G | u i = 0}.ncard ≤ 1 := by
  apply (Set.ncard_le_one ((cuts_finite F G).subset (fun _ h => h.1))).mpr
  intro u hu v hv
  rcases le_total (u (1 - i)) (v (1 - i)) with hle | hle
  · apply cuts_antichain F G hu.1 hv.1
    intro j
    fin_cases i <;> fin_cases j <;> simp_all
  · symm
    apply cuts_antichain F G hv.1 hu.1
    intro j
    fin_cases i <;> fin_cases j <;> simp_all

theorem cuts_card_bound (F : InternalFrontend k M h) (G : NormalizedSources F) :
    (cuts F G).ncard ≤ 2 + L3A.q_fs F.initial.ideal := by
  have hcover : cuts F G ⊆ {u ∈ cuts F G | u 0 = 0} ∪
      {u ∈ cuts F G | u 1 = 0} ∪ mixedCuts F G := by
    intro u hu
    by_cases hy : u 0 = 0
    · exact Or.inl (Or.inl ⟨hu, hy⟩)
    by_cases hz : u 1 = 0
    · exact Or.inl (Or.inr ⟨hu, hz⟩)
    · exact Or.inr ⟨hu, Nat.pos_of_ne_zero hy, Nat.pos_of_ne_zero hz⟩
  have h0 := (cuts_finite F G).subset (show {u ∈ cuts F G | u 0 = 0} ⊆ cuts F G from fun _ h => h.1)
  have h1 := (cuts_finite F G).subset (show {u ∈ cuts F G | u 1 = 0} ⊆ cuts F G from fun _ h => h.1)
  have hm := (cuts_finite F G).subset (show mixedCuts F G ⊆ cuts F G from fun _ h => h.1)
  have hle := Set.ncard_le_ncard hcover ((h0.union h1).union hm)
  have hu := Set.ncard_union_le ({u ∈ cuts F G | u 0 = 0} ∪ {u ∈ cuts F G | u 1 = 0}) (mixedCuts F G)
  have hv := Set.ncard_union_le {u ∈ cuts F G | u 0 = 0} {u ∈ cuts F G | u 1 = 0}
  have hx := cuts_axis_card_le_one F G 0
  have hy := cuts_axis_card_le_one F G 1
  have hz := mixedCuts_card_le_qfs F G
  omega

theorem delta1_cut_bound (F : InternalFrontend k M h) :
    F.delta1 ≤ 2 + (L3A.q_fs F.initial.ideal : ℤ) ∧ F.delta1 ≤ 3 := by
  obtain ⟨G⟩ := normalized_sources_exist F
  have hc := cuts_card_bound F G
  have he := cuts_card_eq_delta1 F G
  have hq := F.q_fs_le_one
  omega

theorem fullSupportGenerators_eq_sources (F : InternalFrontend k M h) (G : NormalizedSources F) :
    L3A.fullSupportGenerators F.initial.ideal =
      G.exponents '' {s | L3A.FullSupport (G.exponents s)} := by
  ext u
  constructor
  · rintro ⟨hu, hfull⟩
    rw [minimal_eq_old_union_wraps F G] at hu
    rcases hu with ⟨s | t, rfl⟩ | ⟨⟨s, hs, rfl⟩, hm⟩
    · exact ⟨s, hfull, rfl⟩
    · have hz := hfull (F.normal.perm 1)
      simpa [oldExponents, F.normal.alpha_eq, F.normal.perm.injective.eq_iff] using hz
    · have hz := hfull (F.normal.perm 0)
      rw [wrap_x_zero] at hz
      omega
  · rintro ⟨s, hs, rfl⟩
    exact ⟨old_minimal_actual F G (Sum.inl s), hs⟩

theorem qfs_source_count (F : InternalFrontend k M h) (G : NormalizedSources F) :
    L3A.q_fs F.initial.ideal =
      {s | 0 < G.exponents s (F.normal.perm 0) ∧
        0 < planarSource F G s 0 ∧ 0 < planarSource F G s 1}.ncard := by
  rw [L3A.q_fs, fullSupportGenerators_eq_sources F G]
  have hinj : Function.Injective G.exponents := by
    intro s t he
    have hh := oldExponents_injective F G (show oldExponents F G (Sum.inl s) =
      oldExponents F G (Sum.inl t) from he)
    exact Sum.inl.inj hh
  rw [Set.ncard_image_of_injective _ hinj]
  congr 1
  ext s
  exact source_full_support_iff F G s

end NS25Lean.L3C
