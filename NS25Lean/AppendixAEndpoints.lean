import NS25Lean.AppendixACompensation

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

def effectivePureExponents (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Set PlanarExponent :=
  {u | Minimal (fun w => monomial w (1 : k) ∈ planarJ F G) u ∧
    monomial u (1 : k) ∉ planarA F G ∧ (u 0 = 0 ∨ u 1 = 0)}

def pureClipIdeal (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Ideal (PlanarPolynomial k) :=
  Ideal.span ((fun u => monomial u (1 : k)) '' effectivePureExponents F G)

/-- Actual colon differs from A only by pure minimal clips when q_fs=1. -/
theorem pure_clip_ideal_formula (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) : planarJ F G = planarA F G ⊔ pureClipIdeal F G := by
  apply le_antisymm
  · rw [exact_colon_ideal]
    apply Ideal.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    have huJ := (exact_colon_monomial F G u).mpr ⟨u, hu, le_rfl⟩
    obtain ⟨w, hwu, hw⟩ := (Set.isPWO_of_wellQuasiOrderedLE
      {z : PlanarExponent | monomial z (1 : k) ∈ planarJ F G}).exists_le_minimal huJ
    apply (planarA F G ⊔ pureClipIdeal F G).mem_of_dvd
      (monomial_one_dvd_monomial_one.mpr hwu)
    by_cases hwA : monomial w (1 : k) ∈ planarA F G
    · exact Ideal.mem_sup_left hwA
    · apply Ideal.mem_sup_right
      apply Ideal.subset_span
      refine ⟨w, ⟨hw, hwA, ?_⟩, rfl⟩
      by_contra hn
      exact no_effective_mixed_of_qfs_one F G hq w hw hwA (by omega) (by omega)
  · apply sup_le (planarA_le_planarJ F G)
    apply Ideal.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    exact hu.1.1

theorem pure_clips_axis_subsingleton (F : InternalFrontend k M h)
    (G : NormalizedSources F) (i : Fin 2) :
    {u ∈ effectivePureExponents F G | u i = 0}.Subsingleton := by
  intro u hu v hv
  have hcmp : u ≤ v ∨ v ≤ u := by
    rcases le_total (u (1 - i)) (v (1 - i)) with hh | hh
    · left; intro j; fin_cases i <;> fin_cases j <;> simp_all
    · right; intro j; fin_cases i <;> fin_cases j <;> simp_all
  rcases hcmp with hle | hle
  · exact le_antisymm hle (hv.1.1.2 hu.1.1.1 hle)
  · exact le_antisymm (hu.1.1.2 hv.1.1.1 hle) hle

theorem old_not_le_minimal_wrap (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s t : Source M.base) (ht : wrap F (G.exponents t) ∈ L3A.minimalExponents F.initial.ideal) :
    ¬ G.exponents s ≤ wrap F (G.exponents t) := by
  intro hle
  exact wrap_not_le_source F G t s (ht.2 (normalized_source_mem_initial F G s) hle)

/-- Exterior maximal D corner to the left of a cut. -/
theorem exterior_y_corner (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) (hu : u ∈ cuts F G) (hp : 0 < u 0) :
    ∃ t ∈ planarMaxD F G, t 0 = u 0 - 1 ∧ u 1 ≤ t 1 := by
  classical
  let seed : PlanarExponent := Finsupp.single 0 (u 0 - 1) + Finsupp.single 1 (u 1)
  have hs0 : seed 0 = u 0 - 1 := by simp [seed]
  have hs1 : seed 1 = u 1 := by simp [seed]
  have hsu : seed ≤ u := by intro i; fin_cases i <;> simp [seed]
  have hsD : seed ∈ planarD F G := by
    intro hsA
    have h := (cuts_common_minimal F G hu).1.2 hsA hsu
    have := h 0
    omega
  obtain ⟨t, hst, ht⟩ := (planarD_finite F G).exists_le_maximal hsD
  have hmax : t ∈ planarMaxD F G := (planarMaxD_iff_maximal F G t).mpr ht
  have htu : t 0 < u 0 := by
    by_contra hn
    apply ht.1
    apply (planarA F G).mem_of_dvd _ (cuts_common_minimal F G hu).1.1
    apply monomial_one_dvd_monomial_one.mpr
    intro i
    fin_cases i
    · change u 0 ≤ t 0; omega
    · change u 1 ≤ t 1; have := hst 1; omega
  exact ⟨t, hmax, by have := hst 0; omega, by have := hst 1; omega⟩

/-- Exterior maximal D corner below a cut, symmetric in the actual planar coordinates. -/
theorem exterior_z_corner (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) (hu : u ∈ cuts F G) (hp : 0 < u 1) :
    ∃ t ∈ planarMaxD F G, t 1 = u 1 - 1 ∧ u 0 ≤ t 0 := by
  classical
  let seed : PlanarExponent := Finsupp.single 0 (u 0) + Finsupp.single 1 (u 1 - 1)
  have hs0 : seed 0 = u 0 := by simp [seed]
  have hs1 : seed 1 = u 1 - 1 := by simp [seed]
  have hsu : seed ≤ u := by intro i; fin_cases i <;> simp [seed]
  have hsD : seed ∈ planarD F G := by
    intro hsA
    have h := (cuts_common_minimal F G hu).1.2 hsA hsu
    have := h 1
    omega
  obtain ⟨t, hst, ht⟩ := (planarD_finite F G).exists_le_maximal hsD
  have hmax : t ∈ planarMaxD F G := (planarMaxD_iff_maximal F G t).mpr ht
  have htu : t 1 < u 1 := by
    by_contra hn
    apply ht.1
    apply (planarA F G).mem_of_dvd _ (cuts_common_minimal F G hu).1.1
    apply monomial_one_dvd_monomial_one.mpr
    intro i
    fin_cases i
    · change u 0 ≤ t 0; have := hst 0; omega
    · change u 1 ≤ t 1; omega
  exact ⟨t, hmax, by have := hst 1; omega, by have := hst 0; omega⟩

theorem minimal_axis_eq (J : Ideal (PlanarPolynomial k)) (w : PlanarExponent) (i : Fin 2) (P : ℕ)
    (hw : Minimal (fun z => monomial z (1 : k) ∈ J) w)
    (hP : Minimal (fun z => monomial z (1 : k) ∈ J) (Finsupp.single i P))
    (hz : w i.rev = 0) : w = Finsupp.single i P := by
  have he : w = Finsupp.single i (w i) := by
    ext j
    fin_cases i <;> fin_cases j <;> simp_all
  rcases le_total (w i) P with hle | hle
  · have hd : w ≤ Finsupp.single i P := by rw [he]; exact Finsupp.single_le_single.mpr hle
    exact le_antisymm hd (hP.2 hw.1 hd)
  · have hd : Finsupp.single i P ≤ w := by nth_rw 1 [he]; exact Finsupp.single_le_single.mpr hle
    exact le_antisymm (hw.2 hP.1 hd) hd

theorem colon_below_two_clips_in_A (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) (P Q : ℕ)
    (hP : Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) (Finsupp.single 0 P))
    (hQ : Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) (Finsupp.single 1 Q))
    (u : PlanarExponent) (hu : monomial u (1 : k) ∈ planarJ F G)
    (hu0 : u 0 < P) (hu1 : u 1 < Q) : monomial u (1 : k) ∈ planarA F G := by
  obtain ⟨w, hwu, hw⟩ := (Set.isPWO_of_wellQuasiOrderedLE
    {z : PlanarExponent | monomial z (1 : k) ∈ planarJ F G}).exists_le_minimal hu
  by_cases hwA : monomial w (1 : k) ∈ planarA F G
  · exact (planarA F G).mem_of_dvd (monomial_one_dvd_monomial_one.mpr hwu) hwA
  have hpure : w 0 = 0 ∨ w 1 = 0 := by
    by_contra hn
    exact no_effective_mixed_of_qfs_one F G hq w hw hwA (by omega) (by omega)
  rcases hpure with hw0 | hw1
  · have he := minimal_axis_eq (planarJ F G) w 1 Q hw hQ hw0
    have hh := hwu 1
    simp only [he, Finsupp.single_eq_same] at hh
    omega
  · have he := minimal_axis_eq (planarJ F G) w 0 P hw hP hw1
    have hh := hwu 0
    simp only [he, Finsupp.single_eq_same] at hh
    omega

theorem full_sources_unique (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s t : Source M.base) (hs : L3A.FullSupport (G.exponents s))
    (ht : L3A.FullSupport (G.exponents t)) : s = t := by
  have hh := (Set.ncard_le_one (L3A.fullSupportGenerators_finite F.initial.ideal)).mp
    F.q_fs_le_one (G.exponents s) ⟨old_minimal_actual F G (Sum.inl s), hs⟩
    (G.exponents t) ⟨old_minimal_actual F G (Sum.inl t), ht⟩
  apply Subtype.ext
  have he := congrArg (weight M.base) hh
  simpa only [G.degree] using he

/-- A pure zero-layer source yielding a clip must lie strictly beyond every
minimal cut wrap on its axis. -/
theorem pure_source_clip_bound (F : InternalFrontend k M h) (G : NormalizedSources F)
    (t s : Source M.base) (ht : wrap F (G.exponents t) ∈ L3A.minimalExponents F.initial.ideal)
    (hsx : G.exponents s (F.normal.perm 0) = 0) (i : Fin 2) (P : ℕ)
    (hs : planarSource F G s = Finsupp.single i (planarTie F i + P)) :
    planarSource F G t i < P := by
  by_contra hn
  apply old_not_le_minimal_wrap F G s t ht
  rw [← cutWrap_source F G t, cutWrap, le_layerExponent_iff]
  refine ⟨by omega, ?_⟩
  change planarSource F G s ≤ _
  rw [hs]
  apply Finsupp.single_le_iff.mpr
  simp only [Finsupp.add_apply]
  omega

end NS25Lean.L3C
