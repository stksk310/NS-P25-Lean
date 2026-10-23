import NS25Lean.AppendixAClipClassification
import NS25Lean.AppendixAEndpoints

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- An actual D point below every effective pure clip survives in E. -/
theorem planarE_of_clip_bounds (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) (t : PlanarExponent) (ht : t ∈ planarD F G)
    (hy : ∀ P, EffectiveClip F G 0 P → t 0 < P)
    (hz : ∀ Q, EffectiveClip F G 1 Q → t 1 < Q) : t ∈ planarE F G := by
  intro htJ
  obtain ⟨w, hwt, hw⟩ := (Set.isPWO_of_wellQuasiOrderedLE
    {z : PlanarExponent | monomial z (1 : k) ∈ planarJ F G}).exists_le_minimal htJ
  change Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) w at hw
  have hwA : monomial w (1 : k) ∉ planarA F G := by
    intro hm
    exact ht ((planarA F G).mem_of_dvd (monomial_one_dvd_monomial_one.mpr hwt) hm)
  have hpure : w 0 = 0 ∨ w 1 = 0 := by
    by_contra hn
    exact no_effective_mixed_of_qfs_one F G hq w hw hwA (by omega) (by omega)
  rcases hpure with hw0 | hw1
  · have he : w = Finsupp.single 1 (w 1) := by
      ext j
      fin_cases j <;> simp_all
    have hh := hz (w 1) (by simpa only [EffectiveClip, ← he] using And.intro hw hwA)
    have := hwt 1
    omega
  · have he : w = Finsupp.single 0 (w 0) := by
      ext j
      fin_cases j <;> simp_all
    have hh := hy (w 0) (by simpa only [EffectiveClip, ← he] using And.intro hw hwA)
    have := hwt 0
    omega

theorem exterior_y_survives (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) (u : PlanarExponent) (hu : u ∈ cuts F G)
    (hp : 0 < u 0) (hz : ∀ Q, ¬ EffectiveClip F G 1 Q)
    (hy : ∀ P, EffectiveClip F G 0 P → u 0 < P) :
    ∃ t ∈ planarMaxD F G ∩ planarE F G, t 0 = u 0 - 1 := by
  obtain ⟨t, ht, ht0, _⟩ := exterior_y_corner F G u hu hp
  refine ⟨t, ⟨ht, planarE_of_clip_bounds F G hq t ht.1 ?_ ?_⟩, ht0⟩
  · intro P hP
    have := hy P hP
    omega
  · intro Q hQ
    exact (hz Q hQ).elim

theorem exterior_z_survives (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) (u : PlanarExponent) (hu : u ∈ cuts F G)
    (hp : 0 < u 1) (hy : ∀ P, ¬ EffectiveClip F G 0 P)
    (hz : ∀ Q, EffectiveClip F G 1 Q → u 1 < Q) :
    ∃ t ∈ planarMaxD F G ∩ planarE F G, t 1 = u 1 - 1 := by
  obtain ⟨t, ht, ht1, _⟩ := exterior_z_corner F G u hu hp
  refine ⟨t, ⟨ht, planarE_of_clip_bounds F G hq t ht.1 ?_ ?_⟩, ht1⟩
  · intro P hP
    exact (hy P hP).elim
  · intro Q hQ
    have := hz Q hQ
    omega

/-- Every actual cut in Type I has a surviving exterior corner to its left. -/
theorem typeI_exterior_common_corner (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) (hc : F.normal.c = 0)
    (u : PlanarExponent) (hu : u ∈ cuts F G) :
    ∃ t ∈ planarMaxD F G ∩ planarE F G, t 0 = u 0 - 1 := by
  have hup := no_z_axis_cut_of_qfs_one F G hq u hu
  obtain ⟨t, ht, ht0, _⟩ := exterior_y_corner F G u hu hup
  refine ⟨t, ⟨ht, ?_⟩, ht0⟩
  intro htJ
  obtain ⟨w, hwt, hw⟩ := (Set.isPWO_of_wellQuasiOrderedLE
    {z : PlanarExponent | monomial z (1 : k) ∈ planarJ F G}).exists_le_minimal htJ
  change Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) w at hw
  have hwA : monomial w (1 : k) ∉ planarA F G := by
    intro hm
    exact ht.1 ((planarA F G).mem_of_dvd (monomial_one_dvd_monomial_one.mpr hwt) hm)
  have hpure : w 0 = 0 ∨ w 1 = 0 := by
    by_contra hn
    exact no_effective_mixed_of_qfs_one F G hq w hw hwA (by omega) (by omega)
  rcases hpure with hw0 | hw1
  · have he : w = Finsupp.single 1 (w 1) := by
      ext j
      fin_cases j <;> simp_all
    exact qfs_one_typeI_no_effective_z_clip F G hq hc (w 1)
      (by simpa only [EffectiveClip, ← he] using And.intro hw hwA)
  · have he : w = Finsupp.single 0 (w 0) := by
      ext j
      fin_cases j <;> simp_all
    have hclip : EffectiveClip F G 0 (w 0) := by
      simpa only [EffectiveClip, ← he] using And.intro hw hwA
    obtain ⟨s, hsx, hs⟩ := typeI_effective_y_clip_source F G hc (w 0) hclip
    obtain ⟨v, _, hsrc, hmin⟩ := hu
    have hbound := pure_source_clip_bound F G v s hmin hsx 0 (w 0)
      (by simpa [planarTie] using hs)
    have hwle := hwt 0
    rw [← hsrc] at hbound
    omega

/-- Distinct actual cuts admit opposite strict planar orders. -/
theorem ordered_pair_of_two_cuts (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hc : 1 < (cuts F G).ncard) :
    ∃ u ∈ cuts F G, ∃ v ∈ cuts F G, u 0 < v 0 ∧ v 1 < u 1 := by
  have : Finite (cuts F G) := (cuts_finite F G).to_subtype
  obtain ⟨u, hu, v, hv, hne⟩ := Set.one_lt_ncard_iff_nontrivial.mp hc
  have hnuv : ¬ (u 0 ≤ v 0 ∧ u 1 ≤ v 1) := by
    rintro ⟨h0, h1⟩
    exact hne (cuts_antichain F G hu hv (by intro i; fin_cases i <;> assumption))
  have hnvu : ¬ (v 0 ≤ u 0 ∧ v 1 ≤ u 1) := by
    rintro ⟨h0, h1⟩
    exact hne (cuts_antichain F G hv hu (by intro i; fin_cases i <;> assumption)).symm
  by_cases hlt : u 0 < v 0
  · exact ⟨u, hu, v, hv, hlt, by omega⟩
  · exact ⟨v, hv, u, hu, by omega, by omega⟩

/-- Type-I endpoint survival, including zero, one and two actual cuts. -/
theorem typeI_endpoint_survival (F : InternalFrontend k M h)
    (hq : L3A.q_fs F.initial.ideal = 1) (hc : F.normal.c = 0) :
    F.delta1 ≤ F.delta3 := by
  obtain ⟨G⟩ := normalized_sources_exist F
  have hnonneg := delta3_nonneg F G
  by_cases hd0 : F.delta1 ≤ 0
  · omega
  have hcard := cuts_card_eq_delta1 F G
  by_cases hd1 : F.delta1 ≤ 1
  · have hpos : 0 < (cuts F G).ncard := by omega
    obtain ⟨u, hu⟩ := (Set.ncard_pos (cuts_finite F G)).mp hpos
    obtain ⟨t, ht, _⟩ := typeI_exterior_common_corner F G hq hc u hu
    have h3 := delta3_ge_one_of_common_corner F G ⟨t, ht⟩
    omega
  · obtain ⟨u, hu, v, hv, huv, hvu⟩ := ordered_pair_of_two_cuts F G (by omega)
    obtain ⟨t, ht, ht0⟩ := typeI_exterior_common_corner F G hq hc u hu
    obtain ⟨w, hw, hw0, _⟩ := interior_common_corner F G u v hu hv huv hvu
    have hup := no_z_axis_cut_of_qfs_one F G hq u hu
    have hne : t ≠ w := by
      intro he
      rw [he] at ht0
      omega
    have : Finite {u : PlanarExponent // u ∈ planarMaxD F G ∩ planarE F G} :=
      ((planarMaxD_finite F G).inter_of_left _).to_subtype
    have htwo : 1 < (planarMaxD F G ∩ planarE F G).ncard :=
      Set.one_lt_ncard_iff_nontrivial.mpr ⟨t, ht, w, hw, hne⟩
    have hbound := qfs_one_cut_bound F hq
    rw [artificial_socle_formula F G]
    omega

end NS25Lean.L3C
