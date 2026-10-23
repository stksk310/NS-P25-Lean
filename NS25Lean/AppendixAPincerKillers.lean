import NS25Lean.AppendixAEndpoints

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- Actual killer classification of the residue-zero bottom monomial.
Only the full-support wrap can divide it; all old zero-layer and axis-wrap
possibilities contradict the actual source/colon/clip interfaces. -/
theorem pincer_killer_classification (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) (sfull : Source M.base)
    (hfull : L3A.FullSupport (G.exponents sfull)) (P Q : ℕ) (hPpos : 0 < P) (hQpos : 0 < Q)
    (hP : Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) (Finsupp.single 0 P))
    (hQ : Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) (Finsupp.single 1 Q))
    (hPA : monomial (Finsupp.single 0 P) (1 : k) ∉ planarA F G)
    (hQA : monomial (Finsupp.single 1 Q) (1 : k) ∉ planarA F G)
    (u : PlanarExponent) (hu : monomial (layerExponent F 0 u) (1 : k) ∈ F.initial.ideal)
    (hu0 : u 0 < F.normal.b + P) (hu1 : u 1 < F.normal.c + Q) :
    planarTie F + planarSource F G sfull ≤ u := by
  have hpure_in_A_false (w : PlanarExponent) (hwA : monomial w (1 : k) ∈ planarA F G)
      (hw0 : w 0 < P) (hw1 : w 1 < Q) (hpure : w 0 = 0 ∨ w 1 = 0) : False := by
    rcases hpure with hy | hz
    · apply hQA
      apply (planarA F G).mem_of_dvd _ hwA
      apply monomial_one_dvd_monomial_one.mpr
      intro i
      fin_cases i <;> simp_all <;> omega
    · apply hPA
      apply (planarA F G).mem_of_dvd _ hwA
      apply monomial_one_dvd_monomial_one.mpr
      intro i
      fin_cases i <;> simp_all <;> omega
  rw [initial_eq_oneWrapIdeal F G, oneWrapIdeal, L3A.monomial_mem_span_iff] at hu
  obtain ⟨w, (hw | ⟨s, rfl⟩) | ⟨s, hsx, rfl⟩, hle⟩ := hu
  · have he := Set.mem_singleton_iff.mp hw
    subst w
    have hh := hle (F.normal.perm 0)
    rw [F.normal.alpha_eq, Finsupp.single_eq_same, layerExponent_x] at hh
    have := F.normal.a_ge_two
    omega
  · have hh := (le_layerExponent_iff F _ 0 u).mp hle
    have hsx : G.exponents s (F.normal.perm 0) = 0 := by omega
    have hsrc : planarSource F G s ≤ u := hh.2
    let core := planarSource F G s - planarTie F
    have hcoreJ : monomial core (1 : k) ∈ planarJ F G :=
      (exact_colon_monomial F G core).mpr ⟨core, Or.inr ⟨s, hsx, rfl⟩, le_rfl⟩
    have hcore0 : core 0 < P := by
      have := hsrc 0
      simp only [core, Finsupp.tsub_apply, planarTie, Finsupp.add_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), add_zero]
      omega
    have hcore1 : core 1 < Q := by
      have := hsrc 1
      simp only [core, Finsupp.tsub_apply, planarTie, Finsupp.add_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), zero_add]
      omega
    have hcoreA := colon_below_two_clips_in_A F G hq P Q hP hQ core hcoreJ hcore0 hcore1
    by_cases hpure : core 0 = 0 ∨ core 1 = 0
    · exact (hpure_in_A_false core hcoreA hcore0 hcore1 hpure).elim
    have hsum : planarSource F G s = planarTie F + core := by
      ext i
      have hcpos : 0 < core i := by
        fin_cases i
        · change 0 < core 0; omega
        · change 0 < core 1; omega
      have hci : core i = planarSource F G s i - planarTie F i := rfl
      change planarSource F G s i = planarTie F i + core i
      omega
    obtain ⟨v, ⟨t, rfl⟩, htc⟩ := (planar_monomial_mem_span_iff _ core).mp hcoreA
    exfalso
    apply wrap_not_le_source F G t s
    have hg : layerExponent F 0 (planarSource F G s) = G.exponents s := by
      simpa only [hsx, planarSource] using layerExponent_projection F (G.exponents s)
    rw [← hg, le_layerExponent_iff, wrap_x_zero, planarProjection_wrap]
    refine ⟨le_rfl, ?_⟩
    change planarTie F + planarSource F G t ≤ planarSource F G s
    rw [hsum]
    exact add_le_add le_rfl htc
  · have hh := (le_layerExponent_iff F _ 0 u).mp hle
    have hsrc : planarTie F + planarSource F G s ≤ u := by
      simpa only [planarProjection_wrap, planarSource] using hh.2
    have hs0 : planarSource F G s 0 < P := by
      have := hsrc 0
      simp [planarTie] at this
      omega
    have hs1 : planarSource F G s 1 < Q := by
      have := hsrc 1
      simp [planarTie] at this
      omega
    have hsA : monomial (planarSource F G s) (1 : k) ∈ planarA F G :=
      Ideal.subset_span ⟨_, ⟨s, rfl⟩, rfl⟩
    have hsmixed : 0 < planarSource F G s 0 ∧ 0 < planarSource F G s 1 := by
      by_contra hn
      exact hpure_in_A_false _ hsA hs0 hs1 (by omega)
    have he := full_sources_unique F G s sfull
      ((source_full_support_iff F G s).mpr ⟨hsx, hsmixed⟩) hfull
    simpa [he] using hsrc

end NS25Lean.L3C
