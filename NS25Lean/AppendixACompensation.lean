import NS25Lean.AppendixAMixedAxis
import NS25Lean.AppendixAReductions

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

theorem no_mixed_colon_of_positive_residue_source (F : InternalFrontend k M h)
    (G : NormalizedSources F) (s : Source M.base) (d : ℕ)
    (hs : s.val = d * M.base.q.val) (hsx : 0 < G.exponents s (F.normal.perm 0))
    (j : Fin 2) (hsj : 0 < planarSource F G s j)
    (w : PlanarExponent) (hm : Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) w)
    (ha : monomial w (1 : k) ∉ planarA F G) (hy : 0 < w 0) (hz : 0 < w 1) : False := by
  obtain ⟨t, ht0, htw, e, he, ht⟩ := effective_mixed_colon_source F G w hm ha hy hz
  have htj : 0 < planarSource F G t j := by
    rw [htw, Finsupp.add_apply]
    have hwj : 0 < w j := by fin_cases j; exact hy; exact hz
    omega
  exact normalized_residue_zero_firewall F G s t d e hs ht (F.normal.perm j.succ)
    hsj htj hsx ht0

theorem no_effective_mixed_of_qfs_one (F : InternalFrontend k M h)
    (G : NormalizedSources F) (hq : L3A.q_fs F.initial.ideal = 1)
    (w : PlanarExponent) (hm : Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) w)
    (ha : monomial w (1 : k) ∉ planarA F G) (hy : 0 < w 0) (hz : 0 < w 1) : False := by
  obtain ⟨s, hs⟩ := full_source_exists_of_qfs_one F G hq
  obtain ⟨d, hd, he⟩ := full_support_source_residue_zero F s ⟨G.exponents s, G.degree s⟩ hs
  exact no_mixed_colon_of_positive_residue_source F G s d he (hs _) 0 (hs _) w hm ha hy hz

/-- The q_fs=0 branch, including both tie types and zero/one/two cuts. -/
theorem qfs_zero_compensation (F : InternalFrontend k M h)
    (hq : L3A.q_fs F.initial.ideal = 0) : F.delta1 - 1 ≤ F.delta3 := by
  obtain ⟨G⟩ := normalized_sources_exist F
  by_cases hd : F.delta1 ≤ 1
  · have hh := qfs_zero_small_cut_pcr F hq hd
    simpa [hq] using hh
  have hc := cuts_card_eq_delta1 F G
  obtain ⟨u, hu, v, hv, hu0, hv1, hu1, hv0⟩ := two_axis_cuts_of_qfs_zero F G hq (by omega)
  obtain ⟨s, hsx, hsu, hsm⟩ := hu
  have hsy : planarSource F G s 0 = 0 := by simpa [hsu] using hu0
  have hsz : 0 < planarSource F G s 1 := by simpa [hsu] using hu1
  obtain ⟨d, hd, hs⟩ := z_axis_cut_residue_zero F G s hsx hsy hsm
  have hu' : u ∈ cuts F G := ⟨s, hsx, hsu, hsm⟩
  obtain ⟨t, ht, _⟩ := common_corner_of_no_mixed_killer F G u v hu' hv (by omega) (by omega)
    (no_mixed_colon_of_positive_residue_source F G s d hs hsx 1 hsz)
  have h3 := delta3_ge_one_of_common_corner F G ⟨t, ht⟩
  have h1 := (delta1_cut_bound F).1
  omega

theorem no_z_axis_cut_of_qfs_one (F : InternalFrontend k M h)
    (G : NormalizedSources F) (hq : L3A.q_fs F.initial.ideal = 1)
    (u : PlanarExponent) (hu : u ∈ cuts F G) : 0 < u 0 := by
  obtain ⟨s, hsx, rfl, hsm⟩ := hu
  by_contra hn
  have hs0 : planarSource F G s 0 = 0 := by omega
  obtain ⟨d, hd, hs⟩ := z_axis_cut_residue_zero F G s hsx hs0 hsm
  obtain ⟨t, ht⟩ := full_source_exists_of_qfs_one F G hq
  obtain ⟨e, he, hte⟩ := full_support_source_residue_zero F t ⟨G.exponents t, G.degree t⟩ ht
  have heq := residue_zero_source_firewall F s t d e hs hte
    ⟨G.exponents s, G.degree s⟩ ⟨G.exponents t, G.degree t⟩ (F.normal.perm 0) hsx (ht _)
  subst t
  have hp : 0 < planarSource F G s 0 := ht _
  omega

theorem no_y_axis_cut_of_qfs_one_typeII (F : InternalFrontend k M h)
    (G : NormalizedSources F) (hq : L3A.q_fs F.initial.ideal = 1) (hc : 0 < F.normal.c)
    (u : PlanarExponent) (hu : u ∈ cuts F G) : 0 < u 1 := by
  obtain ⟨s, hsx, rfl, hsm⟩ := hu
  by_contra hn
  have hs0 : planarSource F G s 1 = 0 := by omega
  obtain ⟨d, hd, hs⟩ := y_axis_cut_residue_zero F G s hsx hs0 hc hsm
  obtain ⟨t, ht⟩ := full_source_exists_of_qfs_one F G hq
  obtain ⟨e, he, hte⟩ := full_support_source_residue_zero F t ⟨G.exponents t, G.degree t⟩ ht
  have heq := residue_zero_source_firewall F s t d e hs hte
    ⟨G.exponents s, G.degree s⟩ ⟨G.exponents t, G.degree t⟩ (F.normal.perm 0) hsx (ht _)
  subst t
  have hp : 0 < planarSource F G s 1 := ht _
  omega

theorem typeII_cut_bound (F : InternalFrontend k M h)
    (hq : L3A.q_fs F.initial.ideal = 1) (hc : 0 < F.normal.c) : F.delta1 ≤ 1 := by
  obtain ⟨G⟩ := normalized_sources_exist F
  have he : cuts F G = mixedCuts F G := by
    ext u
    exact ⟨fun hu => ⟨hu, no_z_axis_cut_of_qfs_one F G hq u hu,
      no_y_axis_cut_of_qfs_one_typeII F G hq hc u hu⟩, fun hu => hu.1⟩
  have hh := mixedCuts_card_le_qfs F G
  rw [← he] at hh
  have hc := cuts_card_eq_delta1 F G
  omega

theorem qfs_one_cut_bound (F : InternalFrontend k M h)
    (hq : L3A.q_fs F.initial.ideal = 1) : F.delta1 ≤ 2 := by
  obtain ⟨G⟩ := normalized_sources_exist F
  have hcover : cuts F G ⊆ {u ∈ cuts F G | u 1 = 0} ∪ mixedCuts F G := by
    intro u hu
    by_cases hz : u 1 = 0
    · exact Or.inl ⟨hu, hz⟩
    · exact Or.inr ⟨hu, no_z_axis_cut_of_qfs_one F G hq u hu, Nat.pos_of_ne_zero hz⟩
  have hf := cuts_finite F G
  have hle := Set.ncard_le_ncard hcover
    ((hf.subset (fun _ h => h.1)).union (hf.subset (fun _ h => h.1)))
  have hsum := Set.ncard_union_le {u ∈ cuts F G | u 1 = 0} (mixedCuts F G)
  have haxis := cuts_axis_card_le_one F G 1
  have hmix := mixedCuts_card_le_qfs F G
  have he := cuts_card_eq_delta1 F G
  omega

/-- Every ordered cut interval contains an actual surviving maximal corner.
In particular this applies to consecutive cuts; disjoint intervals give distinct points. -/
theorem interior_common_corner (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u v : PlanarExponent) (hu : u ∈ cuts F G) (hv : v ∈ cuts F G)
    (huy : u 0 < v 0) (hvz : v 1 < u 1) :
    ∃ t ∈ planarMaxD F G ∩ planarE F G,
      u 0 ≤ t 0 ∧ t 0 < v 0 ∧ v 1 ≤ t 1 ∧ t 1 < u 1 := by
  apply common_corner_of_no_mixed_killer F G u v hu hv huy hvz
  by_cases hq : L3A.q_fs F.initial.ideal = 1
  · exact no_effective_mixed_of_qfs_one F G hq
  · have hz : L3A.q_fs F.initial.ideal = 0 := by have := F.q_fs_le_one; omega
    have hnot : u ∉ mixedCuts F G := by rw [no_mixed_cuts_of_qfs_zero F G hz]; simp
    have hu0 : u 0 = 0 := by
      by_contra hn
      exact hnot ⟨hu, Nat.pos_of_ne_zero hn, by omega⟩
    obtain ⟨s, hsx, hsu, hsm⟩ := hu
    have hsy : planarSource F G s 0 = 0 := by simpa [hsu] using hu0
    have hsz : 0 < planarSource F G s 1 := by rw [← hsu]; omega
    obtain ⟨d, hd, hs⟩ := z_axis_cut_residue_zero F G s hsx hsy hsm
    exact no_mixed_colon_of_positive_residue_source F G s d hs hsx 1 hsz

theorem disjoint_cut_interval_corners (u v w t t' : PlanarExponent)
    (ht : t 0 < v 0) (ht' : v 0 ≤ t' 0) : t ≠ t' := by
  intro he
  rw [he] at ht
  omega

end NS25Lean.L3C
