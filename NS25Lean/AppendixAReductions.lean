import NS25Lean.AppendixAFerrers
import NS25Lean.AppendixAArtificialSocle
import NS25Lean.AppendixADepth

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

theorem full_source_exists_of_qfs_one (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) :
    ∃ s : Source M.base, L3A.FullSupport (G.exponents s) := by
  have hpos : 0 < (L3A.fullSupportGenerators F.initial.ideal).ncard := by
    change 0 < L3A.q_fs F.initial.ideal
    omega
  obtain ⟨u, hu⟩ := (Set.ncard_pos (L3A.fullSupportGenerators_finite F.initial.ideal)).mp hpos
  rw [fullSupportGenerators_eq_sources F G] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  exact ⟨s, hs⟩

theorem no_mixed_cuts_of_qfs_zero (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 0) : mixedCuts F G = ∅ := by
  have hcard := mixedCuts_card_le_qfs F G
  have hf : (mixedCuts F G).Finite := (cuts_finite F G).subset (fun _ hu => hu.1)
  exact (Set.ncard_eq_zero hf).mp (by omega)

/-- A local Ferrers consequence with its explicit mixed-killer premise.
This is not PCR or an added field on the actual frontend. -/
theorem common_corner_of_no_mixed_killer (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u v : PlanarExponent) (hu : u ∈ cuts F G) (hv : v ∈ cuts F G)
    (huy : u 0 < v 0) (hvz : v 1 < u 1)
    (hno : ∀ w : PlanarExponent, Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) w →
      monomial w (1 : k) ∉ planarA F G → 0 < w 0 → 0 < w 1 → False) :
    ∃ t ∈ planarMaxD F G ∩ planarE F G,
      u 0 ≤ t 0 ∧ t 0 < v 0 ∧ v 1 ≤ t 1 ∧ t 1 < u 1 := by
  obtain ⟨t, ht, h0, h1, h2, h3, he | ⟨w, _, hw, hwA, hw0, hw1⟩⟩ :=
    common_corner_or_mixed_killer F G u v hu hv huy hvz
  · exact ⟨t, ⟨ht, he⟩, h0, h1, h2, h3⟩
  · exact (hno w hw hwA hw0 hw1).elim

theorem delta3_ge_one_of_common_corner (F : InternalFrontend k M h) (G : NormalizedSources F)
    (ht : (planarMaxD F G ∩ planarE F G).Nonempty) : 1 ≤ F.delta3 := by
  rw [artificial_socle_formula F G]
  have hf : (planarMaxD F G ∩ planarE F G).Finite := (planarMaxD_finite F G).inter_of_left _
  have hc := (Set.ncard_pos hf).mpr ht
  omega

theorem zero_cut_pcr (F : InternalFrontend k M h) (hd : F.delta1 = 0) :
    F.delta1 + (L3A.q_fs F.initial.ideal : ℤ) - 1 ≤ F.delta3 := by
  obtain ⟨G⟩ := normalized_sources_exist F
  have h3 := delta3_nonneg F G
  have hq := F.q_fs_le_one
  omega

theorem qfs_zero_small_cut_pcr (F : InternalFrontend k M h)
    (hq : L3A.q_fs F.initial.ideal = 0) (hd : F.delta1 ≤ 1) :
    F.delta1 + (L3A.q_fs F.initial.ideal : ℤ) - 1 ≤ F.delta3 := by
  obtain ⟨G⟩ := normalized_sources_exist F
  have h3 := delta3_nonneg F G
  omega

theorem two_axis_cuts_of_qfs_zero (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 0) (hc : 1 < (cuts F G).ncard) :
    ∃ u ∈ cuts F G, ∃ v ∈ cuts F G, u 0 = 0 ∧ v 1 = 0 ∧ 0 < u 1 ∧ 0 < v 0 := by
  have hfin := cuts_finite F G
  haveI := hfin.to_subtype
  obtain ⟨u, hu, v, hv, hne⟩ := (Set.one_lt_ncard_iff_nontrivial.mp hc)
  have hpure (w : PlanarExponent) (hw : w ∈ cuts F G) : w 0 = 0 ∨ w 1 = 0 := by
    by_contra hn
    have hm : w ∈ mixedCuts F G := ⟨hw, by omega, by omega⟩
    rw [no_mixed_cuts_of_qfs_zero F G hq] at hm
    exact hm
  have hsame (i : Fin 2) (hui : u i = 0) (hvi : v i = 0) : False := by
    have hf : {w ∈ cuts F G | w i = 0}.Finite := hfin.subset (fun _ h => h.1)
    exact hne ((Set.ncard_le_one hf).mp (cuts_axis_card_le_one F G i) u ⟨hu, hui⟩ v ⟨hv, hvi⟩)
  have hpositive {s t : PlanarExponent} (hs : s ∈ cuts F G) (ht : t ∈ cuts F G)
      (hst : s ≠ t) (hs0 : s 0 = 0) (ht1 : t 1 = 0) : 0 < s 1 ∧ 0 < t 0 := by
    constructor
    · by_contra hn
      apply hst
      apply cuts_antichain F G hs ht
      intro i
      fin_cases i <;> simp_all
    · by_contra hn
      apply hst
      symm
      apply cuts_antichain F G ht hs
      intro i
      fin_cases i <;> simp_all
  rcases hpure u hu with hu0 | hu1 <;> rcases hpure v hv with hv0 | hv1
  · exact (hsame 0 hu0 hv0).elim
  · exact ⟨u, hu, v, hv, hu0, hv1, hpositive hu hv hne hu0 hv1⟩
  · exact ⟨v, hv, u, hu, hv0, hu1, hpositive hv hu hne.symm hv0 hu1⟩
  · exact (hsame 1 hu1 hv1).elim

theorem normalized_residue_zero_firewall (F : InternalFrontend k M h)
    (G : NormalizedSources F) (s t : Source M.base) (d e : ℕ)
    (hs : s.val = d * M.base.q.val) (ht : t.val = e * M.base.q.val)
    (j : Fin 3) (hsj : 0 < G.exponents s j) (htj : 0 < G.exponents t j)
    (hsx : 0 < G.exponents s (F.normal.perm 0))
    (htx : G.exponents t (F.normal.perm 0) = 0) : False := by
  have he := residue_zero_source_firewall F s t d e hs ht
    ⟨G.exponents s, G.degree s⟩ ⟨G.exponents t, G.degree t⟩ j hsj htj
  subst t
  omega

end NS25Lean.L3C
