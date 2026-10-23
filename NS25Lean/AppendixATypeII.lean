import NS25Lean.AppendixAPincer
import NS25Lean.AppendixATypeI

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- Every actual Type-II cut has a surviving exterior endpoint. -/
theorem typeII_exterior_common_corner (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) (hc : 0 < F.normal.c)
    (u : PlanarExponent) (hu : u ∈ cuts F G) : (planarMaxD F G ∩ planarE F G).Nonempty := by
  have hu0 := no_z_axis_cut_of_qfs_one F G hq u hu
  have hu1 := no_y_axis_cut_of_qfs_one_typeII F G hq hc u hu
  obtain ⟨sfull, hsx, hsu, hsm⟩ := hu
  have hfull : L3A.FullSupport (G.exponents sfull) :=
    (source_full_support_iff F G sfull).mpr ⟨hsx, hsu ▸ hu0, hsu ▸ hu1⟩
  have hu' : u ∈ cuts F G := ⟨sfull, hsx, hsu, hsm⟩
  have hyBound (P : ℕ) (hP : EffectiveClip F G 0 P) : u 0 < P := by
    obtain ⟨s, d, ell, hs0, hsrc, _⟩ := effective_y_clip_cross_pure F G sfull hfull P hP hc
    have hh := pure_source_clip_bound F G sfull s hsm hs0 0 P
      (by simpa [planarTie] using hsrc)
    simpa only [← hsu] using hh
  have hzBound (Q : ℕ) (hQ : EffectiveClip F G 1 Q) : u 1 < Q := by
    obtain ⟨s, d, ell, hs0, hsrc, _⟩ := effective_z_clip_cross_pure F G sfull hfull Q hQ
    have hh := pure_source_clip_bound F G sfull s hsm hs0 1 Q
      (by simpa [planarTie] using hsrc)
    simpa only [← hsu] using hh
  by_cases hy : ∃ P, EffectiveClip F G 0 P
  · obtain ⟨P, hP⟩ := hy
    have hz : ∀ Q, ¬ EffectiveClip F G 1 Q := fun Q hQ =>
      typeII_no_simultaneous_clips F G hq hc sfull hfull hsm P Q hP hQ
    obtain ⟨t, ht, _⟩ := exterior_y_survives F G hq u hu' hu0 hz hyBound
    exact ⟨t, ht⟩
  · have hy' : ∀ P, ¬ EffectiveClip F G 0 P := fun P hP => hy ⟨P, hP⟩
    obtain ⟨t, ht, _⟩ := exterior_z_survives F G hq u hu' hu1 hy' hzBound
    exact ⟨t, ht⟩

/-- Type-II endpoint pincer, including zero cuts. -/
theorem typeII_endpoint_pincer (F : InternalFrontend k M h)
    (hq : L3A.q_fs F.initial.ideal = 1) (hc : 0 < F.normal.c) : F.delta1 ≤ F.delta3 := by
  obtain ⟨G⟩ := normalized_sources_exist F
  by_cases hd : F.delta1 ≤ 0
  · have hh := delta3_nonneg F G
    omega
  · have hcard := cuts_card_eq_delta1 F G
    have hpos : 0 < (cuts F G).ncard := by omega
    obtain ⟨u, hu⟩ := (Set.ncard_pos (cuts_finite F G)).mp hpos
    have hcorner := typeII_exterior_common_corner F G hq hc u hu
    have h3 := delta3_ge_one_of_common_corner F G hcorner
    have h1 := typeII_cut_bound F hq hc
    omega

end NS25Lean.L3C
