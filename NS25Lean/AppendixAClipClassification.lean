import NS25Lean.AppendixAMixedAxis
import NS25Lean.AppendixAReductions

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

def EffectiveClip (F : InternalFrontend k M h) (G : NormalizedSources F)
    (i : Fin 2) (P : ℕ) : Prop :=
  Minimal (fun u => monomial u (1 : k) ∈ planarJ F G) (Finsupp.single i P) ∧
    monomial (Finsupp.single i P) (1 : k) ∉ planarA F G

theorem planar_other_ne (i : Fin 2) : i.rev ≠ i := by fin_cases i <;> decide

theorem layer_zero_tie (F : InternalFrontend k M h) :
    layerExponent F 0 (planarTie F) = F.normal.beta.val := by
  classical
  ext j
  obtain ⟨l, rfl⟩ := F.normal.perm.surjective j
  fin_cases l <;> simp [layerExponent, planarTie, F.normal.beta_eq,
    F.normal.perm.injective.eq_iff]

theorem planarJ_unit_not_mem (F : InternalFrontend k M h) (G : NormalizedSources F) :
    monomial (0 : PlanarExponent) (1 : k) ∉ planarJ F G := by
  intro hu
  have hm := (cutWrap_mem_actual_iff F G 0).mpr hu
  have he : cutWrap F 0 = F.normal.beta.val := by
    simpa only [cutWrap, add_zero] using layer_zero_tie F
  rw [he] at hm
  apply ((standard_iff_slab_apery F G F.normal.beta.val).mpr ?_) hm
  constructor
  · simp [F.normal.beta_eq, F.normal.perm.injective.eq_iff]
    have := F.normal.a_ge_two
    omega
  · rw [F.normal.beta.property]
    exact F.normal.apery

theorem effectiveClip_positive (F : InternalFrontend k M h) (G : NormalizedSources F)
    {i : Fin 2} {P : ℕ} (hc : EffectiveClip F G i P) : 0 < P := by
  by_contra hn
  have he : P = 0 := by omega
  have hh := hc.1.1
  rw [he, Finsupp.single_zero] at hh
  exact planarJ_unit_not_mem F G hh

theorem effectiveClip_zero_source (F : InternalFrontend k M h) (G : NormalizedSources F)
    {i : Fin 2} {P : ℕ} (hc : EffectiveClip F G i P) :
    ∃ s : Source M.base, G.exponents s (F.normal.perm 0) = 0 ∧
      planarSource F G s - planarTie F = Finsupp.single i P := by
  obtain ⟨w, ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩, hle⟩ :=
    (exact_colon_monomial F G _).mp hc.1.1
  · have hm : monomial (planarSource F G s) (1 : k) ∈ planarA F G :=
      Ideal.subset_span ⟨_, ⟨s, rfl⟩, rfl⟩
    exact (hc.2 ((planarA F G).mem_of_dvd (monomial_one_dvd_monomial_one.mpr hle) hm)).elim
  · have hw : monomial (planarSource F G s - planarTie F) (1 : k) ∈ planarJ F G :=
      (exact_colon_monomial F G _).mpr ⟨_, Or.inr ⟨s, hs, rfl⟩, le_rfl⟩
    exact ⟨s, hs, le_antisymm hle (hc.1.2 hw hle)⟩

/-- A slab pure-axis target cannot be killed by a wrap with positive opposite coordinate. -/
theorem pure_target_mem_A (F : InternalFrontend k M h) (G : NormalizedSources F)
    (i : Fin 2) (P r : ℕ) (hr : r < F.normal.a)
    (hv : 0 < planarTie F i.rev)
    (hm : monomial (layerExponent F r (Finsupp.single i P)) (1 : k) ∈ F.initial.ideal) :
    monomial (Finsupp.single i P) (1 : k) ∈ planarA F G := by
  classical
  rw [actual_layer_monomial F G r hr, layerIdeal, planar_monomial_mem_span_iff] at hm
  obtain ⟨w, ⟨s, _, rfl⟩ | ⟨s, _, rfl⟩, hle⟩ := hm
  · exact (planar_monomial_mem_span_iff _ _).mpr ⟨_, ⟨s, rfl⟩, hle⟩
  · have hh := hle i.rev
    simp only [Finsupp.add_apply, Finsupp.single_apply,
      ite_eq_right (planar_other_ne i).symm] at hh
    omega

theorem zero_layer_not_residue_zero (F : InternalFrontend k M h) (G : NormalizedSources F)
    (sfull : Source M.base) (hfull : L3A.FullSupport (G.exponents sfull))
    (s : Source M.base) (hs : G.exponents s (F.normal.perm 0) = 0)
    (d : ℕ) (hd : s.val = d * M.base.q.val) : False := by
  obtain ⟨df, _, hdf⟩ := full_support_source_residue_zero F sfull
    ⟨G.exponents sfull, G.degree sfull⟩ hfull
  obtain ⟨j, hj⟩ := source_factorization_nonzero M.base s ⟨G.exponents s, G.degree s⟩
  exact normalized_residue_zero_firewall F G sfull s df d hdf hd j
    (hfull j) hj (hfull _) hs

theorem weight_axes (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ) (i : Fin 2) :
    weight M.base u = u (F.normal.perm 0) * weights M.base (F.normal.perm 0) +
      planarProjection F u i * weights M.base (F.normal.perm i.succ) +
      planarProjection F u i.rev * weights M.base (F.normal.perm i.rev.succ) := by
  have he := congrArg (weight M.base) (exponent_three_coordinates F.normal.perm u)
  simp only [map_add, weight_single] at he
  fin_cases i
  · change weight M.base u = u (F.normal.perm 0) * weights M.base (F.normal.perm 0) +
      u (F.normal.perm 1) * weights M.base (F.normal.perm 1) +
      u (F.normal.perm 2) * weights M.base (F.normal.perm 2)
    omega
  · change weight M.base u = u (F.normal.perm 0) * weights M.base (F.normal.perm 0) +
      u (F.normal.perm 2) * weights M.base (F.normal.perm 2) +
      u (F.normal.perm 1) * weights M.base (F.normal.perm 1)
    omega

theorem weight_pure_layer (F : InternalFrontend k M h) (r P : ℕ) (i : Fin 2) :
    weight M.base (layerExponent F r (Finsupp.single i P)) =
      r * weights M.base (F.normal.perm 0) + P * weights M.base (F.normal.perm i.succ) := by
  rw [weight_axes F _ i, layerExponent_x, planarProjection_layerExponent]
  simp [planar_other_ne i]

theorem tie_degree_axes (F : InternalFrontend k M h) (i : Fin 2) :
    F.normal.a * weights M.base (F.normal.perm 0) =
      planarTie F i * weights M.base (F.normal.perm i.succ) +
      planarTie F i.rev * weights M.base (F.normal.perm i.rev.succ) := by
  have he := F.normal.degree_equality
  fin_cases i <;> simp [planarTie] <;> omega

theorem weight_shift_mem_boundary (B : Data Gamma) (u : Fin 3 →₀ ℕ)
    (w : ℕ) (hw : w ∈ Gamma.toAddSubmonoid) (d : ℕ) (hd : 1 ≤ d)
    (he : weight B u = w + d * B.q.val) : weight B u ∈ B.K := by
  have hdq : d * B.q.val = (d - 1) * B.q.val + B.q.val := by
    conv_lhs => rw [← Nat.sub_add_cancel hd]
    rw [Nat.add_mul, one_mul]
  refine ⟨weight_mem_H B u, by omega, ?_⟩
  have hm : w + (d - 1) * B.q.val ∈ Gamma.toAddSubmonoid := by
    simpa [nsmul_eq_mul] using Gamma.toAddSubmonoid.add_mem hw
      (Gamma.toAddSubmonoid.nsmul_mem B.q.property (d - 1))
  convert hm using 1
  omega

/-- CROSS-PURE with the actual source, positive Apéry residual and depth retained. -/
theorem effectiveClip_cross_pure (F : InternalFrontend k M h) (G : NormalizedSources F)
    (sfull : Source M.base) (hfull : L3A.FullSupport (G.exponents sfull))
    (i : Fin 2) (P : ℕ) (hc : EffectiveClip F G i P)
    (hv : 0 < planarTie F i.rev) :
    ∃ (s : Source M.base) (d ell : ℕ),
      G.exponents s (F.normal.perm 0) = 0 ∧
      planarSource F G s = Finsupp.single i (planarTie F i + P) ∧
      1 ≤ d ∧ 0 < ell ∧
      ell * weights M.base (F.normal.perm i.rev.succ) ∈ M.base.apery ∧
      s.val = (planarTie F i + P) * weights M.base (F.normal.perm i.succ) ∧
      s.val = ell * weights M.base (F.normal.perm i.rev.succ) + d * M.base.q.val := by
  classical
  obtain ⟨s, hsx, hs⟩ := effectiveClip_zero_source F G hc
  have hP := effectiveClip_positive F G hc
  have hsi : planarSource F G s i = planarTie F i + P := by
    have he := congrArg (fun u : PlanarExponent => u i) hs
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at he
    omega
  have hsj : planarSource F G s i.rev ≤ planarTie F i.rev := by
    have he := congrArg (fun u : PlanarExponent => u i.rev) hs
    simp only [Finsupp.tsub_apply, Finsupp.single_apply,
      ite_eq_right (planar_other_ne i).symm] at he
    omega
  obtain ⟨omega0, homega, d, hd, hdeg⟩ := source_apery_decomposition F s
  obtain ⟨v, hvx, _⟩ := apery_normalized_factorization_chain F omega0 homega
  have hvi : planarProjection F v.val i = 0 := by
    apply source_apery_support_complement F s omega0 d hd hdeg
      ⟨G.exponents s, G.degree s⟩ v (F.normal.perm i.succ)
    change 0 < planarSource F G s i
    omega
  have hsource := weight_axes F (G.exponents s) i
  rw [G.degree s, hsx, zero_mul, zero_add] at hsource
  change s.val = planarSource F G s i * _ + planarSource F G s i.rev * _ at hsource
  rw [hsi] at hsource
  have hres := weight_axes F v.val i
  rw [v.property, hvi, zero_mul, add_zero] at hres
  have hxzero : v.val (F.normal.perm 0) = 0 := by
    by_contra hn
    have hxpos : 0 < v.val (F.normal.perm 0) := Nat.pos_of_ne_zero hn
    have hr : F.normal.a - v.val (F.normal.perm 0) < F.normal.a := by omega
    have hm : monomial (layerExponent F (F.normal.a - v.val (F.normal.perm 0))
        (Finsupp.single i P)) (1 : k) ∈ F.initial.ideal := by
      apply boundary_mem_initial F
      apply weight_shift_mem_boundary M.base _
        ((planarTie F i.rev + planarProjection F v.val i.rev - planarSource F G s i.rev) *
          weights M.base (F.normal.perm i.rev.succ))
      · simpa [nsmul_eq_mul, weights] using Gamma.toAddSubmonoid.nsmul_mem
          (M.base.H_le (M.base.tailDegrees (F.normal.perm i.rev.succ)).property)
          (planarTie F i.rev + planarProjection F v.val i.rev - planarSource F G s i.rev)
      · exact hd
      · rw [weight_pure_layer]
        have ht := tie_degree_axes F i
        have hxmul : (F.normal.a - v.val (F.normal.perm 0)) * weights M.base (F.normal.perm 0) +
            v.val (F.normal.perm 0) * weights M.base (F.normal.perm 0) =
            F.normal.a * weights M.base (F.normal.perm 0) := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hvx)]
        have hjmul : (planarTie F i.rev + planarProjection F v.val i.rev - planarSource F G s i.rev) *
            weights M.base (F.normal.perm i.rev.succ) +
            planarSource F G s i.rev * weights M.base (F.normal.perm i.rev.succ) =
            (planarTie F i.rev + planarProjection F v.val i.rev) *
              weights M.base (F.normal.perm i.rev.succ) := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        simp only [Nat.add_mul] at hsource hjmul
        omega
    exact hc.2 (pure_target_mem_A F G i P _ hr hv hm)
  have hjzero : planarSource F G s i.rev = 0 := by
    by_contra hn
    have hvj : planarProjection F v.val i.rev = 0 :=
      source_apery_support_complement F s omega0 d hd hdeg
        ⟨G.exponents s, G.degree s⟩ v (F.normal.perm i.rev.succ) (Nat.pos_of_ne_zero hn)
    have homegazero : omega0 = 0 := by simpa [hxzero, hvj] using hres
    exact zero_layer_not_residue_zero F G sfull hfull s hsx d (by simpa [homegazero] using hdeg)
  have hsourcepure : planarSource F G s = Finsupp.single i (planarTie F i + P) := by
    ext j
    by_cases he : j = i
    · subst j; simpa using hsi
    · have hej : j = i.rev := by fin_cases i <;> fin_cases j <;> simp_all
      subst j
      simp [hjzero, (planar_other_ne i).symm]
  have hres' : omega0 = planarProjection F v.val i.rev *
      weights M.base (F.normal.perm i.rev.succ) := by simpa [hxzero] using hres
  have hell : 0 < planarProjection F v.val i.rev := by
    by_contra hn
    have hz : omega0 = 0 := by
      have hh : planarProjection F v.val i.rev = 0 := by omega
      simpa [hh] using hres'
    exact zero_layer_not_residue_zero F G sfull hfull s hsx d (by simpa [hz] using hdeg)
  refine ⟨s, d, planarProjection F v.val i.rev, hsx, hsourcepure, hd, hell,
    hres' ▸ homega, ?_, ?_⟩
  · simpa [hjzero] using hsource
  · simpa [hres'] using hdeg

/-- The source's residual depth is strictly below the full-support source depth. -/
theorem cross_pure_depth_lt (F : InternalFrontend k M h) (G : NormalizedSources F)
    (sfull : Source M.base) (hfull : L3A.FullSupport (G.exponents sfull))
    (df : ℕ) (hf : sfull.val = df * M.base.q.val)
    (s : Source M.base) (j : Fin 3) (d ell : ℕ) (hell : 0 < ell)
    (ha : ell * weights M.base j ∈ M.base.apery)
    (hs : s.val = ell * weights M.base j + d * M.base.q.val) : d < df :=
  full_support_depth_dominance F s sfull _ d df ha
    (Nat.mul_pos hell (weights_positive _ _)).ne' hs hf
    ⟨G.exponents sfull, G.degree sfull⟩ hfull

theorem effective_y_clip_cross_pure (F : InternalFrontend k M h) (G : NormalizedSources F)
    (sfull : Source M.base) (hfull : L3A.FullSupport (G.exponents sfull))
    (P : ℕ) (hc : EffectiveClip F G 0 P) (hcpos : 0 < F.normal.c) :
    ∃ (s : Source M.base) (d ell : ℕ),
      G.exponents s (F.normal.perm 0) = 0 ∧
      planarSource F G s = Finsupp.single 0 (F.normal.b + P) ∧
      1 ≤ d ∧ 0 < ell ∧ ell * weights M.base (F.normal.perm 2) ∈ M.base.apery ∧
      s.val = (F.normal.b + P) * weights M.base (F.normal.perm 1) ∧
      s.val = ell * weights M.base (F.normal.perm 2) + d * M.base.q.val := by
  simpa [planarTie] using effectiveClip_cross_pure F G sfull hfull 0 P hc
    (by simpa [planarTie] using hcpos)

theorem effective_z_clip_cross_pure (F : InternalFrontend k M h) (G : NormalizedSources F)
    (sfull : Source M.base) (hfull : L3A.FullSupport (G.exponents sfull))
    (Q : ℕ) (hc : EffectiveClip F G 1 Q) :
    ∃ (s : Source M.base) (d ell : ℕ),
      G.exponents s (F.normal.perm 0) = 0 ∧
      planarSource F G s = Finsupp.single 1 (F.normal.c + Q) ∧
      1 ≤ d ∧ 0 < ell ∧ ell * weights M.base (F.normal.perm 1) ∈ M.base.apery ∧
      s.val = (F.normal.c + Q) * weights M.base (F.normal.perm 2) ∧
      s.val = ell * weights M.base (F.normal.perm 1) + d * M.base.q.val := by
  have hb : 0 < F.normal.b := F.normal.b_positive
  simpa [planarTie] using effectiveClip_cross_pure F G sfull hfull 1 Q hc
    (by simpa [planarTie] using hb)

/-- Type I has no effective z-clip in the presence of the actual full-support source. -/
theorem typeI_no_effective_z_clip (F : InternalFrontend k M h) (G : NormalizedSources F)
    (sfull : Source M.base) (hfull : L3A.FullSupport (G.exponents sfull))
    (hc : F.normal.c = 0) (Q : ℕ) : ¬ EffectiveClip F G 1 Q := by
  intro hclip
  obtain ⟨s, d, ell, _, hs, _⟩ := effective_z_clip_cross_pure F G sfull hfull Q hclip
  have hm : monomial (planarSource F G s) (1 : k) ∈ planarA F G :=
    Ideal.subset_span ⟨_, ⟨s, rfl⟩, rfl⟩
  apply hclip.2
  simpa [hs, hc] using hm

theorem qfs_one_typeI_no_effective_z_clip (F : InternalFrontend k M h)
    (G : NormalizedSources F) (hq : L3A.q_fs F.initial.ideal = 1)
    (hc : F.normal.c = 0) (Q : ℕ) : ¬ EffectiveClip F G 1 Q := by
  obtain ⟨s, hs⟩ := full_source_exists_of_qfs_one F G hq
  exact typeI_no_effective_z_clip F G s hs hc Q

/-- In Type I, exact colon already makes the y-clip source pure. -/
theorem typeI_effective_y_clip_source (F : InternalFrontend k M h)
    (G : NormalizedSources F) (hc : F.normal.c = 0)
    (P : ℕ) (hclip : EffectiveClip F G 0 P) :
    ∃ s : Source M.base, G.exponents s (F.normal.perm 0) = 0 ∧
      planarSource F G s = Finsupp.single 0 (F.normal.b + P) := by
  obtain ⟨s, hsx, hs⟩ := effectiveClip_zero_source F G hclip
  have hP := effectiveClip_positive F G hclip
  refine ⟨s, hsx, ?_⟩
  have hy := congrArg (fun u : PlanarExponent => u 0) hs
  have hz := congrArg (fun u : PlanarExponent => u 1) hs
  simp [planarTie, hc] at hy hz
  ext j
  fin_cases j
  · have he : planarSource F G s 0 = F.normal.b + P := by omega
    simpa using he
  · simpa using hz

end NS25Lean.L3C

