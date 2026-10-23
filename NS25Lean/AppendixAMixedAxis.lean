import NS25Lean.AppendixACuts
import NS25Lean.AppendixADepth
import NS25Lean.AppendixAArtificialSocle

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- A mixed zero-layer colon core gives an actual full-support factorization
of the same minimal source degree and hence has residue zero. -/
theorem mixed_colon_source_residue_zero (F : InternalFrontend k M h)
    (G : NormalizedSources F) (s : Source M.base)
    (hs : G.exponents s (F.normal.perm 0) = 0) (w : PlanarExponent)
    (hw : planarSource F G s = planarTie F + w) (hy : 0 < w 0) (hz : 0 < w 1) :
    ∃ d : ℕ, 1 ≤ d ∧ s.val = d * M.base.q.val := by
  have hg : layerExponent F 0 (planarSource F G s) = G.exponents s := by
    rw [← hs]
    exact layerExponent_projection F (G.exponents s)
  have hdeg : weight M.base (layerExponent F F.normal.a w) = s.val := by
    rw [weight_top_wrap, add_comm, ← hw, hg, G.degree]
  apply full_support_source_residue_zero F s ⟨_, hdeg⟩
  intro i
  obtain ⟨j, rfl⟩ := F.normal.perm.surjective i
  fin_cases j
  · simpa using (lt_of_lt_of_le (by decide : 0 < 2) F.normal.a_ge_two)
  · simpa [layerExponent, F.normal.perm.injective.eq_iff] using hy
  · simpa [layerExponent, F.normal.perm.injective.eq_iff] using hz

/-- Every effective mixed minimal colon generator has the source claimed in Appendix A. -/
theorem effective_mixed_colon_source (F : InternalFrontend k M h)
    (G : NormalizedSources F) (w : PlanarExponent)
    (hm : Minimal (fun u => monomial u (1 : k) ∈ planarJ F G) w)
    (ha : monomial w (1 : k) ∉ planarA F G) (hy : 0 < w 0) (hz : 0 < w 1) :
    ∃ s : Source M.base, G.exponents s (F.normal.perm 0) = 0 ∧
      planarSource F G s = planarTie F + w ∧
      ∃ d : ℕ, 1 ≤ d ∧ s.val = d * M.base.q.val := by
  obtain ⟨u, ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩, huw⟩ :=
    (exact_colon_monomial F G w).mp hm.1
  · have hh : monomial (planarSource F G s) (1 : k) ∈ planarA F G :=
      Ideal.subset_span ⟨_, ⟨s, rfl⟩, rfl⟩
    exact (ha ((planarA F G).mem_of_dvd (monomial_one_dvd_monomial_one.mpr huw) hh)).elim
  · have hj : monomial (planarSource F G s - planarTie F) (1 : k) ∈ planarJ F G :=
      (exact_colon_monomial F G _).mpr ⟨_, Or.inr ⟨s, hs, rfl⟩, le_rfl⟩
    have he : planarSource F G s - planarTie F = w := le_antisymm huw (hm.2 hj huw)
    have hsum : planarSource F G s = planarTie F + w := by
      ext i
      have hh := congrArg (fun u : PlanarExponent => u i) he
      have hpos : 0 < w i := by
        fin_cases i
        · exact hy
        · exact hz
      simp only [Finsupp.tsub_apply, Finsupp.add_apply] at hh ⊢
      omega
    exact ⟨s, hs, hsum, mixed_colon_source_residue_zero F G s hs w hsum hy hz⟩

/-- General axis-cut argument. The missing source variable occurs in the tie's
other monomial. A nonzero residual exponent would kill a proper divisor of the wrap. -/
theorem axis_cut_source_residue_zero (F : InternalFrontend k M h)
    (G : NormalizedSources F) (s : Source M.base) (j : Fin 3)
    (hβ : 0 < F.normal.beta.val j)
    (hu : ∀ i : Fin 3, i ≠ j → 0 < G.exponents s i)
    (hm : wrap F (G.exponents s) ∈ L3A.minimalExponents F.initial.ideal) :
    ∃ d : ℕ, 1 ≤ d ∧ s.val = d * M.base.q.val := by
  classical
  obtain ⟨ω, hω, d, hd, he⟩ := source_apery_decomposition F s
  obtain ⟨v⟩ := fiber_nonempty M.base ⟨ω, (M.base.apery_eq_compl ▸ hω).1⟩
  have hv : v.val = Finsupp.single j (v.val j) := by
    ext i
    by_cases hi : i = j
    · subst i; simp
    · have hz := source_apery_support_complement F s ω d hd he
        ⟨G.exponents s, G.degree s⟩ v i (hu i hi)
      simpa [Finsupp.single_apply, hi, Ne.symm hi] using hz
  have hωeq : ω = v.val j * weights M.base j := by
    have hh := v.property
    rw [hv, weight_single] at hh
    exact hh.symm
  by_cases hlam : v.val j = 0
  · exact ⟨d, hd, by simpa [hωeq, hlam] using he⟩
  · have hlampos : 1 ≤ v.val j := Nat.one_le_iff_ne_zero.mpr hlam
    let w := wrap F (G.exponents s)
    have hwj : 0 < w j := by
      dsimp [w, wrap]
      omega
    have hrem := removed_weight M.base (weight M.base w) ⟨w, rfl⟩ j hwj
    change weights M.base j + weight M.base (w - Finsupp.single j 1) =
      weight M.base w at hrem
    have hwdeg := wrap_weight F G s
    change weight M.base w = s.val +
      (F.normal.a - G.exponents s (F.normal.perm 0)) * weights M.base (F.normal.perm 0) at hwdeg
    have hlammul : (v.val j - 1) * weights M.base j + weights M.base j =
        v.val j * weights M.base j := by
      rw [← Nat.add_one_mul, Nat.sub_add_cancel hlampos]
    have hdmul : (d - 1) * M.base.q.val + M.base.q.val = d * M.base.q.val := by
      rw [← Nat.add_one_mul, Nat.sub_add_cancel hd]
    have hΓ : (v.val j - 1) * weights M.base j +
        (F.normal.a - G.exponents s (F.normal.perm 0)) * weights M.base (F.normal.perm 0) +
        (d - 1) * M.base.q.val ∈ Gamma.toAddSubmonoid := by
      apply Gamma.toAddSubmonoid.add_mem
      · apply Gamma.toAddSubmonoid.add_mem
        · simpa [nsmul_eq_mul, weights] using Gamma.toAddSubmonoid.nsmul_mem
            (M.base.H_le (M.base.tailDegrees j).property) (v.val j - 1)
        · simpa [nsmul_eq_mul, weights] using Gamma.toAddSubmonoid.nsmul_mem
            (M.base.H_le (M.base.tailDegrees (F.normal.perm 0)).property)
            (F.normal.a - G.exponents s (F.normal.perm 0))
      · simpa [nsmul_eq_mul] using Gamma.toAddSubmonoid.nsmul_mem M.base.q.property (d - 1)
    have hk : weight M.base (w - Finsupp.single j 1) ∈ M.base.K := by
      refine ⟨weight_mem_H M.base _, ?_, ?_⟩
      · omega
      · convert hΓ using 1; omega
    have hdiv := hm.2 (boundary_mem_initial F _ hk) (tsub_le_self)
    have hx := hdiv j
    change w j ≤ (w - Finsupp.single j 1 : Fin 3 →₀ ℕ) j at hx
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hx
    omega

theorem planar_source_nonzero (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) : planarSource F G s ≠ 0 := by
  intro hz
  have hg : G.exponents s = Finsupp.single (F.normal.perm 0)
      (G.exponents s (F.normal.perm 0)) := by
    calc
      G.exponents s = layerExponent F (G.exponents s (F.normal.perm 0))
          (planarSource F G s) := (layerExponent_projection F (G.exponents s)).symm
      _ = _ := by rw [hz]; simp [layerExponent]
  apply source_not_le_tie F G s
  rw [hg, F.normal.alpha_eq]
  apply Finsupp.single_le_iff.mpr
  simpa using (G.slab s).le

theorem y_axis_cut_residue_zero (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) (hr : 0 < G.exponents s (F.normal.perm 0))
    (hz : planarSource F G s 1 = 0) (hc : 0 < F.normal.c)
    (hm : wrap F (G.exponents s) ∈ L3A.minimalExponents F.initial.ideal) :
    ∃ d : ℕ, 1 ≤ d ∧ s.val = d * M.base.q.val := by
  have hy : 0 < planarSource F G s 0 := by
    by_contra hn
    apply planar_source_nonzero F G s
    ext i
    fin_cases i <;> simp_all
  apply axis_cut_source_residue_zero F G s (F.normal.perm 2) ?_ ?_ hm
  · simpa [F.normal.beta_eq, F.normal.perm.injective.eq_iff] using hc
  · intro i hi
    obtain ⟨j, rfl⟩ := F.normal.perm.surjective i
    fin_cases j
    · exact hr
    · exact hy
    · exact (hi rfl).elim

theorem z_axis_cut_residue_zero (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) (hr : 0 < G.exponents s (F.normal.perm 0))
    (hy : planarSource F G s 0 = 0)
    (hm : wrap F (G.exponents s) ∈ L3A.minimalExponents F.initial.ideal) :
    ∃ d : ℕ, 1 ≤ d ∧ s.val = d * M.base.q.val := by
  have hz : 0 < planarSource F G s 1 := by
    by_contra hn
    apply planar_source_nonzero F G s
    ext i
    fin_cases i <;> simp_all
  apply axis_cut_source_residue_zero F G s (F.normal.perm 1) ?_ ?_ hm
  · simpa [F.normal.beta_eq, F.normal.perm.injective.eq_iff] using
      (lt_of_lt_of_le (by decide : 0 < 1) F.normal.b_positive)
  · intro i hi
    obtain ⟨j, rfl⟩ := F.normal.perm.surjective i
    fin_cases j
    · exact hr
    · exact (hi rfl).elim
    · exact hz

end NS25Lean.L3C
