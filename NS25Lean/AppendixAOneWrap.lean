import NS25Lean.OneDefectFrontend

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
open scoped MonomialOrder
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

theorem tie_leading_mem (F : InternalFrontend k M h) :
    monomial F.normal.alpha.val (1 : k) ∈ F.initial.ideal := by
  classical
  let m := permutationOrder F.normal.perm
  have hf : monomial F.normal.alpha.val (1 : k) - monomial F.normal.beta.val 1 ∈
      M.base.J k := by
    rw [← F.generator_span]
    exact Ideal.subset_span ⟨Sum.inr (), rfl⟩
  have hd : m.degree (monomial F.normal.beta.val (1 : k)) ≺[m]
      m.degree (monomial F.normal.alpha.val (1 : k)) := by
    simpa only [m.degree_monomial, one_ne_zero, ite_false] using F.normal.order_tie
  have he : m.leadingTerm (monomial F.normal.alpha.val (1 : k) -
      monomial F.normal.beta.val 1) = monomial F.normal.alpha.val 1 := by
    rw [MonomialOrder.leadingTerm, m.degree_sub_of_lt hd, m.leadingCoeff_sub_of_lt hd]
    simp [m.degree_monomial]
  exact he ▸ Ideal.subset_span ⟨_, hf, rfl⟩

/-- The actual initial ideal's standard monomials lie in the x-slab. -/
theorem standard_slab (F : InternalFrontend k M h)
    (u : L3A.standardExponents F.initial.ideal) : u.val (F.normal.perm 0) < F.normal.a := by
  by_contra hn
  have hd : F.normal.alpha.val ≤ u.val := by
    rw [F.normal.alpha_eq]
    exact Finsupp.single_le_iff.mpr (by omega)
  exact u.property (F.initial.ideal.mem_of_dvd (monomial_one_dvd_monomial_one.mpr hd)
    (tie_leading_mem F))

/-- All fields are already proved by the frozen normalization theorem; no wrap claim. -/
structure NormalizedSources (F : InternalFrontend k M h) where
  exponents : Source M.base → Fin 3 →₀ ℕ
  slab : ∀ s, exponents s (F.normal.perm 0) < F.normal.a
  degree : ∀ s, weight M.base (exponents s) = s.val
  span : Ideal.span (Set.range
    (normalizedFamily k M.base F.normal.alpha.val F.normal.beta.val exponents)) = M.base.J k
  minimal : ∀ i, normalizedFamily k M.base F.normal.alpha.val F.normal.beta.val exponents i ∉
    Ideal.span (normalizedFamily k M.base F.normal.alpha.val F.normal.beta.val exponents ''
      {j | j ≠ i})

theorem normalized_sources_exist (F : InternalFrontend k M h) : Nonempty (NormalizedSources F) := by
  obtain ⟨g, hg, hs, hm⟩ := normalized_source_generators k M F.one_defect h
    F.unique_degree.2 F.normal
  exact ⟨⟨g, fun s => (hg s).1, fun s => (hg s).2.1, hs, hm⟩⟩

def transverse (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ) : Fin 3 →₀ ℕ :=
  u - Finsupp.single (F.normal.perm 0) (u (F.normal.perm 0))

def wrap (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ) : Fin 3 →₀ ℕ :=
  F.normal.beta.val + transverse F u

theorem transverse_add (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ) :
    transverse F u + Finsupp.single (F.normal.perm 0) (u (F.normal.perm 0)) = u :=
  tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr le_rfl)

theorem wrap_x_zero (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ) :
    wrap F u (F.normal.perm 0) = 0 := by
  classical
  simp [wrap, transverse, F.normal.beta_eq, F.normal.perm.injective.eq_iff]

theorem wrap_weight (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) :
    weight M.base (wrap F (G.exponents s)) = s.val +
      (F.normal.a - G.exponents s (F.normal.perm 0)) * weights M.base (F.normal.perm 0) := by
  have hu := congrArg (weight M.base) (transverse_add F (G.exponents s))
  simp only [map_add, weight_single, G.degree] at hu
  have ha := F.normal.degree_equality.1
  have hr := G.slab s
  have hs : (F.normal.a - G.exponents s (F.normal.perm 0)) * weights M.base (F.normal.perm 0) +
      G.exponents s (F.normal.perm 0) * weights M.base (F.normal.perm 0) =
      F.normal.a * weights M.base (F.normal.perm 0) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hr)]
  simp only [wrap, map_add, F.normal.beta.property]
  omega

theorem normalized_source_mem_initial (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) : monomial (G.exponents s) (1 : k) ∈ F.initial.ideal := by
  have hf := boundary_monomial_mem_J k M.base (G.exponents s) ((G.degree s).symm ▸ s.property.1)
  exact Ideal.subset_span ⟨_, hf, (permutationOrder F.normal.perm).leadingTerm_monomial _ _⟩

theorem wrap_mem_initial (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) : monomial (wrap F (G.exponents s)) (1 : k) ∈ F.initial.ideal := by
  have hH : (F.normal.a - G.exponents s (F.normal.perm 0)) *
      weights M.base (F.normal.perm 0) ∈ M.base.H := by
    exact M.base.H.nsmul_mem (M.base.tailDegrees (F.normal.perm 0)).property _
  have hK : weight M.base (wrap F (G.exponents s)) ∈ M.base.K := by
    rw [wrap_weight F G s]
    exact FourGeneratedBridge.aperyTail_add_mem M.base.H_le s.property.1 hH
  have hf := boundary_monomial_mem_J k M.base _ hK
  exact Ideal.subset_span ⟨_, hf, (permutationOrder F.normal.perm).leadingTerm_monomial _ _⟩

def oneWrapExponents (F : InternalFrontend k M h) (G : NormalizedSources F) : Set (Fin 3 →₀ ℕ) :=
  {F.normal.alpha.val} ∪ Set.range G.exponents ∪
    {u | ∃ s, 0 < G.exponents s (F.normal.perm 0) ∧ u = wrap F (G.exponents s)}

def oneWrapIdeal (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Ideal (ToricPresentation.Poly k 3) :=
  Ideal.span ((fun u => monomial u (1 : k)) '' oneWrapExponents F G)

/-- Forward inclusion only; the reverse Groebner inclusion is a separate obligation. -/
theorem oneWrapIdeal_le_initial (F : InternalFrontend k M h) (G : NormalizedSources F) :
    oneWrapIdeal F G ≤ F.initial.ideal := by
  apply Ideal.span_le.mpr
  rintro _ ⟨u, (hu | ⟨s, rfl⟩) | ⟨s, _, rfl⟩, rfl⟩
  · exact Set.mem_singleton_iff.mp hu ▸ tie_leading_mem F
  · exact normalized_source_mem_initial F G s
  · exact wrap_mem_initial F G s

end NS25Lean.L3C
