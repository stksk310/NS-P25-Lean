import NS25Lean.AppendixAOneWrap

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
open scoped MonomialOrder
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- The monomial part of the completed presentation, without the leading tie. -/
def wrapBoundaryExponents (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Set (Fin 3 →₀ ℕ) :=
  Set.range G.exponents ∪
    {u | ∃ s, 0 < G.exponents s (F.normal.perm 0) ∧ u = wrap F (G.exponents s)}

def wrapBoundaryIdeal (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Ideal (ToricPresentation.Poly k 3) :=
  Ideal.span ((fun u => monomial u (1 : k)) '' wrapBoundaryExponents F G)

theorem wrapBoundaryIdeal_le_oneWrap (F : InternalFrontend k M h) (G : NormalizedSources F) :
    wrapBoundaryIdeal F G ≤ oneWrapIdeal F G := by
  apply Ideal.span_mono
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨u, ?_, rfl⟩
  rcases hu with hu | hu
  · exact Or.inl (Or.inr hu)
  · exact Or.inr hu

theorem wrapBoundary_term (F : InternalFrontend k M h) (G : NormalizedSources F)
    {p : ToricPresentation.Poly k 3} (hp : p ∈ wrapBoundaryIdeal F G)
    {u : Fin 3 →₀ ℕ} (hu : u ∈ p.support) :
    monomial u (1 : k) ∈ wrapBoundaryIdeal F G :=
  (L3A.monomial_mem_span_iff _ _).mpr (mem_ideal_span_monomial_image.mp hp u hu)

theorem wrapBoundary_monomial_coeff (F : InternalFrontend k M h) (G : NormalizedSources F)
    {u : Fin 3 →₀ ℕ} (hu : monomial u (1 : k) ∈ wrapBoundaryIdeal F G) (c : k) :
    monomial u c ∈ wrapBoundaryIdeal F G := by
  simpa only [C_mul_monomial, mul_one] using
    (wrapBoundaryIdeal F G).mul_mem_left (C c) hu

/-- Reducing one leading-tie multiple preserves the completed monomial boundary. -/
theorem wrapBoundary_tie_reduction (F : InternalFrontend k M h) (G : NormalizedSources F)
    (t : Fin 3 →₀ ℕ)
    (ht : monomial (t + F.normal.alpha.val) (1 : k) ∈ wrapBoundaryIdeal F G) :
    monomial (t + F.normal.beta.val) (1 : k) ∈ wrapBoundaryIdeal F G := by
  classical
  obtain ⟨u, hu, hut⟩ := (L3A.monomial_mem_span_iff _ _).mp ht
  have haway (i : Fin 3) (hi : i ≠ F.normal.perm 0) : u i ≤ t i := by
    have hh := hut i
    simpa [F.normal.alpha_eq, Finsupp.single_apply, hi, Ne.symm hi] using hh
  rcases hu with ⟨s, rfl⟩ | ⟨s, hs, rfl⟩
  · by_cases hs : G.exponents s (F.normal.perm 0) = 0
    · apply (L3A.monomial_mem_span_iff _ _).mpr
      refine ⟨G.exponents s, Or.inl ⟨s, rfl⟩, ?_⟩
      intro i
      by_cases hi : i = F.normal.perm 0
      · subst i; simp [hs]
      · exact le_trans (haway i hi) (by simp)
    · apply (L3A.monomial_mem_span_iff _ _).mpr
      refine ⟨wrap F (G.exponents s), Or.inr ⟨s, Nat.pos_of_ne_zero hs, rfl⟩, ?_⟩
      intro i
      by_cases hi : i = F.normal.perm 0
      · subst i; rw [wrap_x_zero]; exact Nat.zero_le _
      · have hu := haway i hi
        simpa [wrap, transverse, Finsupp.single_apply, hi, Ne.symm hi,
          add_comm] using Nat.add_le_add_right hu (F.normal.beta.val i)
  · apply (L3A.monomial_mem_span_iff _ _).mpr
    refine ⟨wrap F (G.exponents s), Or.inr ⟨s, hs, rfl⟩, ?_⟩
    intro i
    by_cases hi : i = F.normal.perm 0
    · subst i; rw [wrap_x_zero]; exact Nat.zero_le _
    · exact le_trans (haway i hi) (by simp)

def tiePolynomial (F : InternalFrontend k M h) : ToricPresentation.Poly k 3 :=
  monomial F.normal.alpha.val 1 - monomial F.normal.beta.val 1

theorem tiePolynomial_leading (F : InternalFrontend k M h) :
    (permutationOrder F.normal.perm).leadingTerm (tiePolynomial F) =
      monomial F.normal.alpha.val (1 : k) := by
  classical
  let m := permutationOrder F.normal.perm
  have hd : m.degree (monomial F.normal.beta.val (1 : k)) ≺[m]
      m.degree (monomial F.normal.alpha.val (1 : k)) := by
    simpa only [m.degree_monomial, one_ne_zero, ite_false] using F.normal.order_tie
  rw [tiePolynomial, MonomialOrder.leadingTerm, m.degree_sub_of_lt hd,
    m.leadingCoeff_sub_of_lt hd]
  simp [m.degree_monomial]

theorem leading_product_mem_oneWrap (F : InternalFrontend k M h) (G : NormalizedSources F)
    (p : ToricPresentation.Poly k 3) :
    (permutationOrder F.normal.perm).leadingTerm (tiePolynomial F * p) ∈ oneWrapIdeal F G := by
  rw [MonomialOrder.leadingTerm_mul, tiePolynomial_leading]
  apply (oneWrapIdeal F G).mul_mem_right
  exact Ideal.subset_span ⟨F.normal.alpha.val, Or.inl (Or.inl rfl), rfl⟩

theorem J_le_completed_presentation (F : InternalFrontend k M h) (G : NormalizedSources F) :
    M.base.J k ≤ wrapBoundaryIdeal F G ⊔ Ideal.span {tiePolynomial F} := by
  rw [← G.span]
  apply Ideal.span_le.mpr
  rintro _ ⟨s | u, rfl⟩
  · apply (show wrapBoundaryIdeal F G ≤
        wrapBoundaryIdeal F G ⊔ Ideal.span {tiePolynomial F} from le_sup_left)
    exact Ideal.subset_span ⟨G.exponents s, Or.inl ⟨s, rfl⟩, rfl⟩
  · apply (show Ideal.span {tiePolynomial F} ≤
        wrapBoundaryIdeal F G ⊔ Ideal.span {tiePolynomial F} from le_sup_right)
    exact Ideal.subset_span rfl

theorem tiePolynomial_ne_zero (F : InternalFrontend k M h) : tiePolynomial F ≠ 0 := by
  intro hz
  have hh := tiePolynomial_leading F
  rw [hz, MonomialOrder.leadingTerm_zero] at hh
  exact one_ne_zero (monomial_eq_zero.mp hh.symm)

theorem tiePolynomial_degree (F : InternalFrontend k M h) :
    (permutationOrder F.normal.perm).degree (tiePolynomial F) = F.normal.alpha.val := by
  classical
  have hh := congrArg (permutationOrder F.normal.perm).degree (tiePolynomial_leading F)
  simpa only [MonomialOrder.degree_leadingTerm, MonomialOrder.degree_monomial,
    one_ne_zero, ite_false] using hh

theorem wrapBoundary_leading (F : InternalFrontend k M h) (G : NormalizedSources F)
    {p : ToricPresentation.Poly k 3} (hp : p ∈ wrapBoundaryIdeal F G) :
    (permutationOrder F.normal.perm).leadingTerm p ∈ wrapBoundaryIdeal F G := by
  by_cases hz : p = 0
  · subst p; simp
  · exact wrapBoundary_monomial_coeff F G
      (wrapBoundary_term F G hp ((permutationOrder F.normal.perm).degree_mem_support hz)) _

theorem support_card_sub_leading_lt (m : MonomialOrder (Fin 3))
    (p : ToricPresentation.Poly k 3) (hp : p ≠ 0) :
    (p - m.leadingTerm p).support.card < p.support.card := by
  classical
  have hs : (p - m.leadingTerm p).support ⊆ p.support.erase (m.degree p) := by
    intro u hu
    have hc := mem_support_iff.mp hu
    have hn : u ≠ m.degree p := by
      intro he
      subst u
      simp [MonomialOrder.leadingTerm, MonomialOrder.leadingCoeff] at hc
    apply Finset.mem_erase.mpr
    refine ⟨hn, mem_support_iff.mpr ?_⟩
    simpa [MonomialOrder.leadingTerm, coeff_monomial, hn, Ne.symm hn] using hc
  exact lt_of_le_of_lt (Finset.card_le_card hs)
    (Finset.card_erase_lt_of_mem (m.degree_mem_support hp))

/-- Cancel a multiple whose leading monomial lies in the completed boundary;
the trailing monomial also lies there by one-wrap reduction stability. -/
theorem tie_leading_multiple_mem_boundary (F : InternalFrontend k M h)
    (G : NormalizedSources F) (p : ToricPresentation.Poly k 3)
    (hp : monomial ((permutationOrder F.normal.perm).degree p + F.normal.alpha.val)
      (1 : k) ∈ wrapBoundaryIdeal F G) :
    tiePolynomial F * (permutationOrder F.normal.perm).leadingTerm p ∈
      wrapBoundaryIdeal F G := by
  have ha := wrapBoundary_monomial_coeff F G hp
    ((permutationOrder F.normal.perm).leadingCoeff p)
  have hb := wrapBoundary_monomial_coeff F G (wrapBoundary_tie_reduction F G _ hp)
    ((permutationOrder F.normal.perm).leadingCoeff p)
  simpa only [tiePolynomial, MonomialOrder.leadingTerm, sub_mul,
    monomial_mul, one_mul, add_comm] using (wrapBoundaryIdeal F G).sub_mem ha hb

/-- Direct completion proof by eliminating canceled leading terms of the multiplier.
The strictly decreasing measure is its finite monomial support; no Buchberger
criterion or additional source hypothesis is assumed. -/
theorem completed_presentation_leading (F : InternalFrontend k M h)
    (G : NormalizedSources F) (p q : ToricPresentation.Poly k 3)
    (hq : q ∈ wrapBoundaryIdeal F G) :
    (permutationOrder F.normal.perm).leadingTerm (q + tiePolynomial F * p) ∈
      oneWrapIdeal F G := by
  classical
  let m := permutationOrder F.normal.perm
  generalize hc : p.support.card = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
    by_cases hp0 : p = 0
    · subst p
      simpa using wrapBoundaryIdeal_le_oneWrap F G (wrapBoundary_leading F G hq)
    by_cases hq0 : q = 0
    · subst q
      simpa using leading_product_mem_oneWrap F G p
    by_cases ht : monomial (m.degree p + F.normal.alpha.val) (1 : k) ∈
        wrapBoundaryIdeal F G
    · have hmove := tie_leading_multiple_mem_boundary F G p ht
      have hsmall : (p - m.leadingTerm p).support.card < n :=
        hc ▸ support_card_sub_leading_lt m p hp0
      have hi := ih _ hsmall (p - m.leadingTerm p)
        (q + tiePolynomial F * m.leadingTerm p)
        ((wrapBoundaryIdeal F G).add_mem hq hmove) rfl
      have he : q + tiePolynomial F * p =
          (q + tiePolynomial F * m.leadingTerm p) +
            tiePolynomial F * (p - m.leadingTerm p) := by ring
      rw [he]
      exact hi
    · have hdeg : m.degree (tiePolynomial F * p) = F.normal.alpha.val + m.degree p := by
        rw [m.degree_mul (tiePolynomial_ne_zero F) hp0, tiePolynomial_degree]
      rcases lt_trichotomy (m.toSyn (m.degree q))
        (m.toSyn (m.degree (tiePolynomial F * p))) with hlt | heq | hgt
      · have he : m.leadingTerm (q + tiePolynomial F * p) =
            m.leadingTerm (tiePolynomial F * p) := by
          rw [add_comm, MonomialOrder.leadingTerm, m.degree_add_of_lt hlt,
            m.leadingCoeff_add_of_lt hlt]
          rfl
        rw [he]
        exact leading_product_mem_oneWrap F G p
      · have he := m.toSyn.injective heq
        have hm := wrapBoundary_term F G hq (m.degree_mem_support hq0)
        rw [he, hdeg, add_comm] at hm
        exact (ht hm).elim
      · have he : m.leadingTerm (q + tiePolynomial F * p) = m.leadingTerm q := by
          rw [MonomialOrder.leadingTerm, m.degree_add_of_lt hgt,
            m.leadingCoeff_add_of_lt hgt]
          rfl
        rw [he]
        exact wrapBoundaryIdeal_le_oneWrap F G (wrapBoundary_leading F G hq)

/-- The reverse inclusion in the actual One-Wrap initial-ideal formula. -/
theorem initial_le_oneWrapIdeal (F : InternalFrontend k M h) (G : NormalizedSources F) :
    F.initial.ideal ≤ oneWrapIdeal F G := by
  apply Ideal.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, r, hr, he⟩ := Submodule.mem_sup.mp (J_le_completed_presentation F G hp)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hr
  rw [← he, hs]
  exact completed_presentation_leading F G s q hq

/-- Exact actual One-Wrap theorem: there are no further initial generators. -/
theorem initial_eq_oneWrapIdeal (F : InternalFrontend k M h) (G : NormalizedSources F) :
    F.initial.ideal = oneWrapIdeal F G :=
  le_antisymm (initial_le_oneWrapIdeal F G) (oneWrapIdeal_le_initial F G)

end NS25Lean.L3C
