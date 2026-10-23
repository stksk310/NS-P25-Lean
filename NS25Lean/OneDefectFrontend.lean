import NS25Lean.OneDefectBetti

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3B
open ChosenBase L2B L2B2A L2B2A2 MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem source_sum_unit_card (B : Data Gamma) : Nat.card (Source B ⊕ Unit) = sourceCount B + 1 := by
  classical
  letI := Fintype.ofFinite (Source B)
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_unique (α := Unit)]
  congr 1
  exact Nat.card_eq_fintype_card.symm

theorem normal_form_generators (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 1) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (N : TieNormalForm M.base h) :
    Ideal.span (Set.range (tieGenerators k M.base N.alpha.val N.beta.val)) = M.base.J k ∧
      ∀ i, tieGenerators k M.base N.alpha.val N.beta.val i ∉
        Ideal.span (tieGenerators k M.base N.alpha.val N.beta.val '' {j | j ≠ i}) := by
  classical
  have hg := internal_tie_generators_span k M h hz N.alpha N.beta N.exactly_two
  refine ⟨hg, ?_⟩
  letI := Fintype.ofFinite (Source M.base)
  apply irredundant_of_card_eq_mu _ _ hg
  rw [← Nat.card_eq_fintype_card, source_sum_unit_card, M.base.muj k]
  have := sourceCount_add_defect M.base
  omega

def normalizedFamily (k : Type*) [Field k] (B : Data Gamma) (α β : Fin 3 →₀ ℕ)
    (g : Source B → Fin 3 →₀ ℕ) : Source B ⊕ Unit → ToricPresentation.Poly k 3 :=
  Sum.elim (fun s => monomial (g s) 1) (fun _ => monomial α 1 - monomial β 1)

/-- Simultaneous normalization preserves source degrees, the actual ideal, and minimality. -/
theorem normalized_source_generators (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 1) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (N : TieNormalForm M.base h) :
    ∃ g : Source M.base → Fin 3 →₀ ℕ,
      (∀ s, (g s) (N.perm 0) < N.a ∧ weight M.base (g s) = s.val ∧
        sourcePolynomial k M.base s - monomial (g s) 1 ∈
          Ideal.span {monomial N.alpha.val (1 : k) - monomial N.beta.val 1}) ∧
      Ideal.span (Set.range (normalizedFamily k M.base N.alpha.val N.beta.val g)) = M.base.J k ∧
      ∀ i, normalizedFamily k M.base N.alpha.val N.beta.val g i ∉
        Ideal.span (normalizedFamily k M.base N.alpha.val N.beta.val g '' {j | j ≠ i}) := by
  classical
  choose g hsmall hdeg hrel using fun s : Source M.base =>
    N.normalize_monomial k (sourceRepresentative M.base s).val
  let z := normalizedFamily k M.base N.alpha.val N.beta.val g
  let L := Ideal.span (Set.range z)
  let f := monomial N.alpha.val (1 : k) - monomial N.beta.val 1
  have hfL : f ∈ L := Ideal.subset_span ⟨Sum.inr (), rfl⟩
  have hfJ : f ∈ M.base.J k := by
    have hle : M.base.IH k ≤ M.base.J k := by rw [M.base.J_eq_IH_sup_MK k]; exact le_sup_left
    exact hle (binomial_mem_IH k M.base _ _ (N.alpha.property.trans N.beta.property.symm))
  have hspanL : Ideal.span {f} ≤ L := Ideal.span_le.mpr (by rintro _ rfl; exact hfL)
  have hspanJ : Ideal.span {f} ≤ M.base.J k := Ideal.span_le.mpr (by rintro _ rfl; exact hfJ)
  have hgen : L = M.base.J k := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨s | u, rfl⟩
      · change monomial (g s) (1 : k) ∈ M.base.J k
        have hs : sourcePolynomial k M.base s ∈ M.base.J k :=
          boundary_monomial_mem_J k M.base _
            ((sourceRepresentative M.base s).property.symm ▸ s.property.1)
        have hh := (M.base.J k).sub_mem hs (hspanJ (hrel s))
        simpa only [sourcePolynomial, sub_sub_cancel] using hh
      · exact hfJ
    · rw [← (normal_form_generators k M hp h hz N).1]
      apply Ideal.span_le.mpr
      rintro _ ⟨s | u, rfl⟩
      · change sourcePolynomial k M.base s ∈ L
        have hs : monomial (g s) (1 : k) ∈ L := Ideal.subset_span ⟨Sum.inl s, rfl⟩
        have hh := L.add_mem (hspanL (hrel s)) hs
        simpa only [sourcePolynomial, sub_add_cancel] using hh
      · exact hfL
  refine ⟨g, fun s => ⟨hsmall s, (hdeg s).trans (sourceRepresentative M.base s).property,
    hrel s⟩, hgen, ?_⟩
  letI := Fintype.ofFinite (Source M.base)
  apply irredundant_of_card_eq_mu _ _ hgen
  rw [← Nat.card_eq_fintype_card, source_sum_unit_card, M.base.muj k]
  have := sourceCount_add_defect M.base
  omega

/-- Exact data exported to Appendix A. None of its deferred conclusions is a field. -/
structure InternalFrontend (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ) where
  normal : TieNormalForm M.base h
  one_defect : chosenDefect M.base = 1
  unique_degree : fiberContribution M h = 1 ∧ ∀ d, d ≠ h → fiberContribution M d = 0
  unique_betti : ∀ d, (d ∈ M.base.apery ∧ L2C.Betti M.base d) ↔ d = h
  singleton_components : ∀ u v : FactorizationFiber M.base h,
    (fiberGraph M.base h).connectedComponentMk u = (fiberGraph M.base h).connectedComponentMk v → u = v
  coprime : IsRelPrime (monomial normal.alpha.val (1 : k)) (monomial normal.beta.val 1)
  generator_span : Ideal.span (Set.range
    (tieGenerators k M.base normal.alpha.val normal.beta.val)) = M.base.J k
  generator_minimal : ∀ i, tieGenerators k M.base normal.alpha.val normal.beta.val i ∉
    Ideal.span (tieGenerators k M.base normal.alpha.val normal.beta.val '' {j | j ≠ i})

def InternalFrontend.initial {k : Type*} [Field k] {M : MultiplicityBase Gamma} {h : ℕ}
    (F : InternalFrontend k M h) : L3A.ArtinianMonomial k :=
  actualInitialArtinianMonomial k M.base (permutationOrder F.normal.perm)

theorem InternalFrontend.q_fs_le_one {k : Type*} [Field k] {M : MultiplicityBase Gamma} {h : ℕ}
    (F : InternalFrontend k M h) : L3A.q_fs F.initial.ideal ≤ 1 :=
  actualInitial_q_fs k M.base (permutationOrder F.normal.perm)

/-- Raw integer differences only. Nonnegativity and PCR are deliberately absent. -/
def InternalFrontend.delta1 {k : Type*} [Field k] {M : MultiplicityBase Gamma} {h : ℕ}
    (F : InternalFrontend k M h) : ℤ :=
  (L3A.mu F.initial.ideal : ℤ) - ((sourceCount M.base : ℤ) + 1)

def InternalFrontend.delta3 {k : Type*} [Field k] {M : MultiplicityBase Gamma} {h : ℕ}
    (F : InternalFrontend k M h) : ℤ :=
  (L3A.quotientType F.initial.ideal : ℤ) - (Gamma.asRelativeIdeal.idealType : ℤ)

theorem internal_frontend_exists (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 1) (h : ℕ) (hh : fiberContribution M h = 1)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h) :
    Nonempty (InternalFrontend k M h) := by
  obtain ⟨N⟩ := exists_tie_normal_form M h hz ht
  have hg := normal_form_generators k M hp h hz N
  exact ⟨⟨N, hp, ⟨hh, hz⟩, unique_full_apery_betti M h hz ht,
    internal_tie_components_singleton M h hz ht,
    internal_tie_coprime k M h hz ht N.alpha N.beta N.distinct, hg.1, hg.2⟩⟩

/-- Chosen-pivot frontend closure; the internal branch exports data, not a PCR-dependent bound. -/
theorem chosen_one_defect_frontend (k : Type*) [Field k] (B : Data Gamma)
    (hp : chosenDefect B = 1) :
    ∃ h, fiberContribution (transferBase B) h = 1 ∧
      (∀ d, d ≠ h → fiberContribution (transferBase B) d = 0) ∧
      (MonomializableAt (transferBase B) h ∨ InternalTieAt (transferBase B) h) ∧
      (MonomializableAt (transferBase B) h →
        IsMonomialIdeal k ((transferBase B).base.J k) ∧
        Gamma.asRelativeIdeal.idealType ≤ sourceCount B ∧
        sourceCount B = Presentation.rho Gamma - 1) ∧
      (InternalTieAt (transferBase B) h → Nonempty (InternalFrontend k (transferBase B) h)) := by
  have ht := one_defect_transfer k B hp
  have hpt := ht.2.2.2.2.2.2
  obtain ⟨h, hh, hz⟩ := unique_active_degree (transferBase B) hpt
  refine ⟨h, hh, hz, local_one_defect_split _ h hh, ?_, ?_⟩
  · intro hb
    exact ⟨monomializable_J k _ h hz hb, transferred_monomializable_bound k B hp h hz hb⟩
  · exact internal_frontend_exists k _ hpt h hh hz

end NS25Lean.L3B

