import NS25Lean.OneDefectTie

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3B
open ChosenBase L2B L2B2A L2B2A2 MvPolynomial
variable {Gamma : NumericalSemigroup}

def sourcePolynomial (k : Type*) [Field k] (B : Data Gamma) (s : Source B) :
    ToricPresentation.Poly k 3 := monomial (sourceRepresentative B s).val 1

def tieGenerators (k : Type*) [Field k] (B : Data Gamma) (α β : Fin 3 →₀ ℕ) :
    Source B ⊕ Unit → ToricPresentation.Poly k 3 :=
  Sum.elim (sourcePolynomial k B) (fun _ => monomial α 1 - monomial β 1)

/-- Degreewise graded induction: every nJ relation is assembled from strictly lower moves. -/
theorem nJ_mem_of_lower (k : Type*) [Field k] (B : Data Gamma)
    (L : Ideal (ToricPresentation.Poly k 3)) (d : ℕ)
    (hl : ∀ e, e < d →
      (∀ u v : FactorizationFiber B e, monomial u.val (1 : k) - monomial v.val 1 ∈ L) ∧
      (∀ u : FactorizationFiber B e, e ∈ B.K → monomial u.val (1 : k) ∈ L))
    (f : ToricPresentation.Poly k 3) (hf : f.IsWeightedHomogeneous (weights B) d)
    (hn : f ∈ variableIdeal k * B.J k) : f ∈ L := by
  have hs := (nJ_degree_mem_iff k B d f hf).mp hn
  have hle : Submodule.span k (degreeSharedMoves k B d ∪ degreeBoundaryMoves k B d) ≤
      L.restrictScalars k := by
    apply Submodule.span_le.mpr
    intro g hg
    rcases hg with ⟨u, v, ⟨j, hu, hv⟩, rfl⟩ | ⟨u, ⟨j, hu, hk⟩, rfl⟩
    · change monomial u.val (1 : k) - monomial v.val 1 ∈ L
      have heu := removed_weight B d u j hu
      have hev := removed_weight B d v j hv
      have hp := weights_positive B j
      let u' : FactorizationFiber B (d - weights B j) :=
        ⟨u.val - Finsupp.single j 1, by omega⟩
      let v' : FactorizationFiber B (d - weights B j) :=
        ⟨v.val - Finsupp.single j 1, by omega⟩
      have hh := L.mul_mem_left (X j) ((hl _ (by omega)).1 u' v')
      simpa only [mul_sub, u', v', variable_mul_removed k u.val j hu,
        variable_mul_removed k v.val j hv] using hh
    · change monomial u.val (1 : k) ∈ L
      have heu := removed_weight B d u j hu
      have hp := weights_positive B j
      let u' : FactorizationFiber B (d - weights B j) :=
        ⟨u.val - Finsupp.single j 1, by omega⟩
      have hh := L.mul_mem_left (X j) ((hl _ (by omega)).2 u' hk)
      simpa only [u', variable_mul_removed k u.val j hu] using hh
  exact hle hs

theorem binomial_mem_nJ_of_contribution_zero (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (d : ℕ) (hz : fiberContribution M d = 0)
    (u v : FactorizationFiber M.base d) :
    monomial u.val (1 : k) - monomial v.val 1 ∈ variableIdeal k * M.base.J k := by
  have he : tailDegreeImage k M.base d = ⊥ :=
    Submodule.finrank_eq_zero.mp ((tailDegreeImage_finrank_eq_fiberContribution k M d).trans hz)
  let f : M.base.IH k := ⟨monomial u.val 1 - monomial v.val 1,
    binomial_mem_IH k M.base _ _ (u.property.trans v.property.symm)⟩
  have hf : f ∈ tailDegreeSpace k M.base d :=
    (isWeightedHomogeneous_monomial (weights M.base) u.val (1 : k) u.property).sub
      (isWeightedHomogeneous_monomial (weights M.base) v.val (1 : k) v.property)
  have hm : tailToGeneratorQuotient k M.base f ∈ tailDegreeImage k M.base d := ⟨f, hf, rfl⟩
  rw [he] at hm
  exact (Submodule.Quotient.mk_eq_zero (generatorRelations k M.base)).mp hm

/-- Actual ideal generation, using the source representatives and the two actual factorizations. -/
theorem internal_tie_generators_span (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0)
    (α β : FactorizationFiber M.base h)
    (htwo : ∀ u : FactorizationFiber M.base h, u = α ∨ u = β) :
    Ideal.span (Set.range (tieGenerators k M.base α.val β.val)) = M.base.J k := by
  let L := Ideal.span (Set.range (tieGenerators k M.base α.val β.val))
  have hf : monomial α.val (1 : k) - monomial β.val 1 ∈ L :=
    Ideal.subset_span ⟨Sum.inr (), rfl⟩
  have hg (s : Source M.base) : sourcePolynomial k M.base s ∈ L :=
    Ideal.subset_span ⟨Sum.inl s, rfl⟩
  have hall (d : ℕ) :
      (∀ u v : FactorizationFiber M.base d, monomial u.val (1 : k) - monomial v.val 1 ∈ L) ∧
      (∀ u : FactorizationFiber M.base d, d ∈ M.base.K → monomial u.val (1 : k) ∈ L) := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      have hn := nJ_mem_of_lower k M.base L d ih
      have hb (u v : FactorizationFiber M.base d) :
          monomial u.val (1 : k) - monomial v.val 1 ∈ L := by
        by_cases he : d = h
        · subst d
          rcases htwo u with rfl | rfl <;> rcases htwo v with rfl | rfl
          · simp
          · exact hf
          · simpa only [neg_sub] using L.neg_mem hf
          · simp
        · exact hn _ ((isWeightedHomogeneous_monomial _ u.val (1 : k) u.property).sub
            (isWeightedHomogeneous_monomial _ v.val (1 : k) v.property))
            (binomial_mem_nJ_of_contribution_zero k M d (hz d he) u v)
      refine ⟨hb, ?_⟩
      intro u hu
      by_cases hs : FourGeneratedBridge.IsMinimalTailGenerator M.base.H M.base.K d
      · let s : Source M.base := ⟨d, hs⟩
        have hh := L.add_mem (hb u (sourceRepresentative M.base s)) (hg s)
        simpa only [sourcePolynomial, sub_add_cancel] using hh
      · obtain ⟨v, hv, hvn⟩ := nonminimal_boundary_representative k M.base u.val
          (u.property.symm ▸ hu) (u.property.symm ▸ hs)
        let v' : FactorizationFiber M.base d := ⟨v, hv.trans u.property⟩
        have hvL := hn _ (isWeightedHomogeneous_monomial _ v (1 : k) v'.property) hvn
        have hh := L.add_mem (hb u v') hvL
        simpa only [v', sub_add_cancel] using hh
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨s | u, rfl⟩
    · exact boundary_monomial_mem_J k M.base _
        ((sourceRepresentative M.base s).property.symm ▸ s.property.1)
    · have hle : M.base.IH k ≤ M.base.J k := by rw [M.base.J_eq_IH_sup_MK k]; exact le_sup_left
      exact hle (binomial_mem_IH k M.base _ _ (α.property.trans β.property.symm))
  · rw [J_eq_ideal_span_moves]
    apply Ideal.span_le.mpr
    rintro _ (⟨u, v, he, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact (hall (weight M.base u)).1 ⟨u, rfl⟩ ⟨v, he.symm⟩
    · exact (hall (weight M.base u)).2 ⟨u, rfl⟩ hu

/-- A generating family attaining the actual generator number is irredundant. -/
theorem irredundant_of_card_eq_mu {R ι : Type*} [CommRing R] [Fintype ι]
    (g : ι → R) (I : Ideal R) (hgen : Ideal.span (Set.range g) = I)
    (hcard : Fintype.card ι = I.spanFinrank) :
    ∀ i, g i ∉ Ideal.span (g '' {j | j ≠ i}) := by
  classical
  intro i hi
  let s := (Finset.univ.erase i).image g
  have hs : (s : Set R) = g '' {j | j ≠ i} := by
    ext x; simp [s]
  have he : Ideal.span (s : Set R) = I := by
    rw [hs, ← hgen]
    apply le_antisymm (Ideal.span_mono (Set.image_subset_range _ _))
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j; exact hi
    · exact Ideal.subset_span ⟨j, hj, rfl⟩
  have hb : I.spanFinrank ≤ s.card := by
    rw [← he]
    simpa only [Set.ncard_coe_finset] using Submodule.spanFinrank_span_le_ncard_of_finite s.finite_toSet
  have hlt : s.card < Fintype.card ι :=
    lt_of_le_of_lt Finset.card_image_le (by
      haveI : Nonempty ι := ⟨i⟩
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      have hpos : 0 < Fintype.card ι := Fintype.card_pos
      omega)
  omega

/-- S source monomials plus one binomial, with actual generation and actual irredundancy. -/
theorem internal_tie_minimal_generators (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 1) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h) :
    ∃ α β : FactorizationFiber M.base h, α ≠ β ∧
      (∀ u : FactorizationFiber M.base h, u = α ∨ u = β) ∧
      IsRelPrime (monomial α.val (1 : k)) (monomial β.val 1) ∧
      Ideal.span (Set.range (tieGenerators k M.base α.val β.val)) = M.base.J k ∧
      ∀ i, tieGenerators k M.base α.val β.val i ∉
        Ideal.span (tieGenerators k M.base α.val β.val '' {j | j ≠ i}) := by
  classical
  obtain ⟨α, β, hne, htwo⟩ := internal_tie_two_factorizations M h hz ht
  have hgen := internal_tie_generators_span k M h hz α β htwo
  refine ⟨α, β, hne, htwo, internal_tie_coprime k M h hz ht α β hne, hgen, ?_⟩
  letI := Fintype.ofFinite (Source M.base)
  apply irredundant_of_card_eq_mu _ _ hgen
  rw [Fintype.card_sum, show Fintype.card Unit = 1 from Fintype.card_unique, M.base.muj k]
  have hs : Fintype.card (Source M.base) = sourceCount M.base := Nat.card_eq_fintype_card.symm
  rw [hs]
  have := sourceCount_add_defect M.base
  omega

end NS25Lean.L3B


