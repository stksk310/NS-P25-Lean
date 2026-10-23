import NS25Lean.PresentationNumber
import NS25Lean.FourGeneratedToric

set_option linter.style.header false

noncomputable section
namespace NS25Lean.Presentation
variable (k : Type*) [Field k]
variable {σ H : Type*} [AddCommMonoid H]

def factorizationAlgebraMap (w : σ → H) :
    MvPolynomial σ k →ₐ[k] AddMonoidAlgebra k H :=
  AddMonoidAlgebra.mapDomainAlgHom k k (factorizationMap w)

@[simp] theorem factorizationAlgebraMap_monomial (w : σ → H) (u : σ →₀ ℕ) (a : k) :
    factorizationAlgebraMap k w (MvPolynomial.monomial u a) =
      AddMonoidAlgebra.single (factorizationMap w u) a := by
  change AddMonoidAlgebra.mapDomain (factorizationMap w) (AddMonoidAlgebra.single u a) = _
  exact AddMonoidAlgebra.mapDomain_single ..

theorem factorizationAlgebraMap_eq_toricMap {n : ℕ} (H : AddSubmonoid ℕ) (w : Fin n → H) :
    factorizationAlgebraMap k w = ToricPresentation.toricMap k H w := by
  ext i : 1
  change factorizationAlgebraMap k w (MvPolynomial.monomial (Finsupp.single i 1) 1) = _
  simp

/-- The full factorization-congruence binomial ideal is the actual algebra kernel. -/
theorem relationIdeal_factorization_eq_ker (w : σ → H) :
    relationIdeal k {p | factorizationCongruence w p.1 p.2} =
      RingHom.ker (factorizationAlgebraMap k w).toRingHom := by
  classical
  let I := relationIdeal k {p | factorizationCongruence w p.1 p.2}
  let q := Ideal.Quotient.mkₐ k I
  let rep : H → (σ →₀ ℕ) := fun h =>
    if hh : ∃ u, factorizationMap w u = h then Classical.choose hh else 0
  have hrep (u : σ →₀ ℕ) : factorizationMap w (rep (factorizationMap w u)) =
      factorizationMap w u := by
    dsimp only [rep]
    rw [dite_eq_left (show ∃ v, factorizationMap w v = factorizationMap w u from ⟨u, rfl⟩)]
    exact Classical.choose_spec
      (show ∃ v, factorizationMap w v = factorizationMap w u from ⟨u, rfl⟩)
  let L : AddMonoidAlgebra k H →ₗ[k] (MvPolynomial σ k ⧸ I) :=
    (Finsupp.linearCombination k (fun h => q (MvPolynomial.monomial (rep h) 1))).comp
      (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap
  have hL (h : H) (a : k) : L (AddMonoidAlgebra.single h a) =
      a • q (MvPolynomial.monomial (rep h) 1) := by
    change Finsupp.linearCombination k _ (Finsupp.single h a) = _
    exact Finsupp.linearCombination_single ..
  have hcomp (f : MvPolynomial σ k) : L (factorizationAlgebraMap k w f) = q f := by
    induction f using MvPolynomial.induction_on' with
    | monomial u a =>
        rw [factorizationAlgebraMap_monomial, hL]
        have hbin : relationBinomial k (rep (factorizationMap w u), u) ∈ I :=
          Ideal.subset_span ⟨_, hrep u, rfl⟩
        have hq : q (MvPolynomial.monomial (rep (factorizationMap w u)) 1) =
            q (MvPolynomial.monomial u 1) :=
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hbin
        have hm : a • MvPolynomial.monomial u (1 : k) = MvPolynomial.monomial u a := by
          simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [hq, ← map_smul, hm]
    | add f g hf hg => simp only [map_add, hf, hg]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨u, v⟩, huv, rfl⟩
    change factorizationAlgebraMap k w (MvPolynomial.monomial u 1 -
      MvPolynomial.monomial v 1) = 0
    simp only [map_sub, factorizationAlgebraMap_monomial]
    rw [show factorizationMap w u = factorizationMap w v from huv, sub_self]
  · intro f hf
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    change q f = 0
    rw [← hcomp f, show factorizationAlgebraMap k w f = 0 from hf, map_zero]

theorem relationIdeal_eq_of_generatedCongruence_eq (r s : Set ((σ →₀ ℕ) × (σ →₀ ℕ)))
    (h : generatedCongruence r = generatedCongruence s) :
    relationIdeal k r = relationIdeal k s := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨u, v⟩, huv, rfl⟩
    apply relationBinomial_mem_of_generated
    rw [← h]
    exact AddConGen.Rel.of _ _ huv
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨u, v⟩, huv, rfl⟩
    apply relationBinomial_mem_of_generated
    rw [h]
    exact AddConGen.Rel.of _ _ huv

/-- Presenting the factorization congruence is equivalent to generating the kernel by binomials. -/
theorem isPresentation_iff_relationIdeal_eq_ker (w : σ → H)
    (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) :
    IsPresentation w s ↔ relationIdeal k (s : Set _) =
      RingHom.ker (factorizationAlgebraMap k w).toRingHom := by
  rw [← relationIdeal_factorization_eq_ker]
  constructor
  · intro hs
    apply relationIdeal_eq_of_generatedCongruence_eq
    rw [generatedCongruence_all_relations]
    exact hs
  · intro hs
    have he := generatedCongruence_eq_of_relationIdeal_eq k _ _ hs
    change generatedCongruence (s : Set _) = factorizationCongruence w
    simpa only [generatedCongruence_all_relations] using he

theorem toricGeneratorNumber_le_card_of_presentation {n : ℕ}
    (H : AddSubmonoid ℕ) (w : Fin n → H)
    (s : Finset ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))) (hs : IsPresentation w s) :
    ToricPresentation.toricGeneratorNumber k H w ≤ s.card := by
  classical
  have he := (isPresentation_iff_relationIdeal_eq_ker k w s).mp hs
  rw [factorizationAlgebraMap_eq_toricMap] at he
  change relationIdeal k (s : Set _) = ToricPresentation.toricIdeal k H w at he
  let t := s.image (relationBinomial k)
  have ht : Submodule.span (MvPolynomial (Fin n) k) (t : Set _) =
      ToricPresentation.toricIdeal k H w := by
    unfold relationIdeal at he
    change Submodule.span (MvPolynomial (Fin n) k) _ = _ at he
    simpa only [t, Finset.coe_image] using he
  have hb := Submodule.spanFinrank_span_le_ncard_of_finite (R := MvPolynomial (Fin n) k)
    t.finite_toSet
  rw [ht] at hb
  have hb' : ToricPresentation.toricGeneratorNumber k H w ≤ t.card := by
    simpa only [ToricPresentation.toricGeneratorNumber, Set.ncard_coe_finset] using hb
  exact hb'.trans Finset.card_image_le

/-- Verified one-sided bridge. The converse for arbitrary polynomial generators is separate. -/
theorem toricGeneratorNumber_le_presentationNumber {n : ℕ}
    (H : AddSubmonoid ℕ) (w : Fin n → H) :
    ToricPresentation.toricGeneratorNumber k H w ≤ presentationNumber w := by
  obtain ⟨s, hs, hc⟩ := presentationNumber_attained w
  exact hc ▸ toricGeneratorNumber_le_card_of_presentation k H w s hs

open Classical in
/-- Inclusion-minimality implies algebraic irredundancy of the associated binomials.
This does not identify irredundant size with the minimum arbitrary generator number. -/
theorem binomial_not_mem_erase_of_minimal (w : σ → H)
    (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) (hs : IsMinimalPresentation w s)
    (p : (σ →₀ ℕ) × (σ →₀ ℕ)) (hp : p ∈ s) :
    relationBinomial k p ∉ relationIdeal k (s.erase p : Set _) := by
  classical
  intro hmem
  have he : relationIdeal k (s : Set ((σ →₀ ℕ) × (σ →₀ ℕ))) =
      relationIdeal k (s.erase p : Set ((σ →₀ ℕ) × (σ →₀ ℕ))) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨q, hq, rfl⟩
      by_cases hqp : q = p
      · subst q; exact hmem
      · exact Ideal.subset_span ⟨q, Finset.mem_erase.mpr ⟨hqp, hq⟩, rfl⟩
    · exact Ideal.span_mono (Set.image_mono (by
        intro q hq; exact Finset.mem_of_mem_erase hq))
  have ht : IsPresentation w (s.erase p) :=
    (isPresentation_iff_relationIdeal_eq_ker k w _).mpr
      (he.symm.trans ((isPresentation_iff_relationIdeal_eq_ker k w s).mp hs.1))
  have hbad := hs.2 _ (Finset.erase_subset _ _) ht hp
  simp at hbad

theorem relationBinomial_injOn_of_minimal (w : σ → H)
    (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) (hs : IsMinimalPresentation w s) :
    Set.InjOn (relationBinomial k) (s : Set ((σ →₀ ℕ) × (σ →₀ ℕ))) := by
  classical
  intro p hp q hq he
  by_contra hpq
  apply binomial_not_mem_erase_of_minimal k w s hs p hp
  rw [he]
  exact Ideal.subset_span ⟨q, Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩, rfl⟩

open Classical in
/-- Passing from an inclusion-minimal relation set to its binomial set loses no elements. -/
theorem minimal_binomial_image_card (w : σ → H)
    (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) (hs : IsMinimalPresentation w s) :
    (s.image (relationBinomial k)).card = s.card := by
  classical
  exact Finset.card_image_iff.mpr (relationBinomial_injOn_of_minimal k w s hs)

end NS25Lean.Presentation
