import NS25Lean.HomogeneousGeneratorNumber
import NS25Lean.CoarseP25
import Mathlib.Data.Finsupp.Ext

set_option linter.style.header false

/-! Standard congruence-presentation cardinality and the actual toric generator number. -/

noncomputable section
namespace NS25Lean.Presentation
open MvPolynomial ToricPresentation FourGeneratedBridge

theorem weight_factorization_val {σ : Type*} (H : AddSubmonoid ℕ) (w : σ → H)
    (u : σ →₀ ℕ) : Finsupp.weight (fun i => (w i).val) u = (factorizationMap w u).val := by
  have he : Finsupp.weight (fun i => (w i).val) = H.subtype.comp (factorizationMap w) := by
    apply Finsupp.addHom_ext
    intro i n
    simp [Finsupp.weight_single]
  exact DFunLike.congr_fun he u

theorem relationBinomial_homogeneous (k : Type*) [Field k] {σ : Type*}
    (H : AddSubmonoid ℕ) (w : σ → H) (p : (σ →₀ ℕ) × (σ →₀ ℕ))
    (hp : factorizationCongruence w p.1 p.2) :
    MvPolynomial.IsWeightedHomogeneous (fun i => (w i).val)
      (relationBinomial k p) (factorizationMap w p.1).val := by
  change factorizationMap w p.1 = factorizationMap w p.2 at hp
  exact (isWeightedHomogeneous_monomial _ _ _ (weight_factorization_val H w p.1)).sub
    (isWeightedHomogeneous_monomial _ _ _
      ((weight_factorization_val H w p.2).trans (congrArg Subtype.val hp.symm)))

/-- A minimal congruence presentation is no larger than any arbitrary toric ideal generating set. -/
theorem minimalPresentation_card_le_generators (k : Type*) [Field k] {n : ℕ}
    (H : AddSubmonoid ℕ) (w : Fin n → H) (hw : ∀ i, 0 < (w i).val)
    (s : Finset ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))) (hs : IsMinimalPresentation w s)
    (t : Finset (MvPolynomial (Fin n) k)) (ht : Ideal.span (t : Set _) = toricIdeal k H w) :
    s.card ≤ t.card := by
  classical
  let g : s → MvPolynomial (Fin n) k := fun p => relationBinomial k p.val
  let d : s → ℕ := fun p => (factorizationMap w p.val.1).val
  have hg : ∀ p : s, (g p).IsWeightedHomogeneous (fun i => (w i).val) (d p) := by
    intro p
    apply relationBinomial_homogeneous k H w p.val
    have he : generatedCongruence (s : Set _) = factorizationCongruence w := hs.1
    rw [← he]
    exact AddConGen.Rel.of _ _ p.property
  have hm : ∀ p : s, g p ∉ Ideal.span (g '' {q | q ≠ p}) := by
    intro p hp
    apply binomial_not_mem_erase_of_minimal k w s hs p.val p.property
    have hsub : g '' {q | q ≠ p} ⊆
        relationBinomial k '' (s.erase p.val : Set ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))) := by
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨q.val, Finset.mem_erase.mpr ⟨fun h => hq (Subtype.ext h), q.property⟩, rfl⟩
    simpa only [relationIdeal, g, Finset.coe_erase] using (Ideal.span_mono hsub hp)
  have hrange : Set.range g = relationBinomial k '' (s : Set ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))) := by
    ext f
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have he := (isPresentation_iff_relationIdeal_eq_ker k w s).mp hs.1
  rw [factorizationAlgebraMap_eq_toricMap] at he
  change relationIdeal k (s : Set _) = toricIdeal k H w at he
  have ht' : Ideal.span (t : Set _) = Ideal.span (Set.range g) := by
    rw [hrange]
    exact ht.trans he.symm
  have hc := PositivePresentation.homogeneous_card_le_generators
    (fun i => (w i).val) hw g d hg hm t ht'
  simpa only [Fintype.card_coe] using hc

/-- Every inclusion-minimal presentation has exactly the arbitrary toric generator number. -/
theorem minimalPresentation_card_eq_toricGeneratorNumber (k : Type*) [Field k] {n : ℕ}
    (H : AddSubmonoid ℕ) (w : Fin n → H) (hw : ∀ i, 0 < (w i).val)
    (s : Finset ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))) (hs : IsMinimalPresentation w s) :
    s.card = toricGeneratorNumber k H w := by
  obtain ⟨t, hc, ht⟩ := toricGeneratorNumber_attained k H w
  apply le_antisymm
  · exact hc ▸ minimalPresentation_card_le_generators k H w hw s hs t ht
  · exact toricGeneratorNumber_le_card_of_presentation k H w s hs.1

theorem presentationNumber_eq_toricGeneratorNumber (k : Type*) [Field k] {n : ℕ}
    (H : AddSubmonoid ℕ) (w : Fin n → H) (hw : ∀ i, 0 < (w i).val) :
    presentationNumber w = toricGeneratorNumber k H w := by
  obtain ⟨s, hs, hc⟩ := exists_minimalPresentation w
  exact hc.symm.trans (minimalPresentation_card_eq_toricGeneratorNumber k H w hw s hs)

/-- The missing reverse inequality, for every finite number of positive generator degrees. -/
theorem presentationNumber_le_toricGeneratorNumber (k : Type*) [Field k] {n : ℕ}
    (H : AddSubmonoid ℕ) (w : Fin n → H) (hw : ∀ i, 0 < (w i).val) :
    presentationNumber w ≤ toricGeneratorNumber k H w :=
  (presentationNumber_eq_toricGeneratorNumber k H w hw).le

/-- Ordinary inclusion-minimality, not minimum-cardinality minimality, determines the size. -/
theorem card_eq_presentationNumber_of_minimal {n : ℕ}
    (H : AddSubmonoid ℕ) (w : Fin n → H) (hw : ∀ i, 0 < (w i).val)
    (s : Finset ((Fin n →₀ ℕ) × (Fin n →₀ ℕ))) (hs : IsMinimalPresentation w s) :
    s.card = presentationNumber w :=
  (minimalPresentation_card_eq_toricGeneratorNumber ℚ H w hw s hs).trans
    (presentationNumber_eq_toricGeneratorNumber ℚ H w hw).symm

theorem toricGeneratorNumber_field_independent (k K : Type*) [Field k] [Field K] {n : ℕ}
    (H : AddSubmonoid ℕ) (w : Fin n → H) (hw : ∀ i, 0 < (w i).val) :
    toricGeneratorNumber k H w = toricGeneratorNumber K H w :=
  (presentationNumber_eq_toricGeneratorNumber k H w hw).symm.trans
    (presentationNumber_eq_toricGeneratorNumber K H w hw)

/-- The standard intrinsic congruence invariant equals the source's algebraic rho. -/
theorem rho_eq_toricGeneratorNumber (k : Type*) [Field k]
    (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    rho Gamma = toricGeneratorNumber k Gamma.toAddSubmonoid (fourDegrees Gamma m n₁ n₂ n₃ h) := by
  rw [rho_eq_four_presentationNumber Gamma m n₁ n₂ n₃ h]
  exact presentationNumber_eq_toricGeneratorNumber k _ _
    (fourDegrees_minimal_data Gamma m n₁ n₂ n₃ h).2.1

theorem fourGenerated_minimalPresentation_card_eq_rho
    (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃)
    (s : Finset ((Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ)))
    (hs : IsMinimalPresentation (fourDegrees Gamma m n₁ n₂ n₃ h) s) : s.card = rho Gamma := by
  rw [rho_eq_four_presentationNumber Gamma m n₁ n₂ n₃ h]
  exact card_eq_presentationNumber_of_minimal _ _
    (fourDegrees_minimal_data Gamma m n₁ n₂ n₃ h).2.1 s hs

/-- All inclusion-minimal presentations on the intrinsic atoms have the standard size. -/
theorem minimalPresentation_card_eq_rho (Gamma : NumericalSemigroup)
    (s : Finset ((Atom Gamma →₀ ℕ) × (Atom Gamma →₀ ℕ)))
    (hs : IsMinimalPresentation (atomDegrees Gamma) s) : s.card = rho Gamma := by
  classical
  let := Fintype.ofFinite (Atom Gamma)
  let e := Fintype.equivFin (Atom Gamma)
  let v : Fin (Fintype.card (Atom Gamma)) → Gamma.toAddSubmonoid :=
    fun i => atomDegrees Gamma (e.symm i)
  have he : ∀ i, v (e i) = atomDegrees Gamma i := by intro i; simp [v]
  have hv : ∀ i, 0 < (v i).val := by
    intro i
    exact Nat.pos_of_ne_zero (e.symm i).property.2.1
  have ht := isMinimalPresentation_reindex e (atomDegrees Gamma) v he s hs
  have hc := card_eq_presentationNumber_of_minimal Gamma.toAddSubmonoid v hv _ ht
  have hn : presentationNumber v = rho Gamma :=
    presentationNumber_reindex e (atomDegrees Gamma) v he
  have hc' : s.card = presentationNumber v := by
    simpa only [transportRelations_card] using hc
  exact hc'.trans hn

theorem minimalPresentation_card_invariant (Gamma : NumericalSemigroup)
    (s t : Finset ((Atom Gamma →₀ ℕ) × (Atom Gamma →₀ ℕ)))
    (hs : IsMinimalPresentation (atomDegrees Gamma) s)
    (ht : IsMinimalPresentation (atomDegrees Gamma) t) : s.card = t.card :=
  (minimalPresentation_card_eq_rho Gamma s hs).trans
    (minimalPresentation_card_eq_rho Gamma t ht).symm

/-- Both the coefficient field and the chosen ordering/presentation may change. -/
theorem fourGenerated_toricGeneratorNumber_presentation_independent
    (k K : Type*) [Field k] [Field K] (Gamma : NumericalSemigroup)
    (m n₁ n₂ n₃ a b c d : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃)
    (h' : IsMinimallyGeneratedByFour Gamma a b c d) :
    toricGeneratorNumber k Gamma.toAddSubmonoid (fourDegrees Gamma m n₁ n₂ n₃ h) =
      toricGeneratorNumber K Gamma.toAddSubmonoid (fourDegrees Gamma a b c d h') :=
  (rho_eq_toricGeneratorNumber k Gamma m n₁ n₂ n₃ h).symm.trans
    (rho_eq_toricGeneratorNumber K Gamma a b c d h')

theorem atoms_card_of_embeddingDimensionFour (Gamma : NumericalSemigroup)
    (he : CoarseP25.HasEmbeddingDimensionFour Gamma) : Nat.card (Atom Gamma) = 4 := by
  obtain ⟨m, n₁, n₂, n₃, h⟩ := he
  obtain ⟨hg, hp, hm⟩ := fourDegrees_minimal_data Gamma m n₁ n₂ n₃ h
  have hc := Nat.card_congr (degreeAtomEquiv Gamma (fourDegrees Gamma m n₁ n₂ n₃ h) hg hp hm)
  simpa using hc.symm

theorem fourGenerated_weakPresentation_standard
    (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    tailGeneratorCount (generatedThree n₁ n₂ n₃)
      (aperyTail Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) m) ≤ rho Gamma := by
  rw [rho_eq_toricGeneratorNumber ℚ Gamma m n₁ n₂ n₃ h]
  exact fourGenerated_tailGeneratorCount_le_toricGeneratorNumber ℚ Gamma m n₁ n₂ n₃ h

theorem fourGenerated_coarseP25_standard
    (Gamma : NumericalSemigroup) (m n₁ n₂ n₃ : ℕ)
    (h : IsMinimallyGeneratedByFour Gamma m n₁ n₂ n₃) :
    Gamma.asRelativeIdeal.idealType ≤ 2 * rho Gamma := by
  rw [rho_eq_toricGeneratorNumber ℚ Gamma m n₁ n₂ n₃ h]
  exact CoarseP25.fourGenerated_coarseP25_toric ℚ Gamma m n₁ n₂ n₃ h

/-- JoA Theorem 2.10, now using the intrinsic standard minimal-presentation invariant. -/
theorem joa_theorem_2_10 (Gamma : NumericalSemigroup)
    (he : CoarseP25.HasEmbeddingDimensionFour Gamma) :
    Gamma.asRelativeIdeal.idealType ≤ 2 * rho Gamma := by
  obtain ⟨m, n₁, n₂, n₃, h⟩ := he
  exact fourGenerated_coarseP25_standard Gamma m n₁ n₂ n₃ h

end NS25Lean.Presentation
