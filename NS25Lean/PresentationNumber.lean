import NS25Lean.PresentationCongruence
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option linter.style.header false

/-! Finite presentations of the usual factorization congruence.
`IsMinimalPresentation` means inclusion-minimal, whereas `presentationNumber`
is the least finite presentation cardinality. Equality of the cardinalities of
all inclusion-minimal presentations is a separate, non-definitional obligation.
-/

noncomputable section
namespace NS25Lean.Presentation

variable {σ τ : Type*} {H : Type*} [AddCommMonoid H]

def factorizationMap (w : σ → H) : (σ →₀ ℕ) →+ H :=
  (Finsupp.linearCombination ℕ w).toAddMonoidHom

@[simp] theorem factorizationMap_single (w : σ → H) (i : σ) (n : ℕ) :
    factorizationMap w (Finsupp.single i n) = n • w i :=
  Finsupp.linearCombination_single ..

def factorizationCongruence (w : σ → H) : AddCon (σ →₀ ℕ) :=
  AddCon.ker (factorizationMap w)

@[simp] theorem factorizationCongruence_iff (w : σ → H) (u v : σ →₀ ℕ) :
    factorizationCongruence w u v ↔ factorizationMap w u = factorizationMap w v := Iff.rfl

def IsPresentation (w : σ → H) (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) : Prop :=
  generatedCongruence (s : Set _) = factorizationCongruence w

/-- Ordinary minimality under deletion of relations, not minimum cardinality. -/
def IsMinimalPresentation (w : σ → H) (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) : Prop :=
  IsPresentation w s ∧ ∀ t ⊆ s, IsPresentation w t → s ⊆ t

theorem exists_presentation [Finite σ] (w : σ → H) :
    ∃ s, IsPresentation w s := exists_finset_generating_congruence (factorizationCongruence w)

/-- Least cardinality of finite presentations of the factorization congruence.
The definition contains neither a field nor a polynomial ideal. -/
def presentationNumber (w : σ → H) : ℕ :=
  sInf {n | ∃ s, IsPresentation w s ∧ s.card = n}

theorem presentationNumber_le_card (w : σ → H)
    (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) (hs : IsPresentation w s) :
    presentationNumber w ≤ s.card := csInf_le' ⟨s, hs, rfl⟩

theorem presentationNumber_attained [Finite σ] (w : σ → H) :
    ∃ s, IsPresentation w s ∧ s.card = presentationNumber w := by
  obtain ⟨s, hs⟩ := exists_presentation w
  exact csInf_mem (s := {n | ∃ s, IsPresentation w s ∧ s.card = n}) ⟨s.card, s, hs, rfl⟩

theorem isMinimalPresentation_of_card_eq (w : σ → H)
    (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) (hs : IsPresentation w s)
    (hcard : s.card = presentationNumber w) : IsMinimalPresentation w s := by
  refine ⟨hs, fun t hts ht => ?_⟩
  have hle : s.card ≤ t.card := hcard ▸ presentationNumber_le_card w t ht
  exact (Finset.eq_of_subset_of_card_le hts hle).symm.subset

theorem exists_minimalPresentation [Finite σ] (w : σ → H) :
    ∃ s, IsMinimalPresentation w s ∧ s.card = presentationNumber w := by
  obtain ⟨s, hs, hc⟩ := presentationNumber_attained w
  exact ⟨s, isMinimalPresentation_of_card_eq w s hs hc, hc⟩

def transportRelations {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (e : M ≃+ N) (s : Finset (M × M)) : Finset (N × N) :=
  s.map (e.toEquiv.prodCongr e.toEquiv).toEmbedding

@[simp] theorem transportRelations_card {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (e : M ≃+ N) (s : Finset (M × M)) : (transportRelations e s).card = s.card :=
  Finset.card_map _

@[simp] theorem mem_transportRelations {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (e : M ≃+ N) (s : Finset (M × M)) (x y : M) :
    (e x, e y) ∈ transportRelations e s ↔ (x, y) ∈ s := by
  change (e.toEquiv.prodCongr e.toEquiv) (x, y) ∈
    s.map (e.toEquiv.prodCongr e.toEquiv).toEmbedding ↔ _
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem generatedCongruence_transport {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (e : M ≃+ N) (s : Finset (M × M)) (x y : M) :
    generatedCongruence (transportRelations e s : Set _) (e x) (e y) ↔
      generatedCongruence (s : Set _) x y := by
  have he := AddCon.comap_addConGen_equiv e
    (fun u v => (u, v) ∈ (transportRelations e s : Set _))
  have hr : (fun u v => (e u, e v) ∈ (transportRelations e s : Set _)) =
      (fun u v => (u, v) ∈ (s : Set _)) := by
    funext u v
    exact propext (mem_transportRelations e s u v)
  rw [hr] at he
  exact Iff.of_eq (congrArg (fun c : AddCon M => c x y) he)

theorem factorizationMap_reindex (e : σ ≃ τ) (w : σ → H) (v : τ → H)
    (hw : ∀ i, v (e i) = w i) (u : σ →₀ ℕ) :
    factorizationMap v (Finsupp.domCongr e u) = factorizationMap w u := by
  change Finsupp.linearCombination ℕ v (Finsupp.equivMapDomain e u) = _
  rw [Finsupp.linearCombination_equivMapDomain]
  have he : v ∘ e = w := funext hw
  rw [he]
  rfl

theorem isPresentation_reindex (e : σ ≃ τ) (w : σ → H) (v : τ → H)
    (hw : ∀ i, v (e i) = w i) (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ))) :
    IsPresentation v (transportRelations (Finsupp.domCongr e) s) ↔ IsPresentation w s := by
  constructor
  · intro hs
    apply AddCon.ext
    intro x y
    rw [← generatedCongruence_transport (Finsupp.domCongr e), hs]
    simp only [factorizationCongruence_iff, factorizationMap_reindex e w v hw]
  · intro hs
    apply AddCon.ext
    intro x y
    obtain ⟨u, rfl⟩ := (Finsupp.domCongr e).surjective x
    obtain ⟨z, rfl⟩ := (Finsupp.domCongr e).surjective y
    rw [generatedCongruence_transport, hs]
    simp only [factorizationCongruence_iff, factorizationMap_reindex e w v hw]

/-- The minimum congruence-presentation size is independent of reindexing. -/
theorem presentationNumber_reindex [Finite σ] [Finite τ]
    (e : σ ≃ τ) (w : σ → H) (v : τ → H) (hw : ∀ i, v (e i) = w i) :
    presentationNumber v = presentationNumber w := by
  apply le_antisymm
  · obtain ⟨s, hs, hc⟩ := presentationNumber_attained w
    have h := presentationNumber_le_card v _ ((isPresentation_reindex e w v hw s).mpr hs)
    simpa only [transportRelations_card, hc] using h
  · obtain ⟨s, hs, hc⟩ := presentationNumber_attained v
    have hw' : ∀ i, w (e.symm i) = v i := by intro i; simpa using (hw (e.symm i)).symm
    have h := presentationNumber_le_card w _ ((isPresentation_reindex e.symm v w hw' s).mpr hs)
    simpa only [transportRelations_card, hc] using h

@[simp] theorem transportRelations_symm {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (e : M ≃+ N) (s : Finset (M × M)) :
    transportRelations e.symm (transportRelations e s) = s := by
  ext ⟨x, y⟩
  simp [transportRelations, Finset.mem_map_equiv]

theorem transportRelations_mono {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (e : M ≃+ N) {s t : Finset (M × M)} (h : s ⊆ t) :
    transportRelations e s ⊆ transportRelations e t := Finset.map_subset_map.mpr h

/-- Reindexing preserves ordinary inclusion-minimal presentations, with their cardinality. -/
theorem isMinimalPresentation_reindex (e : σ ≃ τ) (w : σ → H) (v : τ → H)
    (hw : ∀ i, v (e i) = w i) (s : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)))
    (hs : IsMinimalPresentation w s) :
    IsMinimalPresentation v (transportRelations (Finsupp.domCongr e) s) := by
  refine ⟨(isPresentation_reindex e w v hw s).mpr hs.1, ?_⟩
  intro t hts ht
  let E : (σ →₀ ℕ) ≃+ (τ →₀ ℕ) := Finsupp.domCongr e
  change t ⊆ transportRelations E s at hts
  have hw' : ∀ i, w (e.symm i) = v i := by intro i; simpa using (hw (e.symm i)).symm
  have htp : IsPresentation w (transportRelations E.symm t) :=
    (isPresentation_reindex e.symm v w hw' t).mpr ht
  have hsub : transportRelations E.symm t ⊆ s := by
    simpa only [transportRelations_symm] using transportRelations_mono E.symm hts
  have hback := hs.2 _ hsub htp
  have hfor := transportRelations_mono E hback
  have hinv := transportRelations_symm E.symm t
  simp only [AddEquiv.symm_symm] at hinv
  rw [hinv] at hfor
  exact hfor

end NS25Lean.Presentation
