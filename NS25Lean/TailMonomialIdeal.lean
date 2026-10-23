import NS25Lean.SpecializationBridge
import NS25Lean.TailIdealNormalization
import Mathlib.Algebra.MonoidAlgebra.Ideal

set_option linter.style.header false

noncomputable section
namespace NS25Lean.ToricPresentation
open FourGeneratedBridge
variable (k : Type*) [Field k]

def tailMonomialIdeal (Gamma H : AddSubmonoid ℕ) (m : ℕ) :
    Ideal (SemigroupAlgebra k H) :=
  Ideal.span (AddMonoidAlgebra.of' k H '' {h : H | h.val ∈ aperyTail Gamma H m})

theorem mem_tailMonomialIdeal_iff (Gamma H : AddSubmonoid ℕ) (m : ℕ)
    (hHGamma : H ≤ Gamma) (f : SemigroupAlgebra k H) :
    f ∈ tailMonomialIdeal k Gamma H m ↔
      ∀ h ∈ f.coeff.support, h.val ∈ aperyTail Gamma H m := by
  rw [tailMonomialIdeal, AddMonoidAlgebra.mem_ideal_span_of'_image]
  constructor
  · intro hf h hh
    obtain ⟨h', hh', d, rfl⟩ := hf h hh
    simpa [add_comm] using aperyTail_add_mem hHGamma hh' d.property
  · intro hf h hh
    exact ⟨h, hf h hh, 0, (zero_add h).symm⟩

theorem single_mem_tailMonomialIdeal_iff (Gamma H : AddSubmonoid ℕ) (m : ℕ)
    (hHGamma : H ≤ Gamma) (h : H) :
    AddMonoidAlgebra.single h (1 : k) ∈ tailMonomialIdeal k Gamma H m ↔
      h.val ∈ aperyTail Gamma H m := by
  rw [mem_tailMonomialIdeal_iff k Gamma H m hHGamma]
  simp

def semigroupEmbedding {Gamma H : AddSubmonoid ℕ} (hHGamma : H ≤ Gamma) :
    SemigroupAlgebra k H →ₐ[k] SemigroupAlgebra k Gamma :=
  AddMonoidAlgebra.mapDomainAlgHom k k (AddSubmonoid.inclusion hHGamma)

theorem semigroupEmbedding_injective {Gamma H : AddSubmonoid ℕ} (hHGamma : H ≤ Gamma) :
    Function.Injective (semigroupEmbedding k hHGamma) :=
  AddMonoidAlgebra.mapDomain_injective
    (fun _a _b h => Subtype.ext (congrArg (fun x : Gamma => x.val) h))

@[simp] theorem semigroupEmbedding_single {Gamma H : AddSubmonoid ℕ}
    (hHGamma : H ≤ Gamma) (h : H) (a : k) :
    semigroupEmbedding k hHGamma (AddMonoidAlgebra.single h a) =
      AddMonoidAlgebra.single (AddSubmonoid.inclusion hHGamma h) a := by
  simp [semigroupEmbedding]

theorem mem_principal_monomial_iff (Gamma : AddSubmonoid ℕ) (m : Gamma)
    (f : SemigroupAlgebra k Gamma) :
    f ∈ Ideal.span {AddMonoidAlgebra.single m (1 : k)} ↔
      ∀ h ∈ f.coeff.support, m.val ≤ h.val ∧ h.val - m.val ∈ Gamma := by
  have hs : ({AddMonoidAlgebra.single m (1 : k)} : Set (SemigroupAlgebra k Gamma)) =
      AddMonoidAlgebra.of' k Gamma '' {m} := by simp [AddMonoidAlgebra.of'_apply]
  rw [hs, AddMonoidAlgebra.mem_ideal_span_of'_image]
  simp only [Set.mem_singleton_iff, exists_eq_left]
  constructor
  · intro hf h hh
    obtain ⟨d, hd⟩ := hf h hh
    have hv : h.val = d.val + m.val := congrArg Subtype.val hd
    exact ⟨by omega, by simp [hv]⟩
  · intro hf h hh
    obtain ⟨hle, hmem⟩ := hf h hh
    refine ⟨⟨h.val - m.val, hmem⟩, ?_⟩
    apply Subtype.ext
    change h.val = h.val - m.val + m.val
    omega

theorem single_dvd_single_iff (H : AddSubmonoid ℕ) (x y : H) :
    AddMonoidAlgebra.single y (1 : k) ∣ AddMonoidAlgebra.single x (1 : k) ↔
      y.val ≤ x.val ∧ x.val - y.val ∈ H := by
  rw [← Ideal.mem_span_singleton, mem_principal_monomial_iff]
  simp

/-- Pointwise dictionary using the frozen minimal-tail-generator predicate.
This does not yet identify the number of arbitrary ideal generators. -/
theorem isMinimalTailGenerator_iff_monomial (Gamma H : AddSubmonoid ℕ)
    (m : ℕ) (hHGamma : H ≤ Gamma) (x : H) :
    IsMinimalTailGenerator H (aperyTail Gamma H m) x.val ↔
      AddMonoidAlgebra.single x (1 : k) ∈ tailMonomialIdeal k Gamma H m ∧
      ∀ y : H, AddMonoidAlgebra.single y (1 : k) ∈ tailMonomialIdeal k Gamma H m →
        AddMonoidAlgebra.single y (1 : k) ∣ AddMonoidAlgebra.single x (1 : k) → y = x := by
  simp only [single_mem_tailMonomialIdeal_iff k Gamma H m hHGamma,
    single_dvd_single_iff]
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    intro y hy hdiv
    apply Subtype.ext
    by_contra hne
    have hdne : x.val - y.val ≠ 0 := by omega
    have hm := hmin (x.val - y.val) hdiv.2 hdne
    have hsub : x.val - (x.val - y.val) = y.val := by omega
    rcases hm with hm | hm
    · omega
    · exact hm (hsub.symm ▸ hy)
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    intro h hh hne
    by_cases hlt : x.val < h
    · exact Or.inl hlt
    · right
      intro hy
      let y : H := ⟨x.val - h, hy.1⟩
      have heq := hmin y hy ⟨by dsimp [y]; omega, by
        change x.val - (x.val - h) ∈ H
        have he : x.val - (x.val - h) = h := by omega
        simpa [he] using hh⟩
      have hev := congrArg Subtype.val heq
      change x.val - h = x.val at hev
      omega

/-- The tail ideal is the inverse image of (t^m) in k[Gamma]. -/
theorem comap_principal_eq_tailMonomialIdeal (Gamma H : AddSubmonoid ℕ)
    (hHGamma : H ≤ Gamma) (m : Gamma) :
    Ideal.comap (semigroupEmbedding k hHGamma).toRingHom
        (Ideal.span {AddMonoidAlgebra.single m (1 : k)}) =
      tailMonomialIdeal k Gamma H m.val := by
  classical
  ext f
  rw [Ideal.mem_comap, mem_principal_monomial_iff,
    mem_tailMonomialIdeal_iff k Gamma H m.val hHGamma]
  let e : H ↪ Gamma := ⟨AddSubmonoid.inclusion hHGamma,
    fun a b h => Subtype.ext (congrArg (fun x : Gamma => x.val) h)⟩
  change (∀ h ∈ (Finsupp.mapDomain e f.coeff).support,
    m.val ≤ h.val ∧ h.val - m.val ∈ Gamma) ↔ _
  rw [Finsupp.support_mapDomain_embedding]
  simp only [Finset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro hf h hh
    exact ⟨h.property, hf h hh⟩
  · intro hf h hh
    exact (hf h hh).2

/-- The commuting toric maps identify the preimage of the actual tail ideal. -/
theorem JGamma_eq_comap_tailMonomialIdeal (Gamma H : AddSubmonoid ℕ)
    (hHGamma : H ≤ Gamma) (w : Fin 4 → Gamma) (v : Fin 3 → H)
    (hw : ∀ i, AddSubmonoid.inclusion hHGamma (v i) = w i.succ)
    (hgen : AddSubmonoid.closure (Set.range w) = ⊤) :
    JGamma k Gamma w = Ideal.comap (toricMap k H v).toRingHom
      (tailMonomialIdeal k Gamma H (w 0).val) := by
  have hc : (semigroupEmbedding k hHGamma).comp (toricMap k H v) =
      toricMap k Gamma (fun i => w i.succ) := by
    ext i
    simp [hw]
  rw [JGamma_eq_comap_principal k Gamma w hgen,
    ← comap_principal_eq_tailMonomialIdeal k Gamma H hHGamma (w 0)]
  ext f
  change (toricMap k Gamma (fun i => w i.succ) f ∈
    Ideal.span {AddMonoidAlgebra.single (w 0) (1 : k)}) ↔
    (semigroupEmbedding k hHGamma (toricMap k H v f) ∈
      Ideal.span {AddMonoidAlgebra.single (w 0) (1 : k)})
  rw [← AlgHom.comp_apply, hc]

/-- Image version of J/I_H = I_K, in the intrinsic algebra k[H]. -/
theorem map_JGamma_eq_tailMonomialIdeal (Gamma H : AddSubmonoid ℕ)
    (hHGamma : H ≤ Gamma) (w : Fin 4 → Gamma) (v : Fin 3 → H)
    (hw : ∀ i, AddSubmonoid.inclusion hHGamma (v i) = w i.succ)
    (hgen : AddSubmonoid.closure (Set.range w) = ⊤)
    (hvgen : AddSubmonoid.closure (Set.range v) = ⊤) :
    Ideal.map (toricMap k H v).toRingHom (JGamma k Gamma w) =
      tailMonomialIdeal k Gamma H (w 0).val := by
  rw [JGamma_eq_comap_tailMonomialIdeal k Gamma H hHGamma w v hw hgen]
  exact Ideal.map_comap_of_surjective (toricMap k H v).toRingHom
    (toricMap_surjective k H v hvgen) _

theorem intrinsic_tailToricIdeal_le_JGamma (Gamma H : AddSubmonoid ℕ)
    (hHGamma : H ≤ Gamma) (w : Fin 4 → Gamma) (v : Fin 3 → H)
    (hw : ∀ i, AddSubmonoid.inclusion hHGamma (v i) = w i.succ)
    (hgen : AddSubmonoid.closure (Set.range w) = ⊤) :
    toricIdeal k H v ≤ JGamma k Gamma w := by
  rw [JGamma_eq_comap_tailMonomialIdeal k Gamma H hHGamma w v hw hgen]
  intro f hf
  change toricMap k H v f ∈ tailMonomialIdeal k Gamma H (w 0).val
  rw [show toricMap k H v f = 0 from hf]
  exact Ideal.zero_mem _

/-- Genuine algebraic generator comparison; the tailGeneratorCount dictionary
and the standard minimal-presentation invariant remain separate obligations. -/
theorem tailMonomialIdeal_generatorNumber_le (Gamma H : AddSubmonoid ℕ)
    (hHGamma : H ≤ Gamma) (w : Fin 4 → Gamma) (v : Fin 3 → H)
    (hw : ∀ i, AddSubmonoid.inclusion hHGamma (v i) = w i.succ)
    (hgen : AddSubmonoid.closure (Set.range w) = ⊤)
    (hvgen : AddSubmonoid.closure (Set.range v) = ⊤) :
    (tailMonomialIdeal k Gamma H (w 0).val).spanFinrank ≤ toricGeneratorNumber k Gamma w := by
  rw [← map_JGamma_eq_tailMonomialIdeal k Gamma H hHGamma w v hw hgen hvgen]
  exact (Ideal.spanFinrank_map_le_of_fg (toricMap k H v).toRingHom
    (Ideal.fg_of_isNoetherianRing _)).trans (JGamma_generatorNumber_le k Gamma w)

end NS25Lean.ToricPresentation
