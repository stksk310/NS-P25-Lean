import NS25Lean.AppendixASources
import NS25Lean.AppendixAChains
import NS25Lean.AppendixAOneWrap
import NS25Lean.PrincipalSourceFibers

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B FourGeneratedBridge MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

theorem weight_mem_H (B : Data Gamma) (u : Fin 3 →₀ ℕ) : weight B u ∈ B.H := by
  rw [weight_eq_degree]
  exact (Presentation.factorizationMap B.tailDegrees u).property

theorem source_no_positive_translate (B : Data Gamma) (s t : Source B)
    (w : ℕ) (hw : w ∈ B.H) (hp : 0 < w) (he : t.val = s.val + w) : False := by
  rcases t.property.2 w hw hp.ne' with ht | ht
  · omega
  · apply ht
    convert s.property.1 using 1 <;> omega

theorem normalized_source_antichain (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s t : Source M.base) (hst : s ≠ t) : ¬ G.exponents s ≤ G.exponents t := by
  intro hle
  have he := congrArg (weight M.base) (tsub_add_cancel_of_le hle)
  simp only [map_add, G.degree] at he
  have hp : 0 < weight M.base (G.exponents t - G.exponents s) := by
    by_contra hn
    have hv : s.val = t.val := by omega
    exact hst (Subtype.ext hv)
  exact source_no_positive_translate M.base s t _ (weight_mem_H _ _) hp (by omega)

/-- Source level reversal, including the actual original source degrees. -/
theorem source_level_reversal (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s t : Source M.base) (hst : s ≠ t)
    (hu : transverse F (G.exponents s) ≤ transverse F (G.exponents t)) :
    G.exponents t (F.normal.perm 0) < G.exponents s (F.normal.perm 0) := by
  by_contra hn
  apply normalized_source_antichain F G s t hst
  rw [← transverse_add F (G.exponents s), ← transverse_add F (G.exponents t)]
  exact add_le_add hu (Finsupp.single_le_single.mpr (by omega))

/-- No wrap, even before minimal-wrap selection, can divide any old source. -/
theorem wrap_not_le_source (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s t : Source M.base) : ¬ wrap F (G.exponents s) ≤ G.exponents t := by
  intro hle
  let w := G.exponents t - wrap F (G.exponents s)
  have he := congrArg (weight M.base) (tsub_add_cancel_of_le hle)
  simp only [map_add, G.degree, wrap_weight F G s] at he
  have hp : 0 < (F.normal.a - G.exponents s (F.normal.perm 0)) *
      weights M.base (F.normal.perm 0) :=
    Nat.mul_pos (Nat.sub_pos_of_lt (G.slab s)) (weights_positive _ _)
  have hH : (F.normal.a - G.exponents s (F.normal.perm 0)) *
      weights M.base (F.normal.perm 0) + weight M.base w ∈ M.base.H := by
    apply M.base.H.add_mem
    · exact M.base.H.nsmul_mem (M.base.tailDegrees (F.normal.perm 0)).property _
    · exact weight_mem_H _ _
  apply source_no_positive_translate M.base s t _ hH (by omega)
  dsimp [w]
  omega

theorem wrap_not_le_transverse (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s t : Source M.base) : ¬ wrap F (G.exponents s) ≤ transverse F (G.exponents t) := by
  intro he
  exact wrap_not_le_source F G s t (he.trans (tsub_le_self))

theorem boundary_not_below_apery (B : Data Gamma) (u v : Fin 3 →₀ ℕ)
    (hu : weight B u ∈ B.K) (hv : weight B v ∈ B.apery) : ¬ u ≤ v := by
  intro hle
  have he := congrArg (weight B) (tsub_add_cancel_of_le hle)
  simp only [map_add] at he
  have hm := aperyTail_add_mem B.H_le hu (weight_mem_H B (v - u))
  have hnot := (B.apery_eq_compl ▸ hv).2
  have he' : weight B u + weight B (v - u) = weight B v := by omega
  rw [he'] at hm
  exact hnot hm

theorem source_not_le_tie (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) : ¬ G.exponents s ≤ F.normal.alpha.val := by
  apply boundary_not_below_apery M.base
  · rw [G.degree]; exact s.property.1
  · rw [F.normal.alpha.property]; exact F.normal.apery

theorem wrap_not_le_tie (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) : ¬ wrap F (G.exponents s) ≤ F.normal.alpha.val := by
  apply boundary_not_below_apery M.base
  · rw [wrap_weight]
    exact aperyTail_add_mem M.base.H_le s.property.1
      (M.base.H.nsmul_mem (M.base.tailDegrees (F.normal.perm 0)).property _)
  · rw [F.normal.alpha.property]; exact F.normal.apery

theorem tie_not_le_source (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) : ¬ F.normal.alpha.val ≤ G.exponents s := by
  intro he
  have hx := he (F.normal.perm 0)
  rw [F.normal.alpha_eq, Finsupp.single_eq_same] at hx
  have := G.slab s
  omega

/-- Compatibility endpoint for the whole-source principal-binomial theorem. -/
theorem shared_source_factorization_difference (F : InternalFrontend k M h)
    (s : Source M.base) (u v : FactorizationFiber M.base s.val) (j : Fin 3)
    (hu : 0 < u.val j) (hv : 0 < v.val j) :
    ∃ z : ℤ, ∀ i, (v.val i : ℤ) = (u.val i : ℤ) + z * tieDelta F.normal i := by
  exact source_factorization_difference F s u v

theorem tie_minimal_oneWrap (F : InternalFrontend k M h) (G : NormalizedSources F) :
    F.normal.alpha.val ∈ L3A.minimalExponents (oneWrapIdeal F G) := by
  refine ⟨Ideal.subset_span ⟨_, Or.inl (Or.inl (Set.mem_singleton _)), rfl⟩, ?_⟩
  intro v hv hvle
  obtain ⟨w, hw, hwv⟩ := (L3A.monomial_mem_span_iff (oneWrapExponents F G) v).mp hv
  rcases hw with (hw | ⟨s, rfl⟩) | ⟨s, _, rfl⟩
  · exact Set.mem_singleton_iff.mp hw ▸ hwv
  · exact (source_not_le_tie F G s (hwv.trans hvle)).elim
  · exact (wrap_not_le_tie F G s (hwv.trans hvle)).elim

theorem source_minimal_oneWrap (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) : G.exponents s ∈ L3A.minimalExponents (oneWrapIdeal F G) := by
  refine ⟨Ideal.subset_span ⟨_, Or.inl (Or.inr ⟨s, rfl⟩), rfl⟩, ?_⟩
  intro v hv hvle
  obtain ⟨w, hw, hwv⟩ := (L3A.monomial_mem_span_iff (oneWrapExponents F G) v).mp hv
  rcases hw with (hw | ⟨t, rfl⟩) | ⟨t, _, rfl⟩
  · have he : w = F.normal.alpha.val := hw
    subst w
    exact (tie_not_le_source F G s (hwv.trans hvle)).elim
  · by_cases ht : t = s
    · subst t; exact hwv
    · exact (normalized_source_antichain F G t s ht (hwv.trans hvle)).elim
  · exact (wrap_not_le_source F G t s (hwv.trans hvle)).elim

def oldExponents (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Source M.base ⊕ Unit → Fin 3 →₀ ℕ :=
  Sum.elim G.exponents (fun _ => F.normal.alpha.val)

theorem oldExponents_injective (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Function.Injective (oldExponents F G) := by
  rintro (s | u) (t | v) he
  · congr 1
    apply Subtype.ext
    have hw := congrArg (weight M.base) he
    simpa only [oldExponents, Sum.elim_inl, G.degree] using hw
  · exact (source_not_le_tie F G s (le_of_eq he)).elim
  · exact (tie_not_le_source F G t (le_of_eq he)).elim
  · exact congrArg Sum.inr (Subsingleton.elim u v)

theorem oldExponents_minimal (F : InternalFrontend k M h) (G : NormalizedSources F)
    (i : Source M.base ⊕ Unit) : oldExponents F G i ∈ L3A.minimalExponents (oneWrapIdeal F G) := by
  rcases i with s | u
  · exact source_minimal_oneWrap F G s
  · exact tie_minimal_oneWrap F G

/-- This count is for the explicit one-wrap ideal. Identification with actual M
is still required before transferring it to the frozen delta1. -/
theorem oneWrap_mu_lower (F : InternalFrontend k M h) (G : NormalizedSources F) :
    sourceCount M.base + 1 ≤ L3A.mu (oneWrapIdeal F G) := by
  classical
  let f : Source M.base ⊕ Unit → L3A.minimalExponents (oneWrapIdeal F G) :=
    fun i => ⟨oldExponents F G i, oldExponents_minimal F G i⟩
  have hf : Function.Injective f := by
    intro i j he
    exact oldExponents_injective F G (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hf
  rw [source_sum_unit_card] at hc
  have hm : IsMonomialIdeal k (oneWrapIdeal F G) := ⟨oneWrapExponents F G, rfl⟩
  rw [L3A.mu_eq_minimal_count (oneWrapIdeal F G) hm]
  simpa only [Nat.card_coe_set_eq] using hc

end NS25Lean.L3C
