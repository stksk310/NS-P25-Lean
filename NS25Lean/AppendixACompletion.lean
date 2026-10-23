import NS25Lean.AppendixASourceOrder
import NS25Lean.AppendixAGroebner

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B FourGeneratedBridge MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

def survivingWraps (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Set (Fin 3 →₀ ℕ) :=
  {u | (∃ s, 0 < G.exponents s (F.normal.perm 0) ∧ wrap F (G.exponents s) = u) ∧
    u ∈ L3A.minimalExponents F.initial.ideal}

theorem old_minimal_actual (F : InternalFrontend k M h) (G : NormalizedSources F)
    (i : Source M.base ⊕ Unit) : oldExponents F G i ∈ L3A.minimalExponents F.initial.ideal := by
  rw [initial_eq_oneWrapIdeal F G]
  exact oldExponents_minimal F G i

theorem delta1_nonneg (F : InternalFrontend k M h) : 0 ≤ F.delta1 := by
  obtain ⟨G⟩ := normalized_sources_exist F
  have hc := oneWrap_mu_lower F G
  rw [← initial_eq_oneWrapIdeal F G] at hc
  dsimp [InternalFrontend.delta1]
  omega

theorem minimal_eq_old_union_wraps (F : InternalFrontend k M h) (G : NormalizedSources F) :
    L3A.minimalExponents F.initial.ideal = Set.range (oldExponents F G) ∪ survivingWraps F G := by
  ext u
  constructor
  · intro hu
    have hm := hu.1
    rw [initial_eq_oneWrapIdeal F G] at hm
    obtain ⟨w, hw, hwu⟩ := (L3A.monomial_mem_span_iff (oneWrapExponents F G) u).mp hm
    have hwM : monomial w (1 : k) ∈ F.initial.ideal := by
      rw [initial_eq_oneWrapIdeal F G]
      exact Ideal.subset_span ⟨w, hw, rfl⟩
    have he : w = u := le_antisymm hwu (hu.2 hwM hwu)
    rcases hw with (hw | ⟨s, hs⟩) | ⟨s, hp, hs⟩
    · left; exact ⟨Sum.inr (), by simpa only [oldExponents, Sum.elim_inr] using (Set.mem_singleton_iff.mp hw).symm.trans he⟩
    · left; exact ⟨Sum.inl s, by simpa only [oldExponents, Sum.elim_inl] using hs.trans he⟩
    · right; exact ⟨⟨s, hp, hs.symm.trans he⟩, hu⟩
  · rintro (⟨i, rfl⟩ | hu)
    · exact old_minimal_actual F G i
    · exact hu.2

theorem old_wrap_disjoint (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Disjoint (Set.range (oldExponents F G)) (survivingWraps F G) := by
  rw [Set.disjoint_left]
  rintro u ⟨i, rfl⟩ ⟨⟨s, _, he⟩, _⟩
  rcases i with t | t
  · exact wrap_not_le_source F G s t (le_of_eq he)
  · exact wrap_not_le_tie F G s (le_of_eq he)

theorem survivingWraps_finite (F : InternalFrontend k M h) (G : NormalizedSources F) :
    (survivingWraps F G).Finite := (L3A.minimalExponents_finite _).subset (fun _ hu => hu.2)

theorem oneWrap_mu_exact (F : InternalFrontend k M h) (G : NormalizedSources F) :
    L3A.mu F.initial.ideal = sourceCount M.base + 1 + (survivingWraps F G).ncard := by
  rw [L3A.mu_eq_minimal_count _ F.initial.monomial, minimal_eq_old_union_wraps F G,
    Set.ncard_union_eq (old_wrap_disjoint F G) (Set.finite_range _) (survivingWraps_finite F G),
    Set.ncard_range_of_injective (oldExponents_injective F G), source_sum_unit_card]

theorem survivingWraps_card_eq_delta1 (F : InternalFrontend k M h) (G : NormalizedSources F) :
    ((survivingWraps F G).ncard : ℤ) = F.delta1 := by
  have hc := oneWrap_mu_exact F G
  dsimp [InternalFrontend.delta1]
  omega

end NS25Lean.L3C
