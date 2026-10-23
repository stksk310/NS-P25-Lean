import NS25Lean.ActiveFiberLocal

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A
open NS25Lean.L2B ChosenBase Presentation ToricPresentation MvPolynomial
variable {Gamma : NumericalSemigroup}

/-- A monomial-stable family generates the same polynomial ideal and coefficient-field span. -/
theorem ideal_span_restrict_eq_span (k : Type*) [Field k]
    (S : Set (Poly k 3))
    (hS : ∀ u f, f ∈ S → monomial u (1 : k) * f ∈ S) :
    (Ideal.span S).restrictScalars k = Submodule.span k S := by
  have hm : ∀ u f, f ∈ Submodule.span k S →
      monomial u (1 : k) * f ∈ Submodule.span k S := by
    intro u f hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact Submodule.subset_span (hS u f hf)
    | zero => simp
    | add f g hf hg ihf ihg =>
        simpa only [mul_add] using (Submodule.span k S).add_mem ihf ihg
    | smul c f hf ih =>
        simpa only [mul_smul_comm] using (Submodule.span k S).smul_mem c ih
  have ha : ∀ a f, f ∈ Submodule.span k S → a * f ∈ Submodule.span k S := by
    intro a f hf
    induction a using MvPolynomial.induction_on' with
    | monomial u c =>
        simpa only [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one] using
          (Submodule.span k S).smul_mem c (hm u f hf)
    | add a b iha ihb =>
        simpa only [add_mul] using (Submodule.span k S).add_mem iha ihb
  apply le_antisymm
  · intro f hf
    change f ∈ Ideal.span S at hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact Submodule.subset_span hf
    | zero => exact Submodule.zero_mem _
    | add f g hf hg ihf ihg => exact Submodule.add_mem _ ihf ihg
    | smul a f hf ih => exact ha a f ih
  · exact Submodule.span_le.mpr fun _ hf => Ideal.subset_span hf

/-- All equal-weight binomials, before multiplication by the variable ideal. -/
def toricMoves (k : Type*) [Field k] (B : Data Gamma) : Set (Poly k 3) :=
  {f | ∃ u v : Fin 3 →₀ ℕ, weight B u = weight B v ∧
    f = monomial u (1 : k) - monomial v 1}

/-- The actual lower-degree moves, characterized by a shared variable. -/
def sharedMoves (k : Type*) [Field k] (B : Data Gamma) : Set (Poly k 3) :=
  {f | ∃ u v : Fin 3 →₀ ℕ, weight B u = weight B v ∧
    (∃ j, 0 < u j ∧ 0 < v j) ∧ f = monomial u (1 : k) - monomial v 1}

/-- The monomial generators of n M_K, with the removed variable explicit. -/
def boundaryMoves (k : Type*) [Field k] (B : Data Gamma) : Set (Poly k 3) :=
  {f | ∃ (j : Fin 3) (v : Fin 3 →₀ ℕ), weight B v ∈ B.K ∧
    f = monomial (Finsupp.single j 1 + v) (1 : k)}

theorem toricMoves_mul_monomial (k : Type*) [Field k] (B : Data Gamma)
    (a : Fin 3 →₀ ℕ) (f : Poly k 3) (hf : f ∈ toricMoves k B) :
    monomial a (1 : k) * f ∈ toricMoves k B := by
  obtain ⟨u, v, he, rfl⟩ := hf
  refine ⟨a + u, a + v, by simp only [map_add, he], ?_⟩
  simp only [mul_sub, monomial_mul, one_mul]

theorem sharedMoves_mul_monomial (k : Type*) [Field k] (B : Data Gamma)
    (a : Fin 3 →₀ ℕ) (f : Poly k 3) (hf : f ∈ sharedMoves k B) :
    monomial a (1 : k) * f ∈ sharedMoves k B := by
  obtain ⟨u, v, he, ⟨j, hu, hv⟩, rfl⟩ := hf
  refine ⟨a + u, a + v, by simp only [map_add, he],
    ⟨j, by simp only [Finsupp.add_apply]; omega,
      by simp only [Finsupp.add_apply]; omega⟩, ?_⟩
  simp only [mul_sub, monomial_mul, one_mul]

theorem boundaryMoves_mul_monomial (k : Type*) [Field k] (B : Data Gamma)
    (a : Fin 3 →₀ ℕ) (f : Poly k 3) (hf : f ∈ boundaryMoves k B) :
    monomial a (1 : k) * f ∈ boundaryMoves k B := by
  obtain ⟨j, v, hv, rfl⟩ := hf
  refine ⟨j, v + a, ?_, ?_⟩
  · rw [map_add]
    exact FourGeneratedBridge.aperyTail_add_mem B.H_le hv
      ((weight_eq_degree B a).symm ▸ (factorizationMap B.tailDegrees a).property)
  · simp only [monomial_mul, one_mul]
    congr 1
    abel_nf

theorem IH_eq_span_toricMoves (k : Type*) [Field k] (B : Data Gamma) :
    (B.IH k).restrictScalars k = Submodule.span k (toricMoves k B) := by
  have he : B.IH k = Ideal.span (toricMoves k B) := by
    rw [IH_eq_relationIdeal, relationIdeal]
    congr 1
    ext f
    constructor
    · rintro ⟨⟨u, v⟩, he, rfl⟩
      exact ⟨u, v, he, rfl⟩
    · rintro ⟨u, v, he, rfl⟩
      exact ⟨(u, v), he, rfl⟩
  rw [he]
  exact ideal_span_restrict_eq_span k _ (toricMoves_mul_monomial k B)

theorem sharedMove_mem_nIH (k : Type*) [Field k] (B : Data Gamma)
    {f : Poly k 3} (hf : f ∈ sharedMoves k B) :
    f ∈ variableIdeal k * B.IH k := by
  obtain ⟨u, v, he, ⟨j, hu, hv⟩, rfl⟩ := hf
  have hlow : weight B (u - Finsupp.single j 1) =
      weight B (v - Finsupp.single j 1) := by
    have h1 := congrArg (weight B) (remove_variable_add u j hu)
    have h2 := congrArg (weight B) (remove_variable_add v j hv)
    simp only [map_add] at h1 h2
    omega
  have hm := Ideal.mul_mem_mul
    (show X j ∈ variableIdeal k from Ideal.subset_span ⟨j, rfl⟩)
    (binomial_mem_IH k B _ _ hlow)
  simpa only [mul_sub, variable_mul_removed k u j hu, variable_mul_removed k v j hv]
    using hm

/-- Converse to the shared-variable vanishing: all of n I_H is this k-linear span. -/
theorem nIH_eq_span_sharedMoves (k : Type*) [Field k] (B : Data Gamma) :
    (variableIdeal k * B.IH k).restrictScalars k = Submodule.span k (sharedMoves k B) := by
  have he : variableIdeal k * B.IH k = Ideal.span (sharedMoves k B) := by
    apply le_antisymm
    · rw [variableIdeal, IH_eq_relationIdeal, relationIdeal, Ideal.span_mul_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨⟨u, v⟩, huv, rfl⟩, rfl⟩
      change weight B u = weight B v at huv
      apply Ideal.subset_span
      refine ⟨Finsupp.single j 1 + u, Finsupp.single j 1 + v,
        by simp only [map_add, huv], ⟨j, by simp, by simp⟩, ?_⟩
      change monomial (Finsupp.single j 1) (1 : k) *
        (monomial u 1 - monomial v 1) = _
      simp only [mul_sub, monomial_mul, one_mul]
    · exact Ideal.span_le.mpr fun _ hf => sharedMove_mem_nIH k B hf
  rw [he]
  exact ideal_span_restrict_eq_span k _ (sharedMoves_mul_monomial k B)

theorem nMK_eq_span_boundaryMoves (k : Type*) [Field k] (B : Data Gamma) :
    (variableIdeal k * B.MK k).restrictScalars k = Submodule.span k (boundaryMoves k B) := by
  have he : variableIdeal k * B.MK k = Ideal.span (boundaryMoves k B) := by
    rw [variableIdeal, Data.MK, Ideal.span_mul_span]
    congr 1
    ext f
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨j, v, (weight_eq_degree B v).symm ▸ hv, ?_⟩
      change monomial (Finsupp.single j 1) (1 : k) * monomial v 1 = _
      simp only [monomial_mul, one_mul]
    · rintro ⟨j, v, hv, rfl⟩
      refine ⟨X j, ⟨j, rfl⟩, monomial v 1,
        ⟨v, show (factorizationMap B.tailDegrees v).val ∈ B.K from
          (weight_eq_degree B v) ▸ hv, rfl⟩, ?_⟩
      change monomial (Finsupp.single j 1) (1 : k) * monomial v 1 = _
      simp only [monomial_mul, one_mul]
  rw [he]
  exact ideal_span_restrict_eq_span k _ (boundaryMoves_mul_monomial k B)

/-- An exact relation presentation of the actual nJ; no dimension invariant is used. -/
theorem nJ_eq_span_moves (k : Type*) [Field k] (B : Data Gamma) :
    (variableIdeal k * B.J k).restrictScalars k =
      Submodule.span k (sharedMoves k B ∪ boundaryMoves k B) := by
  rw [B.J_eq_IH_sup_MK k, Ideal.mul_sup, Submodule.restrictScalars_sup,
    nIH_eq_span_sharedMoves, nMK_eq_span_boundaryMoves, Submodule.span_union]

end NS25Lean.L2B2A
