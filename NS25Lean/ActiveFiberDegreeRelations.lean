import NS25Lean.ActiveFiberRelations

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A
open NS25Lean.L2B ChosenBase Presentation ToricPresentation MvPolynomial
variable {Gamma : NumericalSemigroup}

def degreeToricMoves (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) : Set (Poly k 3) :=
  {f | ∃ u v : FactorizationFiber B h, f = monomial u.val (1 : k) - monomial v.val 1}

def degreeSharedMoves (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) : Set (Poly k 3) :=
  {f | ∃ u v : FactorizationFiber B h, (∃ j, 0 < u.val j ∧ 0 < v.val j) ∧
    f = monomial u.val (1 : k) - monomial v.val 1}

def degreeBoundaryMoves (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) : Set (Poly k 3) :=
  {f | ∃ u : FactorizationFiber B h, (∃ j, 0 < u.val j ∧ h - weights B j ∈ B.K) ∧
    f = monomial u.val (1 : k)}

theorem degreeToricMoves_subset (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) :
    degreeToricMoves k B h ⊆ toricMoves k B := by
  rintro f ⟨u, v, rfl⟩
  exact ⟨u.val, v.val, u.property.trans v.property.symm, rfl⟩

theorem degreeSharedMoves_subset (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) :
    degreeSharedMoves k B h ⊆ sharedMoves k B := by
  rintro f ⟨u, v, hj, rfl⟩
  exact ⟨u.val, v.val, u.property.trans v.property.symm, hj, rfl⟩

theorem degreeBoundaryMoves_subset (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) :
    degreeBoundaryMoves k B h ⊆ boundaryMoves k B := by
  rintro f ⟨u, ⟨j, hj, hk⟩, rfl⟩
  refine ⟨j, u.val - Finsupp.single j 1, ?_, ?_⟩
  · have he := congrArg (weight B) (remove_variable_add u.val j hj)
    simp only [map_add, weight, Finsupp.weight_single, one_nsmul] at he
    have hu := u.property
    have hd : weight B (u.val - Finsupp.single j 1) = h - weights B j := by
      change weights B j + weight B (u.val - Finsupp.single j 1) = weight B u.val at he
      omega
    rwa [hd]
  · rw [remove_variable_add u.val j hj]

theorem project_toricMove (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    {f : Poly k 3} (hf : f ∈ toricMoves k B) :
    weightedHomogeneousComponent (weights B) h f ∈ Submodule.span k (degreeToricMoves k B h) := by
  obtain ⟨u, v, he, rfl⟩ := hf
  have hh : (monomial u (1 : k) - monomial v 1).IsWeightedHomogeneous
      (weights B) (weight B u) :=
    (isWeightedHomogeneous_monomial (weights B) u (1 : k) rfl).sub
      (isWeightedHomogeneous_monomial (weights B) v (1 : k) he.symm)
  by_cases hd : weight B u = h
  · rw [← hd, hh.weightedHomogeneousComponent_same]
    exact Submodule.subset_span ⟨⟨u, rfl⟩, ⟨v, he.symm⟩, rfl⟩
  · rw [hh.weightedHomogeneousComponent_ne h (Ne.symm hd)]
    exact Submodule.zero_mem _

theorem project_sharedMove (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    {f : Poly k 3} (hf : f ∈ sharedMoves k B) :
    weightedHomogeneousComponent (weights B) h f ∈ Submodule.span k (degreeSharedMoves k B h) := by
  obtain ⟨u, v, he, hj, rfl⟩ := hf
  have hh : (monomial u (1 : k) - monomial v 1).IsWeightedHomogeneous
      (weights B) (weight B u) :=
    (isWeightedHomogeneous_monomial (weights B) u (1 : k) rfl).sub
      (isWeightedHomogeneous_monomial (weights B) v (1 : k) he.symm)
  by_cases hd : weight B u = h
  · rw [← hd, hh.weightedHomogeneousComponent_same]
    exact Submodule.subset_span ⟨⟨u, rfl⟩, ⟨v, he.symm⟩, hj, rfl⟩
  · rw [hh.weightedHomogeneousComponent_ne h (Ne.symm hd)]
    exact Submodule.zero_mem _

theorem project_boundaryMove (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    {f : Poly k 3} (hf : f ∈ boundaryMoves k B) :
    weightedHomogeneousComponent (weights B) h f ∈
      Submodule.span k (degreeBoundaryMoves k B h) := by
  obtain ⟨j, v, hv, rfl⟩ := hf
  have hh : (monomial (Finsupp.single j 1 + v) (1 : k)).IsWeightedHomogeneous
      (weights B) (weight B (Finsupp.single j 1 + v)) :=
    isWeightedHomogeneous_monomial (weights B) (Finsupp.single j 1 + v) (1 : k) rfl
  by_cases hd : weight B (Finsupp.single j 1 + v) = h
  · rw [← hd, hh.weightedHomogeneousComponent_same]
    apply Submodule.subset_span
    refine ⟨⟨Finsupp.single j 1 + v, rfl⟩, ⟨j, by simp, ?_⟩, rfl⟩
    simpa only [map_add, weight, Finsupp.weight_single, one_nsmul, Nat.add_sub_cancel_left]
      using hv
  · rw [hh.weightedHomogeneousComponent_ne h (Ne.symm hd)]
    exact Submodule.zero_mem _

/-- Project every generator before restricting to one actual homogeneous piece. -/
theorem homogeneous_span_iff (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    (S T : Set (Poly k 3)) (hTS : T ⊆ S)
    (hproj : ∀ f ∈ S, weightedHomogeneousComponent (weights B) h f ∈ Submodule.span k T)
    (f : Poly k 3) (hf : f.IsWeightedHomogeneous (weights B) h) :
    f ∈ Submodule.span k S ↔ f ∈ Submodule.span k T := by
  constructor
  · intro hmem
    have hp : weightedHomogeneousComponent (weights B) h f ∈ Submodule.span k T := by
      clear hf
      induction hmem using Submodule.span_induction with
      | mem g hg => exact hproj g hg
      | zero => simp
      | add g q hg hq ihg ihq =>
          simpa only [map_add] using (Submodule.span k T).add_mem ihg ihq
      | smul c g hg ih =>
          simpa only [map_smul] using (Submodule.span k T).smul_mem c ih
    rwa [hf.weightedHomogeneousComponent_same] at hp
  · intro hmem
    exact Submodule.span_mono hTS hmem

/-- Every degree-h tail relation is a k-linear combination of actual fiber binomials. -/
theorem IH_degree_mem_iff (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    (f : Poly k 3) (hf : f.IsWeightedHomogeneous (weights B) h) :
    f ∈ B.IH k ↔ f ∈ Submodule.span k (degreeToricMoves k B h) := by
  change f ∈ (B.IH k).restrictScalars k ↔ _
  rw [IH_eq_span_toricMoves]
  exact homogeneous_span_iff k B h _ _ (degreeToricMoves_subset k B h)
    (fun _ hf => project_toricMove k B h hf) f hf

/-- Exact converse for n I_H in degree h, including arbitrary polynomial relations. -/
theorem nIH_degree_mem_iff (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    (f : Poly k 3) (hf : f.IsWeightedHomogeneous (weights B) h) :
    f ∈ variableIdeal k * B.IH k ↔
      f ∈ Submodule.span k (degreeSharedMoves k B h) := by
  change f ∈ (variableIdeal k * B.IH k).restrictScalars k ↔ _
  rw [nIH_eq_span_sharedMoves]
  exact homogeneous_span_iff k B h _ _ (degreeSharedMoves_subset k B h)
    (fun _ hf => project_sharedMove k B h hf) f hf

theorem nMK_degree_mem_iff (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    (f : Poly k 3) (hf : f.IsWeightedHomogeneous (weights B) h) :
    f ∈ variableIdeal k * B.MK k ↔
      f ∈ Submodule.span k (degreeBoundaryMoves k B h) := by
  change f ∈ (variableIdeal k * B.MK k).restrictScalars k ↔ _
  rw [nMK_eq_span_boundaryMoves]
  exact homogeneous_span_iff k B h _ _ (degreeBoundaryMoves_subset k B h)
    (fun _ hf => project_boundaryMove k B h hf) f hf

/-- The actual degree-h relation space in J/nJ, with both inclusions proved. -/
theorem nJ_degree_mem_iff (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    (f : Poly k 3) (hf : f.IsWeightedHomogeneous (weights B) h) :
    f ∈ variableIdeal k * B.J k ↔
      f ∈ Submodule.span k (degreeSharedMoves k B h ∪ degreeBoundaryMoves k B h) := by
  change f ∈ (variableIdeal k * B.J k).restrictScalars k ↔ _
  rw [nJ_eq_span_moves]
  apply homogeneous_span_iff k B h
  · exact Set.union_subset_union (degreeSharedMoves_subset k B h) (degreeBoundaryMoves_subset k B h)
  · intro g hg
    rcases hg with hg | hg
    · exact Submodule.span_mono Set.subset_union_left (project_sharedMove k B h hg)
    · exact Submodule.span_mono Set.subset_union_right (project_boundaryMove k B h hg)
  · exact hf

end NS25Lean.L2B2A
