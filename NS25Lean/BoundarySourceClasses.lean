import NS25Lean.BoundarySourceCoordinates

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A2
open NS25Lean.L2B NS25Lean.L2B2A ChosenBase Presentation ToricPresentation
  FourGeneratedBridge MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem boundary_monomial_mem_J (k : Type*) [Field k] (B : Data Gamma)
    (u : Fin 3 →₀ ℕ) (hu : weight B u ∈ B.K) : monomial u (1 : k) ∈ B.J k := by
  rw [B.J_eq_IH_sup_MK k]
  have hm : monomial u (1 : k) ∈ B.MK k := by
    apply Ideal.subset_span
    refine ⟨u, ?_, rfl⟩
    change (factorizationMap B.tailDegrees u).val ∈ B.K
    rwa [← weight_eq_degree B u]
  exact (show B.MK k ≤ B.IH k ⊔ B.MK k from le_sup_right) hm

def sourceRepresentative (B : Data Gamma) (x : Source B) : FactorizationFiber B x.val :=
  Classical.choice (fiber_nonempty B ⟨x.val, x.property.1.1⟩)

def sourceClass (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (x : Source M.base) : BoundaryGeneratorQuotient k M :=
  boundaryClass k M ⟨monomial (sourceRepresentative M.base x).val 1,
    boundary_monomial_mem_J k M.base _ (by
      rw [(sourceRepresentative M.base x).property]; exact x.property.1)⟩

theorem sourceClass_coordinates (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (x : Source M.base) : boundarySourceCoordinates k M (sourceClass k M x) = Pi.single x 1 := by
  classical
  ext y
  rw [sourceClass, boundarySourceCoordinates_class, sourceCoordinates_monomial,
    (sourceRepresentative M.base x).property]
  simp only [Pi.single_apply, Subtype.val_inj, eq_comm]

theorem boundaryClass_eq_of_sub_mem_IH (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (f g : M.base.J k) (hfg : f.val - g.val ∈ M.base.IH k) :
    boundaryClass k M f = boundaryClass k M g := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact boundaryClass_IH k M (f - g) hfg

theorem boundaryClass_monomial_source (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (u : Fin 3 →₀ ℕ) (hu : weight M.base u ∈ M.base.K)
    (hs : IsMinimalTailGenerator M.base.H M.base.K (weight M.base u)) :
    boundaryClass k M ⟨monomial u 1, boundary_monomial_mem_J k M.base u hu⟩ =
      sourceClass k M ⟨weight M.base u, hs⟩ := by
  unfold sourceClass
  apply boundaryClass_eq_of_sub_mem_IH k M
  exact binomial_mem_IH k M.base _ _
    (sourceRepresentative M.base ⟨weight M.base u, hs⟩).property.symm

/-- A nonminimal K-degree has a representative divisible by a variable times a
K-monomial. The difference from any other representative belongs to I_H. -/
theorem nonminimal_boundary_representative (k : Type*) [Field k] (B : Data Gamma)
    (u : Fin 3 →₀ ℕ) (hu : weight B u ∈ B.K)
    (hs : ¬ IsMinimalTailGenerator B.H B.K (weight B u)) :
    ∃ v : Fin 3 →₀ ℕ, weight B v = weight B u ∧
      monomial v (1 : k) ∈ variableIdeal k * B.J k := by
  classical
  have hh : ¬ ∀ h, h ∈ B.H → h ≠ 0 → (weight B u < h ∨ weight B u - h ∉ B.K) :=
    fun h => hs ⟨hu, h⟩
  push Not at hh
  obtain ⟨a, haH, ha0, hau, haK⟩ := hh
  obtain ⟨v, hv⟩ := factorizationMap_surjective B.tailDegrees B.tailDegrees_generate ⟨a, haH⟩
  obtain ⟨w, hw⟩ := factorizationMap_surjective B.tailDegrees B.tailDegrees_generate
    ⟨weight B u - a, haK.1⟩
  have hvw : weight B v = a := (weight_eq_degree B v).trans (congrArg Subtype.val hv)
  have hww : weight B w = weight B u - a :=
    (weight_eq_degree B w).trans (congrArg Subtype.val hw)
  have hv0 : v ≠ 0 := by intro he; simp only [he, map_zero] at hvw; exact ha0 hvw.symm
  obtain ⟨j, hj⟩ : ∃ j, 0 < v j := by
    by_contra hn
    push Not at hn
    exact hv0 (by ext j; exact Nat.eq_zero_of_le_zero (hn j))
  have hm : monomial v (1 : k) ∈ variableIdeal k := by
    rw [← variable_mul_removed k v j hj]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨v + w, by rw [map_add, hvw, hww]; omega, ?_⟩
  have hn := Ideal.mul_mem_mul hm (boundary_monomial_mem_J k B w (by rwa [hww]))
  simpa only [monomial_mul, one_mul] using hn

theorem boundaryClass_monomial_nonminimal (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (u : Fin 3 →₀ ℕ) (hu : weight M.base u ∈ M.base.K)
    (hs : ¬ IsMinimalTailGenerator M.base.H M.base.K (weight M.base u)) :
    boundaryClass k M ⟨monomial u 1, boundary_monomial_mem_J k M.base u hu⟩ = 0 := by
  obtain ⟨v, hv, hn⟩ := nonminimal_boundary_representative k M.base u hu hs
  let f : M.base.J k := ⟨monomial u 1, boundary_monomial_mem_J k M.base u hu⟩
  let g : M.base.J k := ⟨monomial v 1, boundary_monomial_mem_J k M.base v (by rwa [hv])⟩
  have he := boundaryClass_eq_of_sub_mem_IH k M f g
    (binomial_mem_IH k M.base u v hv.symm)
  exact he.trans (boundaryClass_nJ k M g hn)

end NS25Lean.L2B2A2
