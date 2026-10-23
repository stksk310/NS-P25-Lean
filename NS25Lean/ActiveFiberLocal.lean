import NS25Lean.ActiveFiberObjects
import NS25Lean.DilationIdeals

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase Presentation ToricPresentation MvPolynomial
variable {Gamma : NumericalSemigroup}

/-- The actual degree-h part of the tail relation ideal. -/
def tailDegreeSpace (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) : Submodule k (B.IH k) :=
  (weightedHomogeneousSubmodule k (weights B) h).comap ((B.IH k).subtype.restrictScalars k)

/-- The degreewise tail contribution in the actual J/nJ. -/
def tailDegreeImage (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) :
    Submodule k (GeneratorQuotient k B) :=
  (tailDegreeSpace k B h).map (tailToGeneratorQuotient k B)

theorem binomial_mem_IH (k : Type*) [Field k] (B : Data Gamma) (u v : Fin 3 →₀ ℕ)
    (he : weight B u = weight B v) : monomial u (1 : k) - monomial v 1 ∈ B.IH k := by
  rw [IH_eq_relationIdeal, relationIdeal]
  exact Ideal.subset_span ⟨(u, v), he, rfl⟩

theorem remove_variable_add (u : Fin 3 →₀ ℕ) (j : Fin 3) (hj : 0 < u j) :
    Finsupp.single j 1 + (u - Finsupp.single j 1) = u :=
  add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hj)

theorem variable_mul_removed (k : Type*) [Field k] (u : Fin 3 →₀ ℕ) (j : Fin 3)
    (hj : 0 < u j) : X j * monomial (u - Finsupp.single j 1) (1 : k) = monomial u 1 := by
  change monomial (Finsupp.single j 1) (1 : k) * _ = _
  rw [monomial_mul, one_mul, remove_variable_add u j hj]

/-- Sharing a variable gives a relation in nJ by an explicit lower-degree factorization. -/
theorem edge_binomial_mem_nJ (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    (u v : FactorizationFiber B h) (j : Fin 3) (huj : 0 < u.val j) (hvj : 0 < v.val j) :
    monomial u.val (1 : k) - monomial v.val 1 ∈ variableIdeal k * B.J k := by
  have hdeg : weight B (u.val - Finsupp.single j 1) =
      weight B (v.val - Finsupp.single j 1) := by
    have hu := congrArg (weight B) (remove_variable_add u.val j huj)
    have hv := congrArg (weight B) (remove_variable_add v.val j hvj)
    simp only [map_add, u.property, v.property] at hu hv
    omega
  have hlow := binomial_mem_IH k B _ _ hdeg
  have hle : B.IH k ≤ B.J k := by rw [B.J_eq_IH_sup_MK k]; exact le_sup_left
  have hm := Ideal.mul_mem_mul
    (show X j ∈ variableIdeal k from Ideal.subset_span ⟨j, rfl⟩) (hle hlow)
  simpa only [mul_sub, variable_mul_removed k u.val j huj, variable_mul_removed k v.val j hvj]
    using hm

theorem edge_tail_class_zero (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    (u v : FactorizationFiber B h) (j : Fin 3) (huj : 0 < u.val j) (hvj : 0 < v.val j) :
    tailToGeneratorQuotient k B
      ⟨monomial u.val (1 : k) - monomial v.val 1,
        binomial_mem_IH k B _ _ (u.property.trans v.property.symm)⟩ = 0 := by
  apply (Submodule.Quotient.mk_eq_zero (generatorRelations k B)).mpr
  exact edge_binomial_mem_nJ k B h u v j huj hvj

/-- Boundary killing is proved directly in nJ; no use of MUJ or a dimension count. -/
theorem boundary_monomial_mem_nJ (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ)
    (u : FactorizationFiber M.base h) (j : Fin 3) (huj : 0 < u.val j)
    (hk : h - weights M.base j ∈ M.base.K) :
    monomial u.val (1 : k) ∈ variableIdeal k * M.base.J k := by
  have hdeg : weight M.base (u.val - Finsupp.single j 1) = h - weights M.base j := by
    have he := congrArg (weight M.base) (remove_variable_add u.val j huj)
    simp only [map_add, weight, Finsupp.weight_single, one_nsmul] at he
    change weights M.base j + weight M.base (u.val - Finsupp.single j 1) = weight M.base u.val at he
    have hudeg := u.property
    omega
  have hm : monomial (u.val - Finsupp.single j 1) (1 : k) ∈ M.base.MK k := by
    apply Ideal.subset_span
    refine ⟨u.val - Finsupp.single j 1, ?_, rfl⟩
    change (factorizationMap M.base.tailDegrees _).val ∈ M.base.K
    rw [← weight_eq_degree, hdeg]
    exact hk
  have hle : M.base.MK k ≤ M.base.J k := by rw [M.base.J_eq_IH_sup_MK k]; exact le_sup_right
  have hp := Ideal.mul_mem_mul
    (show X j ∈ variableIdeal k from Ideal.subset_span ⟨j, rfl⟩) (hle hm)
  simpa only [variable_mul_removed k u.val j huj] using hp

theorem reachable_binomial_mem_nJ (k : Type*) [Field k] (B : Data Gamma) (h : ℕ)
    (u v : FactorizationFiber B h) (hr : (fiberGraph B h).Reachable u v) :
    monomial u.val (1 : k) - monomial v.val 1 ∈ variableIdeal k * B.J k := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => simp
  | @cons u v w hadj p ih =>
    obtain ⟨j, huj, hvj⟩ := hadj.2
    have he := edge_binomial_mem_nJ k B h u v j huj hvj
    have ht := (variableIdeal k * B.J k).add_mem he ih
    convert ht using 1 <;> abel

/-- Boundary killing propagates across a component through explicit relations in nJ. -/
theorem killed_component_monomial_mem_nJ (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (h : ℕ) (C : FiberComponent M.base h) (hC : BoundaryKilled M h C)
    (u : FactorizationFiber M.base h) (hu : (fiberGraph M.base h).connectedComponentMk u = C) :
    monomial u.val (1 : k) ∈ variableIdeal k * M.base.J k := by
  obtain ⟨v, hv, j, hvj, hk⟩ := hC
  have hr := SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)
  have he := reachable_binomial_mem_nJ k M.base h u v hr
  have hb := boundary_monomial_mem_nJ k M h v j hvj hk
  have ht := (variableIdeal k * M.base.J k).add_mem he hb
  simpa only [sub_add_cancel] using ht

end NS25Lean.L2B
