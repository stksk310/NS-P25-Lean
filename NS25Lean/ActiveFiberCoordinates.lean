import NS25Lean.ActiveFiberDegreeRelations

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A
open NS25Lean.L2B ChosenBase Presentation ToricPresentation MvPolynomial
variable {Gamma : NumericalSemigroup}

open Classical in
def survivingUnit (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ)
    (C : FiberComponent M.base h) : FiberComponent M.base h →₀ k :=
  if BoundaryKilled M h C then 0 else Finsupp.single C 1

open Classical in
/-- Component sums of the degree-h coefficients, with exactly the boundary coordinates removed. -/
def survivingCoordinates (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ) :
    Poly k 3 →ₗ[k] (FiberComponent M.base h →₀ k) :=
  (basisMonomials (Fin 3) k).constr k fun u =>
    if hu : weight M.base u = h then
      survivingUnit k M h ((fiberGraph M.base h).connectedComponentMk ⟨u, hu⟩) else 0

theorem survivingCoordinates_monomial (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (h : ℕ) (u : FactorizationFiber M.base h) :
    survivingCoordinates k M h (monomial u.val (1 : k)) =
      survivingUnit k M h ((fiberGraph M.base h).connectedComponentMk u) := by
  classical
  change (basisMonomials (Fin 3) k).constr k _ ((basisMonomials (Fin 3) k) u.val) = _
  rw [Module.Basis.constr_basis]
  simp only [dite_eq_left u.property]
  rfl

theorem shared_connectedComponent_eq (B : Data Gamma) (h : ℕ)
    (u v : FactorizationFiber B h) (hj : ∃ j, 0 < u.val j ∧ 0 < v.val j) :
    (fiberGraph B h).connectedComponentMk u = (fiberGraph B h).connectedComponentMk v := by
  by_cases he : u = v
  · rw [he]
  · exact SimpleGraph.ConnectedComponent.sound
      (show (fiberGraph B h).Adj u v from ⟨he, hj⟩).reachable

theorem survivingCoordinates_shared (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (h : ℕ) {f : Poly k 3} (hf : f ∈ degreeSharedMoves k M.base h) :
    survivingCoordinates k M h f = 0 := by
  obtain ⟨u, v, hj, rfl⟩ := hf
  rw [map_sub, survivingCoordinates_monomial, survivingCoordinates_monomial,
    shared_connectedComponent_eq M.base h u v hj, sub_self]

theorem survivingCoordinates_boundary (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (h : ℕ) {f : Poly k 3} (hf : f ∈ degreeBoundaryMoves k M.base h) :
    survivingCoordinates k M h f = 0 := by
  classical
  obtain ⟨u, hj, rfl⟩ := hf
  rw [survivingCoordinates_monomial, survivingUnit, ite_eq_left]
  exact ⟨u, rfl, hj⟩

theorem survivingCoordinates_zero_of_mem_nJ (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) (f : Poly k 3)
    (hf : f.IsWeightedHomogeneous (weights M.base) h)
    (hmem : f ∈ variableIdeal k * M.base.J k) : survivingCoordinates k M h f = 0 := by
  have hle : Submodule.span k (degreeSharedMoves k M.base h ∪ degreeBoundaryMoves k M.base h) ≤
      LinearMap.ker (survivingCoordinates k M h) := by
    apply Submodule.span_le.mpr
    intro g hg
    rcases hg with hg | hg
    · exact survivingCoordinates_shared k M h hg
    · exact survivingCoordinates_boundary k M h hg
  exact hle ((nJ_degree_mem_iff k M.base h f hf).mp hmem)

/-- The ambient quotient uses the actual product ideal nJ. -/
def ambientRelations (k : Type*) [Field k] (M : MultiplicityBase Gamma) : Submodule k (Poly k 3) :=
  (variableIdeal k * M.base.J k).restrictScalars k

def componentReconstruction (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ) :
    (FiberComponent M.base h →₀ k) →ₗ[k] (Poly k 3 ⧸ ambientRelations k M) :=
  Finsupp.linearCombination k fun C =>
    (ambientRelations k M).mkQ (monomial C.out.val (1 : k))

theorem componentReconstruction_unit (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (h : ℕ) (u : FactorizationFiber M.base h) :
    componentReconstruction k M h
        (survivingUnit k M h ((fiberGraph M.base h).connectedComponentMk u)) =
      (ambientRelations k M).mkQ (monomial u.val (1 : k)) := by
  classical
  let C := (fiberGraph M.base h).connectedComponentMk u
  change componentReconstruction k M h (survivingUnit k M h C) = _
  by_cases hk : BoundaryKilled M h C
  · rw [survivingUnit, ite_eq_left hk, map_zero]
    symm
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact killed_component_monomial_mem_nJ k M h C hk u rfl
  · rw [survivingUnit, ite_eq_right hk, componentReconstruction, Finsupp.linearCombination_single,
      one_smul]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact reachable_binomial_mem_nJ k M.base h C.out u
      (SimpleGraph.ConnectedComponent.exact C.out_eq)

theorem componentReconstruction_monomial (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (h : ℕ) (u : FactorizationFiber M.base h) (a : k) :
    componentReconstruction k M h (survivingCoordinates k M h (monomial u.val a)) =
      (ambientRelations k M).mkQ (monomial u.val a) := by
  have he : monomial u.val a = a • monomial u.val (1 : k) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, map_smul, map_smul, survivingCoordinates_monomial,
    componentReconstruction_unit]

/-- Actual polynomial reconstruction modulo nJ, not merely an abstract vector-space model. -/
theorem componentReconstruction_homogeneous (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) (f : Poly k 3)
    (hf : f.IsWeightedHomogeneous (weights M.base) h) :
    componentReconstruction k M h (survivingCoordinates k M h f) =
      (ambientRelations k M).mkQ f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  exact componentReconstruction_monomial k M h ⟨u, hf (mem_support_iff.mp hu)⟩ (coeff u f)

/-- Complete local normal form: all surviving component coordinates vanish exactly on nJ. -/
theorem survivingCoordinates_eq_zero_iff (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) (f : Poly k 3)
    (hf : f.IsWeightedHomogeneous (weights M.base) h) :
    survivingCoordinates k M h f = 0 ↔ f ∈ variableIdeal k * M.base.J k := by
  constructor
  · intro hz
    have he := componentReconstruction_homogeneous k M h f hf
    rw [hz, map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero _).mp he.symm
  · exact survivingCoordinates_zero_of_mem_nJ k M h f hf

/-- In particular there is no extra killed component. -/
theorem monomial_mem_nJ_iff_boundaryKilled (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) (u : FactorizationFiber M.base h) :
    monomial u.val (1 : k) ∈ variableIdeal k * M.base.J k ↔
      BoundaryKilled M h ((fiberGraph M.base h).connectedComponentMk u) := by
  classical
  rw [← survivingCoordinates_eq_zero_iff k M h _
    (isWeightedHomogeneous_monomial (weights M.base) u.val (1 : k) u.property),
    survivingCoordinates_monomial, survivingUnit]
  split_ifs with hk
  · simp [hk]
  · simp [hk]

end NS25Lean.L2B2A
