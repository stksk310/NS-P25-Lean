import NS25Lean.ActiveFiberCoordinates

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A
open NS25Lean.L2B ChosenBase Presentation ToricPresentation MvPolynomial
variable {Gamma : NumericalSemigroup}

def rangesEquivOfKerEq {k V W Z : Type*} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    [AddCommGroup Z] [Module k Z] (f : V →ₗ[k] W) (g : V →ₗ[k] Z)
    (hker : LinearMap.ker f = LinearMap.ker g) :
    LinearMap.range f ≃ₗ[k] LinearMap.range g :=
  f.quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans g.quotKerEquivRange)

def coordinateDifferenceSpace (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ) :
    Submodule k (FiberComponent M.base h →₀ k) :=
  Submodule.span k {v | ∃ C D : FiberComponent M.base h,
    v = survivingUnit k M h C - survivingUnit k M h D}

def tailDegreeClassMap (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ) :
    tailDegreeSpace k M.base h →ₗ[k] GeneratorQuotient k M.base :=
  (tailToGeneratorQuotient k M.base).comp (tailDegreeSpace k M.base h).subtype

def tailDegreeCoordinateMap (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ) :
    tailDegreeSpace k M.base h →ₗ[k] (FiberComponent M.base h →₀ k) :=
  (survivingCoordinates k M h).comp
    (((M.base.IH k).subtype.restrictScalars k).comp (tailDegreeSpace k M.base h).subtype)

theorem tailDegreeClassMap_range (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ) :
    LinearMap.range (tailDegreeClassMap k M h) = tailDegreeImage k M.base h := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The two maps have the same kernel by the actual local normal form. -/
theorem tailDegree_maps_ker_eq (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ) :
    LinearMap.ker (tailDegreeClassMap k M h) =
      LinearMap.ker (tailDegreeCoordinateMap k M h) := by
  ext f
  change tailToGeneratorQuotient k M.base f.val = 0 ↔
    survivingCoordinates k M h f.val.val = 0
  change (generatorRelations k M.base).mkQ _ = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (survivingCoordinates_eq_zero_iff k M h f.val.val f.property).symm

theorem tailDegreeCoordinateMap_range (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) :
    LinearMap.range (tailDegreeCoordinateMap k M h) = coordinateDifferenceSpace k M h := by
  apply le_antisymm
  · rintro v ⟨f, rfl⟩
    have hmem := (IH_degree_mem_iff k M.base h f.val.val f.property).mp f.val.property
    change survivingCoordinates k M h f.val.val ∈ coordinateDifferenceSpace k M h
    have hle : Submodule.span k (degreeToricMoves k M.base h) ≤
        (coordinateDifferenceSpace k M h).comap (survivingCoordinates k M h) := by
      apply Submodule.span_le.mpr
      rintro g ⟨u, v, rfl⟩
      change survivingCoordinates k M h (monomial u.val 1 - monomial v.val 1) ∈
        coordinateDifferenceSpace k M h
      rw [map_sub, survivingCoordinates_monomial, survivingCoordinates_monomial]
      exact Submodule.subset_span ⟨_, _, rfl⟩
    exact hle hmem
  · apply Submodule.span_le.mpr
    rintro v ⟨C, D, rfl⟩
    let f : M.base.IH k :=
      ⟨monomial C.out.val 1 - monomial D.out.val 1,
        binomial_mem_IH k M.base _ _ (C.out.property.trans D.out.property.symm)⟩
    have hf : f ∈ tailDegreeSpace k M.base h :=
      (isWeightedHomogeneous_monomial (weights M.base) C.out.val (1 : k) C.out.property).sub
        (isWeightedHomogeneous_monomial (weights M.base) D.out.val (1 : k) D.out.property)
    change ∃ x : tailDegreeSpace k M.base h,
      tailDegreeCoordinateMap k M h x = survivingUnit k M h C - survivingUnit k M h D
    refine ⟨⟨f, hf⟩, ?_⟩
    dsimp only [tailDegreeCoordinateMap, LinearMap.comp_apply,
      Submodule.subtype_apply, LinearMap.restrictScalars_apply, f]
    have hc : (fiberGraph M.base h).connectedComponentMk C.out = C := C.out_eq
    have hd : (fiberGraph M.base h).connectedComponentMk D.out = D := D.out_eq
    rw [map_sub, survivingCoordinates_monomial, survivingCoordinates_monomial, hc, hd]

/-- Actual local kernel and image identification gives equality of the two finite dimensions. -/
theorem tailDegreeImage_finrank_eq_coordinateDifferenceSpace (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) :
    Module.finrank k (tailDegreeImage k M.base h) =
      Module.finrank k (coordinateDifferenceSpace k M h) := by
  have he := (rangesEquivOfKerEq
    (V := tailDegreeSpace k M.base h) (W := GeneratorQuotient k M.base)
    (Z := FiberComponent M.base h →₀ k)
    (tailDegreeClassMap k M h) (tailDegreeCoordinateMap k M h)
    (tailDegree_maps_ker_eq k M h)).finrank_eq
  rw [tailDegreeClassMap_range, tailDegreeCoordinateMap_range] at he
  exact he

end NS25Lean.L2B2A
