import NS25Lean.BoundarySourceDimension
import NS25Lean.WeightedHomogeneousLift
import NS25Lean.CriticalExponent

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A2
open NS25Lean.L2B NS25Lean.L2B2A ChosenBase Presentation ToricPresentation
  FourGeneratedBridge MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem nJ_component_mem (k : Type*) [Field k] (B : Data Gamma)
    (f : Poly k 3) (hf : f ∈ variableIdeal k * B.J k) (h : ℕ) :
    weightedHomogeneousComponent (weights B) h f ∈ variableIdeal k * B.J k := by
  let N := (variableIdeal k * B.J k).restrictScalars k
  have hle : Submodule.span k (sharedMoves k B ∪ boundaryMoves k B) ≤
      N.comap (weightedHomogeneousComponent (weights B) h) := by
    apply Submodule.span_le.mpr
    intro g hg
    change weightedHomogeneousComponent (weights B) h g ∈ N
    rw [show N = Submodule.span k (sharedMoves k B ∪ boundaryMoves k B) from nJ_eq_span_moves k B]
    rcases hg with hg | hg
    · exact Submodule.span_mono
        (fun x hx => Or.inl (degreeSharedMoves_subset k B h hx)) (project_sharedMove k B h hg)
    · exact Submodule.span_mono
        (fun x hx => Or.inr (degreeBoundaryMoves_subset k B h hx)) (project_boundaryMove k B h hg)
  apply hle
  rw [← nJ_eq_span_moves]
  exact hf

def idealDegreeProjection (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) :
    B.J k →ₗ[k] B.J k :=
  ((weightedHomogeneousComponent (weights B) h).comp ((B.J k).subtype.restrictScalars k)).codRestrict
    ((B.J k).restrictScalars k) (fun f => J_component_mem k B f.val f.property h)

/-- Homogeneous projection on the actual J/nJ, using stability of nJ. -/
def generatorDegreeProjection (k : Type*) [Field k] (B : Data Gamma) (h : ℕ) :
    GeneratorQuotient k B →ₗ[k] GeneratorQuotient k B :=
  (generatorRelations k B).mapQ (generatorRelations k B) (idealDegreeProjection k B h)
    (by intro f hf; exact nJ_component_mem k B f.val hf h)

theorem generatorDegreeProjection_mk (k : Type*) [Field k] (B : Data Gamma)
    (h : ℕ) (f : B.J k) :
    generatorDegreeProjection k B h ((generatorRelations k B).mkQ f) =
      (generatorRelations k B).mkQ (idealDegreeProjection k B h f) := rfl

theorem generatorDegreeProjection_tailDegree (k : Type*) [Field k] (B : Data Gamma)
    (h d : ℕ) (q : tailDegreeImage k B d) :
    generatorDegreeProjection k B h q.val = if h = d then q.val else 0 := by
  classical
  obtain ⟨f, hf, he⟩ := q.property
  have hh : f.val.IsWeightedHomogeneous (weights B) d := hf
  have hle : B.IH k ≤ B.J k := by rw [B.J_eq_IH_sup_MK k]; exact le_sup_left
  let g : B.J k := ⟨f.val, hle f.property⟩
  have hq : q.val = (generatorRelations k B).mkQ g := he.symm
  rw [hq, generatorDegreeProjection_mk]
  by_cases hd : h = d
  · subst h
    rw [ite_eq_left rfl]
    congr 1
    apply Subtype.ext
    exact hh.weightedHomogeneousComponent_same
  · rw [ite_eq_right hd]
    have hz : idealDegreeProjection k B h g = 0 := by
      apply Subtype.ext
      exact hh.weightedHomogeneousComponent_ne h hd
    rw [hz, map_zero]

instance finiteTailDegreeImage (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ) :
    Module.Finite k (tailDegreeImage k M.base h) := by
  have e := rangesEquivOfKerEq
    (V := tailDegreeSpace k M.base h) (W := GeneratorQuotient k M.base)
    (Z := FiberComponent M.base h →₀ k)
    (tailDegreeClassMap k M h) (tailDegreeCoordinateMap k M h)
    (tailDegree_maps_ker_eq k M h)
  have hi : Module.Finite k (LinearMap.range (tailDegreeClassMap k M h)) :=
    Module.Finite.equiv e.symm
  rw [tailDegreeClassMap_range] at hi
  exact hi

theorem tailDegreeImage_eq_bot_outside (k : Type*) [Field k] (M : MultiplicityBase Gamma)
    (h : ℕ) (hh : h ∉ activeDegreeFinset M) : tailDegreeImage k M.base h = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  rw [tailDegreeImage_finrank_eq_fiberContribution, contribution_zero_outside_active M h hh]

end NS25Lean.L2B2A2
