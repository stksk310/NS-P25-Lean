import NS25Lean.GeneratorDegreeProjection

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A2
open NS25Lean.L2B NS25Lean.L2B2A ChosenBase Presentation ToricPresentation
  FourGeneratedBridge MvPolynomial
variable {Gamma : NumericalSemigroup}

section LinearAssembly
variable {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]

def pieceSum (P : ι → Submodule k V) : (∀ i, P i) →ₗ[k] V :=
  ∑ i, (P i).subtype.comp (LinearMap.proj i)

theorem pieceSum_apply (P : ι → Submodule k V) (x : ∀ i, P i) :
    pieceSum P x = ∑ i, (x i).val := by
  simp only [pieceSum, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply]

theorem pieceSum_single (P : ι → Submodule k V) [DecidableEq ι] (i : ι) (x : P i) :
    pieceSum P (Pi.single i x) = x.val := by
  rw [pieceSum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem pieceSum_injective [DecidableEq ι] (P : ι → Submodule k V) (pr : ι → V →ₗ[k] V)
    (hp : ∀ i j (x : P j), pr i x.val = if i = j then x.val else 0) :
    Function.Injective (pieceSum P) := by
  classical
  intro x y he
  funext i
  apply Subtype.ext
  have hx : pr i (pieceSum P x) = (x i).val := by
    rw [pieceSum_apply, map_sum]
    simp only [hp]
    simp
  have hy : pr i (pieceSum P y) = (y i).val := by
    rw [pieceSum_apply, map_sum]
    simp only [hp]
    simp
  exact hx.symm.trans ((congrArg (pr i) he).trans hy)
end LinearAssembly

abbrev ActiveIndex (M : MultiplicityBase Gamma) := {h : ℕ // h ∈ activeDegreeFinset M}

def activeTailSum (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    (∀ h : ActiveIndex M, tailDegreeImage k M.base h.val) →ₗ[k] GeneratorQuotient k M.base :=
  pieceSum (fun h : ActiveIndex M => tailDegreeImage k M.base h.val)

theorem activeTailSum_injective (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    Function.Injective (activeTailSum k M) := by
  classical
  apply pieceSum_injective _ (fun h : ActiveIndex M => generatorDegreeProjection k M.base h.val)
  intro h d x
  rw [generatorDegreeProjection_tailDegree]
  simp only [Subtype.val_inj]

theorem activeTailSum_range (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    LinearMap.range (activeTailSum k M) = tailGeneratorImage k M.base := by
  classical
  apply le_antisymm
  · rintro q ⟨x, rfl⟩
    change pieceSum (fun h : ActiveIndex M => tailDegreeImage k M.base h.val) x ∈ _
    rw [pieceSum_apply]
    apply Submodule.sum_mem
    intro h _
    obtain ⟨f, _, he⟩ := (x h).property
    exact ⟨f, he⟩
  · rintro q ⟨f, rfl⟩
    apply map_mem_of_spanning ((M.base.IH k).restrictScalars k) (toricMoves k M.base)
      (IH_eq_span_toricMoves k M.base) (tailToGeneratorQuotient k M.base)
      (LinearMap.range (activeTailSum k M)) _ f
    rintro ⟨g, hg⟩ ⟨u, v, he, rfl⟩
    let f : M.base.IH k := ⟨monomial u 1 - monomial v 1, hg⟩
    have hd : f ∈ tailDegreeSpace k M.base (weight M.base u) :=
      (isWeightedHomogeneous_monomial (weights M.base) u (1 : k) rfl).sub
        (isWeightedHomogeneous_monomial (weights M.base) v (1 : k) he.symm)
    let q : tailDegreeImage k M.base (weight M.base u) :=
      ⟨tailToGeneratorQuotient k M.base f, ⟨f, hd, rfl⟩⟩
    by_cases ha : weight M.base u ∈ activeDegreeFinset M
    · refine ⟨Pi.single (⟨weight M.base u, ha⟩ : ActiveIndex M) q, ?_⟩
      exact pieceSum_single (fun h : ActiveIndex M => tailDegreeImage k M.base h.val)
        ⟨weight M.base u, ha⟩ q
    · have hz : q.val = 0 := by
        exact (tailDegreeImage_eq_bot_outside k M _ ha).le q.property
      change q.val ∈ LinearMap.range (activeTailSum k M)
      exact hz.symm ▸ (LinearMap.range (activeTailSum k M)).zero_mem

instance finiteTailGeneratorImage (k : Type*) [Field k] (M : MultiplicityBase Gamma) :
    Module.Finite k (tailGeneratorImage k M.base) := by
  have hi : Module.Finite k (LinearMap.range (activeTailSum k M)) := inferInstance
  rw [activeTailSum_range] at hi
  exact hi

/-- Finite graded assembly of the frozen local normal-form calculation. -/
theorem tailGeneratorImage_finrank_eq_contribution_sum (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) :
    Module.finrank k (tailGeneratorImage k M.base) =
      ∑ h ∈ activeDegreeFinset M, fiberContribution M h := by
  have he := (LinearEquiv.ofInjective (activeTailSum k M) (activeTailSum_injective k M)).finrank_eq
  rw [activeTailSum_range, Module.finrank_pi_fintype] at he
  rw [← he]
  simp only [tailDegreeImage_finrank_eq_fiberContribution]
  exact Finset.sum_coe_sort (activeDegreeFinset M) (fiberContribution M)

end NS25Lean.L2B2A2
