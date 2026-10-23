import NS25Lean.AppendixAEndpoints

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- None means the corresponding pure clip is absent (the source's infinity convention). -/
def optionalAxis (i : Fin 2) : Option ℕ → Set PlanarExponent
  | none => ∅
  | some P => {Finsupp.single i P}

theorem pure_clip_axis_optional (F : InternalFrontend k M h) (G : NormalizedSources F)
    (i : Fin 2) : ∃ P : Option ℕ,
      {u ∈ effectivePureExponents F G | u i.rev = 0} = optionalAxis i P := by
  classical
  by_cases hn : ({u ∈ effectivePureExponents F G | u i.rev = 0} : Set PlanarExponent).Nonempty
  · obtain ⟨u, hu⟩ := hn
    refine ⟨some (u i), ?_⟩
    have he : u = Finsupp.single i (u i) := by
      ext j
      fin_cases i <;> fin_cases j <;> simp_all
    have hsub := pure_clips_axis_subsingleton F G i.rev
    ext v
    constructor
    · intro hv
      have hvu : v = u := hsub hv hu
      exact Set.mem_singleton_iff.mpr (hvu.trans he)
    · intro hv
      have hvu : v = u := (Set.mem_singleton_iff.mp hv).trans he.symm
      simpa only [hvu] using hu
  · refine ⟨none, ?_⟩
    exact Set.not_nonempty_iff_eq_empty.mp hn

/-- Literal two optional pure-power clip interface for the actual colon ideal. -/
theorem pure_clip_two_power_formula (F : InternalFrontend k M h) (G : NormalizedSources F)
    (hq : L3A.q_fs F.initial.ideal = 1) :
    ∃ P Q : Option ℕ, planarJ F G = planarA F G ⊔
      Ideal.span ((fun u => monomial u (1 : k)) '' (optionalAxis 0 P ∪ optionalAxis 1 Q)) := by
  obtain ⟨P, hP⟩ := pure_clip_axis_optional F G 0
  obtain ⟨Q, hQ⟩ := pure_clip_axis_optional F G 1
  refine ⟨P, Q, ?_⟩
  rw [pure_clip_ideal_formula F G hq, pureClipIdeal]
  congr 2
  have he : effectivePureExponents F G = optionalAxis 0 P ∪ optionalAxis 1 Q := by
    rw [← hP, ← hQ]
    ext u
    constructor
    · intro hu
      rcases hu.2.2 with h0 | h1
      · exact Or.inr ⟨hu, h0⟩
      · exact Or.inl ⟨hu, h1⟩
    · rintro (hu | hu) <;> exact hu.1
  rw [he]

end NS25Lean.L3C
