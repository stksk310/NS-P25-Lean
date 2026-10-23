import NS25Lean.ActiveFiberTailCoordinates
import Mathlib.LinearAlgebra.Dimension.Finite

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B2A
open NS25Lean.L2B ChosenBase Presentation ToricPresentation MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem single_sub_linearIndependent (k : Type*) [Field k] {ι : Type*} [Finite ι] (o : ι) :
    LinearIndependent k (fun i : {i : ι // i ≠ o} =>
      Finsupp.single i.val (1 : k) - Finsupp.single o 1) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have he := congrArg (fun v : ι →₀ k => v i.val) ha
  simpa [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.sub_apply,
    Finsupp.single_apply, i.property, Ne.symm i.property, Subtype.val_inj] using he

/-- The full component-coordinate sum-zero space has c-1 dimensions, including the empty fiber. -/
theorem finrank_single_differences (k : Type*) [Field k] (ι : Type*) [Finite ι] :
    Module.finrank k (Submodule.span k {v : ι →₀ k | ∃ C D : ι,
      v = Finsupp.single C 1 - Finsupp.single D 1}) = Nat.card ι - 1 := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  by_cases hn : Nonempty ι
  · obtain ⟨o⟩ := hn
    let g : {i : ι // i ≠ o} → (ι →₀ k) :=
      fun i => Finsupp.single i.val 1 - Finsupp.single o 1
    have hmem : ∀ C : ι, Finsupp.single C 1 - Finsupp.single o 1 ∈
        Submodule.span k (Set.range g) := by
      intro C
      by_cases hc : C = o
      · subst C; simp
      · exact Submodule.subset_span ⟨⟨C, hc⟩, rfl⟩
    have he : Submodule.span k {v : ι →₀ k | ∃ C D : ι,
        v = Finsupp.single C 1 - Finsupp.single D 1} = Submodule.span k (Set.range g) := by
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro v ⟨C, D, rfl⟩
        change Finsupp.single C (1 : k) - Finsupp.single D 1 ∈ Submodule.span k (Set.range g)
        have hh := (Submodule.span k (Set.range g)).sub_mem (hmem C) (hmem D)
        simpa only [sub_sub_sub_cancel_right] using hh
      · apply Submodule.span_le.mpr
        rintro v ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i.val, o, rfl⟩
    rw [he, finrank_span_eq_card (single_sub_linearIndependent k o)]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  · have : IsEmpty ι := not_nonempty_iff.mp hn
    have he : {v : ι →₀ k | ∃ C D : ι,
        v = Finsupp.single C 1 - Finsupp.single D 1} = ∅ := by ext v; simp
    rw [he, Submodule.span_empty]
    simp only [finrank_bot, Nat.card_eq_fintype_card, Fintype.card_eq_zero, Nat.zero_sub]

theorem coordinateDifferenceSpace_no_killing (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) (hk : ∀ C, ¬BoundaryKilled M h C) :
    coordinateDifferenceSpace k M h = Submodule.span k
      {v : FiberComponent M.base h →₀ k | ∃ C D : FiberComponent M.base h,
        v = Finsupp.single C 1 - Finsupp.single D 1} := by
  classical
  simp only [coordinateDifferenceSpace, survivingUnit, ite_eq_right (hk _)]

theorem coordinateDifferenceSpace_with_killing (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) (o : FiberComponent M.base h)
    (ho : BoundaryKilled M h o) :
    coordinateDifferenceSpace k M h = Submodule.span k
      (Set.range (fun C : {C : FiberComponent M.base h // ¬BoundaryKilled M h C} =>
        Finsupp.single C.val (1 : k))) := by
  classical
  let N := Submodule.span k
    (Set.range (fun C : {C : FiberComponent M.base h // ¬BoundaryKilled M h C} =>
      Finsupp.single C.val (1 : k)))
  have hmem : ∀ C, survivingUnit k M h C ∈ N := by
    intro C
    by_cases hc : BoundaryKilled M h C
    · simp [survivingUnit, hc, N]
    · rw [survivingUnit, ite_eq_right hc]
      exact Submodule.subset_span ⟨⟨C, hc⟩, rfl⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨C, D, rfl⟩
    exact N.sub_mem (hmem C) (hmem D)
  · apply Submodule.span_le.mpr
    rintro v ⟨C, rfl⟩
    have he : Finsupp.single C.val (1 : k) = survivingUnit k M h C.val - survivingUnit k M h o := by
      simp [survivingUnit, C.property, ho]
    change Finsupp.single C.val (1 : k) ∈ coordinateDifferenceSpace k M h
    rw [he]
    exact Submodule.subset_span ⟨C.val, o, rfl⟩

theorem coordinateDifferenceSpace_finrank (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) :
    Module.finrank k (coordinateDifferenceSpace k M h) = fiberContribution M h := by
  classical
  let : Fintype (FiberComponent M.base h) := Fintype.ofFinite _
  by_cases hd : killedCount M h = 0
  · have hk : ∀ C, ¬BoundaryKilled M h C := by
      intro C hc
      have hp : 0 < killedCount M h :=
        Nat.card_pos_iff.mpr ⟨⟨⟨C, hc⟩⟩, inferInstance⟩
      omega
    rw [coordinateDifferenceSpace_no_killing k M h hk, finrank_single_differences,
      fiberContribution, ite_eq_left hd]
    rfl
  · obtain ⟨o, ho⟩ := (Nat.card_ne_zero.mp hd).1
    rw [coordinateDifferenceSpace_with_killing k M h o ho]
    have hli : LinearIndependent k
        (fun C : {C : FiberComponent M.base h // ¬BoundaryKilled M h C} =>
          Finsupp.single C.val (1 : k)) :=
      (Finsupp.linearIndependent_single_one (ι := FiberComponent M.base h) (R := k)).comp
        Subtype.val Subtype.val_injective
    rw [finrank_span_eq_card hli, Fintype.card_subtype_compl,
      fiberContribution, ite_eq_right hd]
    simp only [componentCount, killedCount, Nat.card_eq_fintype_card]

/-- The required local active-fiber theorem, proved through actual nJ component coordinates. -/
theorem tailDegreeImage_finrank_eq_fiberContribution (k : Type*) [Field k]
    (M : MultiplicityBase Gamma) (h : ℕ) :
    Module.finrank k (tailDegreeImage k M.base h) = fiberContribution M h := by
  rw [tailDegreeImage_finrank_eq_coordinateDifferenceSpace, coordinateDifferenceSpace_finrank]

end NS25Lean.L2B2A
