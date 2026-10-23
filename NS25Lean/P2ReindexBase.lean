import NS25Lean.P2Sectors

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A1R

open ChosenBase L2B
variable {Gamma : NumericalSemigroup}

/-- Extend a tail permutation by fixing the distinguished zero coordinate. -/
def tailLift (e : Fin 3 ≃ Fin 3) : Fin 4 ≃ Fin 4 where
  toFun := Fin.cases 0 (fun i => (e i).succ)
  invFun := Fin.cases 0 (fun i => (e.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp

@[simp] theorem tailLift_zero (e : Fin 3 ≃ Fin 3) : tailLift e 0 = 0 := rfl

@[simp] theorem tailLift_succ (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    tailLift e i.succ = (e i).succ := rfl

@[simp] theorem tailLift_symm (e : Fin 3 ≃ Fin 3) :
    (tailLift e).symm = tailLift e.symm := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [tailLift]

/-- The displayed-family permutation obtained by conjugating the tail permutation
through the chosen-base ordering. It fixes the actual pivot. -/
def familyPerm (B : Data Gamma) (e : Fin 3 ≃ Fin 3) : Fin 4 ≃ Fin 4 :=
  B.order.symm.trans ((tailLift e).trans B.order)

@[simp] theorem familyPerm_order (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 4) :
    familyPerm B e (B.order i) = B.order (tailLift e i) := by
  simp [familyPerm]

@[simp] theorem familyPerm_pivot (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    familyPerm B e B.pivot = B.pivot := by
  have h0 : B.order 0 = B.pivot := by simp [Data.order]
  rw [← h0, familyPerm_order, tailLift_zero, h0]

/-- Reindex only the three tail coordinates, retaining the same actual pivot. -/
def reindexData (B : Data Gamma) (e : Fin 3 ≃ Fin 3) : Data Gamma where
  family := B.family ∘ familyPerm B e
  generates := by
    have hr : Set.range (fun i => ((B.family ∘ familyPerm B e) i).val) =
        Set.range (fun i => (B.family i).val) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨familyPerm B e i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨(familyPerm B e).symm i, by simp⟩
    rw [hr, B.generates]
  positive := fun i => B.positive (familyPerm B e i)
  minimal := by
    intro i hi
    apply B.minimal (familyPerm B e i)
    apply AddSubmonoid.closure_mono _ hi
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨familyPerm B e j, fun heq => hj ((familyPerm B e).injective heq), rfl⟩
  pivot := B.pivot

@[simp] theorem reindexData_family (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 4) :
    (reindexData B e).family i = B.family (familyPerm B e i) := rfl

@[simp] theorem reindexData_pivot (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (reindexData B e).pivot = B.pivot := rfl

@[simp] theorem reindexData_order (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (reindexData B e).order = B.order := rfl

@[simp] theorem reindexData_degrees (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 4) :
    (reindexData B e).degrees i = B.degrees (tailLift e i) := by
  change B.family (familyPerm B e (B.order i)) = B.family (B.order (tailLift e i))
  rw [familyPerm_order]

@[simp] theorem reindexData_q (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (reindexData B e).q = B.q := by
  simp [Data.q, reindexData]

@[simp] theorem weights_reindex_data (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    weights (reindexData B e) i = weights B (e i) := by
  simp [weights, Data.tailDegrees]

theorem isMultiplicity_reindex (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hB : IsMultiplicity B) : IsMultiplicity (reindexData B e) := by
  simpa [IsMultiplicity] using hB

/-- Actual multiplicity-base reindexing with convention
`weights (M.reindex e) i = weights M (e i)`. -/
def reindexMultiplicityBase (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    MultiplicityBase Gamma :=
  ⟨reindexData M.base e, isMultiplicity_reindex M.base e M.isMultiplicity⟩

@[simp] theorem reindexMultiplicityBase_pivot (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) :
    (reindexMultiplicityBase M e).base.pivot = M.base.pivot := rfl

@[simp] theorem weights_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (i : Fin 3) :
    weights (reindexMultiplicityBase M e).base i = weights M.base (e i) :=
  weights_reindex_data M.base e i

/-- Extensionality for chosen-base data: proof fields are propositions. -/
theorem data_eq_of_family_pivot {B D : Data Gamma} (hfamily : B.family = D.family)
    (hpivot : B.pivot = D.pivot) : B = D := by
  cases B
  cases D
  simp_all

/-- Extensionality for actual multiplicity bases. -/
theorem multiplicityBase_eq_of_base {M N : MultiplicityBase Gamma} (hbase : M.base = N.base) :
    M = N := by
  cases M
  cases N
  simp_all

@[simp] theorem familyPerm_reindex_symm (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    familyPerm (reindexData B e) e.symm = (familyPerm B e).symm := by
  ext i
  simp [familyPerm, tailLift_symm]

@[simp] theorem reindexData_symm (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    reindexData (reindexData B e) e.symm = B := by
  apply data_eq_of_family_pivot
  · funext i
    simp [reindexData_family]
  · rfl

end NS25Lean.L5A1R
