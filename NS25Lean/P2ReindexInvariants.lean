import NS25Lean.P2ReindexFibers

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A1R

open ChosenBase L2B
variable {Gamma : NumericalSemigroup}

/-- Reindexing by the inverse permutation restores the actual multiplicity base. -/
theorem reindexMultiplicityBase_symm (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    reindexMultiplicityBase (reindexMultiplicityBase M e) e.symm = M := by
  apply multiplicityBase_eq_of_base
  exact reindexData_symm M.base e

/-- The actual boundary-killed predicate is preserved through the induced
component equivalence, not merely its cardinality. -/
theorem boundaryKilled_reindex_iff (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (h : ℕ) (C : FiberComponent M.base h) :
    BoundaryKilled (reindexMultiplicityBase M e) h (fiberComponentEquiv M e h C) ↔
      BoundaryKilled M h C := by
  let F := factorizationFiberEquiv M e h
  let G := fiberGraphIso M e h
  constructor
  · rintro ⟨u, huC, j, huj, huK⟩
    let v : FactorizationFiber M.base h := F.symm u
    have hvC : (fiberGraph M.base h).connectedComponentMk v = C := by
      calc
        (fiberGraph M.base h).connectedComponentMk v =
            G.connectedComponentEquiv.symm
              ((fiberGraph (reindexMultiplicityBase M e).base h).connectedComponentMk u) := by
          rfl
        _ = G.connectedComponentEquiv.symm (G.connectedComponentEquiv C) :=
          congrArg G.connectedComponentEquiv.symm huC
        _ = C := G.connectedComponentEquiv.symm_apply_apply C
    refine ⟨v, hvC, e j, ?_, ?_⟩
    · have hvj := factorizationFiberEquiv_apply M e h v j
      change 0 < v.val (e j)
      rw [← hvj]
      simpa [F, v] using huj
    · simpa using huK
  · rintro ⟨u, huC, j, huj, huK⟩
    refine ⟨F u, ?_, e.symm j, ?_, ?_⟩
    · change (fiberGraph (reindexMultiplicityBase M e).base h).connectedComponentMk
          (G.toEquiv u) = G.connectedComponentEquiv C
      exact congrArg (fun X => G.connectedComponentEquiv X) huC
    · simpa [F]
    · simpa using huK

/-- Equivalence of the actual boundary-killed component subtypes. -/
def killedComponentEquiv (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) (h : ℕ) :
    {C : FiberComponent M.base h // BoundaryKilled M h C} ≃
      {C : FiberComponent (reindexMultiplicityBase M e).base h //
        BoundaryKilled (reindexMultiplicityBase M e) h C} where
  toFun C := ⟨fiberComponentEquiv M e h C.val,
    (boundaryKilled_reindex_iff M e h C.val).2 C.property⟩
  invFun C := ⟨(fiberComponentEquiv M e h).symm C.val, by
    apply (boundaryKilled_reindex_iff M e h _).1
    simpa using C.property⟩
  left_inv C := by apply Subtype.ext; simp
  right_inv C := by apply Subtype.ext; simp

theorem killedCount_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) (h : ℕ) :
    killedCount (reindexMultiplicityBase M e) h = killedCount M h := by
  exact (Nat.card_congr (killedComponentEquiv M e h)).symm

theorem fiberContribution_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (h : ℕ) :
    fiberContribution (reindexMultiplicityBase M e) h = fiberContribution M h := by
  simp [fiberContribution, killedCount_reindex, componentCount_reindex]

end NS25Lean.L5A1R
