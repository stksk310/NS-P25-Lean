import NS25Lean.P2ReindexBase

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A1R

open ChosenBase L2B L2B2A2
variable {Gamma : NumericalSemigroup}

@[simp] theorem H_reindex_data (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (reindexData B e).H = B.H := by
  unfold Data.H
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, by simp [weights, Data.tailDegrees]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp [weights, Data.tailDegrees]⟩

@[simp] theorem K_reindex_data (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (reindexData B e).K = B.K := by
  simp [Data.K]

@[simp] theorem H_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    (reindexMultiplicityBase M e).base.H = M.base.H :=
  H_reindex_data M.base e

@[simp] theorem K_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    (reindexMultiplicityBase M e).base.K = M.base.K :=
  K_reindex_data M.base e

theorem isMinimalTailGenerator_reindex_iff (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) (h : ℕ) :
    FourGeneratedBridge.IsMinimalTailGenerator
        (reindexMultiplicityBase M e).base.H (reindexMultiplicityBase M e).base.K h ↔
      FourGeneratedBridge.IsMinimalTailGenerator M.base.H M.base.K h := by
  rw [H_reindex, K_reindex]

/-- Coordinate convention: the transported exponent satisfies `uᵉ i = u (e i)`. -/
def coordinateReindex (e : Fin 3 ≃ Fin 3) : (Fin 3 →₀ ℕ) ≃+ (Fin 3 →₀ ℕ) :=
  Finsupp.domCongr e.symm

@[simp] theorem coordinateReindex_apply (e : Fin 3 ≃ Fin 3) (u : Fin 3 →₀ ℕ)
    (i : Fin 3) : coordinateReindex e u i = u (e i) := by
  simp [coordinateReindex, Finsupp.equivMapDomain_apply]

@[simp] theorem coordinateReindex_symm (e : Fin 3 ≃ Fin 3) :
    (coordinateReindex e).symm = coordinateReindex e.symm := rfl

theorem weight_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (u : Fin 3 →₀ ℕ) :
    weight (reindexMultiplicityBase M e).base (coordinateReindex e u) = weight M.base u := by
  simp only [weight_eq_sum, coordinateReindex_apply, weights_reindex]
  exact Equiv.sum_comp e (fun i => u i * weights M.base i)

/-- Every actual factorization fiber is transported degree-for-degree. -/
def factorizationFiberEquiv (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) (h : ℕ) :
    FactorizationFiber M.base h ≃
      FactorizationFiber (reindexMultiplicityBase M e).base h where
  toFun u := ⟨coordinateReindex e u.val, (weight_reindex M e u.val).trans u.property⟩
  invFun v := ⟨coordinateReindex e.symm v.val, by
    have hw := weight_reindex M e (coordinateReindex e.symm v.val)
    rw [← coordinateReindex_symm e] at hw
    rw [(coordinateReindex e).apply_symm_apply] at hw
    exact hw.symm.trans v.property⟩
  left_inv u := by
    apply Subtype.ext
    exact (coordinateReindex e).symm_apply_apply u.val
  right_inv v := by
    apply Subtype.ext
    exact (coordinateReindex e).apply_symm_apply v.val

@[simp] theorem factorizationFiberEquiv_apply (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) (h : ℕ) (u : FactorizationFiber M.base h) (i : Fin 3) :
    (factorizationFiberEquiv M e h u).val i = u.val (e i) :=
  coordinateReindex_apply e u.val i

/-- Reindexing is an isomorphism of every actual tail fiber graph. -/
def fiberGraphIso (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) (h : ℕ) :
    fiberGraph M.base h ≃g fiberGraph (reindexMultiplicityBase M e).base h where
  toEquiv := factorizationFiberEquiv M e h
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨hne, i, hu, hv⟩
      refine ⟨fun heq => hne (congrArg _ heq), e i, ?_, ?_⟩
      · simpa using hu
      · simpa using hv
    · rintro ⟨hne, i, hu, hv⟩
      refine ⟨fun heq => hne ((factorizationFiberEquiv M e h).injective heq), e.symm i, ?_, ?_⟩
      · simpa using hu
      · simpa using hv

/-- The induced actual connected-component equivalence. -/
def fiberComponentEquiv (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) (h : ℕ) :
    FiberComponent M.base h ≃ FiberComponent (reindexMultiplicityBase M e).base h :=
  (fiberGraphIso M e h).connectedComponentEquiv

theorem componentCount_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) (h : ℕ) :
    componentCount (reindexMultiplicityBase M e).base h = componentCount M.base h := by
  exact (Nat.card_congr (fiberComponentEquiv M e h)).symm

/-- Minimal tail sources are literally the same degrees after tail-coordinate reindexing. -/
def sourceEquiv (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    Source M.base ≃ Source (reindexMultiplicityBase M e).base where
  toFun s := ⟨s.val, by
    change FourGeneratedBridge.IsMinimalTailGenerator
      (reindexMultiplicityBase M e).base.H (reindexMultiplicityBase M e).base.K s.val
    rw [H_reindex, K_reindex]
    exact s.property⟩
  invFun s := ⟨s.val, by
    change FourGeneratedBridge.IsMinimalTailGenerator M.base.H M.base.K s.val
    rw [← H_reindex M e, ← K_reindex M e]
    exact s.property⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

theorem sourceCount_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    sourceCount (reindexMultiplicityBase M e).base = sourceCount M.base := by
  change Nat.card (Source (reindexMultiplicityBase M e).base) = Nat.card (Source M.base)
  exact Nat.card_congr (sourceEquiv M e) |>.symm

theorem chosenDefect_reindex (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    chosenDefect (reindexMultiplicityBase M e).base = chosenDefect M.base := by
  simp [chosenDefect, sourceCount_reindex]

end NS25Lean.L5A1R
