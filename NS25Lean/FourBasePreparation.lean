import NS25Lean.FourSourceBridge

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase
variable {Gamma : NumericalSemigroup}

def atPivot (B : Data Gamma) (i : Fin 4) : Data Gamma := { B with pivot := i }

@[simp] theorem atPivot_pivot (B : Data Gamma) (i : Fin 4) : (atPivot B i).pivot = i := rfl
@[simp] theorem atPivot_family (B : Data Gamma) (i : Fin 4) : (atPivot B i).family = B.family := rfl
@[simp] theorem atPivot_componentCount (B : Data Gamma) (i : Fin 4) (d : ℕ) :
    componentCount (atPivot B i) d = componentCount B d := rfl
@[simp] theorem atPivot_bettiDegrees (B : Data Gamma) (i : Fin 4) :
    bettiDegrees (atPivot B i) = bettiDegrees B := rfl
@[simp] theorem atPivot_essentialVariables (B : Data Gamma) (i : Fin 4) (d : ℕ) :
    essentialVariables (atPivot B i) d = essentialVariables B d := rfl
@[simp] theorem atPivot_internalLoad (B : Data Gamma) (i j : Fin 4) :
    internalLoad (atPivot B i) j = internalLoad B j := rfl

theorem every_pivot_source_formula (B : Data Gamma) (i : Fin 4) :
    L2B.sourceCount (atPivot B i) =
      ((bettiDegrees B).filter (fun d => i ∈ essentialVariables B d)).card :=
  sourceCount_eq_essential_card (atPivot B i)

theorem every_pivot_defect_formula (B : Data Gamma) (i : Fin 4) :
    L2B.chosenDefect (atPivot B i) = ∑ d ∈ bettiDegrees B,
      (componentCount B d - 1 - if i ∈ essentialVariables B d then 1 else 0) :=
  chosenDefect_eq_essential_sum (atPivot B i)

theorem every_pivot_monomial (k : Type*) [Field k] (B : Data Gamma) (i : Fin 4)
    (hz : internalLoad B i = 0) : L2B.IsMonomialIdeal k ((atPivot B i).J k) :=
  monomial_pivot k (atPivot B i) hz

theorem every_pivot_W6 (k : Type*) [Field k] (B : Data Gamma) (i : Fin 4)
    (hz : internalLoad B i = 0) (m : MonomialOrder (Fin 3)) :
    (atPivot B i).J k = L2B.monomialInitialIdeal k (L2B.weightRefinement (atPivot B i) m)
      (L2B.latticeIdeal k (atPivot B i)) :=
  monomial_pivot_W6 k (atPivot B i) hz m

theorem weight_reindex (B D : Data Gamma) (e : Fin 4 ≃ Fin 4)
    (hw : ∀ i, D.family (e i) = B.family i) (u : Fin 4 →₀ ℕ) :
    weight D (Finsupp.domCongr e u) = weight B u := by
  rw [weight_eq_degree, weight_eq_degree]
  exact congrArg Subtype.val (Presentation.factorizationMap_reindex e B.family D.family hw u)

def fiberReindex (B D : Data Gamma) (e : Fin 4 ≃ Fin 4)
    (hw : ∀ i, D.family (e i) = B.family i) (d : ℕ) :
    FactorizationFiber B d ≃ FactorizationFiber D d where
  toFun u := ⟨Finsupp.domCongr e u.val, (weight_reindex B D e hw u.val).trans u.property⟩
  invFun v := ⟨(Finsupp.domCongr e).symm v.val, by
    have h := weight_reindex B D e hw ((Finsupp.domCongr e).symm v.val)
    rw [AddEquiv.apply_symm_apply] at h
    exact h.symm.trans v.property⟩
  left_inv u := Subtype.ext ((Finsupp.domCongr e).symm_apply_apply u.val)
  right_inv v := Subtype.ext ((Finsupp.domCongr e).apply_symm_apply v.val)

theorem fiberReindex_apply (B D : Data Gamma) (e : Fin 4 ≃ Fin 4)
    (hw : ∀ i, D.family (e i) = B.family i) (d : ℕ) (u : FactorizationFiber B d) (j : Fin 4) :
    (fiberReindex B D e hw d u).val j = u.val (e.symm j) :=
  Finsupp.equivMapDomain_apply e u.val j

/-- Equivariance under an arbitrary permutation of the displayed generators. -/
def graphReindex (B D : Data Gamma) (e : Fin 4 ≃ Fin 4)
    (hw : ∀ i, D.family (e i) = B.family i) (d : ℕ) : fiberGraph B d ≃g fiberGraph D d where
  toEquiv := fiberReindex B D e hw d
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨hne, j, hu, hv⟩
      refine ⟨fun he => hne (congrArg _ he), e.symm j, ?_, ?_⟩
      · simpa only [fiberReindex_apply] using hu
      · simpa only [fiberReindex_apply] using hv
    · rintro ⟨hne, j, hu, hv⟩
      refine ⟨fun he => hne ((fiberReindex B D e hw d).injective he), e j, ?_, ?_⟩
      · simpa only [fiberReindex_apply, Equiv.symm_apply_apply] using hu
      · simpa only [fiberReindex_apply, Equiv.symm_apply_apply] using hv

theorem componentCount_reindex (B D : Data Gamma) (e : Fin 4 ≃ Fin 4)
    (hw : ∀ i, D.family (e i) = B.family i) (d : ℕ) :
    componentCount B d = componentCount D d :=
  Nat.card_congr (graphReindex B D e hw d).connectedComponentEquiv

theorem betti_reindex (B D : Data Gamma) (e : Fin 4 ≃ Fin 4)
    (hw : ∀ i, D.family (e i) = B.family i) (d : ℕ) : Betti B d ↔ Betti D d := by
  unfold Betti
  rw [componentCount_reindex B D e hw d]

/-- All six L2-C branches, uniformly over every displayed pivot and coefficient field. -/
theorem four_base_preparation (k : Type*) [Field k] (B : Data Gamma) :
    (∀ d, d ∈ bettiDegrees B ↔ Betti B d) ∧
    Presentation.rho Gamma = ∑ d ∈ bettiDegrees B, (componentCount B d - 1) ∧
    (∀ i, L2B.sourceCount (atPivot B i) =
      ((bettiDegrees B).filter (fun d => i ∈ essentialVariables B d)).card) ∧
    (∀ i, L2B.chosenDefect (atPivot B i) = ∑ d ∈ bettiDegrees B,
      (componentCount B d - 1 - if i ∈ essentialVariables B d then 1 else 0)) ∧
    (∀ i, internalLoad B i = 0 → L2B.IsMonomialIdeal k ((atPivot B i).J k)) ∧
    ∑ i : Fin 4, internalLoad B i ≤ 4 :=
  ⟨mem_bettiDegrees B, rho_eq_betti_sum B, every_pivot_source_formula B,
    every_pivot_defect_formula B, every_pivot_monomial k B, four_base_budget B⟩

end NS25Lean.L2C
