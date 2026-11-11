import NS25Lean.SharedTailKernel
import NS25Lean.SharedTailPrimitiveLattice
import NS25Lean.SharedTailPurePairApery
import NS25Lean.SharedTailPermutation

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse CriticalCapGeometry CriticalPresentationModes L3C

theorem Positive.no_side_unique {H : NumericalSemigroup} (D : Positive H) (e : Exponent)
    (hshort : ∀ lr∈(D.toMode 1 (by decide)).relations, ¬lr.1≤e ∧ ¬lr.2≤e) :
    ∀ f, D.triple.weight f=D.triple.weight e → f=e :=
  CriticalShortFibers.unique_of_no_toric_side D.triple (D.toMode 1 (by decide)).relations
    (D.exact_ideal ℚ) e hshort

theorem Positive.relation_critical_degree {H : NumericalSemigroup} (D : Positive H)
    (lr : Exponent×Exponent) (hlr : lr∈(D.toMode 1 (by decide)).relations) :
    ∃ i : Fin 3, D.triple.weight lr.1=D.critical.exponent i*D.triple.g i ∧
      D.triple.weight lr.2=D.critical.exponent i*D.triple.g i := by
  change lr∈{(vector D.A 0 0,vector 0 D.p D.q),
    (vector 0 D.B 0,vector D.u 0 D.v),(vector 0 0 D.C,vector D.w D.z 0)} at hlr
  rcases hlr with rfl | rfl | rfl
  · exact ⟨0,by simp [vector_weight,Triple.grid],by simpa [Positive.witness] using D.witness_weight 0⟩
  · exact ⟨1,by simp [vector_weight,Triple.grid],by simpa [Positive.witness] using D.witness_weight 1⟩
  · exact ⟨2,by simp [vector_weight,Triple.grid],by simpa [Positive.witness] using D.witness_weight 2⟩

/-- Every genuinely nonunique degree has a critical degree as an actual
H-divisor. The divisor is extracted from the first contextual move. -/
theorem Positive.nonunique_critical_divisor {H : NumericalSemigroup} (D : Positive H)
    (e f : Exponent) (hne : e≠f) (he : D.triple.weight e=D.triple.weight f) :
    ∃ (i : Fin 3) (d : ℕ), d∈H ∧
      D.triple.weight e=D.critical.exponent i*D.triple.g i+d := by
  classical
  have hp := D.connected e f he
  obtain ⟨v,hstep⟩ : ∃ v : Exponent, ContextStep (D.toMode 1 (by decide)).relations e v := by
    by_contra hn
    push Not at hn
    exact hne (ReturnSourceRigidity.path_eq_of_no_move hp hn)
  obtain ⟨lr,hlr,t,h⟩ := hstep
  obtain ⟨i,hleft,hright⟩ := D.relation_critical_degree lr hlr
  refine ⟨i,D.triple.weight t,D.triple.member t,?_⟩
  rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩
  · rw [map_add,hleft,add_comm]
  · rw [map_add,hright,add_comm]

end NS25Lean.SharedTail
