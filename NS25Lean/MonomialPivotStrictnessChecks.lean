import NS25Lean.MonomialPivotStrictness

set_option linter.style.header false
noncomputable section
namespace NS25Lean.MonomialPivotStrictnessChecks
open ChosenBase L2B L3A MonomialPivotStrictness
variable {Gamma : NumericalSemigroup} (k : Type*) [Field k]

/-- Public original-pivot API with an existential full-support input. -/
example (B : Data Gamma) (hJ : IsMonomialIdeal k (B.J k))
    (hfull : Nonempty (fullSupportGenerators (B.J k))) : chosenDefect B≤1 := by
  obtain ⟨g⟩ := hfull
  exact original_pivot_full_support_defect_le_one k B hJ g.val g.property

/-- One original datum supplies both manuscript consequences, with unchanged
actual J, original defect, semigroup type, and rho. -/
example (B : Data Gamma) (hJ : IsMonomialIdeal k (B.J k)) (hp : 2≤chosenDefect B) :
    q_fs (B.J k)=0 ∧ Gamma.asRelativeIdeal.idealType≤Presentation.rho Gamma-2 :=
  ⟨original_pivot_monomial_q_fs_zero k B hJ hp,
    original_pivot_monomial_strict_type k B hJ hp⟩

end NS25Lean.MonomialPivotStrictnessChecks

#print axioms NS25Lean.MonomialPivotStrictness.monomial_apery_unique
#print axioms NS25Lean.MonomialPivotStrictness.two_axis_distinct_degree_impossible
#print axioms NS25Lean.MonomialPivotStrictness.positive_has_nonunique_pure
#print axioms NS25Lean.MonomialPivotStrictness.monomial_positive_degree_unique
#print axioms NS25Lean.MonomialPivotStrictness.monomial_contribution_le_one
#print axioms NS25Lean.MonomialPivotStrictness.original_pivot_full_support_defect_le_one
#print axioms NS25Lean.MonomialPivotStrictness.original_pivot_monomial_q_fs_zero
#print axioms NS25Lean.MonomialPivotStrictness.original_pivot_monomial_strict_type
