import NS25Lean.ECPivotRestrictionR70

set_option autoImplicit false
set_option linter.style.header false
namespace NS25Lean.OriginalPivotStrictBounds
open ChosenBase L2B
variable {Gamma : NumericalSemigroup}

/-- The literal original source-count version of F2. The underlying strict
bound retains its proved dilation implementation; the endpoint is on B. -/
theorem p2_original_source_bound (B : Data Gamma) (hp : chosenDefect B=2) :
    Gamma.asRelativeIdeal.idealType≤sourceCount B := by
  have hb := EC.R70.arbitrary_pivot_p2_strong B hp
  have hs := sourceCount_add_defect B
  omega

/-- The literal original source-count version of F3, with this same B's
source count and no canonical/multiplicity pivot hypothesis. -/
theorem p3_original_source_bound (B : Data Gamma) (hp : chosenDefect B=3) :
    Gamma.asRelativeIdeal.idealType≤sourceCount B+1 := by
  have hb := EC.R70.arbitrary_pivot_p3_strong B hp
  have hs := sourceCount_add_defect B
  omega

/-- Both source-count conclusions hold at every supplied original index. -/
theorem all_original_pivot_source_bounds (B : Data Gamma) (i : Fin 4) :
    (chosenDefect (L2C.atPivot B i)=2 →
      Gamma.asRelativeIdeal.idealType≤sourceCount (L2C.atPivot B i)) ∧
    (chosenDefect (L2C.atPivot B i)=3 →
      Gamma.asRelativeIdeal.idealType≤sourceCount (L2C.atPivot B i)+1) :=
  ⟨p2_original_source_bound (L2C.atPivot B i),p3_original_source_bound (L2C.atPivot B i)⟩
end NS25Lean.OriginalPivotStrictBounds

#print axioms NS25Lean.OriginalPivotStrictBounds.p2_original_source_bound
#print axioms NS25Lean.OriginalPivotStrictBounds.p3_original_source_bound
