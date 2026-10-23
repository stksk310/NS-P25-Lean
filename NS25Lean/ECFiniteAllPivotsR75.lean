import NS25Lean.ECFiniteIntrinsicR75

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.EC.R75
open ChosenBase L2B L2C L3A
variable {Gamma : NumericalSemigroup}

def PivotFiniteCertificate (B : ChosenBase.Data Gamma) : Prop :=
  (L2B.chosenDefect B = 0 ∧ MonomialFiniteCertificate B) ∨
  (L2B.chosenDefect B = 1 ∧
    (MonomialFiniteCertificate B ∨ OneTieFiniteCertificate B))

/-- Every invariant is tied to the originally chosen B, with no defect premise. -/
theorem arbitrary_pivot_transfer_invariants (B : ChosenBase.Data Gamma) :
    (L3B.transferBase B).base.q.val = B.q.val ∧
    IsMultiplicity (L3B.transferBase B).base ∧
    (L3B.transferBase B).base.J ℚ = B.J ℚ ∧
    Presentation.rho (L3B.transferSemigroup B) = Presentation.rho Gamma ∧
    (L3B.transferSemigroup B).asRelativeIdeal.idealType = Gamma.asRelativeIdeal.idealType ∧
    sourceCount (L3B.transferBase B).base = sourceCount B ∧
    L2B.chosenDefect (L3B.transferBase B).base = L2B.chosenDefect B := by
  have ht := dilation_transfer B (L3B.transferScale B) (L3B.transferScale_gt B)
    (L3B.transferScale_coprime B)
  exact ⟨rfl,ht.1,dilatedData_J ℚ B (L3B.transferScale B) (L3B.transferScale_gt B)
    (L3B.transferScale_coprime B),ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2⟩

theorem pivot_finite_equality_iff (B : ChosenBase.Data Gamma) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      PivotFiniteCertificate B :=
  chosen_pivot_finite_equality_iff B

/-- Transport only invariants to apply the original-M theorem on the derived witness. -/
theorem equality_iff_transferred_multiplicity_certificate (B : ChosenBase.Data Gamma) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      FiniteEqualityCertificate (L3B.transferBase B) := by
  have ht := arbitrary_pivot_transfer_invariants B
  have he := finite_intrinsic_equality_iff (L3B.transferSemigroup B) (L3B.transferBase B)
  rw [ht.2.2.2.1,ht.2.2.2.2.1] at he
  exact he

theorem pivot_certificate_iff_transferred_certificate (B : ChosenBase.Data Gamma) :
    PivotFiniteCertificate B ↔ FiniteEqualityCertificate (L3B.transferBase B) :=
  (pivot_finite_equality_iff B).symm.trans (equality_iff_transferred_multiplicity_certificate B)

theorem equality_all_original_pivots (B : ChosenBase.Data Gamma)
    (he : Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1) :
    ∀ i : Fin 4, PivotFiniteCertificate (atPivot B i) :=
  fun i => (pivot_finite_equality_iff (atPivot B i)).mp he

theorem equality_iff_all_original_pivots (B : ChosenBase.Data Gamma) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      ∀ i : Fin 4, PivotFiniteCertificate (atPivot B i) := by
  exact ⟨equality_all_original_pivots B,fun h =>
    (pivot_finite_equality_iff (atPivot B 0)).mpr (h 0)⟩

theorem equality_iff_some_original_pivot (B : ChosenBase.Data Gamma) :
    Gamma.asRelativeIdeal.idealType = Presentation.rho Gamma - 1 ↔
      ∃ i : Fin 4, PivotFiniteCertificate (atPivot B i) := by
  constructor
  · intro he
    exact ⟨0,equality_all_original_pivots B he 0⟩
  · rintro ⟨i,h⟩
    exact (pivot_finite_equality_iff (atPivot B i)).mpr h

end NS25Lean.EC.R75
