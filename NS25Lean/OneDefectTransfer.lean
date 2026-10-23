import NS25Lean.DilationTransfer
import NS25Lean.MultiplicityDefectClosure
import NS25Lean.MonomialEngineClosure

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3B
open ChosenBase L2B
variable {Gamma : NumericalSemigroup}

def transferScale (B : Data Gamma) : ℕ := 1 + B.q.val

theorem transferScale_gt (B : Data Gamma) : B.q.val < transferScale B := by
  unfold transferScale; omega

theorem transferScale_coprime (B : Data Gamma) : Nat.Coprime (transferScale B) B.q.val := by
  exact Nat.coprime_add_self_left.mpr (Nat.coprime_one_left _)

def transferSemigroup (B : Data Gamma) : NumericalSemigroup :=
  dilatedSemigroup B (transferScale B) (transferScale_coprime B)

def transferBase (B : Data Gamma) : MultiplicityBase (transferSemigroup B) :=
  ⟨dilatedData B (transferScale B) (transferScale_gt B) (transferScale_coprime B),
    dilatedData_isMultiplicity B _ _ _⟩

/-- The canonical identity on polynomial representatives of the actual quotients. -/
def transferQuotientEquiv (k : Type*) [Field k] (B : Data Gamma) :
    (ToricPresentation.Poly k 3 ⧸ (transferBase B).base.J k) ≃ₐ[k]
      (ToricPresentation.Poly k 3 ⧸ B.J k) :=
  dilationQuotientEquiv k B (transferScale B) (transferScale_gt B) (transferScale_coprime B)

theorem transferQuotientEquiv_mk (k : Type*) [Field k] (B : Data Gamma)
    (f : ToricPresentation.Poly k 3) :
    transferQuotientEquiv k B (Ideal.Quotient.mk ((transferBase B).base.J k) f) =
      Ideal.Quotient.mk (B.J k) f := dilationQuotientEquiv_mk k B (transferScale B) (transferScale_gt B) (transferScale_coprime B) f

/-- Actual frozen dilation transfer, starting at an arbitrary chosen pivot. -/
theorem one_defect_transfer (k : Type*) [Field k] (B : Data Gamma)
    (hp : chosenDefect B = 1) :
    (transferBase B).base.q.val = B.q.val ∧
    IsMultiplicity (transferBase B).base ∧
    (transferBase B).base.J k = B.J k ∧
    Presentation.rho (transferSemigroup B) = Presentation.rho Gamma ∧
    (transferSemigroup B).asRelativeIdeal.idealType = Gamma.asRelativeIdeal.idealType ∧
    sourceCount (transferBase B).base = sourceCount B ∧
    chosenDefect (transferBase B).base = 1 := by
  have ht := dilation_transfer B (transferScale B) (transferScale_gt B) (transferScale_coprime B)
  exact ⟨rfl, ht.1, dilatedData_J k B (transferScale B) (transferScale_gt B) (transferScale_coprime B), ht.2.1, ht.2.2.1,
    ht.2.2.2.1, ht.2.2.2.2.trans hp⟩

theorem one_defect_sourceCount (B : Data Gamma) (hp : chosenDefect B = 1) :
    sourceCount B = Presentation.rho Gamma - 1 := by
  have := sourceCount_add_defect B
  omega

end NS25Lean.L3B

