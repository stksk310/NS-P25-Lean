import Mathlib.Data.Int.Basic

set_option autoImplicit false

namespace NS25Lean.EqualityLossAlgebra

/-- The support-refined monomial loss. All arguments and subtractions are integers. -/
def bpsLoss (muI typeI Q : ℤ) : ℤ := muI + Q - 2 - typeI

def generatorLoss (muI rho : ℤ) : ℤ := muI - rho

def typeLoss (typeI t : ℤ) : ℤ := typeI - t

/-- The second loss, common to the monomial and one-tie specializations. -/
def compensationLoss (rho t muI typeI Q : ℤ) : ℤ :=
  typeLoss typeI t - generatorLoss muI rho - Q + 1

theorem two_loss_identity (rho t muI typeI Q : ℤ) :
    rho - 1 - t = bpsLoss muI typeI Q + compensationLoss rho t muI typeI Q := by
  unfold bpsLoss compensationLoss typeLoss generatorLoss
  omega

/-- Equality is simultaneous saturation of both nonnegative integer losses. -/
theorem two_loss_saturation_iff (rho t muI typeI Q : ℤ)
    (hB : 0 ≤ bpsLoss muI typeI Q)
    (hC : 0 ≤ compensationLoss rho t muI typeI Q) :
    rho - 1 = t ↔ bpsLoss muI typeI Q = 0 ∧
      typeLoss typeI t = generatorLoss muI rho + Q - 1 := by
  have hi := two_loss_identity rho t muI typeI Q
  unfold compensationLoss at hC hi
  omega

theorem count_qfs_zero_iff (N W : ℕ) :
    (N : ℤ) = (W : ℤ) + 0 - 1 ↔ 0 < W ∧ N + 1 = W := by
  omega

theorem count_qfs_one_iff (N W : ℕ) :
    (N : ℤ) = (W : ℤ) + 1 - 1 ↔ N = W := by
  omega

/-- No nonnegative survivor count can satisfy PC when both Q and W vanish. -/
theorem count_qfs_zero_wrap_zero_impossible (N : ℕ) :
    ¬ ((N : ℤ) = (0 : ℤ) + 0 - 1) := by
  omega

end NS25Lean.EqualityLossAlgebra
