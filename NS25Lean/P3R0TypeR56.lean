import NS25Lean.P3FirstPureReturnR56
import NS25Lean.MonomialEngineClosure
import NS25Lean.MonomialPivotStrictness

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R56
open ChosenBase L2B L5A1
variable {Gamma : NumericalSemigroup}

/-- R0 excludes every actual fully-supported minimal generator of J. -/
theorem r0_no_full_support (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0)
    (k : Type*) [Field k] (g : Fin 3 →₀ ℕ)
    (hg : g ∈ L3A.fullSupportGenerators (M.base.J k)) : False := by
  have hle := MonomialPivotStrictness.original_pivot_full_support_defect_le_one k
    M.base (P3R54.r0_J_monomial M hR0 k) g hg
  omega

theorem r0_q_fs_zero (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0)
    (k : Type*) [Field k] : L3A.q_fs (M.base.J k) = 0 := by
  exact MonomialPivotStrictness.original_pivot_monomial_q_fs_zero k M.base
    (P3R54.r0_J_monomial M hR0 k) (by omega)

/-- Original R0 type bound, proved independently of normalized principal rigidity. -/
theorem r0_type_bound (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  exact MonomialPivotStrictness.original_pivot_monomial_strict_type ℚ M.base
    (P3R54.r0_J_monomial M hR0 ℚ) (by omega)

end NS25Lean.P3R56
