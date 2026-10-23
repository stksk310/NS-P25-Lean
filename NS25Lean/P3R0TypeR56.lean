import NS25Lean.P3FirstPureReturnR56
import NS25Lean.MonomialEngineClosure

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
  obtain ⟨j, X, ell, hX, hXA, hmin, hell, he⟩ := r0_pure_minimal_zero_return M hp hR0 k
  have hr : Nat.ModEq M.base.q.val (weight M.base (Finsupp.single j X)) 0 := by
    rw [he]
    simp [Nat.ModEq]
  exact L5A2R49.pure_residue_zero_excludes_full_support k M.base
    (P3R54.r0_apery_fiber_unique M hR0) j X hX hmin hr g hg

theorem r0_q_fs_zero (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0)
    (k : Type*) [Field k] : L3A.q_fs (M.base.J k) = 0 := by
  change (L3A.fullSupportGenerators (M.base.J k)).ncard = 0
  rw [Set.ncard_eq_zero (hs := L3A.fullSupportGenerators_finite _)]
  ext g
  simp only [Set.mem_empty_iff_false, iff_false]
  exact r0_no_full_support M hp hR0 k g

/-- Original R0 type bound, proved independently of normalized principal rigidity. -/
theorem r0_type_bound (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  have hb := L3A.support_refined_monomial_type_bound
    (L3A.chosenArtinianMonomial M.base MonomialOrder.degLex (P3R54.r0_J_monomial M hR0 ℚ))
  change L3A.quotientType (M.base.J ℚ) ≤ L3A.mu (M.base.J ℚ) + L3A.q_fs (M.base.J ℚ) - 2 at hb
  rw [L3A.chosen_type_eq (k := ℚ), L3A.chosen_mu_eq (k := ℚ), r0_q_fs_zero M hp hR0 ℚ] at hb
  simpa only [Nat.add_zero] using hb

end NS25Lean.P3R56
