import NS25Lean.StaircaseCornerBound
import NS25Lean.MonomialEngineBridge

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3A
open ChosenBase
variable {k : Type*} [Field k]

def latticeArtinianMonomial (L : AddSubgroup (Fin 3 →₀ ℤ)) (m : MonomialOrder (Fin 3))
    [IsArtinianRing (Polynomial k ⧸ L2B.monomialInitialIdeal k m (latticeIdeal L))] :
    ArtinianMonomial k where
  ideal := L2B.monomialInitialIdeal k m (latticeIdeal L)
  monomial := initial_isMonomial m (latticeIdeal L)
  proper := lattice_initial_proper L m
  artinian := inferInstance

/-- CSCL for every Artinian lattice initial ideal, with no type-bound premise. -/
theorem cscl (L : AddSubgroup (Fin 3 →₀ ℤ)) (m : MonomialOrder (Fin 3))
    [IsArtinianRing (Polynomial k ⧸ L2B.monomialInitialIdeal k m (latticeIdeal L))] :
    quotientType (L2B.monomialInitialIdeal k m (latticeIdeal L)) ≤
      mu (L2B.monomialInitialIdeal k m (latticeIdeal L)) - 1 :=
  cscl_of_support_refined L m (support_refined_monomial_type_bound (latticeArtinianMonomial L m))

theorem cscl_add_one (L : AddSubgroup (Fin 3 →₀ ℤ)) (m : MonomialOrder (Fin 3))
    [IsArtinianRing (Polynomial k ⧸ L2B.monomialInitialIdeal k m (latticeIdeal L))] :
    quotientType (L2B.monomialInitialIdeal k m (latticeIdeal L)) + 1 ≤
      mu (L2B.monomialInitialIdeal k m (latticeIdeal L)) :=
  cscl_add_one_of_support_refined L m
    (support_refined_monomial_type_bound (latticeArtinianMonomial L m))

/-- Nonnegativity of the frozen integer-valued monomial slack. -/
theorem monomialSlack_nonneg (L : AddSubgroup (Fin 3 →₀ ℤ)) (m : MonomialOrder (Fin 3))
    [IsArtinianRing (Polynomial k ⧸ L2B.monomialInitialIdeal k m (latticeIdeal L))] :
    0 ≤ monomialSlack (k := k) L m :=
  (monomialSlack_nonneg_iff L m).mpr (cscl_add_one L m)

variable {Gamma : NumericalSemigroup}

/-- The actual chosen-base ideal inherits CSCL through the frozen weighted refinement. -/
theorem chosen_cscl (B : Data Gamma) (hJ : L2B.IsMonomialIdeal k (B.J k)) :
    quotientType (B.J k) ≤ mu (B.J k) - 1 := by
  have hb := support_refined_monomial_type_bound (chosenArtinianMonomial B MonomialOrder.degLex hJ)
  have hq := chosen_q_fs_le_one B MonomialOrder.degLex hJ
  change quotientType (B.J k) ≤ mu (B.J k) + q_fs (B.J k) - 2 at hb
  omega

/-- Paper-facing type bound from actual chosen-base monomiality, type, and MUJ. -/
theorem monomial_pivot_type_bound (B : Data Gamma) (hJ : L2B.IsMonomialIdeal k (B.J k)) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 1 := by
  rw [← chosen_type_eq (k := k) B, ← chosen_mu_eq (k := k) B]
  exact chosen_cscl B hJ

include k in
/-- Direct consequence of the frozen L2-C zero-internal-load monomial pivot. -/
theorem zero_internal_load_type_bound (B : Data Gamma)
    (hz : L2C.internalLoad B B.pivot = 0) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 1 :=
  monomial_pivot_type_bound B (L2C.monomial_pivot k B hz)

end NS25Lean.L3A
