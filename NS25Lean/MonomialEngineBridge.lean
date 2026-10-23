import NS25Lean.LatticeFullSupport
import NS25Lean.MonomialStaircase

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3A
open MvPolynomial ChosenBase
variable {k : Type*} [Field k]

/-- Conditional assembly only: the displayed support-refined hypothesis is still required. -/
theorem cscl_of_support_refined (L : AddSubgroup (Fin 3 →₀ ℤ))
    (m : MonomialOrder (Fin 3))
    (hbound : quotientType (L2B.monomialInitialIdeal k m (latticeIdeal L)) ≤
      mu (L2B.monomialInitialIdeal k m (latticeIdeal L)) +
        q_fs (L2B.monomialInitialIdeal k m (latticeIdeal L)) - 2) :
    quotientType (L2B.monomialInitialIdeal k m (latticeIdeal L)) ≤
      mu (L2B.monomialInitialIdeal k m (latticeIdeal L)) - 1 := by
  have hq := q_fs_lattice_initial_le_one (k := k) L m
  omega

theorem cscl_add_one_of_support_refined (L : AddSubgroup (Fin 3 →₀ ℤ))
    (m : MonomialOrder (Fin 3))
    [IsArtinianRing (Polynomial k ⧸ L2B.monomialInitialIdeal k m (latticeIdeal L))]
    (hbound : quotientType (L2B.monomialInitialIdeal k m (latticeIdeal L)) ≤
      mu (L2B.monomialInitialIdeal k m (latticeIdeal L)) +
        q_fs (L2B.monomialInitialIdeal k m (latticeIdeal L)) - 2) :
    quotientType (L2B.monomialInitialIdeal k m (latticeIdeal L)) + 1 ≤
      mu (L2B.monomialInitialIdeal k m (latticeIdeal L)) := by
  have hp := mu_positive_of_artinian _ (initial_isMonomial m (latticeIdeal (k := k) L))
  have hb := cscl_of_support_refined L m hbound
  omega

/-- Integer-valued slack, indexed by a lattice and an order; no truncated nonnegativity trick. -/
def monomialSlack (L : AddSubgroup (Fin 3 →₀ ℤ)) (m : MonomialOrder (Fin 3)) : ℤ :=
  (mu (L2B.monomialInitialIdeal k m (latticeIdeal L)) : ℤ) - 1 -
    quotientType (L2B.monomialInitialIdeal k m (latticeIdeal L))

theorem monomialSlack_nonneg_iff (L : AddSubgroup (Fin 3 →₀ ℤ)) (m : MonomialOrder (Fin 3)) :
    0 ≤ monomialSlack (k := k) L m ↔
      quotientType (L2B.monomialInitialIdeal k m (latticeIdeal L)) + 1 ≤
        mu (L2B.monomialInitialIdeal k m (latticeIdeal L)) := by
  unfold monomialSlack
  omega

theorem monomialSlack_nonneg_of_support_refined (L : AddSubgroup (Fin 3 →₀ ℤ))
    (m : MonomialOrder (Fin 3))
    [IsArtinianRing (Polynomial k ⧸ L2B.monomialInitialIdeal k m (latticeIdeal L))]
    (hbound : quotientType (L2B.monomialInitialIdeal k m (latticeIdeal L)) ≤
      mu (L2B.monomialInitialIdeal k m (latticeIdeal L)) +
        q_fs (L2B.monomialInitialIdeal k m (latticeIdeal L)) - 2) :
    0 ≤ monomialSlack (k := k) L m :=
  (monomialSlack_nonneg_iff L m).mpr (cscl_add_one_of_support_refined L m hbound)

variable {Gamma : NumericalSemigroup}

theorem chosen_latticeIdeal_eq (B : Data Gamma) :
    latticeIdeal (k := k) (L2B.residueLattice B) = L2B.latticeIdeal k B := rfl

/-- Unconditional eligibility of an actual monomial chosen-base pivot. -/
theorem chosen_monomial_initial (B : Data Gamma) (m : MonomialOrder (Fin 3))
    (hJ : L2B.IsMonomialIdeal k (B.J k)) :
    B.J k = L2B.monomialInitialIdeal k (L2B.weightRefinement B m)
      (latticeIdeal (L2B.residueLattice B)) :=
  L2B.monomial_J_eq_refinement k B m hJ

theorem chosen_q_fs_le_one (B : Data Gamma) (m : MonomialOrder (Fin 3))
    (hJ : L2B.IsMonomialIdeal k (B.J k)) : q_fs (B.J k) ≤ 1 := by
  rw [chosen_monomial_initial B m hJ]
  exact q_fs_lattice_initial_le_one _ _

theorem chosen_socle_eq (B : Data Gamma) : socle (B.J k) = B.soclePolynomialQuotient k := by
  ext x
  exact (B.soclePolynomialQuotient_iff_variables k x).symm

theorem chosen_type_eq (B : Data Gamma) : quotientType (B.J k) = Gamma.asRelativeIdeal.idealType := by
  unfold quotientType
  rw [chosen_socle_eq]
  exact B.quotient_type_eq k

theorem chosen_mu_eq (B : Data Gamma) : mu (B.J k) = Presentation.rho Gamma := B.muj k

def chosenArtinianMonomial (B : Data Gamma) (m : MonomialOrder (Fin 3))
    (hJ : L2B.IsMonomialIdeal k (B.J k)) : ArtinianMonomial k where
  ideal := B.J k
  monomial := hJ
  proper := by rw [chosen_monomial_initial B m hJ]; exact lattice_initial_proper _ _
  artinian := inferInstance

/-- Actual frozen type/MUJ consequence, with the remaining M2 premise explicit. -/
theorem chosen_type_le_rho_sub_one_of_support_refined (B : Data Gamma)
    (m : MonomialOrder (Fin 3)) (hJ : L2B.IsMonomialIdeal k (B.J k))
    (hbound : quotientType (B.J k) ≤ mu (B.J k) + q_fs (B.J k) - 2) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 1 := by
  have hq := chosen_q_fs_le_one B m hJ
  rw [← chosen_type_eq (k := k) B, ← chosen_mu_eq (k := k) B]
  omega

/-- The frozen L2-C zero-load pivot supplies the real monomiality premise. -/
theorem zero_load_type_le_rho_sub_one_of_support_refined (B : Data Gamma)
    (m : MonomialOrder (Fin 3)) (hz : L2C.internalLoad B B.pivot = 0)
    (hbound : quotientType (B.J k) ≤ mu (B.J k) + q_fs (B.J k) - 2) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 1 :=
  chosen_type_le_rho_sub_one_of_support_refined B m (L2C.monomial_pivot k B hz) hbound

end NS25Lean.L3A
