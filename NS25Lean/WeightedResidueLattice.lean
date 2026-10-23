import NS25Lean.MultiplicityBase
import Mathlib.Data.ZMod.Basic

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase MvPolynomial
variable {Gamma : NumericalSemigroup}

def weights (B : Data Gamma) : Fin 3 → ℕ := fun j => (B.tailDegrees j).val
def weight (B : Data Gamma) : (Fin 3 →₀ ℕ) →+ ℕ := Finsupp.weight (weights B)
def integerWeight (B : Data Gamma) : (Fin 3 →₀ ℤ) →+ ℤ :=
  Finsupp.weight (fun j => (weights B j : ℤ))

theorem weights_positive (B : Data Gamma) (j : Fin 3) : 0 < weights B j :=
  B.degrees_positive j.succ

theorem weight_eq_degree (B : Data Gamma) (u : Fin 3 →₀ ℕ) :
    weight B u = (Presentation.factorizationMap B.tailDegrees u).val :=
  Presentation.weight_factorization_val B.H B.tailDegrees u

theorem weight_eq_sum (B : Data Gamma) (u : Fin 3 →₀ ℕ) :
    weight B u = ∑ j, u j * weights B j := by
  simp only [weight, Finsupp.weight_eq_sum, smul_eq_mul]

def residueLattice (B : Data Gamma) : AddSubgroup (Fin 3 →₀ ℤ) where
  carrier := {z | (B.q.val : ℤ) ∣ integerWeight B z}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change _ ∣ integerWeight B (a + b)
    rw [map_add]
    exact dvd_add ha hb
  neg_mem' := by intro a ha; change _ ∣ integerWeight B (-a); rw [map_neg]; exact dvd_neg.mpr ha

def exponentDifference (u v : Fin 3 →₀ ℕ) : Fin 3 →₀ ℤ :=
  u.mapRange (Nat.castAddMonoidHom ℤ) (by simp) - v.mapRange (Nat.castAddMonoidHom ℤ) (by simp)

theorem integerWeight_difference (B : Data Gamma) (u v : Fin 3 →₀ ℕ) :
    integerWeight B (exponentDifference u v) = (weight B u : ℤ) - weight B v := by
  simp only [integerWeight, exponentDifference, map_sub, Finsupp.weight_eq_sum,
    Finsupp.mapRange_apply, smul_eq_mul, weight_eq_sum, Nat.cast_sum, Nat.cast_mul]
  rfl

theorem difference_mem_lattice_iff (B : Data Gamma) (u v : Fin 3 →₀ ℕ) :
    exponentDifference u v ∈ residueLattice B ↔
      Int.ModEq B.q.val (weight B u) (weight B v) := by
  change ((B.q.val : ℤ) ∣ integerWeight B (exponentDifference u v)) ↔ _
  rw [integerWeight_difference, Int.modEq_iff_dvd]
  exact dvd_sub_comm

def latticeIdeal (k : Type*) [Field k] (B : Data Gamma) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ((fun p : (Fin 3 →₀ ℕ) × (Fin 3 →₀ ℕ) => monomial p.1 (1 : k) - monomial p.2 1) ''
    {p | exponentDifference p.1 p.2 ∈ residueLattice B})

/-- All maximal-weight terms, including every term of an equal-weight binomial. -/
def weightInitial (k : Type*) [Field k] (B : Data Gamma) (f : MvPolynomial (Fin 3) k) :
    MvPolynomial (Fin 3) k :=
  weightedHomogeneousComponent (weights B) (weightedTotalDegree (weights B) f) f

def weightInitialIdeal (k : Type*) [Field k] (B : Data Gamma)
    (I : Ideal (MvPolynomial (Fin 3) k)) : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span (weightInitial k B '' (I : Set _))

theorem coeff_weightInitial (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (u : Fin 3 →₀ ℕ) :
    coeff u (weightInitial k B f) =
      if weight B u = weightedTotalDegree (weights B) f then coeff u f else 0 := by
  exact coeff_weightedHomogeneousComponent _ _ _

theorem weightInitial_of_homogeneous (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (d : ℕ) (hf : f.IsWeightedHomogeneous (weights B) d) :
    weightInitial k B f = f := by
  by_cases hz : f = 0
  · subst f; simp [weightInitial]
  · have he := hf.weighted_total_degree hz
    rw [weightedTotalDegree_coe _ _ hz] at he
    have hd : weightedTotalDegree (weights B) f = d := WithBot.coe_injective he
    unfold weightInitial
    rw [hd]
    exact hf.weightedHomogeneousComponent_same

end NS25Lean.L2B
