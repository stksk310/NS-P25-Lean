import NS25Lean.P3HerzogLatticeR59
import NS25Lean.P3ShadowArithmeticR59

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R59
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4A L5A2C4D L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4OR5
variable {Gamma : NumericalSemigroup}

/-- The mixed factorization of the actual normalized third critical degree. -/
theorem h3_normalized_relation (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) :
    criticalExponent M.base (e 2) * routingC M.base e =
      P3R57.roleCoefficient M hp e 2 0 * routingA M.base e +
      P3R57.roleCoefficient M hp e 2 1 * routingB M.base e :=
  (coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)).2.2

/-- The full third critical fiber consists of exactly its pure and mixed vertices. -/
theorem h3_critical_two_factorizations (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (A B C : ℕ)
    (hf : A * routingA M.base e + B * routingB M.base e + C * routingC M.base e =
      criticalExponent M.base (e 2) * routingC M.base e) :
    (A = P3R57.roleCoefficient M hp e 2 0 ∧
      B = P3R57.roleCoefficient M hp e 2 1 ∧ C = 0) ∨
      (A = 0 ∧ B = 0 ∧ C = criticalExponent M.base (e 2)) := by
  have hr : (criticalExponent M.base (e 2) : ℤ) * routingC M.base e =
      (P3R57.roleCoefficient M hp e 2 0 : ℤ) * routingA M.base e +
      (P3R57.roleCoefficient M hp e 2 1 : ℤ) * routingB M.base e := by
    exact_mod_cast h3_normalized_relation M hp e
  have hf' : (A : ℤ) * routingA M.base e + (B : ℤ) * routingB M.base e +
      (C : ℤ) * routingC M.base e =
      (criticalExponent M.base (e 2) : ℤ) * routingC M.base e := by
    exact_mod_cast hf
  have hk : ((A : ℤ) - P3R57.roleCoefficient M hp e 2 0) * routingA M.base e +
      ((B : ℤ) - P3R57.roleCoefficient M hp e 2 1) * routingB M.base e +
      (C : ℤ) * routingC M.base e = 0 := by
    linear_combination hf' + hr
  obtain ⟨l,k,hA,hB,hC⟩ := p3_integer_kernel_basis M hp e
    ((A : ℤ) - P3R57.roleCoefficient M hp e 2 0)
    ((B : ℤ) - P3R57.roleCoefficient M hp e 2 1) C hk
  have hs := P3R58.p3_coefficient_sums M hp e
  rw [hs.1] at hA
  rw [hs.2.2] at hC
  push_cast at hA hC
  have hP : (0 : ℤ) < P3R57.roleCoefficient M hp e 0 1 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hQ : (0 : ℤ) < P3R57.roleCoefficient M hp e 0 2 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hU : (0 : ℤ) < P3R57.roleCoefficient M hp e 1 0 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 0 (by decide)
  have hV : (0 : ℤ) < P3R57.roleCoefficient M hp e 1 2 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 2 (by decide)
  have hW : (0 : ℤ) < P3R57.roleCoefficient M hp e 2 0 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  have hZ : (0 : ℤ) < P3R57.roleCoefficient M hp e 2 1 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  have hout := h3_fiber_arithmetic
    (P3R57.roleCoefficient M hp e 0 1) (P3R57.roleCoefficient M hp e 0 2)
    (P3R57.roleCoefficient M hp e 1 0) (P3R57.roleCoefficient M hp e 1 2)
    (P3R57.roleCoefficient M hp e 2 0) (P3R57.roleCoefficient M hp e 2 1)
    A B C l k hP hQ hU hV hW hZ
    (by positivity) (by positivity) (by positivity)
    (by linarith only [hA]) (by linarith only [hB]) hC
  rcases hout with hout | hout
  · left
    exact_mod_cast hout
  · right
    rw [hs.2.2]
    exact_mod_cast hout

end NS25Lean.P3R59
