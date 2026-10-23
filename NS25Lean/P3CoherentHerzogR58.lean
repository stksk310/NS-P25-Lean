import NS25Lean.P3StrictArmConesR57
import NS25Lean.P2SectorCHerzogCanonicalityOwnerReentryR6

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R58
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4A L5A2C4D L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

def roleWitness (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    FactorizationFiber M.base (criticalExponent M.base (e i) * weights M.base (e i)) :=
  ⟨(P3R55.axisRole M hp (e i)).witness.val,
    (P3R55.axisRole M hp (e i)).witness.property.trans (P3R55.axisIndex_degree M hp (e i))⟩

theorem roleWitness_self_zero (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    (roleWitness M hp e i).val (e i) = 0 := by
  simpa only [roleWitness, P3R55.axisRole_pureRole] using
    (P3R55.axisRole M hp (e i)).witness_pure_zero

theorem roleWitness_other_pos (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (i j : Fin 3) (hij : j ≠ i) : 0 < (roleWitness M hp e i).val (e j) := by
  apply P3R55.role_witness_positive (P3R55.axisRole M hp (e i)) (e j)
  simpa only [P3R55.axisRole_pureRole] using (fun h => hij (e.injective h))

/-- The frozen generic structure is populated entirely by actual P3 critical-fiber proofs. -/
def p3_coherentHerzogData (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) : CoherentHerzogData M.base e where
  witness1 := roleWitness M hp e 0
  witness2 := roleWitness M hp e 1
  witness3 := roleWitness M hp e 2
  witness1_self_zero := roleWitness_self_zero M hp e 0
  witness2_self_zero := roleWitness_self_zero M hp e 1
  witness3_self_zero := roleWitness_self_zero M hp e 2
  witness1_left_pos := roleWitness_other_pos M hp e 0 1 (by decide)
  witness1_right_pos := roleWitness_other_pos M hp e 0 2 (by decide)
  witness2_left_pos := roleWitness_other_pos M hp e 1 0 (by decide)
  witness2_right_pos := roleWitness_other_pos M hp e 1 2 (by decide)
  witness3_left_pos := roleWitness_other_pos M hp e 2 0 (by decide)
  witness3_right_pos := roleWitness_other_pos M hp e 2 1 (by decide)

theorem p3_coefficient_sums (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) :
    criticalExponent M.base (e 0) =
        P3R57.roleCoefficient M hp e 1 0 + P3R57.roleCoefficient M hp e 2 0 ∧
      criticalExponent M.base (e 1) =
        P3R57.roleCoefficient M hp e 0 1 + P3R57.roleCoefficient M hp e 2 1 ∧
      criticalExponent M.base (e 2) =
        P3R57.roleCoefficient M hp e 0 2 + P3R57.roleCoefficient M hp e 1 2 :=
  coherent_coefficients M.base e (p3_coherentHerzogData M hp e)

theorem p3_coefficients_positive (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i j : Fin 3) (hij : j ≠ i) :
    0 < P3R57.roleCoefficient M hp e i j := roleWitness_other_pos M hp e i j hij

theorem p3_lshape_canonical (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (i j : ℕ) (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hcorner : i < P3R57.roleCoefficient M hp e 0 1 ∨
      j < P3R57.roleCoefficient M hp e 0 2) :
    IsCanonicalTailGridPoint M.base e i j :=
  herzogLShapeCanonicality M.base e (p3_coherentHerzogData M hp e) i j ⟨hi, hj, hcorner⟩

/-- Every actual tail Apéry representative has a genuine a-free factorization. -/
theorem p3_alpha_factorization (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) (s : ZMod (routingA M.base e)) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ∃ I J : ℕ, physicalAlpha M.base e s =
      I * (routingB M.base e : ℤ) + J * (routingC M.base e : ℤ) := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hm := (routingH M.base e).asRelativeIdeal.aperyRepresentative_mem
    (routingA M.base e) s
  obtain ⟨n, hn, he⟩ := hm
  obtain ⟨x, y, z, hf⟩ := routingH_factorization M.base e hn
  have hz : x = 0 := by
    by_contra hx
    have hxp : 0 < x := Nat.pos_of_ne_zero hx
    have hn' : (x - 1) * routingA M.base e + y * routingB M.base e +
        z * routingC M.base e ∈ routingH M.base e := by
      change _ ∈ generatedThree (routingA M.base e) (routingB M.base e) (routingC M.base e)
      exact (mem_generatedThree_iff _ _ _ _).mpr ⟨x - 1, y, z, rfl⟩
    apply (routingH M.base e).asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem
      (routingA M.base e) s
    refine ⟨_, hn', ?_⟩
    have hs := Nat.sub_add_cancel (Nat.one_le_of_lt hxp)
    have hmul := congrArg (fun k : ℕ => k * routingA M.base e) hs
    have hnEq : n = ((x - 1) * routingA M.base e + y * routingB M.base e +
        z * routingC M.base e) + routingA M.base e := by nlinarith only [hf, hmul]
    rw [he, hnEq]
    simp only [Nat.cast_add]
    ring
  refine ⟨y, z, ?_⟩
  change (routingH M.base e).asRelativeIdeal.aperyRepresentative (routingA M.base e) s = _
  rw [he, hf, hz]
  push_cast
  ring

end NS25Lean.P3R58
