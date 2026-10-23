import NS25Lean.P3PrefixRoutingR60
import NS25Lean.P3CommonArmR59
import NS25Lean.P3FreshProvenanceR52

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R60
open ChosenBase FourGeneratedBridge L5A2C4H L5A2C4OR3 L5A2B4AR1
open CombinatorialCore L5A2C4I L2B
variable {Gamma : NumericalSemigroup}

/-- Bounded original physical returns; ell is the original multiplier. -/
def physicalBirthCarrier (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : Set ℕ :=
  {x | x ∈ B.H ∧ ∃ ell : ℕ, 0 < ell ∧ ell ≤ routingD B e * q ∧
    ∃ y : ℕ, y ∈ B.H ∧ x = ell * B.q.val + y}

/-- Cancellation of the tail gcd forces the original multiplier to be D*p. -/
theorem physical_return_multiplier_normalized (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x ell y : ℕ) (hy : y ∈ B.H)
    (he : routingD B e * x = ell * B.q.val + y) :
    ∃ p z : ℕ, ell = routingD B e * p ∧ y = routingD B e * z ∧
      z ∈ routingH B e ∧ x = p * B.q.val + z := by
  let S := buildTailScaling Gamma B.q.val (routingN1 B e) (routingN2 B e)
    (routingN3 B e) (chosenBase_minimalFour B e)
  have hyG : y ∈ generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e) := by
    rwa [← chosenBase_tail_eq_generatedThree B e]
  have hdy : routingD B e ∣ y := S.dvd_of_mem hyG
  have hdprod : routingD B e ∣ ell * B.q.val := by
    have ht := Nat.dvd_sub (dvd_mul_right (routingD B e) x) hdy
    have heSub : routingD B e * x - y = ell * B.q.val := by omega
    exact heSub ▸ ht
  have hcop : Nat.Coprime (routingD B e) B.q.val := routingD_coprime_routingM B e
  obtain ⟨p, hp⟩ := hcop.dvd_of_dvd_mul_right hdprod
  obtain ⟨z, hz⟩ := hdy
  have hzmem : z ∈ routingH B e := (P3R59.routing_scaled_mem_iff B e z).mp (hz ▸ hy)
  refine ⟨p, z, hp, hz, hzmem, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (P3R59.routingD_positive B e)
  rw [he, hp, hz]
  ring

theorem physical_birth_iff_normalized_prefix (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q x : ℕ) : routingD B e * x ∈ physicalBirthCarrier B e q ↔
      (x : ℤ) ∈ prefixCarrier (routingH B e) B.q.val (q + 1) := by
  have hd := P3R59.routingD_positive B e
  constructor
  · rintro ⟨hx, ell, hell, hbound, y, hy, he⟩
    obtain ⟨p, z, hp, hz, hzmem, hxz⟩ :=
      physical_return_multiplier_normalized B e x ell y hy he
    have hpPos : 0 < p := by rw [hp] at hell; nlinarith
    have hpBound : p ≤ q := by rw [hp] at hbound; nlinarith
    refine ⟨p, hpPos, by omega, ⟨⟨x, (P3R59.routing_scaled_mem_iff B e x).mp hx, rfl⟩,
      ⟨z, hzmem, ?_⟩⟩⟩
    push_cast
    have hcast : (x : ℤ) = (p : ℤ) * B.q.val + z := by exact_mod_cast hxz
    omega
  · rintro ⟨p, hp, hpq, hx, z, hz, he⟩
    obtain ⟨w, hw, hwx⟩ := hx
    have hNat : x = p * B.q.val + z := by
      push_cast at he
      omega
    have hwxNat : x = w := by exact_mod_cast hwx
    refine ⟨(P3R59.routing_scaled_mem_iff B e x).mpr (hwxNat ▸ hw),
      routingD B e * p, Nat.mul_pos hd hp,
      Nat.mul_le_mul_left _ (by omega : p ≤ q), routingD B e * z,
      (P3R59.routing_scaled_mem_iff B e z).mpr hz, ?_⟩
    rw [hNat]
    ring

/-- Final USED provenance, always in the original M and e routing data. -/
theorem final_used_iff_seed_v_zero (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    ∀ q : ResidueData.ExactUnusedMergeBases D,
      (∃ s, ResidueData.cFirstStagePairing D s = q) ↔
        D.v (P3R52.backwardSeed D q).val = 0 := P3R52.actual_used_iff_seed_v_zero M e

/-- Final fresh provenance, stated separately from the varying birth prefix. -/
theorem final_fresh_iff_seed_v_positive (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    ∀ q : ResidueData.ExactUnusedMergeBases D,
      (¬ ∃ s, ResidueData.cFirstStagePairing D s = q) ↔
        0 < D.v (P3R52.backwardSeed D q).val := P3R52.actual_fresh_iff_seed_v_positive M e

end NS25Lean.P3R60

