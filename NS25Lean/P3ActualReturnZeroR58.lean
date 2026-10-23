import NS25Lean.P3CoherentHerzogR58

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R58
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4OR1 L5A2C4OR3 L5A2C4OR4
variable {Gamma : NumericalSemigroup}

theorem routing_scale_weights (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B e * routingA B e = weights B (e 0) ∧
      routingD B e * routingB B e = weights B (e 1) ∧
      routingD B e * routingC B e = weights B (e 2) := by
  obtain ⟨ha, hb, hc⟩ := tailGcd_dvd (routingN1 B e) (routingN2 B e) (routingN3 B e)
  exact ⟨Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hb, Nat.mul_div_cancel' hc⟩

theorem normalized_signed_relation_scale (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (d : ℕ) (X Y : ℤ)
    (he : (d : ℤ) * routingA B e = X * routingB B e + Y * routingC B e) :
    (d : ℤ) * weights B (e 0) = X * weights B (e 1) + Y * weights B (e 2) := by
  have hs := routing_scale_weights B e
  have ha : (routingD B e : ℤ) * routingA B e = weights B (e 0) := by exact_mod_cast hs.1
  have hb : (routingD B e : ℤ) * routingB B e = weights B (e 1) := by exact_mod_cast hs.2.1
  have hc : (routingD B e : ℤ) * routingC B e = weights B (e 2) := by exact_mod_cast hs.2.2
  calc
    (d : ℤ) * weights B (e 0) = d * ((routingD B e : ℤ) * routingA B e) := by rw [ha]
    _ = (routingD B e : ℤ) * (d * routingA B e) := by ring
    _ = (routingD B e : ℤ) * (X * routingB B e + Y * routingC B e) := by rw [he]
    _ = X * weights B (e 1) + Y * weights B (e 2) := by rw [← hb, ← hc]; ring

/-- Zero return height is the literal equality of actual tail Apéry representatives. -/
theorem rawCandidate_zero_equation (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (s : ZMod (routingA B e)) (hz : rawCandidate B e q s = 0) :
    (q : ℤ) * B.q.val + physicalAlpha B e (s - (q * B.q.val : ℕ)) =
      physicalAlpha B e s := by
  have h := rawCandidate_spec B e q s
  rw [hz, mul_zero] at h
  change (q : ℤ) * B.q.val + physicalAlpha B e (s - (q * B.q.val : ℕ)) -
    physicalAlpha B e s = 0 at h
  omega

/-- The actual zero equation gives signed coefficients; no Nat subtraction is used. -/
theorem rawCandidate_zero_signed_relation (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (q betaB betaC d rB rC : ℕ)
    (hbeta : (betaB : ℤ) * routingB M.base e + betaC * routingC M.base e =
      q * M.base.q.val + d * routingA M.base e)
    (hcanonical : IsCanonicalTailGridPoint M.base e rB rC)
    (hz : rawCandidate M.base e q (gridResidue M.base e rB rC) = 0) :
    ∃ I J : ℕ,
      (d : ℤ) * weights M.base (e 0) =
        (((betaB + I : ℕ) : ℤ) - rB) * weights M.base (e 1) +
        (((betaC + J : ℕ) : ℤ) - rC) * weights M.base (e 2) := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  obtain ⟨I, J, hIJ⟩ := p3_alpha_factorization M e
    (gridResidue M.base e rB rC - (q * M.base.q.val : ℕ))
  have hzero := rawCandidate_zero_equation M.base e q (gridResidue M.base e rB rC) hz
  have hc : physicalAlpha M.base e (gridResidue M.base e rB rC) =
      (rB : ℤ) * routingB M.base e + rC * routingC M.base e := by
    rw [← hcanonical]
    simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul]
  rw [hIJ, hc] at hzero
  refine ⟨I, J, normalized_signed_relation_scale M.base e d _ _ ?_⟩
  simp only [Nat.cast_add]
  nlinarith only [hbeta, hzero]

/-- Critical minimality excludes zero coefficients as well as both same-sign quadrants. -/
theorem actual_signed_relation_signs (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (d : ℕ) (X Y : ℤ) (hd : 0 < d) (hdc : d < criticalExponent B (e 0))
    (he : (d : ℤ) * weights B (e 0) = X * weights B (e 1) + Y * weights B (e 2)) :
    (0 < X ∧ Y < 0) ∨ (X < 0 ∧ 0 < Y) := by
  have ha : (0 : ℤ) < weights B (e 0) := by exact_mod_cast weights_positive B (e 0)
  have hb : (0 : ℤ) < weights B (e 1) := by exact_mod_cast weights_positive B (e 1)
  have hc : (0 : ℤ) < weights B (e 2) := by exact_mod_cast weights_positive B (e 2)
  have hdp : (0 : ℤ) < d := by exact_mod_cast hd
  have hnn : ¬ (0 ≤ X ∧ 0 ≤ Y) := by
    rintro ⟨hx, hy⟩
    have heN : d * weights B (e 0) = X.toNat * weights B (e 1) +
        Y.toNat * weights B (e 2) := by
      exact_mod_cast (show (d : ℤ) * weights B (e 0) =
        (X.toNat : ℤ) * weights B (e 1) + (Y.toNat : ℤ) * weights B (e 2) by
          rw [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy]; exact he)
    have hm := P3R57.critical_pair_minimum B (e 0) (e 1) (e 2)
      (e.injective.ne (by decide)) (e.injective.ne (by decide)) d X.toNat Y.toNat hd heN
    omega
  have hnp : ¬ (X ≤ 0 ∧ Y ≤ 0) := by
    rintro ⟨hx, hy⟩
    have hx' := mul_nonpos_of_nonpos_of_nonneg hx (le_of_lt hb)
    have hy' := mul_nonpos_of_nonpos_of_nonneg hy (le_of_lt hc)
    nlinarith
  by_cases hx : 0 < X
  · left; refine ⟨hx, ?_⟩
    by_contra hy; exact hnn ⟨le_of_lt hx, by omega⟩
  · right
    have hy : 0 < Y := by by_contra hy; exact hnp ⟨by omega, by omega⟩
    refine ⟨?_, hy⟩
    by_contra hx'; exact hnn ⟨by omega, le_of_lt hy⟩

private theorem signed_horizontal_nat (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (d : ℕ) (X Y : ℤ) (hx : 0 < X) (hy : Y < 0)
    (he : (d : ℤ) * weights B (e 0) = X * weights B (e 1) + Y * weights B (e 2)) :
    X.toNat * weights B (e 1) = d * weights B (e 0) + (-Y).toNat * weights B (e 2) := by
  exact_mod_cast (show (X.toNat : ℤ) * weights B (e 1) =
    (d : ℤ) * weights B (e 0) + ((-Y).toNat : ℤ) * weights B (e 2) by
      rw [Int.toNat_of_nonneg (le_of_lt hx), Int.toNat_of_nonneg (by omega : 0 ≤ -Y)]
      nlinarith only [he])

private theorem signed_vertical_nat (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (d : ℕ) (X Y : ℤ) (hx : X < 0) (hy : 0 < Y)
    (he : (d : ℤ) * weights B (e 0) = X * weights B (e 1) + Y * weights B (e 2)) :
    Y.toNat * weights B (e 2) = d * weights B (e 0) + (-X).toNat * weights B (e 1) := by
  exact_mod_cast (show (Y.toNat : ℤ) * weights B (e 2) =
    (d : ℤ) * weights B (e 0) + ((-X).toNat : ℤ) * weights B (e 1) by
      rw [Int.toNat_of_nonneg (le_of_lt hy), Int.toNat_of_nonneg (by omega : 0 ≤ -X)]
      nlinarith only [he])

theorem actual_signed_rb_cones (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (d : ℕ) (X Y : ℤ) (hd : 0 < d) (hdu : d < P3R57.roleCoefficient M hp e 1 0)
    (he : (d : ℤ) * weights M.base (e 0) =
      X * weights M.base (e 1) + Y * weights M.base (e 2)) :
    (0 < X ∧ Y < 0 ∧
      (P3R57.roleCoefficient M hp e 1 2 + criticalExponent M.base (e 2) : ℕ) ≤ -Y) ∨
      (X < 0 ∧ 0 < Y ∧ (P3R57.roleCoefficient M hp e 2 1 : ℤ) ≤ -X) := by
  have hdc := lt_trans hdu (P3R57.roleCoefficient_lt_critical M hp e 1 0 (by decide))
  rcases actual_signed_relation_signs M.base e d X Y hd hdc he with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hb := P3R57.actual_rb_horizontal_cone M hp e d X.toNat (-Y).toNat hd hdu
      (signed_horizontal_nat M.base e d X Y hx hy he)
    left; refine ⟨hx, hy, ?_⟩
    have ht : ((-Y).toNat : ℤ) = -Y := Int.toNat_of_nonneg (by omega)
    exact (show ((P3R57.roleCoefficient M hp e 1 2 +
      criticalExponent M.base (e 2) : ℕ) : ℤ) ≤ (-Y).toNat by exact_mod_cast hb).trans_eq ht
  · have hb := P3R57.actual_rb_vertical_cone M hp e d Y.toNat (-X).toNat hd hdu
      (signed_vertical_nat M.base e d X Y hx hy he)
    right; refine ⟨hx, hy, ?_⟩
    have ht : ((-X).toNat : ℤ) = -X := Int.toNat_of_nonneg (by omega)
    exact (show (P3R57.roleCoefficient M hp e 2 1 : ℤ) ≤ (-X).toNat by exact_mod_cast hb).trans_eq ht

theorem actual_signed_lt_cones (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (d : ℕ) (X Y : ℤ) (hd : 0 < d) (hdw : d < P3R57.roleCoefficient M hp e 2 0)
    (he : (d : ℤ) * weights M.base (e 0) =
      X * weights M.base (e 1) + Y * weights M.base (e 2)) :
    (0 < X ∧ Y < 0 ∧ (P3R57.roleCoefficient M hp e 1 2 : ℤ) ≤ -Y) ∨
      (X < 0 ∧ 0 < Y ∧
        (P3R57.roleCoefficient M hp e 2 1 + criticalExponent M.base (e 1) : ℕ) ≤ -X) := by
  have hdc := lt_trans hdw (P3R57.roleCoefficient_lt_critical M hp e 2 0 (by decide))
  rcases actual_signed_relation_signs M.base e d X Y hd hdc he with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hb := P3R57.actual_lt_horizontal_cone M hp e d X.toNat (-Y).toNat hd hdw
      (signed_horizontal_nat M.base e d X Y hx hy he)
    left; refine ⟨hx, hy, ?_⟩
    have ht : ((-Y).toNat : ℤ) = -Y := Int.toNat_of_nonneg (by omega)
    exact (show (P3R57.roleCoefficient M hp e 1 2 : ℤ) ≤ (-Y).toNat by exact_mod_cast hb).trans_eq ht
  · have hb := P3R57.actual_lt_vertical_cone M hp e d Y.toNat (-X).toNat hd hdw
      (signed_vertical_nat M.base e d X Y hx hy he)
    right; refine ⟨hx, hy, ?_⟩
    have ht : ((-X).toNat : ℤ) = -X := Int.toNat_of_nonneg (by omega)
    exact (show ((P3R57.roleCoefficient M hp e 2 1 +
      criticalExponent M.base (e 1) : ℕ) : ℤ) ≤ (-X).toNat by exact_mod_cast hb).trans_eq ht

end NS25Lean.P3R58
