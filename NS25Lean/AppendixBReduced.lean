import NS25Lean.AppendixBTwoGenerator

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A

/-- The source quotient semigroup, as an actual additive submonoid. -/
def twoQuotient (A B v : ℕ) : AddSubmonoid ℕ where
  carrier := {r | v * r ∈ twoGenerator A B}
  zero_mem' := by simpa using (twoGenerator A B).zero_mem
  add_mem' := by
    intro x y hx hy
    change v * (x + y) ∈ twoGenerator A B
    rw [mul_add]
    exact (twoGenerator A B).add_mem hx hy

@[simp] theorem mem_twoQuotient (A B v r : ℕ) :
    r ∈ twoQuotient A B v ↔ v * r ∈ twoGenerator A B := Iff.rfl

def reducedGenerator (A v : ℕ) : ℕ := A / A.gcd v
def reducedScale (A B v : ℕ) : ℕ := v / (A.gcd v * B.gcd v)

theorem pair_gcds_coprime (A B v : ℕ) (hc : A.Coprime B) :
    (A.gcd v).Coprime (B.gcd v) :=
  Nat.Coprime.of_dvd (Nat.gcd_dvd_left A v) (Nat.gcd_dvd_left B v) hc

theorem pair_gcd_product_dvd (A B v : ℕ) (hc : A.Coprime B) :
    A.gcd v * B.gcd v ∣ v :=
  (pair_gcds_coprime A B v hc).mul_dvd_of_dvd_of_dvd
    (Nat.gcd_dvd_right A v) (Nat.gcd_dvd_right B v)

theorem reduced_generators_coprime (A B v : ℕ) (hc : A.Coprime B) :
    (reducedGenerator A v).Coprime (reducedGenerator B v) :=
  Nat.Coprime.of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left A v))
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left B v)) hc

theorem reduced_generator_positive (A v : ℕ) (ha : 0 < A) :
    0 < reducedGenerator A v := by
  have he : A.gcd v * reducedGenerator A v = A :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left A v)
  by_contra hn
  have hz : reducedGenerator A v = 0 := by omega
  rw [hz, mul_zero] at he
  omega

theorem reduced_scale_exact (A B v : ℕ) (hc : A.Coprime B) :
    (A.gcd v * B.gcd v) * reducedScale A B v = v :=
  Nat.mul_div_cancel' (pair_gcd_product_dvd A B v hc)

theorem reduced_scale_positive (A B v : ℕ) (hc : A.Coprime B) (hv : 0 < v) :
    0 < reducedScale A B v := by
  have he := reduced_scale_exact A B v hc
  by_contra hn
  have hz : reducedScale A B v = 0 := by omega
  rw [hz, mul_zero] at he
  omega

/-- Exact reduction of the source quotient, retaining the actual gcd definitions. -/
theorem reduced_twoGenerator_iff (A B v r : ℕ) (ha : 0 < A) (hb : 0 < B)
    (hc : A.Coprime B) :
    v * r ∈ twoGenerator A B ↔
      reducedScale A B v * r ∈ twoGenerator (reducedGenerator A v) (reducedGenerator B v) := by
  let ga := A.gcd v
  let gb := B.gcd v
  let a := reducedGenerator A v
  let b := reducedGenerator B v
  let w := reducedScale A B v
  have hga : 0 < ga := Nat.gcd_pos_of_pos_left v ha
  have hgb : 0 < gb := Nat.gcd_pos_of_pos_left v hb
  have hprod : 0 < ga * gb := Nat.mul_pos hga hgb
  have hA : ga * a = A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A v)
  have hB : gb * b = B := Nat.mul_div_cancel' (Nat.gcd_dvd_left B v)
  have hv : (ga * gb) * w = v := reduced_scale_exact A B v hc
  have hgbA : gb.Coprime A := Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left B v) hc.symm
  have hgaB : ga.Coprime B := Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left A v) hc
  simp only [mem_twoGenerator]
  constructor
  · rintro ⟨R, S, he⟩
    have hgbS : gb ∣ B * S := dvd_mul_of_dvd_left (Nat.gcd_dvd_left B v) S
    have hgbSum : gb ∣ B * S + A * R := by
      rw [add_comm, ← he]
      exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right B v) r
    have hR : gb ∣ R := hgbA.dvd_of_dvd_mul_left ((Nat.dvd_add_right hgbS).mp hgbSum)
    have hgaR : ga ∣ A * R := dvd_mul_of_dvd_left (Nat.gcd_dvd_left A v) R
    have hgaSum : ga ∣ A * R + B * S := by
      rw [← he]
      exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right A v) r
    have hS : ga ∣ S := hgaB.dvd_of_dvd_mul_left ((Nat.dvd_add_right hgaR).mp hgaSum)
    obtain ⟨R', hR⟩ := hR
    obtain ⟨S', hS⟩ := hS
    refine ⟨R', S', ?_⟩
    change w * r = a * R' + b * S'
    apply Nat.eq_of_mul_eq_mul_left hprod
    calc
      (ga * gb) * (w * r) = v * r := by rw [← mul_assoc, hv]
      _ = A * R + B * S := he
      _ = (ga * gb) * (a * R' + b * S') := by rw [← hA, ← hB, hR, hS]; ring
  · rintro ⟨R, S, he⟩
    refine ⟨gb * R, ga * S, ?_⟩
    change w * r = a * R + b * S at he
    calc
      v * r = (ga * gb) * (w * r) := by rw [← mul_assoc, hv]
      _ = (ga * gb) * (a * R + b * S) := by rw [he]
      _ = A * (gb * R) + B * (ga * S) := by rw [← hA, ← hB]; ring

theorem reduced_quotient_eq (A B v : ℕ) (ha : 0 < A) (hb : 0 < B)
    (hc : A.Coprime B) :
    twoQuotient A B v =
      twoQuotient (reducedGenerator A v) (reducedGenerator B v) (reducedScale A B v) := by
  ext r
  exact reduced_twoGenerator_iff A B v r ha hb hc

/-- Positive source coefficients remain positive after the exact gcd reduction. -/
theorem reduced_positive_representation (A B v r : ℕ) (ha : 0 < A) (hb : 0 < B)
    (hc : A.Coprime B)
    (hrep : ∃ R S : ℕ, 0 < R ∧ 0 < S ∧ v * r = A * R + B * S) :
    ∃ R S : ℕ, 0 < R ∧ 0 < S ∧
      reducedScale A B v * r = reducedGenerator A v * R + reducedGenerator B v * S := by
  obtain ⟨R, S, hRpos, hSpos, he⟩ := hrep
  let ga := A.gcd v
  let gb := B.gcd v
  let a := reducedGenerator A v
  let b := reducedGenerator B v
  let w := reducedScale A B v
  have hga : 0 < ga := Nat.gcd_pos_of_pos_left v ha
  have hgb : 0 < gb := Nat.gcd_pos_of_pos_left v hb
  have hA : ga * a = A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A v)
  have hB : gb * b = B := Nat.mul_div_cancel' (Nat.gcd_dvd_left B v)
  have hv : (ga * gb) * w = v := reduced_scale_exact A B v hc
  have hgbA : gb.Coprime A := Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left B v) hc.symm
  have hgaB : ga.Coprime B := Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left A v) hc
  have hgbS : gb ∣ B * S := dvd_mul_of_dvd_left (Nat.gcd_dvd_left B v) S
  have hgbSum : gb ∣ B * S + A * R := by
    rw [add_comm, ← he]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right B v) r
  have hR : gb ∣ R := hgbA.dvd_of_dvd_mul_left ((Nat.dvd_add_right hgbS).mp hgbSum)
  have hgaR : ga ∣ A * R := dvd_mul_of_dvd_left (Nat.gcd_dvd_left A v) R
  have hgaSum : ga ∣ A * R + B * S := by
    rw [← he]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right A v) r
  have hS : ga ∣ S := hgaB.dvd_of_dvd_mul_left ((Nat.dvd_add_right hgaR).mp hgaSum)
  obtain ⟨R', hR⟩ := hR
  obtain ⟨S', hS⟩ := hS
  refine ⟨R', S', by nlinarith [hR], by nlinarith [hS], ?_⟩
  change w * r = a * R' + b * S'
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hga hgb)
  calc
    (ga * gb) * (w * r) = v * r := by rw [← mul_assoc, hv]
    _ = A * R + B * S := he
    _ = (ga * gb) * (a * R' + b * S') := by rw [← hA, ← hB, hR, hS]; ring

/-- The source lower bound on the quotient scale follows from positive representations. -/
theorem quotient_scale_gt (a b w : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (hpos : ∀ r ∈ twoQuotient a b w, 0 < r →
      ∃ R S : ℕ, 0 < R ∧ 0 < S ∧ w * r = a * R + b * S) :
    max a b < w := by
  have hma : a ∈ twoQuotient a b w :=
    (mem_twoGenerator a b _).mpr ⟨w, 0, by ring⟩
  have hmb : b ∈ twoQuotient a b w :=
    (mem_twoGenerator a b _).mpr ⟨0, w, by ring⟩
  obtain ⟨R, S, hR, hS, he⟩ := hpos a hma ha
  have hdS : a ∣ S := hc.dvd_of_dvd_mul_left
    ((Nat.dvd_add_right (dvd_mul_right a R)).mp (by rw [← he]; exact dvd_mul_left a w))
  have hSa : a ≤ S := Nat.le_of_dvd hS hdS
  have hwa : b < w := by nlinarith
  obtain ⟨R', S', hR', hS', he'⟩ := hpos b hmb hb
  have hdR : b ∣ R' := hc.symm.dvd_of_dvd_mul_left
    ((Nat.dvd_add_right (dvd_mul_right b S')).mp (by rw [add_comm, ← he']; exact dvd_mul_left b w))
  have hRb : b ≤ R' := Nat.le_of_dvd hR' hdR
  have hwb : a < w := by nlinarith
  exact max_lt hwb hwa

end NS25Lean.L4A

