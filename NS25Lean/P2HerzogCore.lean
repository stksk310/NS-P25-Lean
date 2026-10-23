import NS25Lean.P2PrefixDictionary
import NS25Lean.CriticalExponent

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR3

open ChosenBase FourGeneratedBridge L2B L5A2B4AR1

variable {Gamma : NumericalSemigroup}

/-- The source-exact critical exponent in coordinate `i` after reindexing. -/
def herzogC (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) : ℕ :=
  criticalExponent B (e i)

/-- The actual factorization selected from the critical-exponent witness. -/
def herzogWitness (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    Fin 3 →₀ ℕ :=
  Classical.choose (criticalExponent_spec B (e i)).2

theorem herzogC_positive (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    0 < herzogC B e i :=
  (criticalExponent_spec B (e i)).1

theorem herzogWitness_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i : Fin 3) : herzogWitness B e i (e i) = 0 :=
  (Classical.choose_spec (criticalExponent_spec B (e i)).2).1

theorem herzogWitness_weight (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i : Fin 3) :
    weight B (herzogWitness B e i) = herzogC B e i * weights B (e i) :=
  (Classical.choose_spec (criticalExponent_spec B (e i)).2).2

/-- Expansion of an actual factorization in any reindexed three-coordinate frame. -/
theorem weight_three_coordinates (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (v : Fin 3 →₀ ℕ) :
    weight B v = v (e 0) * weights B (e 0) +
      v (e 1) * weights B (e 1) + v (e 2) * weights B (e 2) := by
  rw [weight_eq_sum, ← Equiv.sum_comp e]
  simp [Fin.sum_univ_succ, Nat.add_assoc]

abbrev c1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := herzogC B e 0
abbrev c2 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := herzogC B e 1
abbrev c3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := herzogC B e 2

abbrev r12 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 0 (e 1)
abbrev r13 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 0 (e 2)
abbrev r21 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 1 (e 0)
abbrev r23 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 1 (e 2)
abbrev r31 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 2 (e 0)
abbrev r32 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 2 (e 1)

/-- The three weighted Herzog relations, derived from the selected actual
outside factorizations rather than accepted as package fields. -/
theorem actual_herzog_relations (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    c1 B e * weights B (e 0) =
        r12 B e * weights B (e 1) + r13 B e * weights B (e 2) ∧
      c2 B e * weights B (e 1) =
        r21 B e * weights B (e 0) + r23 B e * weights B (e 2) ∧
      c3 B e * weights B (e 2) =
        r31 B e * weights B (e 0) + r32 B e * weights B (e 1) := by
  have h1 := herzogWitness_weight B e 0
  have h2 := herzogWitness_weight B e 1
  have h3 := herzogWitness_weight B e 2
  rw [weight_three_coordinates B e] at h1 h2 h3
  simp only [herzogWitness_zero, zero_mul, zero_add, add_zero] at h1 h2 h3
  exact ⟨h1.symm, h2.symm, h3.symm⟩

theorem actual_herzog_coefficients_positive (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    0 < c1 B e ∧ 0 < c2 B e ∧ 0 < c3 B e :=
  ⟨herzogC_positive B e 0, herzogC_positive B e 1,
    herzogC_positive B e 2⟩

/-- At the generic witness level the six cross coordinates are known only to
be natural (hence nonnegative); strict positivity is deliberately not claimed. -/
theorem actual_cross_coefficients_nonnegative (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    0 ≤ r12 B e ∧ 0 ≤ r13 B e ∧ 0 ≤ r21 B e ∧
      0 ≤ r23 B e ∧ 0 ≤ r31 B e ∧ 0 ≤ r32 B e := by
  omega

/-- The gcd-normalized weight attached to an actual chosen-base tail coordinate. -/
abbrev normalizedWeight (B : Data Gamma) (i : Fin 3) : ℕ :=
  weights B i /
    tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val (B.tailDegrees 2).val

private theorem tailGcd_dvd_weight (B : Data Gamma) (i : Fin 3) :
    tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val
        (B.tailDegrees 2).val ∣ weights B i := by
  obtain ⟨h0, h1, h2⟩ := tailGcd_dvd
    (B.tailDegrees 0).val (B.tailDegrees 1).val (B.tailDegrees 2).val
  fin_cases i <;> assumption

theorem normalizedWeight_scale (B : Data Gamma) (i : Fin 3) :
    tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val
        (B.tailDegrees 2).val * normalizedWeight B i = weights B i := by
  exact Nat.mul_div_cancel' (tailGcd_dvd_weight B i)

/-- The same actual witness coordinates give the three relations after gcd
normalization.  The normalization is proved by positive gcd cancellation. -/
theorem actual_normalized_herzog_relations
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    c1 B e * normalizedWeight B (e 0) =
        r12 B e * normalizedWeight B (e 1) +
          r13 B e * normalizedWeight B (e 2) ∧
      c2 B e * normalizedWeight B (e 1) =
        r21 B e * normalizedWeight B (e 0) +
          r23 B e * normalizedWeight B (e 2) ∧
      c3 B e * normalizedWeight B (e 2) =
        r31 B e * normalizedWeight B (e 0) +
          r32 B e * normalizedWeight B (e 1) := by
  let d := tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val
    (B.tailDegrees 2).val
  have hd : 0 < d := tailGcd_pos (B.degrees_positive 1)
  obtain ⟨h1, h2, h3⟩ := actual_herzog_relations B e
  have hs (i : Fin 3) : d * normalizedWeight B i = weights B i :=
    normalizedWeight_scale B i
  constructor
  · apply Nat.eq_of_mul_eq_mul_left hd
    calc
      d * (c1 B e * normalizedWeight B (e 0)) =
          c1 B e * weights B (e 0) := by rw [← hs]; ring
      _ = r12 B e * weights B (e 1) + r13 B e * weights B (e 2) := h1
      _ = d * (r12 B e * normalizedWeight B (e 1) +
          r13 B e * normalizedWeight B (e 2)) := by rw [← hs, ← hs]; ring
  constructor
  · apply Nat.eq_of_mul_eq_mul_left hd
    calc
      d * (c2 B e * normalizedWeight B (e 1)) =
          c2 B e * weights B (e 1) := by rw [← hs]; ring
      _ = r21 B e * weights B (e 0) + r23 B e * weights B (e 2) := h2
      _ = d * (r21 B e * normalizedWeight B (e 0) +
          r23 B e * normalizedWeight B (e 2)) := by rw [← hs, ← hs]; ring
  · apply Nat.eq_of_mul_eq_mul_left hd
    calc
      d * (c3 B e * normalizedWeight B (e 2)) =
          c3 B e * weights B (e 2) := by rw [← hs]; ring
      _ = r31 B e * weights B (e 0) + r32 B e * weights B (e 1) := h3
      _ = d * (r31 B e * normalizedWeight B (e 0) +
          r32 B e * normalizedWeight B (e 1)) := by rw [← hs, ← hs]; ring

/-- Actual chosen-base specialization in the frozen B4A-R2 normalization.
It combines the already-derived minimal-three theorem with the source-exact
critical coefficient positivity and normalized weighted relations. -/
theorem actual_normalized_chosenBase_herzog_core (B : Data Gamma) :
    (normalizedH B).IsMinimallyGeneratedByThree
        (normalizedA B) (normalizedB B) (normalizedC B) ∧
      0 < c1 B (Equiv.refl (Fin 3)) ∧
      0 < c2 B (Equiv.refl (Fin 3)) ∧
      0 < c3 B (Equiv.refl (Fin 3)) ∧
      c1 B (Equiv.refl (Fin 3)) * normalizedA B =
        r12 B (Equiv.refl (Fin 3)) * normalizedB B +
          r13 B (Equiv.refl (Fin 3)) * normalizedC B ∧
      c2 B (Equiv.refl (Fin 3)) * normalizedB B =
        r21 B (Equiv.refl (Fin 3)) * normalizedA B +
          r23 B (Equiv.refl (Fin 3)) * normalizedC B ∧
      c3 B (Equiv.refl (Fin 3)) * normalizedC B =
        r31 B (Equiv.refl (Fin 3)) * normalizedA B +
          r32 B (Equiv.refl (Fin 3)) * normalizedB B := by
  refine ⟨normalized_minimalThree B, ?_⟩
  obtain ⟨hc1, hc2, hc3⟩ :=
    actual_herzog_coefficients_positive B (Equiv.refl (Fin 3))
  obtain ⟨h1, h2, h3⟩ :=
    actual_normalized_herzog_relations B (Equiv.refl (Fin 3))
  refine ⟨hc1, hc2, hc3, ?_, ?_, ?_⟩
  · simpa [normalizedWeight, weights, normalizedA, normalizedB, normalizedC] using h1
  · simpa [normalizedWeight, weights, normalizedA, normalizedB, normalizedC] using h2
  · simpa [normalizedWeight, weights, normalizedA, normalizedB, normalizedC] using h3

/-- Assumption-free specialization of the normalized chosen-base core to the
actual base carried by Sector B.  The Sector-B signature selects the lane but
is not used as an extra mathematical premise for the generic Herzog facts. -/
theorem sectorB_actual_normalized_herzog_core
    (P : L5A1.P2Data Gamma) (_hB : L5A1.SectorB P.M) :
    (normalizedH P.M.base).IsMinimallyGeneratedByThree
        (normalizedA P.M.base) (normalizedB P.M.base) (normalizedC P.M.base) ∧
      0 < c1 P.M.base (Equiv.refl (Fin 3)) ∧
      0 < c2 P.M.base (Equiv.refl (Fin 3)) ∧
      0 < c3 P.M.base (Equiv.refl (Fin 3)) ∧
      c1 P.M.base (Equiv.refl (Fin 3)) * normalizedA P.M.base =
        r12 P.M.base (Equiv.refl (Fin 3)) * normalizedB P.M.base +
          r13 P.M.base (Equiv.refl (Fin 3)) * normalizedC P.M.base ∧
      c2 P.M.base (Equiv.refl (Fin 3)) * normalizedB P.M.base =
        r21 P.M.base (Equiv.refl (Fin 3)) * normalizedA P.M.base +
          r23 P.M.base (Equiv.refl (Fin 3)) * normalizedC P.M.base ∧
      c3 P.M.base (Equiv.refl (Fin 3)) * normalizedC P.M.base =
        r31 P.M.base (Equiv.refl (Fin 3)) * normalizedA P.M.base +
          r32 P.M.base (Equiv.refl (Fin 3)) * normalizedB P.M.base :=
  actual_normalized_chosenBase_herzog_core P.M.base

end NS25Lean.L5A2B4AR3
