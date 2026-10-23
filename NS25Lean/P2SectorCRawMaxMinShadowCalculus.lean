import NS25Lean.P2SectorCActualOwnerSelectorBridge

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR2

open L5A2C4H L5A2C4OR1

variable {Gamma : NumericalSemigroup}

/-- Translation of the residue argument occurring in the raw candidate cocycle. -/
theorem candidateTranslatedResidue
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q r : ℕ) (s : ZMod (routingA B e)) :
    s - ((q + r) * routingM B e : ℕ) =
      (s - (q * routingM B e : ℕ)) - (r * routingM B e : ℕ) := by
  rw [Nat.add_mul]
  push_cast
  ring

/-- Literal numerator cocycle, derived from the actual Apéry representatives. -/
theorem rawCandidateNumerator_cocycle
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q r : ℕ) (s : ZMod (routingA B e)) :
    rawCandidateNumerator B e (q + r) s =
      rawCandidateNumerator B e q s +
        rawCandidateNumerator B e r (s - (q * routingM B e : ℕ)) := by
  rw [rawCandidateNumerator, rawCandidateNumerator, rawCandidateNumerator,
    candidateTranslatedResidue B e q r s]
  push_cast
  ring

/-- Candidate cocycle `R_(q+r)(s) = R_q(s) + R_r(s-qm)`. -/
theorem rawCandidate_cocycle
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q r : ℕ) (s : ZMod (routingA B e)) :
    rawCandidate B e (q + r) s =
      rawCandidate B e q s +
        rawCandidate B e r (s - (q * routingM B e : ℕ)) := by
  have hsum := rawCandidate_spec B e (q + r) s
  have hq := rawCandidate_spec B e q s
  have hr := rawCandidate_spec B e r (s - (q * routingM B e : ℕ))
  rw [rawCandidateNumerator_cocycle B e q r s, hq, hr] at hsum
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  nlinarith

/-- A positive increment after MAX-MIN is strictly more expensive. -/
theorem rawCandidate_currentSelector_lt_add
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) {r : ℕ} (hr : 0 < r) :
    rawCandidate B e (currentSelector B e s) s <
      rawCandidate B e (currentSelector B e s + r) s := by
  let q := currentSelector B e s
  have hq : 0 < q := currentSelector_pos B e s
  have hqmin : rawCandidate B e q s = rawMinimum B e s :=
    rawCandidate_currentSelector B e s
  have hsum_pos : 0 < q + r := Nat.add_pos_left hq r
  have hle : rawMinimum B e s ≤ rawCandidate B e (q + r) s :=
    rawMinimum_le B e s hsum_pos
  by_contra hnot
  have hrev : rawCandidate B e (q + r) s ≤ rawCandidate B e q s :=
    le_of_not_gt hnot
  have hsum_min : rawCandidate B e (q + r) s = rawMinimum B e s := by
    omega
  have hmax : q + r ≤ currentSelector B e s :=
    minimizer_le_currentSelector B e s hsum_pos hsum_min
  change q + r ≤ q at hmax
  omega

/-- Every positive candidate at the translated residue has positive value. -/
theorem rawCandidate_shadow_pos
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) {r : ℕ} (hr : 0 < r) :
    0 < rawCandidate B e r
      (s - (currentSelector B e s * routingM B e : ℕ)) := by
  have hstrict := rawCandidate_currentSelector_lt_add B e s hr
  have hcocycle := rawCandidate_cocycle B e (currentSelector B e s) r s
  linarith

/-- Raw UMSP: the shadow behind MAX-MIN has strictly positive raw minimum. -/
theorem rawUMSP
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    0 < rawMinimum B e
      (s - (currentSelector B e s * routingM B e : ℕ)) := by
  let Y := s - (currentSelector B e s * routingM B e : ℕ)
  let r := currentSelector B e Y
  have hr : 0 < r := currentSelector_pos B e Y
  have hpos : 0 < rawCandidate B e r Y :=
    rawCandidate_shadow_pos B e s hr
  have hmin : rawCandidate B e r Y = rawMinimum B e Y :=
    rawCandidate_currentSelector B e Y
  linarith

/-- The RMF difference index is positive. -/
theorem relativeMaxMin_difference_pos {q p : ℕ} (hqp : q < p) :
    0 < p - q := by
  omega

/-- Relative MAX-MIN factorization: translating by a positive prefix subtracts
that prefix candidate from the global minimum. -/
theorem relativeMaxMin_minimum
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) {q p : ℕ}
    (hq : 0 < q) (hqp : q < p)
    (hpmin : rawCandidate B e p s = rawMinimum B e s) :
    rawMinimum B e (s - (q * routingM B e : ℕ)) =
      rawMinimum B e s - rawCandidate B e q s := by
  let Y := s - (q * routingM B e : ℕ)
  let d := p - q
  have hd : 0 < d := by simp only [d]; omega
  have hqd : q + d = p := by simp only [d]; omega
  have hcoc_d := rawCandidate_cocycle B e q d s
  have hdval : rawCandidate B e d Y =
      rawMinimum B e s - rawCandidate B e q s := by
    rw [hqd] at hcoc_d
    linarith
  have hmu_le : rawMinimum B e Y ≤
      rawMinimum B e s - rawCandidate B e q s := by
    have := rawMinimum_le B e Y hd
    linarith
  have hdiff_le : rawMinimum B e s - rawCandidate B e q s ≤
      rawMinimum B e Y := by
    let t := currentSelector B e Y
    have ht : 0 < t := currentSelector_pos B e Y
    have hs_le : rawMinimum B e s ≤ rawCandidate B e (q + t) s :=
      rawMinimum_le B e s (Nat.add_pos_left hq t)
    have hcoc_t := rawCandidate_cocycle B e q t s
    have htmin : rawCandidate B e t Y = rawMinimum B e Y :=
      rawCandidate_currentSelector B e Y
    linarith
  exact le_antisymm hmu_le hdiff_le

/-- In RMF, the positive difference index is a global minimizer at the shadow. -/
theorem relativeMaxMin_shadow_minimizer
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) {q p : ℕ}
    (hq : 0 < q) (hqp : q < p)
    (hpmin : rawCandidate B e p s = rawMinimum B e s) :
    rawCandidate B e (p - q) (s - (q * routingM B e : ℕ)) =
      rawMinimum B e (s - (q * routingM B e : ℕ)) := by
  have hcoc := rawCandidate_cocycle B e q (p - q) s
  have hqp' : q + (p - q) = p := by omega
  rw [hqp'] at hcoc
  rw [relativeMaxMin_minimum B e s hq hqp hpmin]
  linarith

/-- If `p` is MAX-MIN at `s`, then the translated difference is MAX-MIN at
the shadow residue. -/
theorem relativeMaxMin_selector_difference
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) {q p : ℕ}
    (hq : 0 < q) (hqp : q < p)
    (hpselector : p = currentSelector B e s) :
    p - q = currentSelector B e (s - (q * routingM B e : ℕ)) := by
  let Y := s - (q * routingM B e : ℕ)
  let d := p - q
  let t := currentSelector B e Y
  have hd : 0 < d := by simp only [d]; omega
  have ht : 0 < t := currentSelector_pos B e Y
  have hpmin : rawCandidate B e p s = rawMinimum B e s := by
    rw [hpselector]
    exact rawCandidate_currentSelector B e s
  have hdmin : rawCandidate B e d Y = rawMinimum B e Y := by
    simpa [d, Y] using
      relativeMaxMin_shadow_minimizer B e s hq hqp hpmin
  have hdt : d ≤ t := minimizer_le_currentSelector B e Y hd hdmin
  have hformula := relativeMaxMin_minimum B e s hq hqp hpmin
  have htmin : rawCandidate B e t Y = rawMinimum B e Y :=
    rawCandidate_currentSelector B e Y
  have hcoc := rawCandidate_cocycle B e q t s
  have hqtmin : rawCandidate B e (q + t) s = rawMinimum B e s := by
    change rawMinimum B e Y = rawMinimum B e s - rawCandidate B e q s at hformula
    linarith
  have hqtpos : 0 < q + t := Nat.add_pos_left hq t
  have hqt_le : q + t ≤ currentSelector B e s :=
    minimizer_le_currentSelector B e s hqtpos hqtmin
  rw [← hpselector] at hqt_le
  change d = t
  omega

/-- Raw activity theorem: a minimizing index is MAX-MIN exactly when its
translated shadow minimum is positive. -/
theorem rawActivity_iff
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (Q : ZMod (routingA B e)) {r p : ℕ}
    (hr : 0 < r)
    (hrmin : rawCandidate B e r Q = rawMinimum B e Q)
    (hp : p = currentSelector B e Q) :
    r = p ↔ 0 < rawMinimum B e (Q - (r * routingM B e : ℕ)) := by
  constructor
  · intro hrp
    rw [hrp, hp]
    exact rawUMSP B e Q
  · intro hshadow
    have hrle : r ≤ p := by
      rw [hp]
      exact minimizer_le_currentSelector B e Q hr hrmin
    by_contra hrp
    have hrp_lt : r < p := lt_of_le_of_ne hrle hrp
    have hpmin : rawCandidate B e p Q = rawMinimum B e Q := by
      rw [hp]
      exact rawCandidate_currentSelector B e Q
    have hformula := relativeMaxMin_minimum B e Q hr hrp_lt hpmin
    rw [hrmin] at hformula
    have : rawMinimum B e (Q - (r * routingM B e : ℕ)) = 0 := by
      linarith
    linarith

/-- Raw floor theorem: a minimizing index lies strictly below MAX-MIN exactly
when the translated shadow minimum is zero. -/
theorem rawFloor_iff
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (Q : ZMod (routingA B e)) {r p : ℕ}
    (hr : 0 < r)
    (hrmin : rawCandidate B e r Q = rawMinimum B e Q)
    (hp : p = currentSelector B e Q) :
    r < p ↔ rawMinimum B e (Q - (r * routingM B e : ℕ)) = 0 := by
  constructor
  · intro hrp
    have hpmin : rawCandidate B e p Q = rawMinimum B e Q := by
      rw [hp]
      exact rawCandidate_currentSelector B e Q
    have hformula := relativeMaxMin_minimum B e Q hr hrp hpmin
    rw [hrmin] at hformula
    linarith
  · intro hzero
    have hrle : r ≤ p := by
      rw [hp]
      exact minimizer_le_currentSelector B e Q hr hrmin
    rcases hrle.eq_or_lt with hrp | hrp
    · have hpositive :
          0 < rawMinimum B e (Q - (r * routingM B e : ℕ)) := by
        rw [hrp, hp]
        exact rawUMSP B e Q
      linarith
    · exact hrp

/-- Raw UMSP evaluated at an actual in-range C4K history station. -/
theorem actual_history_currentSelector_rawUMSP
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ (H : L5A2C4K.ResidueData.RawHistory D) (k : ℕ),
      k ≤ L5A2C4K.ResidueData.RawHistory.length D H →
      let s := L5A2C4K.ResidueData.RawHistory.stateAt D H k
      let q := currentSelector B e s
      0 < q ∧
        0 < rawMinimum B e (s - (q * routingM B e : ℕ)) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro H k _hk
  exact ⟨currentSelector_pos B e _, rawUMSP B e _⟩

end NS25Lean.L5A2C4OR2
