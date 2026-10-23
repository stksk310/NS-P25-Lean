import NS25Lean.P2SectorCOwnerComponentDischarge

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR1

open L5A2C4H

variable {Gamma : NumericalSemigroup}

/-- The actual chosen-base pivot, viewed on the normalized routing residue
lattice.  No divisibility of the pivot by the tail gcd is assumed. -/
abbrev routingM (B : ChosenBase.Data Gamma) (_e : Fin 3 ≃ Fin 3) : ℕ :=
  B.q.val

theorem routingM_pos (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    0 < routingM B e := B.q_positive

private noncomputable def rawAlpha
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) : ℤ := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact (routingH B e).asRelativeIdeal.aperyRepresentative (routingA B e) s

/-- The literal numerator in the paper candidate
`q*m + alpha_(s-q*m) - alpha_s`. -/
def rawCandidateNumerator
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (s : ZMod (routingA B e)) : ℤ :=
  q * routingM B e +
    rawAlpha B e (s - (q * routingM B e : ℕ)) - rawAlpha B e s

/-- Exact divisibility of the raw candidate numerator by the actual modulus. -/
theorem rawCandidateNumerator_dvd
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (s : ZMod (routingA B e)) :
    (routingA B e : ℤ) ∣ rawCandidateNumerator B e q s := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmod :
      ((0 : ℤ) : ZMod (routingA B e)) =
        (rawCandidateNumerator B e q s : ZMod (routingA B e)) := by
    norm_num
    simp [rawCandidateNumerator, rawAlpha,
      RelativeIdeal.aperyRepresentative_mod]
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (0 : ℤ) (rawCandidateNumerator B e q s) (routingA B e)).mp hmod
  simpa using hdvd

/-- The integer-valued paper candidate.  It can be negative. -/
def rawCandidate
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (s : ZMod (routingA B e)) : ℤ :=
  rawCandidateNumerator B e q s / routingA B e

theorem rawCandidate_spec
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (s : ZMod (routingA B e)) :
    rawCandidateNumerator B e q s =
      (routingA B e : ℤ) * rawCandidate B e q s := by
  have h := Int.ediv_mul_cancel (rawCandidateNumerator_dvd B e q s)
  simpa [rawCandidate, mul_comm] using h.symm

abbrev candidateGcd (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) : ℕ :=
  Nat.gcd (routingA B e) (routingM B e)

abbrev candidatePeriod (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) : ℕ :=
  routingA B e / candidateGcd B e

abbrev candidateShift (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) : ℕ :=
  routingM B e / candidateGcd B e

theorem candidateGcd_pos (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    0 < candidateGcd B e :=
  Nat.gcd_pos_of_pos_left _ (routingA_pos B e)

theorem candidatePeriod_pos (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    0 < candidatePeriod B e := by
  apply Nat.div_pos
  · exact Nat.gcd_le_left _ (routingA_pos B e)
  · exact candidateGcd_pos B e

theorem candidateShift_pos (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    0 < candidateShift B e := by
  apply Nat.div_pos
  · exact Nat.gcd_le_right _ (routingM_pos B e)
  · exact candidateGcd_pos B e

theorem candidatePeriod_mul
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    candidatePeriod B e * routingM B e =
      routingA B e * candidateShift B e := by
  have ha : candidateGcd B e * candidatePeriod B e = routingA B e :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left (routingA B e) (routingM B e))
  have hm : candidateGcd B e * candidateShift B e = routingM B e :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right (routingA B e) (routingM B e))
  calc
    candidatePeriod B e * routingM B e =
        candidatePeriod B e * (candidateGcd B e * candidateShift B e) := by rw [hm]
    _ = (candidateGcd B e * candidatePeriod B e) * candidateShift B e := by ring
    _ = routingA B e * candidateShift B e := by rw [ha]

theorem candidateResidue_add_period
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (s : ZMod (routingA B e)) :
    s - ((q + candidatePeriod B e) * routingM B e : ℕ) =
      s - (q * routingM B e : ℕ) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  calc
    s - ((q + candidatePeriod B e) * routingM B e : ℕ) =
        s - (q * routingM B e +
          candidatePeriod B e * routingM B e : ℕ) := by rw [Nat.add_mul]
    _ = s - (q * routingM B e +
          routingA B e * candidateShift B e : ℕ) := by
        rw [candidatePeriod_mul B e]
    _ = s - (q * routingM B e : ℕ) := by simp

private theorem rawCandidateNumerator_add_period
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (s : ZMod (routingA B e)) :
    rawCandidateNumerator B e (q + candidatePeriod B e) s =
      rawCandidateNumerator B e q s +
        (routingA B e : ℤ) * candidateShift B e := by
  rw [rawCandidateNumerator, rawCandidateNumerator,
    candidateResidue_add_period B e q s]
  have hnat :
      (q + candidatePeriod B e) * routingM B e =
        q * routingM B e + routingA B e * candidateShift B e := by
    rw [Nat.add_mul, candidatePeriod_mul B e]
  have hint :
      ((q + candidatePeriod B e : ℕ) : ℤ) * routingM B e =
        (q : ℤ) * routingM B e +
          (routingA B e : ℤ) * candidateShift B e := by
    exact_mod_cast hnat
  rw [hint]
  ring

/-- Adding one gcd period strictly raises the raw candidate by the positive
integer `m / gcd(a,m)`. -/
theorem rawCandidate_add_period
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (s : ZMod (routingA B e)) :
    rawCandidate B e (q + candidatePeriod B e) s =
      rawCandidate B e q s + candidateShift B e := by
  have hnew := rawCandidate_spec B e (q + candidatePeriod B e) s
  have hold := rawCandidate_spec B e q s
  rw [rawCandidateNumerator_add_period B e q s, hold] at hnew
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  nlinarith

/-- The representative of a positive candidate index in the canonical range
`1, ..., L`. -/
def canonicalIndex
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : ℕ :=
  (q - 1) % candidatePeriod B e + 1

/-- The number of complete gcd periods removed by `canonicalIndex`. -/
def canonicalPeriodCount
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) : ℕ :=
  (q - 1) / candidatePeriod B e

theorem canonicalIndex_pos
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) :
    0 < canonicalIndex B e q := by
  simp [canonicalIndex]

theorem canonicalIndex_le_period
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ) :
    canonicalIndex B e q ≤ candidatePeriod B e := by
  have hmod := Nat.mod_lt (q - 1) (candidatePeriod_pos B e)
  simp only [canonicalIndex]
  omega

theorem canonical_index_decomposition
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {q : ℕ} (hq : 0 < q) :
    q = canonicalIndex B e q +
      canonicalPeriodCount B e q * candidatePeriod B e := by
  have hdiv := Nat.mod_add_div (q - 1) (candidatePeriod B e)
  have hdiv' :
      (q - 1) % candidatePeriod B e +
        (q - 1) / candidatePeriod B e * candidatePeriod B e = q - 1 := by
    simpa [Nat.mul_comm] using hdiv
  simp only [canonicalIndex, canonicalPeriodCount]
  omega

theorem rawCandidate_add_period_mul
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q n : ℕ) (s : ZMod (routingA B e)) :
    rawCandidate B e (q + n * candidatePeriod B e) s =
      rawCandidate B e q s + n * candidateShift B e := by
  induction n with
  | zero => simp
  | succ n ih =>
      have harg :
          q + (n + 1) * candidatePeriod B e =
            (q + n * candidatePeriod B e) + candidatePeriod B e := by ring
      calc
        rawCandidate B e (q + (n + 1) * candidatePeriod B e) s =
            rawCandidate B e ((q + n * candidatePeriod B e) +
              candidatePeriod B e) s := by rw [harg]
        _ = rawCandidate B e (q + n * candidatePeriod B e) s +
              candidateShift B e := rawCandidate_add_period B e _ s
        _ = rawCandidate B e q s + n * candidateShift B e +
              candidateShift B e := by rw [ih]
        _ = rawCandidate B e q s + (n + 1) * candidateShift B e := by
              push_cast
              ring

/-- Every positive raw candidate is its canonical-range value plus a
nonnegative integral number of positive period shifts. -/
theorem rawCandidate_canonical_decomposition
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {q : ℕ} (hq : 0 < q) (s : ZMod (routingA B e)) :
    rawCandidate B e q s =
      rawCandidate B e (canonicalIndex B e q) s +
        canonicalPeriodCount B e q * candidateShift B e := by
  conv_lhs => rw [canonical_index_decomposition B e hq]
  exact rawCandidate_add_period_mul B e (canonicalIndex B e q)
    (canonicalPeriodCount B e q) s

/-- The finite canonical interval on which the global minimum is attained. -/
def canonicalRange
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) : Finset ℕ :=
  Finset.Icc 1 (candidatePeriod B e)

theorem canonicalRange_nonempty
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (canonicalRange B e).Nonempty := by
  exact Finset.nonempty_Icc.mpr (candidatePeriod_pos B e)

private noncomputable def rawValueRange
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) : Finset ℤ :=
  (canonicalRange B e).image (fun q => rawCandidate B e q s)

private theorem rawValueRange_nonempty
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    (rawValueRange B e s).Nonempty := by
  obtain ⟨q, hq⟩ := canonicalRange_nonempty B e
  exact ⟨rawCandidate B e q s, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩

/-- The global raw-candidate minimum, computed on the canonical range. -/
noncomputable def rawMinimum
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) : ℤ :=
  (rawValueRange B e s).min' (rawValueRange_nonempty B e s)

private theorem rawMinimum_mem_value_range
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    rawMinimum B e s ∈ rawValueRange B e s := by
  exact Finset.min'_mem _ _

private theorem rawMinimum_le_canonical
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) {q : ℕ}
    (hq : q ∈ canonicalRange B e) :
    rawMinimum B e s ≤ rawCandidate B e q s := by
  apply Finset.min'_le (rawValueRange B e s)
  exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

/-- The raw minimum is below every positive-index candidate, not only those
already in the canonical range. -/
theorem rawMinimum_le
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) {q : ℕ} (hq : 0 < q) :
    rawMinimum B e s ≤ rawCandidate B e q s := by
  have hidx : canonicalIndex B e q ∈ canonicalRange B e := by
    exact Finset.mem_Icc.mpr
      ⟨canonicalIndex_pos B e q, canonicalIndex_le_period B e q⟩
  have hmin := rawMinimum_le_canonical B e s hidx
  have hdec := rawCandidate_canonical_decomposition B e hq s
  have hnonneg :
      (0 : ℤ) ≤ canonicalPeriodCount B e q * candidateShift B e := by positivity
  linarith

/-- All canonical indices attaining the global minimum.  Ties are retained. -/
noncomputable def RawMinimizers
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) : Finset ℕ :=
  (canonicalRange B e).filter
    (fun q => rawCandidate B e q s = rawMinimum B e s)

theorem rawMinimizers_nonempty
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    (RawMinimizers B e s).Nonempty := by
  have hmem := rawMinimum_mem_value_range B e s
  obtain ⟨q, hq, hvalue⟩ := Finset.mem_image.mp hmem
  refine ⟨q, Finset.mem_filter.mpr ⟨hq, ?_⟩⟩
  exact hvalue

/-- MAX-MIN tie-breaking: choose the greatest canonical minimizer. -/
noncomputable def currentSelector
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) : ℕ :=
  (RawMinimizers B e s).max' (rawMinimizers_nonempty B e s)

theorem currentSelector_mem
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    currentSelector B e s ∈ RawMinimizers B e s := by
  exact Finset.max'_mem _ _

theorem currentSelector_pos
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    0 < currentSelector B e s := by
  have hmem := currentSelector_mem B e s
  have hcan := (Finset.mem_filter.mp hmem).1
  exact (Finset.mem_Icc.mp hcan).1

theorem rawCandidate_currentSelector
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    rawCandidate B e (currentSelector B e s) s = rawMinimum B e s := by
  exact (Finset.mem_filter.mp (currentSelector_mem B e s)).2

/-- MAX-MIN dominates every positive global minimizer.  No uniqueness of the
underlying owner is asserted or used. -/
theorem minimizer_le_currentSelector
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) {q : ℕ}
    (hq : 0 < q) (hmin : rawCandidate B e q s = rawMinimum B e s) :
    q ≤ currentSelector B e s := by
  let n := canonicalPeriodCount B e q
  let i := canonicalIndex B e q
  have hidec := rawCandidate_canonical_decomposition B e hq s
  have hi_can : i ∈ canonicalRange B e := by
    exact Finset.mem_Icc.mpr
      ⟨canonicalIndex_pos B e q, canonicalIndex_le_period B e q⟩
  have hmu_le := rawMinimum_le_canonical B e s hi_can
  have hshift : (0 : ℤ) < candidateShift B e := by
    exact_mod_cast candidateShift_pos B e
  have hn_nonneg : (0 : ℤ) ≤ n := by positivity
  have hn_zero_int : (n : ℤ) = 0 := by
    rw [hmin] at hidec
    change rawMinimum B e s =
      rawCandidate B e i s + (n : ℤ) * candidateShift B e at hidec
    change rawMinimum B e s ≤ rawCandidate B e i s at hmu_le
    nlinarith
  have hn : n = 0 := by exact_mod_cast hn_zero_int
  have hqi : q = i := by
    have hdecomp := canonical_index_decomposition B e hq
    simpa [n, i, hn] using hdecomp
  have hi_value : rawCandidate B e i s = rawMinimum B e s := by
    simpa [hqi] using hmin
  have hi_mem : i ∈ RawMinimizers B e s :=
    Finset.mem_filter.mpr ⟨hi_can, hi_value⟩
  rw [hqi]
  exact Finset.le_max' _ _ hi_mem

/-- Evaluate the source-exact MAX-MIN selector at an actual in-range station
of a frozen C4K raw history.  The station certificate is retained explicitly;
no source selector, owner, transition, or replay semantics is identified here. -/
theorem actual_current_owner_selector_at_history_state
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ (H : L5A2C4K.ResidueData.RawHistory D) (k : ℕ),
      k ≤ L5A2C4K.ResidueData.RawHistory.length D H →
      let s := L5A2C4K.ResidueData.RawHistory.stateAt D H k
      let q := currentSelector B e s
      0 < q ∧
        q ∈ RawMinimizers B e s ∧
        rawCandidate B e q s = rawMinimum B e s ∧
        ∀ r : ℕ, 0 < r →
          rawCandidate B e r s = rawMinimum B e s → r ≤ q := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro H k _hk
  exact ⟨currentSelector_pos B e _, currentSelector_mem B e _,
    rawCandidate_currentSelector B e _, fun _ hr hmin =>
      minimizer_le_currentSelector B e _ hr hmin⟩

end NS25Lean.L5A2C4OR1
