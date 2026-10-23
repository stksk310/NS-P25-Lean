import NS25Lean.P2SectorCOwnerSelectorTransitionR7

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR8

open L5A2C4H L5A2C4OR1 L5A2C4OR2 L5A2C4OR3

variable {Gamma : NumericalSemigroup}

/-- A zero-center is stated with the actual physical floor.  Its positive
shadow is not a field: it follows from the frozen UMSP theorem. -/
def PhysicalZeroCenter
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (Y : ZMod (routingA B e)) (d : ℕ) : Prop :=
  0 < d ∧ d = currentSelector B e Y ∧ physicalHeight B e Y = 0

def zeroCenterShadow
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (Y : ZMod (routingA B e)) (d : ℕ) : ZMod (routingA B e) :=
  Y - (d * routingM B e : ℕ)

theorem physicalZeroCenter_shadow_pos
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {Y : ZMod (routingA B e)} {d : ℕ}
    (h : PhysicalZeroCenter B e Y d) :
    0 < physicalHeight B e (zeroCenterShadow B e Y d) := by
  rw [zeroCenterShadow, h.2.1]
  exact physicalUMSP B e Y

/-- The source-authority local arithmetic reduction.  This theorem deliberately
does not claim that a C4L `SourceHit` supplies its `h,w,R₁` hypotheses; that
actual bridge is a separate, currently missing interface. -/
theorem sourceHitLocalReduction_zeroCenter
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (Q : ZMod (routingA B e)) (h w H0 c1 : ℕ)
    (hh : h = 0 ∨ h = c1)
    (hw : 0 < w) (hwH0 : w ≤ H0) (hH0c1 : H0 < c1)
    (hR1 : rawCandidate B e 1 Q =
      (physicalHeight B e Q : ℤ) + w - h) :
    ∃ (Y : ZMod (routingA B e)) (d : ℕ),
      PhysicalZeroCenter B e Y d := by
  rcases hh with rfl | rfl
  · let t := currentSelector B e Q
    have htpos : 0 < t := currentSelector_pos B e Q
    have hheight := physicalHeight_eq_max_rawMinimum B e Q
    have hmin_le_max : rawMinimum B e Q ≤
        max 0 (rawMinimum B e Q) := le_max_right _ _
    have hR1gt : rawMinimum B e Q < rawCandidate B e 1 Q := by
      rw [hR1, hheight]
      push_cast
      omega
    have hone_lt : 1 < t := by
      by_contra hnot
      have ht : t = 1 := by omega
      have htmin := rawCandidate_currentSelector B e Q
      rw [← ht] at hR1gt
      linarith
    let Y := Q - (routingM B e : ℕ)
    let d := t - 1
    have hdpos : 0 < d := by simp only [d]; omega
    have hdselector : d = currentSelector B e Y := by
      simpa [d, Y, t] using
        (relativeMaxMin_selector_difference B e Q (q := 1) (p := t)
          (by omega) hone_lt rfl)
    have hpmin : rawCandidate B e t Q = rawMinimum B e Q := by
      exact rawCandidate_currentSelector B e Q
    have hYmin := relativeMaxMin_minimum B e Q (q := 1) (p := t)
      (by omega) hone_lt hpmin
    have hYneg : rawMinimum B e Y < 0 := by
      simp only [Y]
      rw [show (routingM B e : ℕ) = 1 * routingM B e by omega, hYmin]
      linarith
    have hYfloor : physicalHeight B e Y = 0 := by
      have heq := physicalHeight_eq_max_rawMinimum B e Y
      have hcast : (physicalHeight B e Y : ℤ) = 0 := by
        rw [heq]
        omega
      exact_mod_cast hcast
    exact ⟨Y, d, hdpos, hdselector, hYfloor⟩
  · by_cases hfloor : physicalHeight B e Q = 0
    · exact ⟨Q, currentSelector B e Q, currentSelector_pos B e Q,
        rfl, hfloor⟩
    · have hheight_pos : 0 < physicalHeight B e Q := Nat.pos_of_ne_zero hfloor
      have hraw_pos := (physicalHeight_pos_iff B e Q).mp hheight_pos
      have hheight := physicalHeight_eq_max_rawMinimum B e Q
      have hheight_raw : (physicalHeight B e Q : ℤ) = rawMinimum B e Q := by
        rw [hheight, max_eq_right (le_of_lt hraw_pos)]
      have hR1lt : rawCandidate B e 1 Q < rawMinimum B e Q := by
        rw [hR1, hheight_raw]
        omega
      have hle := rawMinimum_le B e Q (q := 1) (by omega)
      linarith

/-- The canonical unit state immediately before a zero-center shadow. -/
def unitZeroCenter
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (Y : ZMod (routingA B e)) (d : ℕ) : ZMod (routingA B e) :=
  zeroCenterShadow B e Y d + (routingM B e : ℕ)

private theorem unitZeroCenter_eq_previous
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {Y : ZMod (routingA B e)} {d : ℕ} (hd : 1 < d) :
    unitZeroCenter B e Y d =
      Y - ((d - 1) * routingM B e : ℕ) := by
  simp only [unitZeroCenter, zeroCenterShadow]
  have hddecomp : d = (d - 1) + 1 := by omega
  rw [hddecomp]
  push_cast
  ring

private theorem rawMinimizers_eq_singleton_of_selector_one
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e))
    (hselector : currentSelector B e s = 1) :
    RawMinimizers B e s = {1} := by
  ext q
  constructor
  · intro hq
    have hcan := (Finset.mem_filter.mp hq).1
    have hqpos := (Finset.mem_Icc.mp hcan).1
    have hqmin := (Finset.mem_filter.mp hq).2
    have hqle := minimizer_le_currentSelector B e s hqpos hqmin
    rw [hselector] at hqle
    simp only [Finset.mem_singleton]
    omega
  · intro hq
    simp only [Finset.mem_singleton] at hq
    subst q
    rw [← hselector]
    exact currentSelector_mem B e s

/-- Universal unit normalization of a genuine physical-floor zero-center.
No uniqueness premise is used: singleton minimizers follow from MAX-MIN being
the greatest positive minimizer and having value one. -/
theorem actual_unit_zeroCenter_normalization
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {Y : ZMod (routingA B e)} {d : ℕ}
    (h : PhysicalZeroCenter B e Y d) :
    currentSelector B e (unitZeroCenter B e Y d) = 1 ∧
      physicalHeight B e (unitZeroCenter B e Y d) = 0 ∧
      unitZeroCenter B e Y d - (routingM B e : ℕ) =
        zeroCenterShadow B e Y d ∧
      RawMinimizers B e (unitZeroCenter B e Y d) = {1} := by
  have hshadow : unitZeroCenter B e Y d - (routingM B e : ℕ) =
      zeroCenterShadow B e Y d := by
    simp [unitZeroCenter]
  by_cases hd : d = 1
  · have hunit : unitZeroCenter B e Y d = Y := by
      rw [hd]
      simp [unitZeroCenter, zeroCenterShadow]
    have hselector : currentSelector B e (unitZeroCenter B e Y d) = 1 := by
      rw [hunit, ← h.2.1, hd]
    refine ⟨hselector, ?_, hshadow, ?_⟩
    · simpa [hunit] using h.2.2
    · exact rawMinimizers_eq_singleton_of_selector_one B e _ hselector
  · have hdpos := h.1
    have hdgt : 1 < d := by omega
    let q := d - 1
    have hqpos : 0 < q := by simp only [q]; omega
    have hqd : q < d := by simp only [q]; omega
    have hpmin : rawCandidate B e d Y = rawMinimum B e Y := by
      rw [h.2.1]
      exact rawCandidate_currentSelector B e Y
    have hselectorPrev := relativeMaxMin_selector_difference B e Y
      (q := q) (p := d) hqpos hqd h.2.1
    have hunitPrev := unitZeroCenter_eq_previous B e (Y := Y) hdgt
    have hselector : currentSelector B e (unitZeroCenter B e Y d) = 1 := by
      rw [hunitPrev]
      have hdq : d - q = 1 := by simp only [q]; omega
      rw [← hselectorPrev, hdq]
    have hminimum := relativeMaxMin_minimum B e Y
      (q := q) (p := d) hqpos hqd hpmin
    have hqle := rawMinimum_le B e Y hqpos
    have hunitRawNonpos : rawMinimum B e (unitZeroCenter B e Y d) ≤ 0 := by
      rw [hunitPrev, hminimum]
      linarith
    have hfloor : physicalHeight B e (unitZeroCenter B e Y d) = 0 := by
      have heq := physicalHeight_eq_max_rawMinimum B e
        (unitZeroCenter B e Y d)
      have hcast : (physicalHeight B e (unitZeroCenter B e Y d) : ℤ) = 0 := by
        rw [heq]
        omega
      exact_mod_cast hcast
    exact ⟨hselector, hfloor, hshadow,
      rawMinimizers_eq_singleton_of_selector_one B e _ hselector⟩

theorem actual_unit_zeroCenter_rawMinimizers
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {Y : ZMod (routingA B e)} {d : ℕ}
    (h : PhysicalZeroCenter B e Y d) :
    RawMinimizers B e (unitZeroCenter B e Y d) = {1} :=
  (actual_unit_zeroCenter_normalization B e h).2.2.2

end NS25Lean.L5A2C4OR8
