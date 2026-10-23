import NS25Lean.P2SectorCRawMaxMinShadowCalculus

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR3

open FourGeneratedBridge L5A2C4H L5A2C4OR1 L5A2C4OR2

variable {Gamma : NumericalSemigroup}

private abbrev routingScaling
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  buildTailScaling Gamma (routingM B e) (routingN1 B e) (routingN2 B e)
    (routingN3 B e) (chosenBase_minimalFour B e)

/-- The normalized-tail ideal Apéry representative is an actual element of
the normalized tail semigroup. -/
theorem routingI_aperyRepresentative_mem_routingH
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingI B e).aperyRepresentative (routingA B e) s ∈
      (routingH B e).asRelativeIdeal := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hI := (routingI B e).aperyRepresentative_mem (routingA B e) s
  change ∃ x : ℕ,
    routingD B e * x ∈
      aperyTail Gamma.toAddSubmonoid
        (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e))
        (routingM B e) ∧
      (routingI B e).aperyRepresentative (routingA B e) s = x at hI
  obtain ⟨x, hx, heq⟩ := hI
  refine ⟨x, ?_, heq⟩
  exact (routingScaling B e).mul_mem_iff x |>.mp hx.1

/-- The normalized-semigroup Apéry representative is no larger than the
normalized-tail-ideal representative in the same residue. -/
theorem routing_aperyRepresentative_le
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingH B e).asRelativeIdeal.aperyRepresentative (routingA B e) s ≤
      (routingI B e).aperyRepresentative (routingA B e) s := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  apply (routingH B e).asRelativeIdeal.aperyRepresentative_le
    (routingA B e) s (routingI_aperyRepresentative_mem_routingH B e s)
  exact (routingI B e).aperyRepresentative_mod (routingA B e) s

private theorem existsUnique_physicalHeight
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ∃! h : ℕ,
      (routingI B e).aperyRepresentative (routingA B e) s =
        (routingH B e).asRelativeIdeal.aperyRepresentative (routingA B e) s +
          routingA B e * h := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let alpha := (routingH B e).asRelativeIdeal.aperyRepresentative (routingA B e) s
  let lambda := (routingI B e).aperyRepresentative (routingA B e) s
  have hle : alpha ≤ lambda := routing_aperyRepresentative_le B e s
  have hmod : (lambda : ZMod (routingA B e)) =
      (alpha : ZMod (routingA B e)) := by
    rw [(routingI B e).aperyRepresentative_mod,
      (routingH B e).asRelativeIdeal.aperyRepresentative_mod]
  obtain ⟨h, heq⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
    (routingA B e) hle hmod
  refine ⟨h, heq, ?_⟩
  intro k hk
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  change lambda = alpha + (routingA B e : ℤ) * k at hk
  rw [heq] at hk
  have hmul : (routingA B e : ℤ) * h = (routingA B e : ℤ) * k := by
    push_cast at heq
    omega
  have hcast : (h : ℤ) = k := mul_left_cancel₀ (ne_of_gt ha) hmul
  exact_mod_cast hcast.symm

/-- The physical residue height, selected from the exact difference of the
two actual Apéry representatives.  It is independent of `rawMinimum`. -/
noncomputable def physicalHeight
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) : ℕ := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact Classical.choose (existsUnique_physicalHeight B e s)

/-- Exact defining equation for the independently constructed physical
height. -/
theorem physicalHeight_spec
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingI B e).aperyRepresentative (routingA B e) s =
      (routingH B e).asRelativeIdeal.aperyRepresentative (routingA B e) s +
        routingA B e * physicalHeight B e s :=
  (Classical.choose_spec (existsUnique_physicalHeight B e s)).1

/-- The pivot is coprime to the actual tail gcd.  This is derived from the
four-generator presentation and cofiniteness of `Gamma`; it is not an input
to the routing data. -/
theorem routingD_coprime_routingM
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Nat.Coprime (routingD B e) (routingM B e) := by
  apply Nat.dvd_one.mp
  let g := Nat.gcd (routingD B e) (routingM B e)
  have hgD : g ∣ routingD B e := Nat.gcd_dvd_left _ _
  have hgm : g ∣ routingM B e := Nat.gcd_dvd_right _ _
  obtain ⟨hd1, hd2, hd3⟩ :=
    tailGcd_dvd (routingN1 B e) (routingN2 B e) (routingN3 B e)
  have hgn1 : g ∣ routingN1 B e := hgD.trans hd1
  have hgn2 : g ∣ routingN2 B e := hgD.trans hd2
  have hgn3 : g ∣ routingN3 B e := hgD.trans hd3
  have hall : ∀ n ∈ Gamma.toAddSubmonoid, g ∣ n := by
    intro n hn
    rw [(chosenBase_minimalFour B e).generated] at hn
    induction hn using AddSubmonoid.closure_induction with
    | mem n hn =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl | rfl | rfl
        · exact hgm
        · exact hgn1
        · exact hgn2
        · exact hgn3
    | zero => simp
    | add x y _ _ hx hy => exact dvd_add hx hy
  obtain ⟨c, hc⟩ := Gamma.exists_conductor
  have hgc : g ∣ c := hall c (hc c le_rfl)
  have hgcs : g ∣ c + 1 := hall (c + 1) (hc (c + 1) (by omega))
  have hg1 := Nat.dvd_sub hgcs hgc
  simpa using hg1

/-- Exact normalized positive-return characterization of the actual tail
ideal.  The positive return index is obtained by cancelling the actual tail
gcd against the pivot via `routingD_coprime_routingM`. -/
theorem mem_routingI_iff_positive_return
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (x : ℤ) :
    x ∈ routingI B e ↔
      ∃ q : ℕ, 0 < q ∧ x ∈ (routingH B e).asRelativeIdeal ∧
        x - q * routingM B e ∈ (routingH B e).asRelativeIdeal := by
  let S := routingScaling B e
  have hd : 0 < routingD B e := S.positive
  have hcop : Nat.Coprime (routingD B e) (routingM B e) :=
    routingD_coprime_routingM B e
  constructor
  · intro hx
    change ∃ y : ℕ,
      routingD B e * y ∈
        aperyTail Gamma.toAddSubmonoid
          (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e))
          (routingM B e) ∧ x = y at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rcases hy with ⟨hyH, hmle, hyGamma⟩
    have hybar : y ∈ routingH B e := S.mul_mem_iff y |>.mp hyH
    have hyGamma' : routingD B e * y - routingM B e ∈
        generatedFour (routingM B e) (routingN1 B e) (routingN2 B e)
          (routingN3 B e) := by
      rwa [← (chosenBase_minimalFour B e).generated]
    obtain ⟨k, h, hh, hdecomp⟩ :=
      generatedFour_isGeneratedOver (routingM B e) (routingN1 B e)
        (routingN2 B e) (routingN3 B e) _ hyGamma'
    have htotal : routingD B e * y =
        (k + 1) * routingM B e + h := by
      calc
        routingD B e * y =
            (routingD B e * y - routingM B e) + routingM B e := by omega
        _ = (k * routingM B e + h) + routingM B e := by rw [hdecomp]
        _ = (k + 1) * routingM B e + h := by ring
    have hdh : routingD B e ∣ h := S.dvd_of_mem hh
    have hdprod : routingD B e ∣ (k + 1) * routingM B e := by
      have hsub := Nat.dvd_sub (dvd_mul_right (routingD B e) y) hdh
      have heq : routingD B e * y - h = (k + 1) * routingM B e := by omega
      exact heq ▸ hsub
    obtain ⟨q, hqeq⟩ := hcop.dvd_of_dvd_mul_right hdprod
    have hq : 0 < q := by
      by_contra hn
      have hq0 : q = 0 := by omega
      simp [hq0] at hqeq
    let t := h / routingD B e
    have ht : t ∈ routingH B e := S.div_mem hh
    have hdth : routingD B e * t = h := by
      exact Nat.mul_div_cancel' hdh
    have hyqt : y = q * routingM B e + t := by
      apply Nat.eq_of_mul_eq_mul_left hd
      calc
        routingD B e * y = (k + 1) * routingM B e + h := htotal
        _ = routingD B e * (q * routingM B e + t) := by
          rw [hqeq, ← hdth]
          ring
    refine ⟨q, hq, ⟨y, hybar, rfl⟩, t, ht, ?_⟩
    omega
  · rintro ⟨q, hq, ⟨y, hy, hxy⟩, ⟨z, hz, hxz⟩⟩
    have hyz : y = q * routingM B e + z := by
      omega
    change ∃ t : ℕ,
      routingD B e * t ∈
        aperyTail Gamma.toAddSubmonoid
          (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e))
          (routingM B e) ∧ x = t
    refine ⟨y, ?_, hxy⟩
    have hdyH : routingD B e * y ∈
        generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e) :=
      (S.mul_mem_iff y).mpr hy
    have hdzH : routingD B e * z ∈
        generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e) :=
      (S.mul_mem_iff z).mpr hz
    have hdq : 0 < routingD B e * q := Nat.mul_pos hd hq
    have htailGamma : routingD B e * z ∈ Gamma.toAddSubmonoid :=
      (routingScaling B e).inclusion hdzH
    have hreturnGamma : routingD B e * y - routingM B e ∈
        Gamma.toAddSubmonoid := by
      have hsum := Gamma.toAddSubmonoid.add_mem
        (Gamma.toAddSubmonoid.nsmul_mem B.q.property (routingD B e * q - 1))
        htailGamma
      have heq : routingD B e * y - routingM B e =
          (routingD B e * q - 1) * routingM B e + routingD B e * z := by
        rw [hyz, Nat.mul_add]
        have hmq : routingM B e ≤
            routingD B e * q * routingM B e :=
          Nat.le_mul_of_pos_left _ hdq
        rw [Nat.sub_mul, one_mul]
        ring_nf
        omega
      simpa [heq, nsmul_eq_mul] using hsum
    exact ⟨hdyH, by rw [hyz]; nlinarith [routingM_pos B e], hreturnGamma⟩

/-- The physical semigroup Apéry representative used in the height equation. -/
noncomputable def physicalAlpha
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) : ℤ := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact (routingH B e).asRelativeIdeal.aperyRepresentative (routingA B e) s

private theorem routingHA
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingA B e ∈ routingH B e :=
  (NumericalSemigroup.mem_generatedByThree_iff
    (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
      (AddSubmonoid.subset_closure (by simp))

private theorem mem_routingH_iff_apery_le
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ZMod (routingA B e)) (z : ℤ)
    (hmod : (z : ZMod (routingA B e)) = r) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    z ∈ (routingH B e).asRelativeIdeal ↔ physicalAlpha B e r ≤ z := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  constructor
  · intro hz
    exact (routingH B e).asRelativeIdeal.aperyRepresentative_le
      (routingA B e) r hz hmod
  · intro hle
    obtain ⟨n, hn⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
      (routingA B e) hle (by
        calc
          (z : ZMod (routingA B e)) = r := hmod
          _ = (physicalAlpha B e r : ZMod (routingA B e)) := by
            symm
            exact (routingH B e).asRelativeIdeal.aperyRepresentative_mod
              (routingA B e) r)
    rw [hn]
    apply (routingH B e).asRelativeIdeal.add_mem_nat
      ((routingH B e).asRelativeIdeal.aperyRepresentative_mem (routingA B e) r)
    have hmul := (routingH B e).toAddSubmonoid.nsmul_mem (routingHA B e) n
    simpa [nsmul_eq_mul, Nat.mul_comm] using hmul

private theorem rawCandidateNumerator_physicalAlpha
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (q : ℕ) (s : ZMod (routingA B e)) :
    rawCandidateNumerator B e q s =
      q * routingM B e +
        physicalAlpha B e (s - (q * routingM B e : ℕ)) -
          physicalAlpha B e s := rfl

/-- Fixed-residue candidate threshold: a positive return by `q*m` exists
exactly at and above the literal integer candidate `R_q(s)`. -/
theorem rawCandidate_threshold
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) {q : ℕ} (_hq : 0 < q) (n : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    physicalAlpha B e s + routingA B e * n - q * routingM B e ∈
        (routingH B e).asRelativeIdeal ↔
      rawCandidate B e q s ≤ n := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let t := s - (q * routingM B e : ℕ)
  have hmod :
      ((physicalAlpha B e s + routingA B e * n - q * routingM B e : ℤ) :
          ZMod (routingA B e)) = t := by
    let a := routingA B e
    change ((physicalAlpha B e s + (a : ℤ) * n -
      (q : ℤ) * routingM B e : ℤ) : ZMod a) = t
    push_cast
    simp [a, physicalAlpha, t, RelativeIdeal.aperyRepresentative_mod]
  rw [mem_routingH_iff_apery_le B e t _ hmod]
  have hspec := rawCandidate_spec B e q s
  rw [rawCandidateNumerator_physicalAlpha B e q s] at hspec
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  change (q : ℤ) * routingM B e +
      physicalAlpha B e t - physicalAlpha B e s =
        (routingA B e : ℤ) * rawCandidate B e q s at hspec
  change physicalAlpha B e t ≤
      physicalAlpha B e s + (routingA B e : ℤ) * n -
        (q : ℤ) * routingM B e ↔
      rawCandidate B e q s ≤ (n : ℤ)
  constructor <;> intro h <;> nlinarith

/-- The actual normalized-tail ideal begins in residue `s` exactly at the
global raw-candidate minimum, with negative minima retained as integers. -/
theorem rawMinimum_threshold
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) (n : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    physicalAlpha B e s + routingA B e * n ∈ routingI B e ↔
      rawMinimum B e s ≤ n := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  rw [mem_routingI_iff_positive_return]
  have hxH : physicalAlpha B e s + routingA B e * n ∈
      (routingH B e).asRelativeIdeal := by
    apply (routingH B e).asRelativeIdeal.add_mem_nat
      ((routingH B e).asRelativeIdeal.aperyRepresentative_mem (routingA B e) s)
    have hmul := (routingH B e).toAddSubmonoid.nsmul_mem (routingHA B e) n
    simpa [nsmul_eq_mul, Nat.mul_comm] using hmul
  simp only [hxH, true_and]
  constructor
  · rintro ⟨q, hq, hret⟩
    have hqle := (rawCandidate_threshold B e s hq n).mp hret
    exact (rawMinimum_le B e s hq).trans hqle
  · intro hmin
    let q := currentSelector B e s
    have hq : 0 < q := currentSelector_pos B e s
    refine ⟨q, hq, (rawCandidate_threshold B e s hq n).mpr ?_⟩
    rw [rawCandidate_currentSelector B e s]
    exact hmin

/-- The physical height defined from actual Apéry representatives is exactly
the nonnegative truncation of the global raw MAX-MIN minimum. -/
theorem physicalHeight_eq_max_rawMinimum
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    (physicalHeight B e s : ℤ) = max 0 (rawMinimum B e s) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let alpha := physicalAlpha B e s
  let lambda := (routingI B e).aperyRepresentative (routingA B e) s
  let h := physicalHeight B e s
  let mu := rawMinimum B e s
  have hspec : lambda = alpha + (routingA B e : ℤ) * h := by
    simpa [alpha, lambda, h, physicalAlpha] using physicalHeight_spec B e s
  have hlamI : lambda ∈ routingI B e :=
    (routingI B e).aperyRepresentative_mem (routingA B e) s
  have hhI : alpha + (routingA B e : ℤ) * h ∈ routingI B e := by
    rwa [← hspec]
  have hmule : mu ≤ (h : ℤ) := by
    exact (rawMinimum_threshold B e s h).mp (by
      simpa [alpha, h] using hhI)
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  by_cases hmu : mu ≤ 0
  · have halphaI : alpha ∈ routingI B e := by
      have := (rawMinimum_threshold B e s 0).mpr hmu
      simpa [alpha] using this
    have hlambda_alpha : lambda ≤ alpha := by
      apply (routingI B e).aperyRepresentative_le (routingA B e) s halphaI
      exact (routingH B e).asRelativeIdeal.aperyRepresentative_mod
        (routingA B e) s
    have hh0 : h = 0 := by
      have hhcast : (h : ℤ) = 0 := by nlinarith
      exact_mod_cast hhcast
    simp [h, mu, hh0, max_eq_left hmu]
  · have hmupos : 0 < mu := lt_of_not_ge hmu
    let n := mu.toNat
    have hncast : (n : ℤ) = mu := Int.toNat_of_nonneg (le_of_lt hmupos)
    have hnI : alpha + (routingA B e : ℤ) * n ∈ routingI B e := by
      have := (rawMinimum_threshold B e s n).mpr (by rw [hncast])
      simpa [alpha] using this
    have hlambda_n : lambda ≤ alpha + (routingA B e : ℤ) * n := by
      apply (routingI B e).aperyRepresentative_le (routingA B e) s hnI
      have hmodAlpha := (routingH B e).asRelativeIdeal.aperyRepresentative_mod
        (routingA B e) s
      let a := routingA B e
      change ((alpha + (routingA B e : ℤ) * n : ℤ) :
        ZMod (routingA B e)) = s
      change ((alpha + (a : ℤ) * n : ℤ) : ZMod a) = s
      push_cast
      rw [show (a : ZMod a) = 0 by simp, zero_mul, add_zero]
      exact hmodAlpha
    have hhle : (h : ℤ) ≤ n := by nlinarith
    have hnle : (n : ℤ) ≤ h := by rw [hncast]; exact hmule
    have hheq : (h : ℤ) = mu := by
      rw [← hncast]
      exact le_antisymm hhle hnle
    rw [hheq, max_eq_right (le_of_lt hmupos)]

/-- Positivity of the physical height is equivalent to positivity of the
untruncated raw MAX-MIN minimum. -/
theorem physicalHeight_pos_iff
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    0 < physicalHeight B e s ↔ 0 < rawMinimum B e s := by
  have hid := physicalHeight_eq_max_rawMinimum B e s
  constructor
  · intro hh
    have hh' : (0 : ℤ) < physicalHeight B e s := by exact_mod_cast hh
    rw [hid] at hh'
    omega
  · intro hmu
    have hh' : (0 : ℤ) < physicalHeight B e s := by
      rw [hid, max_eq_right (le_of_lt hmu)]
      exact hmu
    exact_mod_cast hh'

/-- Physical UMSP: the MAX-MIN shadow has genuinely positive physical
height in the actual normalized-tail ideal. -/
theorem physicalUMSP
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    0 < physicalHeight B e
      (s - (currentSelector B e s * routingM B e : ℕ)) := by
  rw [physicalHeight_pos_iff]
  exact rawUMSP B e s

/-- Physical activity: a positive minimizing index is the MAX-MIN selector
exactly when the physical shadow behind it is positive. -/
theorem physicalActivity_iff
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (Q : ZMod (routingA B e)) {r p : ℕ}
    (hr : 0 < r)
    (hrmin : rawCandidate B e r Q = rawMinimum B e Q)
    (hp : p = currentSelector B e Q) :
    r = p ↔ 0 < physicalHeight B e
      (Q - (r * routingM B e : ℕ)) := by
  rw [physicalHeight_pos_iff]
  exact rawActivity_iff B e Q hr hrmin hp

/-- Physical floor: a positive minimizing index lies below MAX-MIN exactly
when its physical shadow lies on the zero floor. -/
theorem physicalFloor_iff
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (Q : ZMod (routingA B e)) {r p : ℕ}
    (hr : 0 < r)
    (hrmin : rawCandidate B e r Q = rawMinimum B e Q)
    (hp : p = currentSelector B e Q) :
    r < p ↔ physicalHeight B e
      (Q - (r * routingM B e : ℕ)) = 0 := by
  constructor
  · intro hrp
    have hraw := (rawFloor_iff B e Q hr hrmin hp).mp hrp
    have hid := physicalHeight_eq_max_rawMinimum B e
      (Q - (r * routingM B e : ℕ))
    have hcast : (physicalHeight B e
        (Q - (r * routingM B e : ℕ)) : ℤ) = 0 := by
      rw [hid, hraw]
      simp
    exact_mod_cast hcast
  · intro hzero
    have hrle : r ≤ p := by
      rw [hp]
      exact minimizer_le_currentSelector B e Q hr hrmin
    rcases hrle.eq_or_lt with hrp | hrp
    · have hpos := (physicalActivity_iff B e Q hr hrmin hp).mp hrp
      omega
    · exact hrp

/-- Physical UMSP evaluated at an actual in-range C4K raw-history station. -/
theorem actual_history_currentSelector_physicalUMSP
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    let D := routingData B e
    ∀ (H : L5A2C4K.ResidueData.RawHistory D) (k : ℕ),
      k ≤ L5A2C4K.ResidueData.RawHistory.length D H →
      let s := L5A2C4K.ResidueData.RawHistory.stateAt D H k
      let q := currentSelector B e s
      0 < q ∧
        0 < physicalHeight B e (s - (q * routingM B e : ℕ)) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  dsimp only
  intro H k _hk
  exact ⟨currentSelector_pos B e _, physicalUMSP B e _⟩

end NS25Lean.L5A2C4OR3
