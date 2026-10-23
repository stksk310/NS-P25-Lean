import NS25Lean.P2SectorCCanonicalForwardPacketR14

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR15

open L2B L5A1 L5A2C3G L5A2C4A L5A2C4B L5A2C4C L5A2C4D
  L5A2C4G L5A2C4H L5A2C4K L5A2C4L L5A2C4OR1 L5A2C4OR2 L5A2C4OR3
  L5A2C4OR8 L5A2C4OR9 L5A2C4OR10 L5A2C4OR13 L5A2C4OR14 ChosenBase

variable {Gamma : NumericalSemigroup}

/-- If a two-component fiber has two boundary-killed components, every actual
component is boundary-killed.  This is a finite-cardinality consequence, not a
new gate assumption. -/
private theorem all_boundaryKilled_of_localSignature_two_two
    (M : MultiplicityBase Gamma) (h : ℕ)
    (hs : LocalSignature M h 2 2) :
    ∀ C : FiberComponent M.base h, BoundaryKilled M h C := by
  classical
  letI := Fintype.ofFinite (FiberComponent M.base h)
  letI := Fintype.ofFinite {C : FiberComponent M.base h // BoundaryKilled M h C}
  let f : {C : FiberComponent M.base h // BoundaryKilled M h C} →
      FiberComponent M.base h := Subtype.val
  have hcard : Fintype.card {C : FiberComponent M.base h // BoundaryKilled M h C} =
      Fintype.card (FiberComponent M.base h) := by
    simpa [killedCount, componentCount, Nat.card_eq_fintype_card] using
      hs.2.trans hs.1.symm
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨Subtype.val_injective, hcard⟩
  intro C
  obtain ⟨E, hE⟩ := hbij.2 C
  rw [← hE]
  exact E.property

/-- The actual inactive `h1=c1*a` LocalSignature forces the strict origin
height wall.  The proof recovers the killed pure critical component, removes
its actual `a` coordinate, and invokes the eta threshold theorem. -/
theorem inactiveLocalSignature_H0_lt (P : P2Data Gamma) (e : Fin 3 ≃ Fin 3)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2) :
    H0 P.M.base e < c1 P.M.base e := by
  have hKilled := all_boundaryKilled_of_localSignature_two_two P.M
    (c1 P.M.base e * weights P.M.base (e 0)) hInactive
    (critical_pure_component P.M.base (e 0))
  obtain ⟨u, huC, j, huj, hK⟩ := hKilled
  have hjmem : j ∈ componentSupport P.M.base
      (c1 P.M.base e * weights P.M.base (e 0))
      (critical_pure_component P.M.base (e 0)) :=
    (mem_componentSupport P.M.base _ _ j).mpr ⟨u, huC, huj⟩
  have hj : j = e 0 := by
    change j ∈ componentSupport P.M.base
      (criticalExponent P.M.base (e 0) * weights P.M.base (e 0))
      (critical_pure_component P.M.base (e 0)) at hjmem
    rw [critical_component_support_eq_singleton] at hjmem
    exact Finset.mem_singleton.mp hjmem
  subst j
  have hcpos : 0 < c1 P.M.base e := herzogC_positive P.M.base e 0
  have hdegree :
      c1 P.M.base e * weights P.M.base (e 0) - weights P.M.base (e 0) =
        gridDegree P.M.base e (c1 P.M.base e - 1) 0 0 := by
    simp only [gridDegree, zero_mul, add_zero]
    rw [Nat.sub_mul]
    simp
  have heta : H0 P.M.base e ≤ c1 P.M.base e - 1 :=
    (gridDegree_mem_K_iff_eta_le P.M.base e 0 0 (c1 P.M.base e - 1)).mp
      (hdegree ▸ hK)
  omega

/-- Source-exact actual mixed surviving-notch gate.  All inputs are genuine
upstream objects exported by `actual_nonsymmetric_gate_interface`; none of the
three conclusions is stored in a field or accepted as a free hypothesis. -/
theorem actual_cm_gate {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (_hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD) :
    coherentP1 P.M.base e HD = 0 ∧
      coherentQ1 P.M.base e HD = 0 ∧
      H0 P.M.base e < c1 P.M.base e := by
  exact ⟨hNotch.1, hNotch.2, inactiveLocalSignature_H0_lt P e hInactive⟩

/-- R14 positive-seed cap with all three temporary gate hypotheses discharged
from the same actual mixed surviving-notch witness package. -/
theorem actual_cm_sourceHit_positive_seed_cap {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD)
    (incoming : ResidueData.RawHistory (routingData P.M.base e))
    (target : ResidueData.BSourceRootedHistory (routingData P.M.base e))
    (hit : ResidueData.SourceHit (routingData P.M.base e) incoming target.raw)
    (hpositive : 0 < physicalHeight P.M.base e
      (actualSourceHitState P.M.base e incoming target hit)) :
    let D := routingData P.M.base e
    let r := actualSourceHitState P.M.base e incoming target hit
    ∃ i j k,
      L5A2C4OR5.HerzogLShapeDomain HD i j ∧
      gridResidue P.M.base e i j = r ∧
      L5A2C4OR13.CanonicalLocation.Holds HD k i j ∧
      (k = .ordinary ∨ k = .upperRight ∨ k = .bottomTop) ∧
      0 < D.u (D.c r) ∧ D.u (D.c r) ≤ H0 P.M.base e ∧
      H0 P.M.base e < c1 P.M.base e := by
  obtain ⟨hP, hQ, hH⟩ := actual_cm_gate G boundaryPure boundaryMixed e HD
    hInactive hMixed hNotch
  exact actual_sourceHit_positive_seed_cap P.M.base e HD incoming target hit
    hpositive hP hQ hH

/-- A state already on the physical floor is itself a genuine physical
zero-center, with its actual greatest minimizer as depth. -/
theorem zeroHeight_physicalZeroCenter
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) (hzero : physicalHeight B e s = 0) :
    ∃ d, PhysicalZeroCenter B e s d := by
  exact ⟨currentSelector B e s, currentSelector_pos B e s, rfl, hzero⟩

/-- If the actual MAX-MIN owner is larger than one, RMF at the penultimate
owner step constructs a unit physical zero-center.  No local-square or gate
premise is involved. -/
theorem higherOwner_physicalZeroCenter
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e))
    (howner : 1 < currentSelector B e s) :
    ∃ Y d, PhysicalZeroCenter B e Y d := by
  let t := currentSelector B e s
  let q := t - 1
  let Y := s - (q * routingM B e : ℕ)
  have hqpos : 0 < q := by simp only [q, t]; omega
  have hqt : q < t := by simp only [q, t]; omega
  have ht : t = currentSelector B e s := rfl
  have hselector := relativeMaxMin_selector_difference B e s hqpos hqt ht
  have hselectorY : 1 = currentSelector B e Y := by
    have htq : t - q = 1 := by simp only [q]; omega
    simpa only [Y, htq] using hselector
  have htmin : rawCandidate B e t s = rawMinimum B e s := by
    exact rawCandidate_currentSelector B e s
  have hminimum := relativeMaxMin_minimum B e s hqpos hqt htmin
  have hqle := rawMinimum_le B e s hqpos
  have hnonpos : rawMinimum B e Y ≤ 0 := by
    have hminimumY : rawMinimum B e Y =
        rawMinimum B e s - rawCandidate B e q s := by
      simpa only [Y] using hminimum
    rw [hminimumY]
    linarith
  have hfloor : physicalHeight B e Y = 0 := by
    have heq := physicalHeight_eq_max_rawMinimum B e Y
    have hcast : (physicalHeight B e Y : ℤ) = 0 := by
      rw [heq]
      omega
    exact_mod_cast hcast
  exact ⟨Y, 1, by omega, hselectorY, hfloor⟩

/-- Source-exact CM-SHZ early-exit/live-fork split.  Zero seed and every
higher-owner state at the seed/east/north cells produce a physical zero-center.
The remaining branch carries the positive O/AR/BT cap and the three actual
unit-owner facts as output. -/
theorem actual_cm_sourceHit_early_or_live {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD)
    (incoming : ResidueData.RawHistory (routingData P.M.base e))
    (target : ResidueData.BSourceRootedHistory (routingData P.M.base e))
    (hit : ResidueData.SourceHit (routingData P.M.base e) incoming target.raw) :
    let D := routingData P.M.base e
    let r := actualSourceHitState P.M.base e incoming target hit
    (∃ Y d, PhysicalZeroCenter P.M.base e Y d) ∨
      (0 < physicalHeight P.M.base e r ∧
        0 < physicalHeight P.M.base e (D.b r) ∧
        0 < physicalHeight P.M.base e (D.c r) ∧
        currentSelector P.M.base e r = 1 ∧
        currentSelector P.M.base e (D.b r) = 1 ∧
        currentSelector P.M.base e (D.c r) = 1 ∧
        ∃ i j k,
          L5A2C4OR5.HerzogLShapeDomain HD i j ∧
          gridResidue P.M.base e i j = r ∧
          L5A2C4OR13.CanonicalLocation.Holds HD k i j ∧
          (k = .ordinary ∨ k = .upperRight ∨ k = .bottomTop) ∧
          0 < D.u (D.c r) ∧ D.u (D.c r) ≤ H0 P.M.base e ∧
          H0 P.M.base e < c1 P.M.base e) := by
  let D := routingData P.M.base e
  let r := actualSourceHitState P.M.base e incoming target hit
  have hs := actual_sourceHit_sourceTarget_cross P.M.base e incoming target hit
  change D.IsBranch r ∧ D.u r = 0 ∧ D.v r = 0 ∧
    D.u (D.c r) = D.v (D.b r) ∧ 0 < D.u (D.c r) at hs
  by_cases hrzero : physicalHeight P.M.base e r = 0
  · left
    obtain ⟨d, hd⟩ := zeroHeight_physicalZeroCenter P.M.base e r hrzero
    exact ⟨r, d, hd⟩
  · have hrpos : 0 < physicalHeight P.M.base e r := Nat.pos_of_ne_zero hrzero
    have hcap := actual_cm_sourceHit_positive_seed_cap G boundaryPure boundaryMixed
      e HD hInactive hMixed hNotch incoming target hit hrpos
    change ∃ i j k,
      L5A2C4OR5.HerzogLShapeDomain HD i j ∧
      gridResidue P.M.base e i j = r ∧
      L5A2C4OR13.CanonicalLocation.Holds HD k i j ∧
      (k = .ordinary ∨ k = .upperRight ∨ k = .bottomTop) ∧
      0 < D.u (D.c r) ∧ D.u (D.c r) ≤ H0 P.M.base e ∧
      H0 P.M.base e < c1 P.M.base e at hcap
    have hb := physicalHeight_step_b_with_tailCarry P.M.base e r
    have hc := physicalHeight_step_c_with_tailCarry P.M.base e r
    change physicalHeight P.M.base e r + tailBCarry P.M.base e r =
      physicalHeight P.M.base e (D.b r) + D.u r at hb
    change physicalHeight P.M.base e r + tailCCarry P.M.base e r =
      physicalHeight P.M.base e (D.c r) + D.v r at hc
    have hbpos : 0 < physicalHeight P.M.base e (D.b r) := by omega
    have hcpos : 0 < physicalHeight P.M.base e (D.c r) := by omega
    by_cases hrOwner : 1 < currentSelector P.M.base e r
    · left
      exact higherOwner_physicalZeroCenter P.M.base e r hrOwner
    by_cases hbOwner : 1 < currentSelector P.M.base e (D.b r)
    · left
      exact higherOwner_physicalZeroCenter P.M.base e (D.b r) hbOwner
    by_cases hcOwner : 1 < currentSelector P.M.base e (D.c r)
    · left
      exact higherOwner_physicalZeroCenter P.M.base e (D.c r) hcOwner
    · right
      have hrSel := currentSelector_pos P.M.base e r
      have hbSel := currentSelector_pos P.M.base e (D.b r)
      have hcSel := currentSelector_pos P.M.base e (D.c r)
      have hrOne : currentSelector P.M.base e r = 1 := by omega
      have hbOne : currentSelector P.M.base e (D.b r) = 1 := by omega
      have hcOne : currentSelector P.M.base e (D.c r) = 1 := by omega
      exact ⟨hrpos, hbpos, hcpos, hrOne, hbOne, hcOne, hcap⟩

/-- Candidate transport across one `b` edge, expressed with the actual ambient
tail carries.  This is global and wrap-safe. -/
theorem rawCandidate_step_b_with_tailCarry
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ)
    (s : ZMod (routingA B e)) :
    rawCandidate B e q (s + routingB B e) +
        tailBCarry B e (s - (q * routingM B e : ℕ)) =
      rawCandidate B e q s + tailBCarry B e s := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let shadow := s - (q * routingM B e : ℕ)
  have hshadowB :
      s + routingB B e - (q * routingM B e : ℕ) =
        shadow + routingB B e := by
    dsimp only [shadow]
    abel
  have h0 := rawCandidate_spec B e q s
  have hb := rawCandidate_spec B e q (s + routingB B e)
  change (q : ℤ) * routingM B e + physicalAlpha B e shadow -
      physicalAlpha B e s =
        (routingA B e : ℤ) * rawCandidate B e q s at h0
  change (q : ℤ) * routingM B e +
      physicalAlpha B e
        (s + routingB B e - (q * routingM B e : ℕ)) -
      physicalAlpha B e (s + routingB B e) =
        (routingA B e : ℤ) * rawCandidate B e q (s + routingB B e) at hb
  rw [hshadowB] at hb
  have htShadow := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e) shadow
  have htBase := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e) s
  change physicalAlpha B e shadow + routingB B e =
    physicalAlpha B e (shadow + routingB B e) +
      (routingA B e : ℤ) * tailBCarry B e shadow at htShadow
  change physicalAlpha B e s + routingB B e =
    physicalAlpha B e (s + routingB B e) +
      (routingA B e : ℤ) * tailBCarry B e s at htBase
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hprod : (routingA B e : ℤ) *
      (rawCandidate B e q (s + routingB B e) +
        tailBCarry B e shadow - rawCandidate B e q s - tailBCarry B e s) = 0 := by
    linear_combination -(hb - h0 + htShadow - htBase)
  have hz : rawCandidate B e q (s + routingB B e) +
      tailBCarry B e shadow - rawCandidate B e q s - tailBCarry B e s = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
  dsimp only [shadow] at hz
  linarith

/-- Candidate transport across one `c` edge, dual to the preceding theorem. -/
theorem rawCandidate_step_c_with_tailCarry
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (q : ℕ)
    (s : ZMod (routingA B e)) :
    rawCandidate B e q (s + routingC B e) +
        tailCCarry B e (s - (q * routingM B e : ℕ)) =
      rawCandidate B e q s + tailCCarry B e s := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let shadow := s - (q * routingM B e : ℕ)
  have hshadowC :
      s + routingC B e - (q * routingM B e : ℕ) =
        shadow + routingC B e := by
    dsimp only [shadow]
    abel
  have h0 := rawCandidate_spec B e q s
  have hc := rawCandidate_spec B e q (s + routingC B e)
  change (q : ℤ) * routingM B e + physicalAlpha B e shadow -
      physicalAlpha B e s =
        (routingA B e : ℤ) * rawCandidate B e q s at h0
  change (q : ℤ) * routingM B e +
      physicalAlpha B e
        (s + routingC B e - (q * routingM B e : ℕ)) -
      physicalAlpha B e (s + routingC B e) =
        (routingA B e : ℤ) * rawCandidate B e q (s + routingC B e) at hc
  rw [hshadowC] at hc
  have htShadow := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) shadow
  have htBase := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) s
  change physicalAlpha B e shadow + routingC B e =
    physicalAlpha B e (shadow + routingC B e) +
      (routingA B e : ℤ) * tailCCarry B e shadow at htShadow
  change physicalAlpha B e s + routingC B e =
    physicalAlpha B e (s + routingC B e) +
      (routingA B e : ℤ) * tailCCarry B e s at htBase
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hprod : (routingA B e : ℤ) *
      (rawCandidate B e q (s + routingC B e) +
        tailCCarry B e shadow - rawCandidate B e q s - tailCCarry B e s) = 0 := by
    linear_combination -(hc - h0 + htShadow - htBase)
  have hz : rawCandidate B e q (s + routingC B e) +
      tailCCarry B e shadow - rawCandidate B e q s - tailCCarry B e s = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
  dsimp only [shadow] at hz
  linarith

private theorem rawCandidate_one_eq_physicalHeight_of_live
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e))
    (hpositive : 0 < physicalHeight B e s)
    (hselector : currentSelector B e s = 1) :
    rawCandidate B e 1 s = physicalHeight B e s := by
  have hmin := rawCandidate_currentSelector B e s
  rw [hselector] at hmin
  have hmupos := (physicalHeight_pos_iff B e s).mp hpositive
  have hheight := physicalHeight_eq_max_rawMinimum B e s
  have hheightRaw : (physicalHeight B e s : ℤ) = rawMinimum B e s := by
    rw [hheight, max_eq_right (le_of_lt hmupos)]
  rw [hmin, ← hheightRaw]

/-- In the derived owner-one live fork, the MAX-MIN shadow has zero ambient
tail carry in both first directions.  The proof uses the global candidate-edge
identities and the actual zero raw carries at the seed. -/
theorem liveFork_shadow_tail_zero
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e))
    (hu : (routingData B e).u s = 0)
    (hv : (routingData B e).v s = 0)
    (hspos : 0 < physicalHeight B e s)
    (hbpos : 0 < physicalHeight B e (s + routingB B e))
    (hcpos : 0 < physicalHeight B e (s + routingC B e))
    (hsOwner : currentSelector B e s = 1)
    (hbOwner : currentSelector B e (s + routingB B e) = 1)
    (hcOwner : currentSelector B e (s + routingC B e) = 1) :
    let xi := s - (routingM B e : ℕ)
    tailBCarry B e xi = 0 ∧ tailCCarry B e xi = 0 := by
  let xi := s - (routingM B e : ℕ)
  have hRs := rawCandidate_one_eq_physicalHeight_of_live B e s hspos hsOwner
  have hRb := rawCandidate_one_eq_physicalHeight_of_live B e
    (s + routingB B e) hbpos hbOwner
  have hRc := rawCandidate_one_eq_physicalHeight_of_live B e
    (s + routingC B e) hcpos hcOwner
  have hCandB := rawCandidate_step_b_with_tailCarry B e 1 s
  have hCandC := rawCandidate_step_c_with_tailCarry B e 1 s
  have hStepB := physicalHeight_step_b_with_tailCarry B e s
  have hStepC := physicalHeight_step_c_with_tailCarry B e s
  have hxi : s - (1 * routingM B e : ℕ) = xi := by simp [xi]
  rw [hxi, hRs, hRb] at hCandB
  rw [hxi, hRs, hRc] at hCandC
  rw [hu, add_zero] at hStepB
  rw [hv, add_zero] at hStepC
  have hStepBI : (physicalHeight B e s : ℤ) + tailBCarry B e s =
      physicalHeight B e (s + routingB B e) := by exact_mod_cast hStepB
  have hStepCI : (physicalHeight B e s : ℤ) + tailCCarry B e s =
      physicalHeight B e (s + routingC B e) := by exact_mod_cast hStepC
  constructor
  · have hz : (tailBCarry B e xi : ℤ) = 0 := by linarith [hCandB, hStepBI]
    exact_mod_cast hz
  · have hz : (tailCCarry B e xi : ℤ) = 0 := by linarith [hCandC, hStepCI]
    exact_mod_cast hz

/-- A canonical state whose two first ambient tail carries vanish is exactly
ordinary or the central notch cell.  All six other atlas rows are excluded by
their positive coherent lift, including both outer corners. -/
theorem zeroTailCarry_location
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (s : ZMod (routingA B e))
    (hB : tailBCarry B e s = 0) (hC : tailCCarry B e s = 0) :
    ∃ i j k,
      L5A2C4OR5.HerzogLShapeDomain HD i j ∧
      gridResidue B e i j = s ∧
      L5A2C4OR13.CanonicalLocation.Holds HD k i j ∧
      (k = .ordinary ∨ k = .center) := by
  obtain ⟨x, hx⟩ := (L5A2C4OR6.coherent_lShape_residue_bijective B e HD).2 s
  obtain ⟨i, j, hij, hxgrid⟩ :=
    L5A2C4OR11.lShapeIndex_actual_coordinate B e HD x
  have hres : gridResidue B e i j = s := hxgrid.symm.trans hx
  obtain ⟨k, hk⟩ := L5A2C4OR13.canonicalLocation_exists B e HD hij
  refine ⟨i, j, k, hij, hres, hk, ?_⟩
  have hp := coherent_coefficients_positive B e HD
  have hc1pos := herzogC_positive B e 0
  cases k with
  | ordinary => exact Or.inl rfl
  | center => exact Or.inr rfl
  | upperArmInterior =>
      let P := upperArmForwardPacket B e HD i j hk
      have ht := forwardPacket_base_tailBCarry P hij
      rw [hres, hB] at ht
      dsimp [P, upperArmForwardPacket] at ht
      change 0 = c1 B e at ht
      exact ((Nat.ne_of_gt hc1pos) ht.symm).elim
  | upperRight =>
      let P := upperRightForwardPacket B e HD i j hk
      have ht := forwardPacket_base_tailBCarry P hij
      rw [hres, hB] at ht
      dsimp [P, upperRightForwardPacket] at ht
      omega
  | bottomTop =>
      let P := bottomTopForwardPacket B e HD i j hk
      have ht := forwardPacket_base_tailCCarry P hij
      rw [hres, hC] at ht
      dsimp [P, bottomTopForwardPacket] at ht
      omega
  | bottomNotchInterior =>
      let P := bottomNotchForwardPacket B e HD i j hk
      have ht := forwardPacket_base_tailCCarry P hij
      rw [hres, hC] at ht
      dsimp [P, bottomNotchForwardPacket] at ht
      change 0 = c1 B e at ht
      exact ((Nat.ne_of_gt hc1pos) ht.symm).elim
  | kappa1 =>
      let P := kappa1ForwardPacket B e HD i j hk
      have ht := forwardPacket_base_tailBCarry P hij
      rw [hres, hB] at ht
      dsimp [P, kappa1ForwardPacket] at ht
      omega
  | kappa2 =>
      let P := kappa2ForwardPacket B e HD i j hk
      have ht := forwardPacket_base_tailBCarry P hij
      rw [hres, hB] at ht
      dsimp [P, kappa2ForwardPacket] at ht
      change 0 = c1 B e at ht
      exact ((Nat.ne_of_gt hc1pos) ht.symm).elim

/-- On the zero-tail shadow, the two incoming diagonal tail carries agree and
their common value is exactly `0` (ordinary) or `c1` (center). -/
theorem zeroTailCarry_shadow_h
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (s : ZMod (routingA B e))
    (hB : tailBCarry B e s = 0) (hC : tailCCarry B e s = 0) :
    ∃ i j k,
      L5A2C4OR5.HerzogLShapeDomain HD i j ∧
      gridResidue B e i j = s ∧
      L5A2C4OR13.CanonicalLocation.Holds HD k i j ∧
      (k = .ordinary ∨ k = .center) ∧
      tailBCarry B e (s + routingC B e) =
        tailCCarry B e (s + routingB B e) ∧
      (tailBCarry B e (s + routingC B e) = 0 ∨
        tailBCarry B e (s + routingC B e) = c1 B e) := by
  obtain ⟨i, j, k, hij, hres, hk, hloc⟩ :=
    zeroTailCarry_location B e HD s hB hC
  refine ⟨i, j, k, hij, hres, hk, hloc, ?_⟩
  rcases hloc with rfl | rfl
  · let P := ordinaryForwardPacket B e HD i j hk
    have hb := forwardPacket_tailBCarry P hij
    have hc := forwardPacket_tailCCarry P hij
    rw [P.nResidue, hres] at hb
    rw [P.eResidue, hres] at hc
    dsimp [P, ordinaryForwardPacket] at hb hc
    exact ⟨by omega, Or.inl (by omega)⟩
  · let P := centerForwardPacket B e HD i j hk
    have hb := forwardPacket_tailBCarry P hij
    have hc := forwardPacket_tailCCarry P hij
    rw [P.nResidue, hres] at hb
    rw [P.eResidue, hres] at hc
    dsimp [P, centerForwardPacket] at hb hc
    exact ⟨by omega, Or.inr (by omega)⟩

/-- The complete shadow packet in the owner-one live fork.  Its location and
`h`-dichotomy are derived after, rather than stored alongside, the actual
MAX-MIN data. -/
theorem actual_cm_live_shadow_packet
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (s : ZMod (routingA B e))
    (hu : (routingData B e).u s = 0)
    (hv : (routingData B e).v s = 0)
    (hspos : 0 < physicalHeight B e s)
    (hbpos : 0 < physicalHeight B e (s + routingB B e))
    (hcpos : 0 < physicalHeight B e (s + routingC B e))
    (hsOwner : currentSelector B e s = 1)
    (hbOwner : currentSelector B e (s + routingB B e) = 1)
    (hcOwner : currentSelector B e (s + routingC B e) = 1) :
    let xi := s - (routingM B e : ℕ)
    tailBCarry B e xi = 0 ∧ tailCCarry B e xi = 0 ∧
      ∃ i j k,
        L5A2C4OR5.HerzogLShapeDomain HD i j ∧
        gridResidue B e i j = xi ∧
        L5A2C4OR13.CanonicalLocation.Holds HD k i j ∧
        (k = .ordinary ∨ k = .center) ∧
        tailBCarry B e (xi + routingC B e) =
          tailCCarry B e (xi + routingB B e) ∧
        (tailBCarry B e (xi + routingC B e) = 0 ∨
          tailBCarry B e (xi + routingC B e) = c1 B e) := by
  let xi := s - (routingM B e : ℕ)
  have hzero := liveFork_shadow_tail_zero B e s hu hv hspos hbpos hcpos
    hsOwner hbOwner hcOwner
  change tailBCarry B e xi = 0 ∧ tailCCarry B e xi = 0 at hzero
  exact ⟨hzero.1, hzero.2,
    zeroTailCarry_shadow_h B e HD xi hzero.1 hzero.2⟩

/-- Corrected Candidate Transport for the diagonal target of a live branch
seed.  The correction is the actual incoming `b` tail carry at the shadow's
`c`-neighbour; it is not the target seam correction. -/
theorem actual_cm_live_candidate_transport
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e))
    (hcpos : 0 < physicalHeight B e (s + routingC B e))
    (hcOwner : currentSelector B e (s + routingC B e) = 1) :
    let xi := s - (routingM B e : ℕ)
    let Q := s + routingC B e + routingB B e
    let w := (routingData B e).u (s + routingC B e)
    let h := tailBCarry B e (xi + routingC B e)
    rawCandidate B e 1 Q = (physicalHeight B e Q : ℤ) + w - h := by
  let xi := s - (routingM B e : ℕ)
  let Q := s + routingC B e + routingB B e
  let w := (routingData B e).u (s + routingC B e)
  let h := tailBCarry B e (xi + routingC B e)
  have hRN := rawCandidate_one_eq_physicalHeight_of_live B e
    (s + routingC B e) hcpos hcOwner
  have hCand := rawCandidate_step_b_with_tailCarry B e 1
    (s + routingC B e)
  have hPhys := physicalHeight_step_b_with_tailCarry B e
    (s + routingC B e)
  have hshadow :
      s + routingC B e - (1 * routingM B e : ℕ) =
        xi + routingC B e := by
    simp only [xi, one_mul]
    abel
  rw [hshadow] at hCand
  change rawCandidate B e 1 Q + tailBCarry B e (xi + routingC B e) =
    rawCandidate B e 1 (s + routingC B e) +
      tailBCarry B e (s + routingC B e) at hCand
  change physicalHeight B e (s + routingC B e) +
      tailBCarry B e (s + routingC B e) =
    physicalHeight B e Q + w at hPhys
  rw [hRN] at hCand
  dsimp only [Q, w, h]
  linarith

/-- The complete actual C-M source-hit reduction through physical zero-center.
The gate, positive cap, early exits, live shadow, `h`-dichotomy, and Candidate
Transport are all derived from the same actual witness package. -/
theorem actual_cm_sourceHit_physicalZeroCenter {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD)
    (incoming : ResidueData.RawHistory (routingData P.M.base e))
    (target : ResidueData.BSourceRootedHistory (routingData P.M.base e))
    (hit : ResidueData.SourceHit (routingData P.M.base e) incoming target.raw) :
    ∃ Y d, PhysicalZeroCenter P.M.base e Y d := by
  let D := routingData P.M.base e
  let r := actualSourceHitState P.M.base e incoming target hit
  have hsplit := actual_cm_sourceHit_early_or_live G boundaryPure boundaryMixed
    e HD hInactive hMixed hNotch incoming target hit
  change (∃ Y d, PhysicalZeroCenter P.M.base e Y d) ∨
    (0 < physicalHeight P.M.base e r ∧
      0 < physicalHeight P.M.base e (D.b r) ∧
      0 < physicalHeight P.M.base e (D.c r) ∧
      currentSelector P.M.base e r = 1 ∧
      currentSelector P.M.base e (D.b r) = 1 ∧
      currentSelector P.M.base e (D.c r) = 1 ∧
      ∃ i j k,
        L5A2C4OR5.HerzogLShapeDomain HD i j ∧
        gridResidue P.M.base e i j = r ∧
        L5A2C4OR13.CanonicalLocation.Holds HD k i j ∧
        (k = .ordinary ∨ k = .upperRight ∨ k = .bottomTop) ∧
        0 < D.u (D.c r) ∧ D.u (D.c r) ≤ H0 P.M.base e ∧
        H0 P.M.base e < c1 P.M.base e) at hsplit
  rcases hsplit with hzero | hlive
  · exact hzero
  · rcases hlive with ⟨hrpos, hbpos, hcpos, hrOne, hbOne, hcOne,
      i, j, k, hij, hres, hk, hloc, hwpos, hwH0, hH0c1⟩
    have hs := actual_sourceHit_sourceTarget_cross P.M.base e incoming target hit
    change D.IsBranch r ∧ D.u r = 0 ∧ D.v r = 0 ∧
      D.u (D.c r) = D.v (D.b r) ∧ 0 < D.u (D.c r) at hs
    have hbdef : D.b r = r + routingB P.M.base e := rfl
    have hcdef : D.c r = r + routingC P.M.base e := rfl
    rw [hbdef] at hbpos hbOne
    rw [hcdef] at hcpos hcOne
    have hshadow := actual_cm_live_shadow_packet P.M.base e HD r
      hs.2.1 hs.2.2.1 hrpos hbpos hcpos hrOne hbOne hcOne
    let xi := r - (routingM P.M.base e : ℕ)
    change tailBCarry P.M.base e xi = 0 ∧
      tailCCarry P.M.base e xi = 0 ∧ _ at hshadow
    obtain ⟨_hxiB, _hxiC, si, sj, sk, _hsij, _hsres, _hsk, _hsloc,
      _hdiag, hh⟩ := hshadow
    let Q := r + routingC P.M.base e + routingB P.M.base e
    let w := D.u (D.c r)
    let h := tailBCarry P.M.base e (xi + routingC P.M.base e)
    have hR := actual_cm_live_candidate_transport P.M.base e r hcpos hcOne
    change rawCandidate P.M.base e 1 Q =
      (physicalHeight P.M.base e Q : ℤ) + w - h at hR
    have hQ : Q = D.b (D.c r) := by
      dsimp only [Q]
      rfl
    have hw : 0 < w := by exact hwpos
    have hwcap : w ≤ H0 P.M.base e := by exact hwH0
    have hh' : h = 0 ∨ h = c1 P.M.base e := by exact hh
    exact sourceHitLocalReduction_zeroCenter P.M.base e Q h w
      (H0 P.M.base e) (c1 P.M.base e) hh' hw hwcap hH0c1 hR

/-- The frozen R8 unit normalization, specialized to the zero-center now
constructed from the actual mixed surviving-notch source hit. -/
theorem actual_cm_sourceHit_unit_normalization {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData P.M.base e)
    (hInactive : LocalSignature P.M
      (c1 P.M.base e * weights P.M.base (e 0)) 2 2)
    (hMixed : MixedOrientation G boundaryPure boundaryMixed)
    (hNotch : SurvivingNotch P.M.base e HD)
    (incoming : ResidueData.RawHistory (routingData P.M.base e))
    (target : ResidueData.BSourceRootedHistory (routingData P.M.base e))
    (hit : ResidueData.SourceHit (routingData P.M.base e) incoming target.raw) :
    ∃ Y d,
      PhysicalZeroCenter P.M.base e Y d ∧
      currentSelector P.M.base e (unitZeroCenter P.M.base e Y d) = 1 ∧
      physicalHeight P.M.base e (unitZeroCenter P.M.base e Y d) = 0 ∧
      unitZeroCenter P.M.base e Y d - (routingM P.M.base e : ℕ) =
        zeroCenterShadow P.M.base e Y d ∧
      RawMinimizers P.M.base e (unitZeroCenter P.M.base e Y d) = {1} := by
  obtain ⟨Y, d, hzero⟩ := actual_cm_sourceHit_physicalZeroCenter G
    boundaryPure boundaryMixed e HD hInactive hMixed hNotch incoming target hit
  exact ⟨Y, d, hzero, actual_unit_zeroCenter_normalization P.M.base e hzero⟩

end NS25Lean.L5A2C4OR15
