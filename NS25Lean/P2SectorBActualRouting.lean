import NS25Lean.P2SectorBRouting
import NS25Lean.P2ReindexSectors

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B3

open FourGeneratedBridge CombinatorialCore ChosenBase

variable {Gamma H : NumericalSemigroup}

/-- A sink of the concrete normalized Apéry routing graph whose associated
pseudo-Frobenius element lies in the ambient numerical semigroup.  This is a
proper refinement of the full sink type; no equality of the two is asserted. -/
def ActualSink (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) :=
  {r : ZMod a //
    let D := (I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)
    D.IsSink r ∧ I.aperyRepresentative a r - a ∈ H.asRelativeIdeal}

/-- Cardinality of the actual/integral sink subtype. -/
noncomputable def actualSinkCount (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) : ℕ :=
  Nat.card (ActualSink I a b c hbH hcH)

/-- Concrete actual sinks are exactly the integral socle of the normalized
relative ideal.  Full normalized sinks continue to classify all
pseudo-Frobenius elements. -/
noncomputable def actualSinkEquivIntegralSocle
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c)
    (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0) :
    ActualSink I a b c hbH hcH ≃ {w // IsIntegralSocle I w} where
  toFun r := by
    let D := (I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)
    have hsink : D.IsSink r.val := r.property.1
    have hpf : I.IsPseudoFrobenius (I.aperyRepresentative a r.val - a) :=
      (I.concrete_isSink_iff_isPseudoFrobenius
        a b c hgen haH hbH hcH hb hc r.val).1 hsink
    exact ⟨I.aperyRepresentative a r.val - a, r.property.2, hpf.1, hpf.2⟩
  invFun w := by
    have hpf : I.IsPseudoFrobenius w.val :=
      isIntegralSocle_isPseudoFrobenius I w.property
    refine ⟨(w.val + a : ZMod a), ?_, ?_⟩
    · exact (I.concrete_isSink_iff_isPseudoFrobenius
        a b c hgen haH hbH hcH hb hc (w.val + a : ZMod a)).2 (by
          rw [I.aperyRepresentative_sub_modulus_eq_of_isPseudoFrobenius
            a b c hgen hpf]
          exact hpf)
    · rw [I.aperyRepresentative_sub_modulus_eq_of_isPseudoFrobenius
        a b c hgen hpf]
      exact w.property.1
  left_inv r := by
    apply Subtype.ext
    change ((I.aperyRepresentative a (r.val : ZMod a) - a : ℤ) : ZMod a) +
      (a : ZMod a) = r.val
    rw [Int.cast_sub, Int.cast_natCast, I.aperyRepresentative_mod]
    simp
  right_inv w := by
    apply Subtype.ext
    exact I.aperyRepresentative_sub_modulus_eq_of_isPseudoFrobenius
      a b c hgen (isIntegralSocle_isPseudoFrobenius I w.property)

theorem actualSinkCount_eq_integralSocle_card
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c)
    (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0) :
    actualSinkCount I a b c hbH hcH = Nat.card {w // IsIntegralSocle I w} := by
  exact Nat.card_congr
    (actualSinkEquivIntegralSocle I a b c hgen haH hbH hcH hb hc)

/-- MATERIAL checkpoint isolated from the full normalized sink count: the
actual/integral sinks have exactly the type of the original semigroup. -/
theorem exists_exact_actualSinkCount (B : Data Gamma) :
    let n₁ := (B.tailDegrees 0).val
    let n₂ := (B.tailDegrees 1).val
    let n₃ := (B.tailDegrees 2).val
    let h4 := L5A2B2.chosenBase_minimalFour B
    let d := tailGcd n₁ n₂ n₃
    let a := n₁ / d
    let b := n₂ / d
    let c := n₃ / d
    let Hbar := normalizedSemigroup n₁ n₂ n₃ h4.n₁_pos
    let I := normalizedTailIdeal Gamma B.q.val n₁ n₂ n₃ h4
    ∃ ha : 0 < a,
      letI : NeZero a := ⟨Nat.ne_of_gt ha⟩
      ∃ hbH : b ∈ Hbar, ∃ hcH : c ∈ Hbar,
        actualSinkCount I a b c hbH hcH = Gamma.asRelativeIdeal.idealType := by
  dsimp only
  let n₁ := (B.tailDegrees 0).val
  let n₂ := (B.tailDegrees 1).val
  let n₃ := (B.tailDegrees 2).val
  let h4 := L5A2B2.chosenBase_minimalFour B
  let d := tailGcd n₁ n₂ n₃
  let a := n₁ / d
  let b := n₂ / d
  let c := n₃ / d
  let Hbar := normalizedSemigroup n₁ n₂ n₃ h4.n₁_pos
  let I := normalizedTailIdeal Gamma B.q.val n₁ n₂ n₃ h4
  have ha : 0 < a := quotient_pos_of_dvd h4.n₁_pos (tailGcd_dvd n₁ n₂ n₃).1
  refine ⟨ha, ?_⟩
  letI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  have hmin : Hbar.IsMinimallyGeneratedByThree a b c := normalizedSemigroup_minimal h4
  have hbH : b ∈ Hbar := (NumericalSemigroup.mem_generatedByThree_iff hmin.1).2
    (AddSubmonoid.subset_closure (by simp))
  have hcH : c ∈ Hbar := (NumericalSemigroup.mem_generatedByThree_iff hmin.1).2
    (AddSubmonoid.subset_closure (by simp))
  have haH : a ∈ Hbar := (NumericalSemigroup.mem_generatedByThree_iff hmin.1).2
    (AddSubmonoid.subset_closure (by simp))
  have hb : b ≠ 0 := by
    intro hz
    apply hmin.2.2.1
    rw [hz]
    exact AddSubmonoid.zero_mem _
  have hc : c ≠ 0 := by
    intro hz
    apply hmin.2.2.2
    rw [hz]
    exact AddSubmonoid.zero_mem _
  refine ⟨hbH, hcH, ?_⟩
  calc
    actualSinkCount I a b c hbH hcH = Nat.card {w // IsIntegralSocle I w} :=
      actualSinkCount_eq_integralSocle_card I a b c hmin.1 haH hbH hcH hb hc
    _ = Nat.card {w // IsSocle Gamma.toAddSubmonoid
        (generatedThree n₁ n₂ n₃) B.q.val w} :=
      (normalizedTail_socle_card Gamma B.q.val n₁ n₂ n₃ h4).symm
    _ = Gamma.asRelativeIdeal.idealType :=
      (fourGenerated_idealType_eq_natCard_socle Gamma B.q.val n₁ n₂ n₃
        h4.m_pos h4.generated).symm

/-- Route-3 checkpoint.  The normalized graph is retained, while its
actual/integral sink subtype has cardinality exactly the original semigroup
type.  The theorem deliberately keeps the full `D.sinkCount` separate. -/
theorem exists_actualRouting_with_exact_actualSinkCount (B : Data Gamma) :
    let n₁ := (B.tailDegrees 0).val
    let n₂ := (B.tailDegrees 1).val
    let n₃ := (B.tailDegrees 2).val
    let h4 := L5A2B2.chosenBase_minimalFour B
    let d := tailGcd n₁ n₂ n₃
    let a := n₁ / d
    let b := n₂ / d
    let c := n₃ / d
    let Hbar := normalizedSemigroup n₁ n₂ n₃ h4.n₁_pos
    let I := normalizedTailIdeal Gamma B.q.val n₁ n₂ n₃ h4
    ∃ ha : 0 < a,
      letI : NeZero a := ⟨Nat.ne_of_gt ha⟩
      ∃ hbH : b ∈ Hbar, ∃ hcH : c ∈ Hbar,
        let D := (I.toAperyStepData a b c hbH hcH).toResidueData
          (I.toAperyStepData_isValid a b c hbH hcH)
        D.sourceCount = L2B.sourceCount B ∧
        actualSinkCount I a b c hbH hcH = Gamma.asRelativeIdeal.idealType ∧
        D.sinkCount = I.idealType ∧
        actualSinkCount I a b c hbH hcH ≤ D.sinkCount := by
  dsimp only
  let n₁ := (B.tailDegrees 0).val
  let n₂ := (B.tailDegrees 1).val
  let n₃ := (B.tailDegrees 2).val
  let h4 := L5A2B2.chosenBase_minimalFour B
  let d := tailGcd n₁ n₂ n₃
  let a := n₁ / d
  let b := n₂ / d
  let c := n₃ / d
  let Hbar := normalizedSemigroup n₁ n₂ n₃ h4.n₁_pos
  let I := normalizedTailIdeal Gamma B.q.val n₁ n₂ n₃ h4
  have ha : 0 < a := quotient_pos_of_dvd h4.n₁_pos (tailGcd_dvd n₁ n₂ n₃).1
  refine ⟨ha, ?_⟩
  letI : NeZero a := ⟨Nat.ne_of_gt ha⟩
  have hmin : Hbar.IsMinimallyGeneratedByThree a b c := normalizedSemigroup_minimal h4
  have haH : a ∈ Hbar := (NumericalSemigroup.mem_generatedByThree_iff hmin.1).2
    (AddSubmonoid.subset_closure (by simp))
  have hbH : b ∈ Hbar := (NumericalSemigroup.mem_generatedByThree_iff hmin.1).2
    (AddSubmonoid.subset_closure (by simp))
  have hcH : c ∈ Hbar := (NumericalSemigroup.mem_generatedByThree_iff hmin.1).2
    (AddSubmonoid.subset_closure (by simp))
  have hb : b ≠ 0 := by
    intro hz
    apply hmin.2.2.1
    rw [hz]
    exact AddSubmonoid.zero_mem _
  have hc : c ≠ 0 := by
    intro hz
    apply hmin.2.2.2
    rw [hz]
    exact AddSubmonoid.zero_mem _
  refine ⟨hbH, hcH, ?_, ?_, ?_, ?_⟩
  · calc
      _ = I.generatorCount :=
        I.concrete_sourceCount_eq_generatorCount a b c hmin.1 hbH hcH hb hc
      _ = tailGeneratorCount (generatedThree n₁ n₂ n₃)
          (aperyTail Gamma.toAddSubmonoid (generatedThree n₁ n₂ n₃) B.q.val) :=
        normalizedTail_generatorCount Gamma B.q.val n₁ n₂ n₃ h4
      _ = L2B.sourceCount B := by
        rw [L2B.sourceCount, Data.K, L5A2B2.chosenBase_tail_eq_generatedThree B]
  · calc
      actualSinkCount I a b c hbH hcH =
          Nat.card {w // IsIntegralSocle I w} :=
        actualSinkCount_eq_integralSocle_card I a b c hmin.1 haH hbH hcH hb hc
      _ = Nat.card {w // IsSocle Gamma.toAddSubmonoid
          (generatedThree n₁ n₂ n₃) B.q.val w} :=
        (normalizedTail_socle_card Gamma B.q.val n₁ n₂ n₃ h4).symm
      _ = Gamma.asRelativeIdeal.idealType :=
        (fourGenerated_idealType_eq_natCard_socle Gamma B.q.val n₁ n₂ n₃
          h4.m_pos h4.generated).symm
  · exact I.concrete_sinkCount_eq_idealType a b c hmin.1 haH hbH hcH hb hc
  · calc
      actualSinkCount I a b c hbH hcH = Nat.card {w // IsIntegralSocle I w} :=
        actualSinkCount_eq_integralSocle_card I a b c hmin.1 haH hbH hcH hb hc
      _ ≤ I.idealType := natCard_integralSocle_le_idealType I a b c hmin.1
      _ = _ := (I.concrete_sinkCount_eq_idealType
        a b c hmin.1 haH hbH hcH hb hc).symm

/-- Zero killed-component count means every actual component is genuine. -/
theorem all_components_genuine_of_killedCount_eq_zero
    (M : L2B.MultiplicityBase Gamma) (h : ℕ)
    (hk : L2B.killedCount M h = 0) :
    ∀ C : L2B.FiberComponent M.base h, ¬L2B.BoundaryKilled M h C := by
  intro C hC
  have hpos : 0 < Nat.card
      {E : L2B.FiberComponent M.base h // L2B.BoundaryKilled M h E} :=
    Nat.card_pos_iff.mpr ⟨⟨C, hC⟩, inferInstance⟩
  change Nat.card
    {E : L2B.FiberComponent M.base h // L2B.BoundaryKilled M h E} = 0 at hk
  omega

/-- Everything presently derivable from the thin actual Sector-B signature:
two distinct positive degrees, two components at each degree, and no killed
component at either degree. -/
theorem sectorB_actualFiberData (P : L5A1.P2Data Gamma)
    (hB : L5A1.SectorB P.M) :
    ∃ h g, h ≠ g ∧ L5A1.positiveDegrees P.M = {h, g} ∧
      L2B.componentCount P.M.base h = 2 ∧
      L2B.componentCount P.M.base g = 2 ∧
      L2B.killedCount P.M h = 0 ∧
      L2B.killedCount P.M g = 0 ∧
      (∀ C : L2B.FiberComponent P.M.base h, ¬L2B.BoundaryKilled P.M h C) ∧
      (∀ C : L2B.FiberComponent P.M.base g, ¬L2B.BoundaryKilled P.M g C) := by
  rcases hB with ⟨h, g, hne, hdegrees, hh, hg⟩
  refine ⟨h, g, hne, hdegrees, hh.1, hg.1, hh.2, hg.2, ?_, ?_⟩
  · exact all_components_genuine_of_killedCount_eq_zero P.M h hh.2
  · exact all_components_genuine_of_killedCount_eq_zero P.M g hg.2

end NS25Lean.L5A2B3
