import NS25Lean.P2SectorCNonsymmetricDownstream
import NS25Lean.AperyConstruction

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4H

open FourGeneratedBridge CombinatorialCore ChosenBase
open L2B L5A1 L5A2C4C

variable {Gamma H : NumericalSemigroup}

abbrev tailValue (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) : ℕ :=
  (B.tailDegrees (e i)).val

private theorem tail_range_reindexed (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Set.range (fun i : Fin 3 => tailValue B e i) =
      Set.range (fun i : Fin 3 => (B.tailDegrees i).val) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩

theorem chosenBase_tail_eq_generatedThree (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    B.H = generatedThree (tailValue B e 0) (tailValue B e 1) (tailValue B e 2) := by
  rw [generatedThree]
  change AddSubmonoid.closure (Set.range (fun i : Fin 3 => (B.tailDegrees i).val)) = _
  rw [← tail_range_reindexed B e]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩
    · exact ⟨2, hx.symm⟩

private theorem tail_index_ne_pivot (B : Data Gamma) (i : Fin 3) :
    B.order i.succ ≠ B.pivot := by
  intro h
  have hz : B.order 0 = B.pivot := by simp [Data.order]
  exact Fin.succ_ne_zero i (B.order.injective (h.trans hz.symm))

private theorem tail_index_ne (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    {i j : Fin 3} (hij : i ≠ j) : B.order (e i).succ ≠ B.order (e j).succ := by
  intro h
  have hs := B.order.injective h
  have he : e i = e j := Fin.succ_inj.mp hs
  exact hij (e.injective he)

private theorem generator_mem_excluded (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i : Fin 3) {j : Fin 3} (hji : j ≠ i) :
    tailValue B e j ∈ AddSubmonoid.closure
      ((fun k => (B.family k).val) '' {k | k ≠ B.order (e i).succ}) := by
  apply AddSubmonoid.subset_closure
  refine ⟨B.order (e j).succ, ?_, rfl⟩
  exact tail_index_ne B e hji

private theorem pivot_mem_excluded (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    B.q.val ∈ AddSubmonoid.closure
      ((fun k => (B.family k).val) '' {k | k ≠ B.order (e i).succ}) := by
  apply AddSubmonoid.subset_closure
  refine ⟨B.pivot, ?_, rfl⟩
  exact (tail_index_ne_pivot B (e i)).symm

private theorem generatedThree_le_excluded (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) :
    generatedThree B.q.val (tailValue B e j) (tailValue B e k) ≤
      AddSubmonoid.closure
        ((fun x => (B.family x).val) '' {x | x ≠ B.order (e i).succ}) := by
  apply AddSubmonoid.closure_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact pivot_mem_excluded B e i
  · exact generator_mem_excluded B e i hji
  · exact generator_mem_excluded B e i hki

/-- The chosen pivot followed by any explicit `Fin 3` reindexing is an actual
minimal four-generator presentation. -/
theorem chosenBase_minimalFour (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    IsMinimallyGeneratedByFour Gamma B.q.val
      (tailValue B e 0) (tailValue B e 1) (tailValue B e 2) := by
  let n0 := tailValue B e 0
  let n1 := tailValue B e 1
  let n2 := tailValue B e 2
  have hall : Set.range (fun i => (B.degrees i).val) =
      ({B.q.val, n0, n1, n2} : Set ℕ) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [n0, n1, n2, Data.tailDegrees]
      · let k := e.symm j
        have hj : j = e k := by simp [k]
        rw [hj]
        have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hk with hk | hk | hk
        · rw [hk]; exact Or.inr (Or.inl rfl)
        · rw [hk]; exact Or.inr (Or.inr (Or.inl rfl))
        · rw [hk]; exact Or.inr (Or.inr (Or.inr rfl))
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx | hx
      · exact ⟨0, by simpa [Data.tailDegrees] using hx.symm⟩
      · refine ⟨(e 0).succ, ?_⟩
        change tailValue B e 0 = x
        exact hx.symm
      · refine ⟨(e 1).succ, ?_⟩
        change tailValue B e 1 = x
        exact hx.symm
      · refine ⟨(e 2).succ, ?_⟩
        change tailValue B e 2 = x
        exact hx.symm
  have hgen : Gamma.toAddSubmonoid = generatedFour B.q.val n0 n1 n2 := by
    rw [generatedFour]
    exact B.degrees_generate_nat.symm.trans (congrArg AddSubmonoid.closure hall)
  refine { generated := hgen
           m_pos := B.q_positive
           n₁_pos := B.degrees_positive (e 0).succ
           n₂_pos := B.degrees_positive (e 1).succ
           n₃_pos := B.degrees_positive (e 2).succ
           m_minimal := ?_
           n₁_minimal := ?_
           n₂_minimal := ?_
           n₃_minimal := ?_ }
  · rw [← chosenBase_tail_eq_generatedThree B e]
    intro hm
    apply B.minimal B.pivot
    apply (show B.H ≤ AddSubmonoid.closure
      ((fun k => (B.family k).val) '' {k | k ≠ B.pivot}) by
        apply AddSubmonoid.closure_le.mpr
        rintro _ ⟨i, rfl⟩
        apply AddSubmonoid.subset_closure
        exact ⟨B.order i.succ, tail_index_ne_pivot B i, rfl⟩) hm
  · intro hn
    exact B.minimal (B.order (e 0).succ)
      (generatedThree_le_excluded B e 0 1 2 (by decide) (by decide) hn)
  · intro hn
    exact B.minimal (B.order (e 1).succ)
      (generatedThree_le_excluded B e 1 0 2 (by decide) (by decide) hn)
  · intro hn
    exact B.minimal (B.order (e 2).succ)
      (generatedThree_le_excluded B e 2 0 1 (by decide) (by decide) hn)

abbrev routingN1 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := tailValue B e 0
abbrev routingN2 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := tailValue B e 1
abbrev routingN3 (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := tailValue B e 2
abbrev routingD (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  tailGcd (routingN1 B e) (routingN2 B e) (routingN3 B e)
abbrev routingA (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := routingN1 B e / routingD B e
abbrev routingB (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := routingN2 B e / routingD B e
abbrev routingC (B : Data Gamma) (e : Fin 3 ≃ Fin 3) := routingN3 B e / routingD B e
abbrev routingH (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  normalizedSemigroup (routingN1 B e) (routingN2 B e) (routingN3 B e)
    (chosenBase_minimalFour B e).n₁_pos
abbrev routingI (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  normalizedTailIdeal Gamma B.q.val (routingN1 B e) (routingN2 B e) (routingN3 B e)
    (chosenBase_minimalFour B e)

theorem routingA_pos (B : Data Gamma) (e : Fin 3 ≃ Fin 3) : 0 < routingA B e :=
  quotient_pos_of_dvd (chosenBase_minimalFour B e).n₁_pos
    (tailGcd_dvd (routingN1 B e) (routingN2 B e) (routingN3 B e)).1

abbrev routingHB (B : Data Gamma) (e : Fin 3 ≃ Fin 3) : routingB B e ∈ routingH B e :=
  (NumericalSemigroup.mem_generatedByThree_iff
    (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
      (AddSubmonoid.subset_closure (by simp))

abbrev routingHC (B : Data Gamma) (e : Fin 3 ≃ Fin 3) : routingC B e ∈ routingH B e :=
  (NumericalSemigroup.mem_generatedByThree_iff
    (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1).2
      (AddSubmonoid.subset_closure (by simp))

noncomputable def routingData (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ResidueData (ZMod (routingA B e)) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact ((routingI B e).toAperyStepData (routingA B e) (routingB B e) (routingC B e)
    (routingHB B e) (routingHC B e)).toResidueData
      ((routingI B e).toAperyStepData_isValid (routingA B e) (routingB B e)
        (routingC B e) (routingHB B e) (routingHC B e))

/-- H1: all normalized routing data and its source/full-sink bookkeeping are
constructed from the chosen base and the explicit coherent reindexing. -/
theorem exists_actualRoutingCore (P : P2Data Gamma) (e : Fin 3 ≃ Fin 3) :
    ∃ ha : 0 < routingA P.M.base e,
      letI : NeZero (routingA P.M.base e) := ⟨Nat.ne_of_gt ha⟩
      let D := routingData P.M.base e
      D.sourceCount = P.sourceCount ∧
      D.sinkCount = (routingI P.M.base e).idealType ∧
      D.edgeCount + D.sinkCount = Fintype.card (ZMod (routingA P.M.base e)) + D.branchCount ∧
      D.edgeCount + D.sourceCount = Fintype.card (ZMod (routingA P.M.base e)) + D.mergeCount := by
  let B := P.M.base
  refine ⟨routingA_pos B e, ?_⟩
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let D := routingData B e
  have hmin := normalizedSemigroup_minimal (chosenBase_minimalFour B e)
  have haH : routingA B e ∈ routingH B e :=
    (NumericalSemigroup.mem_generatedByThree_iff hmin.1).2
      (AddSubmonoid.subset_closure (by simp))
  have hb : routingB B e ≠ 0 := by
    intro hz; apply hmin.2.2.1
    simpa only [routingB, hz] using (AddSubmonoid.zero_mem _)
  have hc : routingC B e ≠ 0 := by
    intro hz; apply hmin.2.2.2
    simpa only [routingC, hz] using (AddSubmonoid.zero_mem _)
  refine ⟨?_, ?_, D.outgoing_edge_count, D.incoming_edge_count⟩
  · calc
      D.sourceCount = (routingI B e).generatorCount :=
        (routingI B e).concrete_sourceCount_eq_generatorCount
          (routingA B e) (routingB B e) (routingC B e) hmin.1
          (routingHB B e) (routingHC B e) hb hc
      _ = tailGeneratorCount
          (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e))
          (aperyTail Gamma.toAddSubmonoid
            (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e)) B.q.val) :=
        normalizedTail_generatorCount Gamma B.q.val _ _ _ (chosenBase_minimalFour B e)
      _ = P.sourceCount := by
        rw [P2Data.sourceCount, L2B.sourceCount, Data.K,
          chosenBase_tail_eq_generatedThree B e]
  · exact (routingI B e).concrete_sinkCount_eq_idealType
      (routingA B e) (routingB B e) (routingC B e) hmin.1 haH
      (routingHB B e) (routingHC B e) hb hc

def ActualSink (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) :=
  {r : ZMod a //
    let D := (I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)
    D.IsSink r ∧ I.aperyRepresentative a r - a ∈ H.asRelativeIdeal}

def FakeSink (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) :=
  {r : ZMod a //
    let D := (I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)
    D.IsSink r ∧ I.aperyRepresentative a r - a ∉ H.asRelativeIdeal}

def FullSink (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) :=
  {r : ZMod a // ((I.toAperyStepData a b c hbH hcH).toResidueData
    (I.toAperyStepData_isValid a b c hbH hcH)).IsSink r}

noncomputable def actualSinkCount (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) := Nat.card (ActualSink I a b c hbH hcH)

noncomputable def fakeSinkCount (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) := Nat.card (FakeSink I a b c hbH hcH)

noncomputable def actualSinkEquivIntegralSocle
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hgen : H.IsGeneratedByThree a b c)
    (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H)
    (hb : b ≠ 0) (hc : c ≠ 0) :
    ActualSink I a b c hbH hcH ≃ {w // IsIntegralSocle I w} where
  toFun r := by
    have hpf := (I.concrete_isSink_iff_isPseudoFrobenius
      a b c hgen haH hbH hcH hb hc r.val).1 r.property.1
    exact ⟨I.aperyRepresentative a r.val - a, r.property.2, hpf.1, hpf.2⟩
  invFun w := by
    have hpf := isIntegralSocle_isPseudoFrobenius I w.property
    refine ⟨(w.val + a : ZMod a), ?_, ?_⟩
    · apply (I.concrete_isSink_iff_isPseudoFrobenius
        a b c hgen haH hbH hcH hb hc _).2
      rwa [I.aperyRepresentative_sub_modulus_eq_of_isPseudoFrobenius a b c hgen hpf]
    · rw [I.aperyRepresentative_sub_modulus_eq_of_isPseudoFrobenius a b c hgen hpf]
      exact w.property.1
  left_inv r := by
    apply Subtype.ext
    change ((I.aperyRepresentative a r.val - a : ℤ) : ZMod a) + (a : ZMod a) = r.val
    rw [Int.cast_sub, Int.cast_natCast, I.aperyRepresentative_mod]
    simp
  right_inv w := by
    apply Subtype.ext
    exact I.aperyRepresentative_sub_modulus_eq_of_isPseudoFrobenius
      a b c hgen (isIntegralSocle_isPseudoFrobenius I w.property)

theorem fullSink_actual_or_fake (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) (r : ZMod a)
    (hr : ((I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)).IsSink r) :
    (∃ x : ActualSink I a b c hbH hcH, x.val = r) ∨
      (∃ x : FakeSink I a b c hbH hcH, x.val = r) := by
  by_cases hmem : I.aperyRepresentative a r - a ∈ H.asRelativeIdeal
  · exact Or.inl ⟨⟨r, hr, hmem⟩, rfl⟩
  · exact Or.inr ⟨⟨r, hr, hmem⟩, rfl⟩

noncomputable def fullSinkEquivActualSumFake
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) :
    FullSink I a b c hbH hcH ≃
      Sum (ActualSink I a b c hbH hcH) (FakeSink I a b c hbH hcH) := by
  classical
  exact
    { toFun := fun r =>
        if hmem : I.aperyRepresentative a r.val - a ∈ H.asRelativeIdeal
        then Sum.inl ⟨r.val, r.property, hmem⟩
        else Sum.inr ⟨r.val, r.property, hmem⟩
      invFun := fun x => match x with
        | Sum.inl r => ⟨r.val, r.property.1⟩
        | Sum.inr r => ⟨r.val, r.property.1⟩
      left_inv := by
        intro r
        apply Subtype.ext
        by_cases hmem : I.aperyRepresentative a r.val - a ∈ H.asRelativeIdeal
        · simp [hmem]
        · simp [hmem]
      right_inv := by
        intro x
        rcases x with r | r
        · have hr : (⟨r.val, r.property.1, r.property.2⟩ :
              ActualSink I a b c hbH hcH) = r := by
            apply Subtype.ext
            rfl
          simp [r.property.2, hr]
        · have hr : (⟨r.val, r.property.1, r.property.2⟩ :
              FakeSink I a b c hbH hcH) = r := by
            apply Subtype.ext
            rfl
          simp [r.property.2, hr] }

theorem fullSinkCount_eq_actual_add_fake
    (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hbH : b ∈ H) (hcH : c ∈ H) :
    ((I.toAperyStepData a b c hbH hcH).toResidueData
      (I.toAperyStepData_isValid a b c hbH hcH)).sinkCount =
      actualSinkCount I a b c hbH hcH + fakeSinkCount I a b c hbH hcH := by
  letI : Finite (ActualSink I a b c hbH hcH) := Subtype.finite
  letI : Finite (FakeSink I a b c hbH hcH) := Subtype.finite
  exact (Nat.card_congr (fullSinkEquivActualSumFake I a b c hbH hcH)).trans
    Nat.card_sum

/-- H2: actual sinks count the original semigroup type, while the full sink
count remains the (possibly larger) normalized ideal type. -/
theorem exists_actualRouting_with_exact_actualSinkCount
    (P : P2Data Gamma) (e : Fin 3 ≃ Fin 3) :
    ∃ ha : 0 < routingA P.M.base e,
      letI : NeZero (routingA P.M.base e) := ⟨Nat.ne_of_gt ha⟩
      actualSinkCount (routingI P.M.base e) (routingA P.M.base e)
        (routingB P.M.base e) (routingC P.M.base e)
        (routingHB P.M.base e) (routingHC P.M.base e) = Gamma.asRelativeIdeal.idealType ∧
      (routingData P.M.base e).sinkCount = (routingI P.M.base e).idealType := by
  let B := P.M.base
  refine ⟨routingA_pos B e, ?_⟩
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmin := normalizedSemigroup_minimal (chosenBase_minimalFour B e)
  have haH : routingA B e ∈ routingH B e :=
    (NumericalSemigroup.mem_generatedByThree_iff hmin.1).2
      (AddSubmonoid.subset_closure (by simp))
  have hb : routingB B e ≠ 0 := by
    intro hz; apply hmin.2.2.1
    simpa only [routingB, hz] using (AddSubmonoid.zero_mem _)
  have hc : routingC B e ≠ 0 := by
    intro hz; apply hmin.2.2.2
    simpa only [routingC, hz] using (AddSubmonoid.zero_mem _)
  constructor
  · calc
      actualSinkCount (routingI B e) (routingA B e) (routingB B e) (routingC B e)
          (routingHB B e) (routingHC B e) =
          Nat.card {w // IsIntegralSocle (routingI B e) w} :=
        Nat.card_congr (actualSinkEquivIntegralSocle (routingI B e)
          (routingA B e) (routingB B e) (routingC B e) hmin.1 haH
          (routingHB B e) (routingHC B e) hb hc)
      _ = Nat.card {w // IsSocle Gamma.toAddSubmonoid
          (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e)) B.q.val w} :=
        (normalizedTail_socle_card Gamma B.q.val _ _ _ (chosenBase_minimalFour B e)).symm
      _ = Gamma.asRelativeIdeal.idealType :=
        (fourGenerated_idealType_eq_natCard_socle Gamma B.q.val _ _ _
          (chosenBase_minimalFour B e).m_pos (chosenBase_minimalFour B e).generated).symm
  · exact (routingI B e).concrete_sinkCount_eq_idealType
      (routingA B e) (routingB B e) (routingC B e) hmin.1 haH
      (routingHB B e) (routingHC B e) hb hc

/-! ### H3: the actual eta/residue dictionary -/

def normalizedGrid (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (n i j : ℕ) : ℕ :=
  n * routingA B e + i * routingB B e + j * routingC B e

def gridResidue (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    ZMod (routingA B e) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact i * (routingB B e : ZMod (routingA B e)) +
    j * (routingC B e : ZMod (routingA B e))

/-- Raw coordinates scale to the frozen C4C degree.  This equality is before
canonical residue reduction. -/
theorem normalizedGrid_scale (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (n i j : ℕ) :
    routingD B e * normalizedGrid B e n i j = gridDegree B e n i j := by
  obtain ⟨h0, h1, h2⟩ := tailGcd_dvd (routingN1 B e) (routingN2 B e) (routingN3 B e)
  have hd0 := Nat.mul_div_cancel' h0
  have hd1 := Nat.mul_div_cancel' h1
  have hd2 := Nat.mul_div_cancel' h2
  calc
    routingD B e * normalizedGrid B e n i j =
        n * (routingD B e * routingA B e) +
        i * (routingD B e * routingB B e) +
        j * (routingD B e * routingC B e) := by
          simp only [normalizedGrid]; ring
    _ = n * routingN1 B e + i * routingN2 B e + j * routingN3 B e := by
          rw [hd0, hd1, hd2]
    _ = gridDegree B e n i j := rfl

private theorem normalizedGrid_mem_iff_gridDegree_mem
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (n i j : ℕ) :
    (normalizedGrid B e n i j : ℤ) ∈ routingI B e ↔
      gridDegree B e n i j ∈ B.K := by
  let h4 := chosenBase_minimalFour B e
  have hmem := (buildTailScaling Gamma B.q.val (routingN1 B e)
    (routingN2 B e) (routingN3 B e) h4).mem_ideal_nat (normalizedGrid B e n i j)
  change ((normalizedGrid B e n i j : ℕ) : ℤ) ∈
      normalizedTailIdeal Gamma B.q.val (routingN1 B e) (routingN2 B e)
        (routingN3 B e) h4 ↔ _
  change ((normalizedGrid B e n i j : ℕ) : ℤ) ∈
      (buildTailScaling Gamma B.q.val (routingN1 B e) (routingN2 B e)
        (routingN3 B e) h4).ideal ↔ _
  rw [hmem]
  change routingD B e * normalizedGrid B e n i j ∈
      aperyTail Gamma.toAddSubmonoid
        (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e)) B.q.val ↔ _
  rw [normalizedGrid_scale B e]
  simpa [Data.K, chosenBase_tail_eq_generatedThree B e]

/-- The C4C eta threshold and normalized ideal membership are the same
actual statement. -/
theorem normalizedGrid_mem_iff_eta_le
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (n i j : ℕ) :
    (normalizedGrid B e n i j : ℤ) ∈ routingI B e ↔ eta B e i j ≤ n := by
  rw [normalizedGrid_mem_iff_gridDegree_mem, gridDegree_mem_K_iff_eta_le]

theorem normalizedGrid_mod (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (n i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ((normalizedGrid B e n i j : ℕ) : ZMod (routingA B e)) = gridResidue B e i j := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  simp [normalizedGrid, gridResidue]

/-- At the eta height, the raw grid point is a canonical Apéry
representative plus a uniquely determined nonnegative modulus lift. -/
theorem eta_apery_lift (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ∃ k : ℕ, (normalizedGrid B e (eta B e i j) i j : ℤ) =
      (routingI B e).aperyRepresentative (routingA B e) (gridResidue B e i j) +
        routingA B e * k := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmem : (normalizedGrid B e (eta B e i j) i j : ℤ) ∈ routingI B e :=
    (normalizedGrid_mem_iff_eta_le B e _ _ _).2 (le_refl _)
  have hmod : (((normalizedGrid B e (eta B e i j) i j : ℕ) : ℤ) :
      ZMod (routingA B e)) = gridResidue B e i j := by
    exact_mod_cast normalizedGrid_mod B e (eta B e i j) i j
  exact RelativeIdeal.exists_eq_add_mul_of_le_of_modEq (routingA B e)
    ((routingI B e).aperyRepresentative_le (routingA B e) _ hmem hmod) (by
      rw [hmod, (routingI B e).aperyRepresentative_mod])

noncomputable def gridLift (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) : ℕ :=
  by
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    exact Classical.choose (eta_apery_lift B e i j)

theorem gridLift_spec (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (normalizedGrid B e (eta B e i j) i j : ℤ) =
      (routingI B e).aperyRepresentative (routingA B e) (gridResidue B e i j) +
        routingA B e * gridLift B e i j := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact Classical.choose_spec (eta_apery_lift B e i j)

theorem gridResidue_add_b (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    gridResidue B e (i + 1) j = gridResidue B e i j + routingB B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  simp only [gridResidue, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  ac_rfl

theorem gridResidue_add_c (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    gridResidue B e i (j + 1) = gridResidue B e i j + routingC B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  simp only [gridResidue, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  ac_rfl

theorem eta_b_carry_transition (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    eta B e i j + gridLift B e (i + 1) j =
      eta B e (i + 1) j + gridLift B e i j +
        (routingData B e).u (gridResidue B e i j) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change eta B e i j + gridLift B e (i + 1) j =
    eta B e (i + 1) j + gridLift B e i j +
      (routingI B e).aperyStepQuotient (routingA B e) (routingB B e)
        (routingHB B e) (gridResidue B e i j)
  have h0 := gridLift_spec B e i j
  have h1 := gridLift_spec B e (i + 1) j
  have hs := (routingI B e).apery_step_eq (routingA B e) (routingB B e)
    (routingHB B e) (gridResidue B e i j)
  rw [← gridResidue_add_b B e] at hs
  simp only [normalizedGrid, Nat.add_mul, one_mul, Nat.cast_add, Nat.cast_mul] at h0 h1
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  nlinarith

theorem eta_c_carry_transition (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i j : ℕ) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    eta B e i j + gridLift B e i (j + 1) =
      eta B e i (j + 1) + gridLift B e i j +
        (routingData B e).v (gridResidue B e i j) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  change eta B e i j + gridLift B e i (j + 1) =
    eta B e i (j + 1) + gridLift B e i j +
      (routingI B e).aperyStepQuotient (routingA B e) (routingC B e)
        (routingHC B e) (gridResidue B e i j)
  have h0 := gridLift_spec B e i j
  have h1 := gridLift_spec B e i (j + 1)
  have hs := (routingI B e).apery_step_eq (routingA B e) (routingC B e)
    (routingHC B e) (gridResidue B e i j)
  rw [← gridResidue_add_c B e] at hs
  simp only [normalizedGrid, Nat.add_mul, one_mul, Nat.cast_add, Nat.cast_mul] at h0 h1
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  nlinarith

/-! ### H4: routing carry and exact predicates -/

theorem routing_u_nonnegative (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ZMod (routingA B e)) : 0 ≤ (routingData B e).u r := Nat.zero_le _

theorem routing_v_nonnegative (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ZMod (routingA B e)) : 0 ≤ (routingData B e).v r := Nat.zero_le _

theorem routing_b_zero_iff (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ZMod (routingA B e)) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingData B e).u r = 0 ↔
      (routingI B e).aperyRepresentative (routingA B e) (r + routingB B e) -
        routingB B e ∈ routingI B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact (routingI B e).aperyStepQuotient_eq_zero_iff_sub_mem
    (routingA B e) (routingB B e) (routingHB B e) r

theorem routing_c_zero_iff (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ZMod (routingA B e)) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingData B e).v r = 0 ↔
      (routingI B e).aperyRepresentative (routingA B e) (r + routingC B e) -
        routingC B e ∈ routingI B e := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact (routingI B e).aperyStepQuotient_eq_zero_iff_sub_mem
    (routingA B e) (routingC B e) (routingHC B e) r

theorem routing_curl (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ZMod (routingA B e)) :
    (routingData B e).u r + (routingData B e).v ((routingData B e).b r) =
      (routingData B e).v r + (routingData B e).u ((routingData B e).c r) :=
  (routingData B e).diamond r

theorem routing_predicates_exact (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ZMod (routingA B e)) :
    ((routingData B e).IsSource r ↔
      (routingData B e).u ((routingData B e).b.symm r) ≠ 0 ∧
      (routingData B e).v ((routingData B e).c.symm r) ≠ 0) ∧
    ((routingData B e).IsBranch r ↔
      (routingData B e).u r = 0 ∧ (routingData B e).v r = 0) ∧
    ((routingData B e).IsMerge r ↔
      (routingData B e).u ((routingData B e).b.symm r) = 0 ∧
      (routingData B e).v ((routingData B e).c.symm r) = 0) ∧
    ((routingData B e).IsSink r ↔
      (routingData B e).u r ≠ 0 ∧ (routingData B e).v r ≠ 0) := by
  simp [ResidueData.IsSource, ResidueData.IsBranch, ResidueData.IsMerge,
    ResidueData.IsSink]

/-! ### H5: unused merges and first-stage endpoints -/

def UnusedMergeReverseBase {R : Type*} (D : ResidueData R) (r : R) : Prop :=
  0 < D.u r ∧ 0 < D.v r ∧ D.u (D.c r) = 0 ∧ D.v (D.b r) = 0

theorem unusedMergeReverseBase_cross_eq {R : Type*} (D : ResidueData R) {r : R}
    (h : UnusedMergeReverseBase D r) : D.u (D.c r) = D.v (D.b r) := by
  rw [h.2.2.1, h.2.2.2]

theorem unusedMergeReverseBase_isMerge {R : Type*} (D : ResidueData R) {r : R}
    (h : UnusedMergeReverseBase D r) : D.IsMerge (D.branchTarget r) := by
  constructor
  · have hc := h.2.2.1
    have heq : D.b.symm (D.branchTarget r) = D.c r := by
      apply D.b.injective
      simpa [ResidueData.branchTarget] using (D.commute r).symm
    rw [heq]
    exact hc
  · have hb := h.2.2.2
    simpa [ResidueData.branchTarget] using hb

def BPositiveRunEndpoint {R : Type*} (D : ResidueData R) (start finish : R) : Prop :=
  D.IsBranch start ∧ ∃ n : ℕ, 0 < n ∧ finish = (D.b ^ n) start ∧
    (∀ k < n, D.u ((D.b ^ k) start) = 0) ∧
      0 < D.u finish ∧ D.v (D.b.symm finish) = 0

def CPositiveRunEndpoint {R : Type*} (D : ResidueData R) (start finish : R) : Prop :=
  D.IsBranch start ∧ ∃ n : ℕ, 0 < n ∧ finish = (D.c ^ n) start ∧
    (∀ k < n, D.v ((D.c ^ k) start) = 0) ∧
      0 < D.v finish ∧ D.u (D.c.symm finish) = 0

def BEndpointNonexceptional {R : Type*} (D : ResidueData R) (finish : R) : Prop :=
  0 < D.v finish ∧ D.u (D.c finish) = 0 ∧ D.v (D.b finish) = 0

def CEndpointNonexceptional {R : Type*} (D : ResidueData R) (finish : R) : Prop :=
  0 < D.u finish ∧ D.u (D.c finish) = 0 ∧ D.v (D.b finish) = 0

theorem nonexceptional_b_endpoint_unusedMerge {R : Type*} (D : ResidueData R)
    {start finish : R} (h : BPositiveRunEndpoint D start finish)
    (hne : BEndpointNonexceptional D finish) : UnusedMergeReverseBase D finish :=
  ⟨h.2.choose_spec.2.2.2.1, hne.1, hne.2.1, hne.2.2⟩

theorem nonexceptional_c_endpoint_unusedMerge {R : Type*} (D : ResidueData R)
    {start finish : R} (h : CPositiveRunEndpoint D start finish)
    (hne : CEndpointNonexceptional D finish) : UnusedMergeReverseBase D finish :=
  ⟨hne.1, h.2.choose_spec.2.2.2.1, hne.2.1, hne.2.2⟩

end NS25Lean.L5A2C4H
