import NS25Lean.P2BranchBExceptionalResource
import NS25Lean.P2PrefixDictionary

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B2A2 L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2C4H

variable {Gamma : NumericalSemigroup}

private theorem routingB_ne_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingB B e ≠ 0 := by
  intro hz
  apply (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).2.2.1
  simpa only [routingB, hz] using (AddSubmonoid.zero_mem _)

private theorem routingC_ne_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingC B e ≠ 0 := by
  intro hz
  apply (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).2.2.2
  simpa only [routingC, hz] using (AddSubmonoid.zero_mem _)

/-- A routing source is first identified with its actual normalized Apéry
generator. -/
noncomputable def routingSourceEquivNormalizedGenerator
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    {r // (routingData B e).IsSource r} ≃
      {z // (routingI B e).IsMinimalGenerator z} := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact (routingI B e).concreteSourceEquivMinimalGenerator
    (routingA B e) (routingB B e) (routingC B e)
    (normalizedSemigroup_minimal (chosenBase_minimalFour B e)).1
    (routingHB B e) (routingHC B e) (routingB_ne_zero B e) (routingC_ne_zero B e)

private abbrev routingTailScaling (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  buildTailScaling Gamma B.q.val (routingN1 B e) (routingN2 B e) (routingN3 B e)
    (chosenBase_minimalFour B e)

theorem routingD_eq_chosenTailGcd (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B e =
      tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val (B.tailDegrees 2).val := by
  apply Nat.dvd_antisymm
  · have hall (i : Fin 3) : routingD B e ∣ (B.tailDegrees i).val := by
      obtain ⟨j, rfl⟩ := e.surjective i
      fin_cases j
      · exact (tailGcd_dvd _ _ _).1
      · exact (tailGcd_dvd _ _ _).2.1
      · exact (tailGcd_dvd _ _ _).2.2
    exact Nat.dvd_gcd (hall 0) (Nat.dvd_gcd (hall 1) (hall 2))
  · obtain ⟨h0, h1, h2⟩ :=
      tailGcd_dvd (B.tailDegrees 0).val (B.tailDegrees 1).val (B.tailDegrees 2).val
    have hall (i : Fin 3) :
        tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val
            (B.tailDegrees 2).val ∣ (B.tailDegrees (e i)).val := by
      have hi : e i = 0 ∨ e i = 1 ∨ e i = 2 := by omega
      rcases hi with hi | hi | hi
      · simpa [hi] using h0
      · simpa [hi] using h1
      · simpa [hi] using h2
    exact Nat.dvd_gcd (hall 0) (Nat.dvd_gcd (hall 1) (hall 2))

/-- The reindexed three-generator tail is definitionally transported back to
the original chosen-base tail.  Values are unchanged. -/
noncomputable def routingTailGeneratorEquivChosenSource
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    {w : ℕ // IsMinimalTailGenerator
      (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e))
      (aperyTail Gamma.toAddSubmonoid
        (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e)) B.q.val) w} ≃
      Source B where
  toFun w := ⟨w.val, by
    change IsMinimalTailGenerator B.H B.K w.val
    simpa only [Data.K, chosenBase_tail_eq_generatedThree B e] using w.property⟩
  invFun s := ⟨s.val, by
    change IsMinimalTailGenerator
      (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e))
      (aperyTail Gamma.toAddSubmonoid
        (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e)) B.q.val) s.val
    simpa only [Data.K, chosenBase_tail_eq_generatedThree B e] using s.property⟩
  left_inv w := Subtype.ext rfl
  right_inv s := Subtype.ext rfl

/-- Source-exact element dictionary: graph source residue, normalized Apéry
generator, inverse gcd scaling, and chosen-base tail source. -/
noncomputable def routingSourceEquivChosenSource
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    {r // (routingData B e).IsSource r} ≃ Source B := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact (routingSourceEquivNormalizedGenerator B e).trans
    ((routingTailScaling B e).generatorEquiv.symm.trans
      (routingTailGeneratorEquivChosenSource B e))

@[simp] theorem routingSourceEquivNormalizedGenerator_val
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
      {r // (routingData B e).IsSource r}) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingSourceEquivNormalizedGenerator B e r).val =
      (routingI B e).aperyRepresentative (routingA B e) r.val := rfl

@[simp] theorem routingSourceEquivChosenSource_val
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
      {r // (routingData B e).IsSource r}) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingSourceEquivChosenSource B e r).val =
      routingD B e *
        ((routingI B e).aperyRepresentative (routingA B e) r.val).toNat := rfl

theorem routingSource_apery_residue
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
      {r // (routingData B e).IsSource r}) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    ((routingI B e).aperyRepresentative (routingA B e) r.val : ZMod (routingA B e)) =
      r.val := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact (routingI B e).aperyRepresentative_mod (routingA B e) r.val

theorem routingSourceEquivChosenSource_inverse
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
      {r // (routingData B e).IsSource r}) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (routingSourceEquivChosenSource B e).symm
      (routingSourceEquivChosenSource B e r) = r := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  exact (routingSourceEquivChosenSource B e).symm_apply_apply r

private abbrev chosenTailScaling (B : Data Gamma) :=
  buildTailScaling Gamma B.q.val (B.tailDegrees 0).val (B.tailDegrees 1).val
    (B.tailDegrees 2).val (L5A2B2.chosenBase_minimalFour B)

/-- The unpermuted chosen source/normalized-generator dictionary as an
equivalence.  Exposing the equivalence makes change-of-chart inverse laws
available without comparing proof fields. -/
noncomputable def chosenSourceEquivNormalizedGenerator (B : Data Gamma) :
    Source B ≃ {z // (normalizedI B).IsMinimalGenerator z} :=
  (routingTailGeneratorEquivChosenSource B (Equiv.refl (Fin 3))).symm.trans
    (chosenTailScaling B).generatorEquiv

/-- Normalize a chosen-base source in the original, unpermuted chart. -/
noncomputable def chosenSourceNormalizedGenerator (B : Data Gamma) (hs : Source B) :
    {z // (normalizedI B).IsMinimalGenerator z} :=
  chosenSourceEquivNormalizedGenerator B hs

/-- Inverse normalization dictionary for an actual final source.  This is
only an element/source equivalence; it contains no routing branch datum. -/
noncomputable def chosenSourceOfNormalizedFinalSource
    (B : Data Gamma) {s : ℤ}
    (hs : IsSource (normalizedH B) (actualFinalCarrier B) s) : Source B := by
  let z : {z // (normalizedI B).IsMinimalGenerator z} :=
    ⟨s, by
      change IsSource (normalizedH B) (normalizedI B).carrier s
      rw [normalizedTailIdeal_eq_actualFinalCarrier B]
      exact hs⟩
  exact (chosenSourceEquivNormalizedGenerator B).symm z

@[simp] theorem chosenSourceNormalizedGenerator_of_finalSource
    (B : Data Gamma) {s : ℤ}
    (hs : IsSource (normalizedH B) (actualFinalCarrier B) s) :
    (chosenSourceNormalizedGenerator B
      (chosenSourceOfNormalizedFinalSource B hs)).val = s := by
  let z : {z // (normalizedI B).IsMinimalGenerator z} :=
    ⟨s, by
      change IsSource (normalizedH B) (normalizedI B).carrier s
      rw [normalizedTailIdeal_eq_actualFinalCarrier B]
      exact hs⟩
  change ((chosenSourceEquivNormalizedGenerator B)
    ((chosenSourceEquivNormalizedGenerator B).symm z)).val = s
  rw [(chosenSourceEquivNormalizedGenerator B).apply_symm_apply]

@[simp] theorem chosenSourceNormalizedGenerator_val (B : Data Gamma) (hs : Source B) :
    (chosenSourceNormalizedGenerator B hs).val =
      (hs.val / tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val
        (B.tailDegrees 2).val : ℕ) := by
  exact (chosenTailScaling B).generatorEquiv_apply
    ((routingTailGeneratorEquivChosenSource B (Equiv.refl (Fin 3))).symm hs)

theorem chosenSourceNormalizedGenerator_isFinalSource (B : Data Gamma) (hs : Source B) :
    IsSource (normalizedH B) (actualFinalCarrier B)
      (chosenSourceNormalizedGenerator B hs).val := by
  rw [← normalizedTailIdeal_eq_actualFinalCarrier B]
  exact (chosenSourceNormalizedGenerator B hs).property

/-- The inverse final-source dictionary sends the normalized generator of a
chosen source back to that same chosen source. -/
@[simp] theorem chosenSourceOfNormalizedFinalSource_of_chosenSource
    (B : Data Gamma) (hs : Source B) :
    chosenSourceOfNormalizedFinalSource B
      (chosenSourceNormalizedGenerator_isFinalSource B hs) = hs := by
  exact (chosenSourceEquivNormalizedGenerator B).symm_apply_apply hs

theorem chosenSourceNormalizedGenerator_principal_or_birth
    (B : Data Gamma) (hs : Source B) :
    (chosenSourceNormalizedGenerator B hs).val =
        (actualPrincipalIndex B * normalizedM B : ℕ) ∨
      IsBranchBirth (normalizedH B) (normalizedM B) (actualPrincipalIndex B)
        (chosenSourceNormalizedGenerator B hs).val := by
  by_cases hprincipal : (chosenSourceNormalizedGenerator B hs).val =
      (actualPrincipalIndex B * normalizedM B : ℕ)
  · exact Or.inl hprincipal
  · exact Or.inr ⟨chosenSourceNormalizedGenerator_isFinalSource B hs, hprincipal⟩

theorem chosenSourceNormalizedGenerator_routing_apply_val
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
      {r // (routingData B e).IsSource r}) :
    letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
    (chosenSourceNormalizedGenerator B (routingSourceEquivChosenSource B e r)).val =
      (routingI B e).aperyRepresentative (routingA B e) r.val := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  rw [chosenSourceNormalizedGenerator_val, routingSourceEquivChosenSource_val,
    routingD_eq_chosenTailGcd B e]
  rw [Nat.mul_div_cancel_left _
    (tailGcd_pos (L5A2B2.chosenBase_minimalFour B).n₁_pos)]
  have hz : 0 ≤ (routingI B e).aperyRepresentative (routingA B e) r.val := by
    rw [← routingSourceEquivNormalizedGenerator_val B e r]
    exact (routingTailScaling B e).ideal_nonneg
      (routingSourceEquivNormalizedGenerator B e r).property.1
  exact Int.toNat_of_nonneg hz

/-- The source attached to an exceptional branch is its branch target, not
the branch vertex itself. -/
noncomputable def branchBActualExceptionalRoutingSource
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    {r // (routingData P.M.base e).IsSource r} := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let D := routingData P.M.base e
  exact ⟨D.branchTarget x.val.val.val, x.val.val.property.2⟩

noncomputable def branchBActualExceptionalChosenSource
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) : Source P.M.base := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  exact routingSourceEquivChosenSource P.M.base e
    (branchBActualExceptionalRoutingSource P R x)

noncomputable def branchBActualExceptionalNormalizedSource
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    {z // (normalizedI P.M.base).IsMinimalGenerator z} :=
  chosenSourceNormalizedGenerator P.M.base
    (branchBActualExceptionalChosenSource P R x)

/-- Source-exact actual exceptional packet through the routing and original
normalization dictionaries. -/
theorem branchB_actualExceptional_source_packet
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let D := routingData P.M.base e
    let r := branchBActualExceptionalRoutingSource P R x
    let hs := branchBActualExceptionalChosenSource P R x
    let s := branchBActualExceptionalNormalizedSource P R x
    r.val = D.branchTarget x.val.val.val ∧
      hs.val = routingD P.M.base e *
        ((routingI P.M.base e).aperyRepresentative (routingA P.M.base e) r.val).toNat ∧
      s.val =
        (hs.val / tailGcd (P.M.base.tailDegrees 0).val
          (P.M.base.tailDegrees 1).val (P.M.base.tailDegrees 2).val : ℕ) ∧
      s.val = (routingI P.M.base e).aperyRepresentative
        (routingA P.M.base e) r.val ∧
      IsSource (normalizedH P.M.base) (actualFinalCarrier P.M.base) s.val := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  refine ⟨rfl, routingSourceEquivChosenSource_val P.M.base e _,
    chosenSourceNormalizedGenerator_val P.M.base _,
    chosenSourceNormalizedGenerator_routing_apply_val P.M.base e _, ?_⟩
  exact chosenSourceNormalizedGenerator_isFinalSource P.M.base _

/-- The actual exceptional source is either exactly the newly inserted
principal source or is a genuine BranchBirth source. -/
theorem branchB_actualExceptional_source_principal_or_birth
    (P : P2Data Gamma) (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R) :
    let s := branchBActualExceptionalNormalizedSource P R x
    s.val = (actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) ∨
      IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
        (actualPrincipalIndex P.M.base) s.val := by
  exact chosenSourceNormalizedGenerator_principal_or_birth P.M.base
    (branchBActualExceptionalChosenSource P R x)

end NS25Lean.L5A2B4AR5B
