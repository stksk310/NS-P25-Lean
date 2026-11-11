import NS25Lean.P3FreshProvenanceR52
import NS25Lean.P2SectorCLocalCollisionAccounting
import NS25Lean.P3CommonFinalCountAlignment

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section

namespace NS25Lean.P3R52Bridge
open FourGeneratedBridge CombinatorialCore ChosenBase L2B L5A2C4H L5A2C4I
variable {Gamma : NumericalSemigroup}

/-- Routing sources count the tail generators of the original base, without a P2 assumption. -/
theorem routing_sourceCount (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    (routingData M.base e).sourceCount = L2B.sourceCount M.base := by
  let B := M.base
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmin := normalizedSemigroup_minimal (chosenBase_minimalFour B e)
  have hb : routingB B e ≠ 0 := by
    intro hz; apply hmin.2.2.1
    simpa only [routingB, hz] using (AddSubmonoid.zero_mem _)
  have hc : routingC B e ≠ 0 := by
    intro hz; apply hmin.2.2.2
    simpa only [routingC, hz] using (AddSubmonoid.zero_mem _)
  calc
    (routingData B e).sourceCount = (routingI B e).generatorCount :=
      (routingI B e).concrete_sourceCount_eq_generatorCount
        (routingA B e) (routingB B e) (routingC B e) hmin.1
        (routingHB B e) (routingHC B e) hb hc
    _ = tailGeneratorCount
        (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e))
        (aperyTail Gamma.toAddSubmonoid
          (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e)) B.q.val) :=
      normalizedTail_generatorCount Gamma B.q.val _ _ _ (chosenBase_minimalFour B e)
    _ = L2B.sourceCount B := by
      rw [L2B.sourceCount, Data.K, chosenBase_tail_eq_generatedThree B e]

/-- Actual sinks, rather than all normalized sinks, count the original semigroup type. -/
theorem routing_actualSinkCount (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    actualSinkCount (routingI M.base e) (routingA M.base e)
      (routingB M.base e) (routingC M.base e)
      (routingHB M.base e) (routingHC M.base e) = Gamma.asRelativeIdeal.idealType := by
  let B := M.base
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
  calc
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

/-- Direct D5 total-count route on the original final cut, before first-exit
cancellation. Fake sinks are retained as a separate nonnegative resource. -/
theorem type_fake_total_identity (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    Gamma.asRelativeIdeal.idealType +
      fakeSinkCount (routingI M.base e) (routingA M.base e)
        (routingB M.base e) (routingC M.base e) (routingHB M.base e) (routingHC M.base e) +
      Nat.card (ResidueData.ExactUnusedMergeBases D) =
        L2B.sourceCount M.base + ResidueData.sourceTargetBranchCount D := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hsource := routing_sourceCount M e
  have htype := routing_actualSinkCount M e
  have hsinks := fullSinkCount_eq_actual_add_fake (routingI M.base e) (routingA M.base e)
    (routingB M.base e) (routingC M.base e) (routingHB M.base e) (routingHC M.base e)
  have he := P3CommonFinal.euler_total (routingData M.base e)
  rw [htype] at hsinks
  change (routingData M.base e).sourceCount = L2B.sourceCount M.base at hsource
  change (routingData M.base e).sinkCount = _ + _ at hsinks
  omega

/-- Exact original-M accounting: fake sinks are retained, and only genuinely fresh
unused merges appear. Every term uses the same routing role permutation. -/
theorem type_fake_fresh_identity (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    Gamma.asRelativeIdeal.idealType +
      fakeSinkCount (routingI M.base e) (routingA M.base e)
        (routingB M.base e) (routingC M.base e) (routingHB M.base e) (routingHC M.base e) +
      Nat.card (ResidueData.CFreshUnusedMergeBases D) =
        L2B.sourceCount M.base + ResidueData.cExceptionalCount D := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  let D := routingData M.base e
  have hsource := routing_sourceCount M e
  have htype := routing_actualSinkCount M e
  have hsinks := fullSinkCount_eq_actual_add_fake (routingI M.base e) (routingA M.base e)
    (routingB M.base e) (routingC M.base e) (routingHB M.base e) (routingHC M.base e)
  have hfinal := P3CommonFinal.euler_fresh D
  change D.sourceCount = L2B.sourceCount M.base at hsource
  change D.sinkCount = _ + _ at hsinks
  rw [htype] at hsinks
  change Gamma.asRelativeIdeal.idealType + _ + Nat.card (ResidueData.CFreshUnusedMergeBases D) =
    L2B.sourceCount M.base + ResidueData.cExceptionalCount D
  omega

/-- The direct total-UM/ST estimate proves the original type bound without
choosing fresh witnesses. The stronger fresh interface remains separate. -/
theorem type_le_source_add_one_of_total_compensation (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    ResidueData.sourceTargetBranchCount D ≤
      Nat.card (ResidueData.ExactUnusedMergeBases D) + 1 →
      Gamma.asRelativeIdeal.idealType ≤ L2B.sourceCount M.base + 1 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  dsimp only
  intro h
  have hi := type_fake_total_identity M e
  omega

theorem type_le_source_add_one_of_fresh_compensation (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    ResidueData.cExceptionalCount D ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D) + 1 →
      Gamma.asRelativeIdeal.idealType ≤ L2B.sourceCount M.base + 1 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  dsimp only
  intro h
  have htotal := (P3CommonFinal.compensation_iff (routingData M.base e)).mpr h
  exact type_le_source_add_one_of_total_compensation M e htotal

/-- Keeping fake sinks gives an equivalence, before the final inequality drops them. -/
theorem fresh_compensation_iff_type_fake_bound (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    let D := routingData M.base e
    (ResidueData.cExceptionalCount D ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D) + 1) ↔
      Gamma.asRelativeIdeal.idealType +
        fakeSinkCount (routingI M.base e) (routingA M.base e)
          (routingB M.base e) (routingC M.base e) (routingHB M.base e) (routingHC M.base e) ≤
        L2B.sourceCount M.base + 1 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hid := type_fake_fresh_identity M e
  dsimp only
  omega

/-- This is an implication with an explicit compensation premise, not closure of p3. -/
theorem p3_strong_of_fresh_compensation (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3)
    (hcomp : ∃ e : Fin 3 ≃ Fin 3,
      letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      let D := routingData M.base e
      ResidueData.cExceptionalCount D ≤ Nat.card (ResidueData.CFreshUnusedMergeBases D) + 1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  obtain ⟨e, he⟩ := hcomp
  have ht := type_le_source_add_one_of_fresh_compensation M e he
  have hrho := sourceCount_add_defect M.base
  rw [hp] at hrho
  omega

/-- A physical sufficient condition, still conditional on the stated branch/merge geometry. -/
theorem p3_strong_of_two_branches_and_unused (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hc : letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      ResidueData.sourceTargetBranchCount (routingData M.base e) ≤ 2)
    (hq : letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      Nonempty (ResidueData.ExactUnusedMergeBases (routingData M.base e))) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  obtain ⟨q⟩ := hq
  exact p3_strong_of_fresh_compensation M hp
    ⟨e, P3R52.compensation_of_two_branches_and_unused (routingData M.base e) hc q⟩

end NS25Lean.P3R52Bridge
