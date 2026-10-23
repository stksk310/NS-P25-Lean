import NS25Lean.P3OriginalTypeBridgeR52
import NS25Lean.P3CriticalDictionaryR55

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R57
open ChosenBase L2B L5A1 L5A2C4H L5A2C4I CombinatorialCore FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

/-- Exchange the two routing directions, retaining the first tail role and original base. -/
def swapRole (e : Fin 3 ≃ Fin 3) : Fin 3 ≃ Fin 3 := (Equiv.swap 1 2).trans e

@[simp] theorem swapRole_zero (e : Fin 3 ≃ Fin 3) : swapRole e 0 = e 0 := by
  simp [swapRole, Equiv.swap_apply_def]
@[simp] theorem swapRole_one (e : Fin 3 ≃ Fin 3) : swapRole e 1 = e 2 := by simp [swapRole]
@[simp] theorem swapRole_two (e : Fin 3 ≃ Fin 3) : swapRole e 2 = e 1 := by simp [swapRole]

@[simp] theorem routingD_swap (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B (swapRole e) = routingD B e := by
  simp only [routingD, routingN1, routingN2, routingN3, tailValue,
    swapRole_zero, swapRole_one, swapRole_two, tailGcd]
  rw [Nat.gcd_comm (B.tailDegrees (e 2)).val (B.tailDegrees (e 1)).val]

@[simp] theorem routingA_swap (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingA B (swapRole e) = routingA B e := by simp [routingA, routingN1, tailValue]
@[simp] theorem routingB_swap (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingB B (swapRole e) = routingC B e := by simp [routingB, routingC, routingN2, routingN3, tailValue]
@[simp] theorem routingC_swap (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingC B (swapRole e) = routingB B e := by simp [routingB, routingC, routingN2, routingN3, tailValue]

/-- A concrete data swap; it carries no exceptional-count assumption. -/
def swapData {R : Type*} (D : ResidueData R) : ResidueData R where
  u := D.v
  v := D.u
  b := D.c
  c := D.b
  commute := D.commute.symm
  diamond := fun r => (D.diamond r).symm

theorem sourceTargetBranch_swap {R : Type*} [Fintype R] (D : ResidueData R) (r : R) :
    ResidueData.SourceTargetBranch (swapData D) r ↔ ResidueData.SourceTargetBranch D r := by
  simp only [ResidueData.SourceTargetBranch, ResidueData.IsBranch, ResidueData.IsSource,
    ResidueData.branchTarget, swapData]
  rw [D.commute r]
  tauto

noncomputable def exceptionalSwapEquiv {R : Type*} [Fintype R] (D : ResidueData R) :
    ResidueData.CExceptionalBranches (swapData D) ≃ ResidueData.BExceptionalBranches D where
  toFun s := ⟨⟨s.val.val, (sourceTargetBranch_swap D s.val.val).mp s.val.property⟩, s.property⟩
  invFun s := ⟨⟨s.val.val, (sourceTargetBranch_swap D s.val.val).mpr s.val.property⟩, s.property⟩
  left_inv s := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv s := by apply Subtype.ext; apply Subtype.ext; rfl

theorem cExceptional_swapData {R : Type*} [Fintype R] (D : ResidueData R) :
    ResidueData.cExceptionalCount (swapData D) = ResidueData.bExceptionalCount D :=
  Nat.card_congr (exceptionalSwapEquiv D)

theorem aperyRepresentative_carrier_congr {H H' : NumericalSemigroup}
    (I : RelativeIdeal H) (I' : RelativeIdeal H') (a : ℕ) [NeZero a]
    (hI : I'.carrier = I.carrier) : I'.aperyRepresentative a = I.aperyRepresentative a := by
  funext r
  apply le_antisymm
  · apply I'.aperyRepresentative_le a
    · change I.aperyRepresentative a r ∈ I'.carrier
      rw [hI]; exact I.aperyRepresentative_mem a r
    · exact I.aperyRepresentative_mod a r
  · apply I.aperyRepresentative_le a
    · change I'.aperyRepresentative a r ∈ I.carrier
      rw [← hI]; exact I'.aperyRepresentative_mem a r
    · exact I'.aperyRepresentative_mod a r

theorem aperyStepQuotient_carrier_congr {H H' : NumericalSemigroup}
    (I : RelativeIdeal H) (I' : RelativeIdeal H') (a b : ℕ) [NeZero a]
    (hb : b ∈ H) (hb' : b ∈ H') (hI : I'.carrier = I.carrier) :
    I'.aperyStepQuotient a b hb' = I.aperyStepQuotient a b hb := by
  funext r
  have h := I.apery_step_eq a b hb r
  have h' := I'.apery_step_eq a b hb' r
  rw [aperyRepresentative_carrier_congr I I' a hI] at h'
  have ha : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  exact_mod_cast (show (I'.aperyStepQuotient a b hb' r : ℤ) =
    I.aperyStepQuotient a b hb r by nlinarith)

private theorem residueData_ext {R : Type*} {D E : ResidueData R}
    (hu : D.u = E.u) (hv : D.v = E.v) (hb : D.b = E.b) (hc : D.c = E.c) : D = E := by
  cases D; cases E; cases hu; cases hv; cases hb; cases hc; rfl

theorem concrete_cExceptional_swap {H H' : NumericalSemigroup}
    (I : RelativeIdeal H) (I' : RelativeIdeal H')
    (a a' b c b' c' : ℕ) [NeZero a] [NeZero a']
    (hb : b ∈ H) (hc : c ∈ H) (hb' : b' ∈ H') (hc' : c' ∈ H')
    (ha : a' = a) (hbs : b' = c) (hcs : c' = b) (hI : I'.carrier = I.carrier) :
    ResidueData.cExceptionalCount
      ((I'.toAperyStepData a' b' c' hb' hc').toResidueData
        (I'.toAperyStepData_isValid a' b' c' hb' hc')) =
    ResidueData.bExceptionalCount
      ((I.toAperyStepData a b c hb hc).toResidueData
        (I.toAperyStepData_isValid a b c hb hc)) := by
  subst a'; subst b'; subst c'
  let D := (I.toAperyStepData a b c hb hc).toResidueData
    (I.toAperyStepData_isValid a b c hb hc)
  have he : (I'.toAperyStepData a c b hb' hc').toResidueData
      (I'.toAperyStepData_isValid a c b hb' hc') = swapData D := by
    apply residueData_ext
    · exact aperyStepQuotient_carrier_congr I I' a c hc hb' hI
    · exact aperyStepQuotient_carrier_congr I I' a b hb hc' hI
    · rfl
    · rfl
  rw [he]
  exact cExceptional_swapData D

theorem routingI_carrier_swap (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (routingI B (swapRole e)).carrier = (routingI B e).carrier := by
  ext z
  change z ∈ routingI B (swapRole e) ↔ z ∈ routingI B e
  rw [mem_normalizedTailIdeal_iff, mem_normalizedTailIdeal_iff]
  simp only [routingN1, routingN2, routingN3, tailValue,
    swapRole_zero, swapRole_one, swapRole_two, tailGcd, Nat.gcd_comm,
    generatedThree, Set.pair_comm]

/-- Counts from the same original base are exchanged by a legal tail-role swap. -/
theorem routing_cExceptional_swap (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (letI : NeZero (routingA B (swapRole e)) :=
      ⟨Nat.ne_of_gt (routingA_pos B (swapRole e))⟩
     ResidueData.cExceptionalCount (routingData B (swapRole e))) =
    (letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
     ResidueData.bExceptionalCount (routingData B e)) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  letI : NeZero (routingA B (swapRole e)) :=
    ⟨Nat.ne_of_gt (routingA_pos B (swapRole e))⟩
  exact concrete_cExceptional_swap (routingI B e) (routingI B (swapRole e))
    (routingA B e) (routingA B (swapRole e)) (routingB B e) (routingC B e)
    (routingB B (swapRole e)) (routingC B (swapRole e))
    (routingHB B e) (routingHC B e) (routingHB B (swapRole e)) (routingHC B (swapRole e))
    (routingA_swap B e) (routingB_swap B e) (routingC_swap B e) (routingI_carrier_swap B e)

theorem r2_boundary_unique (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR2 : (P3R51.internalDegrees M).card = 2) :
    ∃! h : ℕ, h ∈ P3R51.boundaryDegrees M := by
  classical
  have hs := (P3R51.signature_partition M hp).2.2
  have hc : (P3R51.boundaryDegrees M).card = 1 := by omega
  obtain ⟨h, hh⟩ := Finset.card_eq_one.mp hc
  exact ⟨h, by simp [hh], fun y hy => by simpa [hh] using hy⟩

end NS25Lean.P3R57
