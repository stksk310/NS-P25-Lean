import NS25Lean.P2BranchBFirstReturnDomination

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2B4AR4R2B
open L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR3 L5A2C4OR4 L5A2C4OR6

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- A principal return is a nonnegative raw candidate at every residue.
This is the source-exact Apéry-minimality consequence of `q0*m ∈ H`; it
does not assert that the principal candidate realizes any lower envelope. -/
theorem branchB_principal_rawCandidate_nonnegative
    (R : SectorBCriticalRoleBranchB P)
    (s : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    0 ≤ rawCandidate P.M.base (branchBInactiveReindex R)
      (actualPrincipalIndex P.M.base) s := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let H := routingH B e
  let a := routingA B e
  let q0 := actualPrincipalIndex B
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hq0H : q0 * routingM B e ∈ H := by
    have hH : H = normalizedH B := by
      dsimp only [H, B, e]
      exact branchBRoutingH_eq_normalizedH R
    rw [hH]
    exact (actualPrincipalIndex_spec B).2
  let alpha := H.asRelativeIdeal.aperyRepresentative a s
  let beta := H.asRelativeIdeal.aperyRepresentative a
    (s - (q0 * routingM B e : ℕ))
  have hbeta : beta ∈ H.asRelativeIdeal :=
    H.asRelativeIdeal.aperyRepresentative_mem a _
  have hsum : beta + (q0 * routingM B e : ℕ) ∈ H.asRelativeIdeal :=
    H.asRelativeIdeal.add_mem hbeta hq0H
  have hmod : ((beta + (q0 * routingM B e : ℕ) : ℤ) : ZMod a) = s := by
    dsimp only [beta]
    rw [Int.cast_add, Int.cast_natCast,
      H.asRelativeIdeal.aperyRepresentative_mod]
    push_cast
    ring
  have hle : alpha ≤ beta + (q0 * routingM B e : ℕ) := by
    exact H.asRelativeIdeal.aperyRepresentative_le a s hsum hmod
  have hspec := rawCandidate_spec B e q0 s
  change q0 * routingM B e + beta - alpha =
    (a : ℤ) * rawCandidate B e q0 s at hspec
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  push_cast at hle
  dsimp only [B, e, H, a, q0] at hspec ⊢
  nlinarith

/-- First-return domination works at every residue, not only at the origin. -/
theorem branchB_candidate_first_return_domination
    (R : SectorBCriticalRoleBranchB P)
    (s : ZMod (routingA P.M.base (branchBInactiveReindex R)))
    {q : ℕ} (_hq : 0 < q) :
    rawCandidate P.M.base (branchBInactiveReindex R) q s ≤
      rawCandidate P.M.base (branchBInactiveReindex R)
        (q + actualPrincipalIndex P.M.base) s := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let q0 := actualPrincipalIndex B
  have hcocycle := L5A2C4OR2.rawCandidate_cocycle B e q q0 s
  have htranslated := branchB_principal_rawCandidate_nonnegative R
    (s - (q * routingM B e : ℕ))
  change rawCandidate B e q s ≤ rawCandidate B e (q + q0) s
  linarith

/-- Every positive candidate at an arbitrary residue reduces to the first
principal block without increasing its value. -/
theorem branchB_candidate_reduce_to_first_principal_block
    (R : SectorBCriticalRoleBranchB P)
    (s : ZMod (routingA P.M.base (branchBInactiveReindex R)))
    {k : ℕ} (hk : 0 < k) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ actualPrincipalIndex P.M.base ∧
      rawCandidate P.M.base (branchBInactiveReindex R) j s ≤
        rawCandidate P.M.base (branchBInactiveReindex R) k s := by
  let q0 := actualPrincipalIndex P.M.base
  have hq0pos : 0 < q0 := (actualPrincipalIndex_spec P.M.base).1
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hle : k ≤ q0
      · exact ⟨k, hk, hle, le_rfl⟩
      · have hkq : q0 < k := lt_of_not_ge hle
        let k' := k - q0
        have hk'pos : 0 < k' := by simp [k']; omega
        have hk'lt : k' < k := by simp [k']; omega
        obtain ⟨j, hjpos, hjle, hjcand⟩ := ih k' hk'lt hk'pos
        refine ⟨j, hjpos, hjle, hjcand.trans ?_⟩
        have hdom := branchB_candidate_first_return_domination R s hk'pos
        have hdecomp : k' + q0 = k := by simp [k']; omega
        change rawCandidate P.M.base (branchBInactiveReindex R) k' s ≤
          rawCandidate P.M.base (branchBInactiveReindex R) (k' + q0) s at hdom
        rwa [hdecomp] at hdom

private theorem branchB_ox_seam_canonical
    (R : SectorBCriticalRoleBranchB P) :
    IsCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) := by
  have h := (loadBearingCoordinates_canonical P.M.base
    (branchBInactiveReindex R) (branchB_inactive_coherentHerzogData R)).2.1
  simpa using h

private theorem branchB_oy_seam_canonical
    (R : SectorBCriticalRoleBranchB P) :
    IsCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) := by
  have h := (loadBearingCoordinates_canonical P.M.base
    (branchBInactiveReindex R) (branchB_inactive_coherentHerzogData R)).2.2.1
  simpa using h

/-- Exact red-team split at the OX zero seam.  The current kernel forces a
bounded nonpositive seam candidate, but it permits either a strict-prefix
candidate or genuine principal incidence. -/
theorem branchB_ox_zero_seam_nonprincipal_or_principal_incidence
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0) :
    (∃ j : ℕ, 1 ≤ j ∧ j < actualPrincipalIndex P.M.base ∧
      rawCandidate P.M.base (branchBInactiveReindex R) j
        (gridResidue P.M.base (branchBInactiveReindex R)
          (r31 R - 1) (r32 R)) ≤ 0) ∨
    rawCandidate P.M.base (branchBInactiveReindex R)
      (actualPrincipalIndex P.M.base)
      (gridResidue P.M.base (branchBInactiveReindex R)
        (r31 R - 1) (r32 R)) = 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let s := gridResidue B e (r31 R - 1) (r32 R)
  let k := currentSelector B e s
  have hkpos : 0 < k := currentSelector_pos B e s
  have heta := eta_eq_physicalHeight_of_isCanonical B e _ _
    (branchB_ox_seam_canonical R)
  have hheight := physicalHeight_eq_max_rawMinimum B e s
  have hmin : rawMinimum B e s ≤ 0 := by
    change eta B e (r31 R - 1) (r32 R) = 0 at hP1
    change eta B e (r31 R - 1) (r32 R) = physicalHeight B e s at heta
    rw [hP1] at heta
    have hz : (physicalHeight B e s : ℤ) = 0 := by exact_mod_cast heta.symm
    rw [hheight] at hz
    omega
  have hkvalue : rawCandidate B e k s ≤ 0 := by
    rw [rawCandidate_currentSelector B e s]
    exact hmin
  obtain ⟨j, hjpos, hjle, hjvalue⟩ :=
    branchB_candidate_reduce_to_first_principal_block R s hkpos
  by_cases hjlt : j < actualPrincipalIndex B
  · exact Or.inl ⟨j, hjpos, hjlt, hjvalue.trans hkvalue⟩
  · right
    change j ≤ actualPrincipalIndex B at hjle
    change ¬ j < actualPrincipalIndex B at hjlt
    have hjeq : j = actualPrincipalIndex B := by omega
    have hle : rawCandidate B e (actualPrincipalIndex B) s ≤ 0 := by
      rw [← hjeq]
      exact hjvalue.trans hkvalue
    have hge := branchB_principal_rawCandidate_nonnegative R s
    exact le_antisymm hle hge

/-- Exact cyclic dual of the OX red-team split. -/
theorem branchB_oy_zero_seam_nonprincipal_or_principal_incidence
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0) :
    (∃ j : ℕ, 1 ≤ j ∧ j < actualPrincipalIndex P.M.base ∧
      rawCandidate P.M.base (branchBInactiveReindex R) j
        (gridResidue P.M.base (branchBInactiveReindex R)
          (r31 R) (r32 R - 1)) ≤ 0) ∨
    rawCandidate P.M.base (branchBInactiveReindex R)
      (actualPrincipalIndex P.M.base)
      (gridResidue P.M.base (branchBInactiveReindex R)
        (r31 R) (r32 R - 1)) = 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let s := gridResidue B e (r31 R) (r32 R - 1)
  let k := currentSelector B e s
  have hkpos : 0 < k := currentSelector_pos B e s
  have heta := eta_eq_physicalHeight_of_isCanonical B e _ _
    (branchB_oy_seam_canonical R)
  have hheight := physicalHeight_eq_max_rawMinimum B e s
  have hmin : rawMinimum B e s ≤ 0 := by
    change eta B e (r31 R) (r32 R - 1) = 0 at hQ1
    change eta B e (r31 R) (r32 R - 1) = physicalHeight B e s at heta
    rw [hQ1] at heta
    have hz : (physicalHeight B e s : ℤ) = 0 := by exact_mod_cast heta.symm
    rw [hheight] at hz
    omega
  have hkvalue : rawCandidate B e k s ≤ 0 := by
    rw [rawCandidate_currentSelector B e s]
    exact hmin
  obtain ⟨j, hjpos, hjle, hjvalue⟩ :=
    branchB_candidate_reduce_to_first_principal_block R s hkpos
  by_cases hjlt : j < actualPrincipalIndex B
  · exact Or.inl ⟨j, hjpos, hjlt, hjvalue.trans hkvalue⟩
  · right
    change j ≤ actualPrincipalIndex B at hjle
    change ¬ j < actualPrincipalIndex B at hjlt
    have hjeq : j = actualPrincipalIndex B := by omega
    have hle : rawCandidate B e (actualPrincipalIndex B) s ≤ 0 := by
      rw [← hjeq]
      exact hjvalue.trans hkvalue
    have hge := branchB_principal_rawCandidate_nonnegative R s
    exact le_antisymm hle hge

end NS25Lean.L5A2B4AR5B
