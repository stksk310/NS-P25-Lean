import NS25Lean.P2BranchBInactiveGateExposedPF
import NS25Lean.P2BranchBPrincipalSurgeryChannel

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2B4AR4R2B
open L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR3 L5A2C4OR4 L5A2C4OR5

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Shifting a return level by the first principal return only makes its
return ideal smaller. -/
theorem branchB_returnIdeal_add_principal_subset
    (R : SectorBCriticalRoleBranchB P) (q : ℕ) :
    (returnIdeal (routingH P.M.base (branchBInactiveReindex R))
      ((q + actualPrincipalIndex P.M.base) *
        routingM P.M.base (branchBInactiveReindex R))).carrier ⊆
      (returnIdeal (routingH P.M.base (branchBInactiveReindex R))
        (q * routingM P.M.base (branchBInactiveReindex R))).carrier := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let q0 := actualPrincipalIndex B
  have hq0H : q0 * routingM B e ∈ routingH B e := by
    rw [branchBRoutingH_eq_normalizedH R]
    exact (actualPrincipalIndex_spec B).2
  intro x hx
  change x ∈ returnIdeal (routingH B e) ((q + q0) * routingM B e) at hx
  rcases hx with ⟨hxH, hxshift⟩
  refine ⟨hxH, ?_⟩
  change x - ((q + q0) * routingM B e : ℕ) ∈
    (routingH B e).asRelativeIdeal at hxshift
  have hadd := (routingH B e).asRelativeIdeal.add_mem hxshift hq0H
  change x - (q * routingM B e : ℕ) ∈ (routingH B e).asRelativeIdeal
  have heq : x - (q * routingM B e : ℕ) =
      (x - ((q + q0) * routingM B e : ℕ)) + (q0 * routingM B e : ℕ) := by
    push_cast
    ring
  rw [heq]
  exact hadd

private theorem branchB_origin_physicalAlpha_eq_zero
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4OR3.physicalAlpha P.M.base (branchBInactiveReindex R) 0 = 0 := by
  have h := H0_isCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
  change (normalizedGrid P.M.base (branchBInactiveReindex R) 0 0 0 : ℤ) =
    L5A2C4OR3.physicalAlpha P.M.base (branchBInactiveReindex R)
      (gridResidue P.M.base (branchBInactiveReindex R) 0 0) at h
  simpa [normalizedGrid, gridResidue] using h.symm

/-- Every positive origin candidate is strictly positive.  This is the
source-exact fact needed to use the natural threshold interface. -/
theorem branchB_origin_rawCandidate_pos
    (R : SectorBCriticalRoleBranchB P) {q : ℕ} (hq : 0 < q) :
    0 < rawCandidate P.M.base (branchBInactiveReindex R) q 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  change 0 < rawCandidate B e q 0
  have hthreshold := rawCandidate_threshold B e (0 : ZMod (routingA B e)) hq 0
  have hnotmem :
      L5A2C4OR3.physicalAlpha B e 0 + routingA B e * 0 - q * routingM B e ∉
        (routingH B e).asRelativeIdeal := by
    rw [branchB_origin_physicalAlpha_eq_zero R]
    simp only [mul_zero, add_zero]
    intro hmem
    rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hmem
    obtain ⟨n, _hn, heq⟩ := hmem
    have hm : 0 < q * routingM B e := Nat.mul_pos hq (routingM_pos B e)
    omega
  have hnle : ¬ rawCandidate B e q 0 ≤ 0 := by
    intro hle
    exact hnotmem (hthreshold.mpr hle)
  omega

/-- First-return domination at the origin: adding the first principal return
cannot decrease the actual raw candidate. -/
theorem branchB_origin_candidate_first_return_domination
    (R : SectorBCriticalRoleBranchB P) {q : ℕ} (hq : 0 < q) :
    rawCandidate P.M.base (branchBInactiveReindex R) q 0 ≤
      rawCandidate P.M.base (branchBInactiveReindex R)
        (q + actualPrincipalIndex P.M.base) 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let q0 := actualPrincipalIndex B
  have hq0pos : 0 < q0 := (actualPrincipalIndex_spec B).1
  have hq0H : q0 * routingM B e ∈ routingH B e := by
    rw [branchBRoutingH_eq_normalizedH R]
    exact (actualPrincipalIndex_spec B).2
  have hsumpos : 0 < q + q0 := Nat.add_pos_left hq q0
  have hcandidatePos := branchB_origin_rawCandidate_pos R hsumpos
  let n := (rawCandidate B e (q + q0) 0).toNat
  have hncast : (n : ℤ) = rawCandidate B e (q + q0) 0 :=
    Int.toNat_of_nonneg (le_of_lt hcandidatePos)
  have hlarge :
      L5A2C4OR3.physicalAlpha B e 0 + routingA B e * n -
          (q + q0) * routingM B e ∈ (routingH B e).asRelativeIdeal := by
    apply (rawCandidate_threshold B e 0 hsumpos n).mpr
    rw [hncast]
  have hsmall :
      L5A2C4OR3.physicalAlpha B e 0 + routingA B e * n -
          q * routingM B e ∈ (routingH B e).asRelativeIdeal := by
    have hadd := (routingH B e).asRelativeIdeal.add_mem hlarge hq0H
    have heq :
        L5A2C4OR3.physicalAlpha B e 0 + routingA B e * n -
            q * routingM B e =
          (L5A2C4OR3.physicalAlpha B e 0 + routingA B e * n -
              (q + q0) * routingM B e) + (q0 * routingM B e : ℕ) := by
      push_cast
      ring
    rw [heq]
    exact hadd
  have hle := (rawCandidate_threshold B e 0 hq n).mp hsmall
  rwa [hncast] at hle

/-- Repeated first-return domination reduces every positive origin candidate
to an index in the first principal block `1, ..., q0`. -/
theorem branchB_origin_candidate_reduce_to_first_principal_block
    (R : SectorBCriticalRoleBranchB P) {k : ℕ} (hk : 0 < k) :
    ∃ j : ℕ,
      1 ≤ j ∧
      j ≤ actualPrincipalIndex P.M.base ∧
      rawCandidate P.M.base (branchBInactiveReindex R) j 0 ≤
        rawCandidate P.M.base (branchBInactiveReindex R) k 0 := by
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
        have hdom := branchB_origin_candidate_first_return_domination R hk'pos
        have hdecomp : k' + q0 = k := by simp [k']; omega
        change rawCandidate P.M.base (branchBInactiveReindex R) k' 0 ≤
          rawCandidate P.M.base (branchBInactiveReindex R) (k' + q0) 0 at hdom
        rwa [hdecomp] at hdom

/-- The frozen inactive origin height supplies an actual global origin
candidate strictly below the first critical height. -/
theorem branchB_origin_global_candidate_lt_c3
    (R : SectorBCriticalRoleBranchB P) :
    ∃ k : ℕ,
      0 < k ∧
      rawCandidate P.M.base (branchBInactiveReindex R) k 0 < c3 R := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let k := currentSelector B e 0
  have hkpos : 0 < k := currentSelector_pos B e 0
  have hkmin := rawCandidate_currentSelector B e 0
  have heta := eta_eq_physicalHeight_of_isCanonical B e 0 0
    (H0_isCanonicalTailGridPoint B e)
  have hheight := physicalHeight_eq_max_rawMinimum B e 0
  have hH0 := branchB_inactive_H0_lt R
  change eta B e 0 0 < c3 R at hH0
  have hgrid : gridResidue B e 0 0 = 0 := by simp [gridResidue]
  rw [heta, hgrid] at hH0
  have hcast : (physicalHeight B e 0 : ℤ) < c3 R := by exact_mod_cast hH0
  have hrawlt : rawMinimum B e 0 < c3 R := by
    rw [hheight] at hcast
    omega
  refine ⟨k, hkpos, ?_⟩
  change rawCandidate B e k 0 < c3 R
  rw [hkmin]
  exact hrawlt

/-- The global origin minimizer can be replaced by a (possibly principal)
candidate in the first principal block without assuming a bound on
`currentSelector`. -/
theorem branchB_origin_carver_le_principal
    (R : SectorBCriticalRoleBranchB P) :
    ∃ j : ℕ,
      1 ≤ j ∧
      j ≤ actualPrincipalIndex P.M.base ∧
      rawCandidate P.M.base (branchBInactiveReindex R) j 0 < c3 R := by
  obtain ⟨k, hkpos, hklt⟩ := branchB_origin_global_candidate_lt_c3 R
  obtain ⟨j, hjpos, hjle, hjcand⟩ :=
    branchB_origin_candidate_reduce_to_first_principal_block R hkpos
  exact ⟨j, hjpos, hjle, lt_of_le_of_lt hjcand hklt⟩

end NS25Lean.L5A2B4AR5B

