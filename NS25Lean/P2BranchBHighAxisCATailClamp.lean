import NS25Lean.P2BranchBAxisCSeamAudit
import NS25Lean.P2BranchBSignedSeam

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L5A1 L5A2B4AR1
open L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The strict-prefix part of the B52 return-window barrier.  This is an
integer subtraction statement, so no truncated natural subtraction is used.
The missing endpoint `k = q0` is exactly the principal Apéry barrier that
requires the event-local zero-floor localization. -/
theorem branchB_preprincipal_return_window_a_predecessor_excluded
    (R : SectorBCriticalRoleBranchB P) (k : ℕ)
    (hkpos : 0 < k) (hklt : k < actualPrincipalIndex P.M.base) :
    ((k * normalizedM P.M.base : ℕ) : ℤ) - normalizedA R ∉
      (normalizedH P.M.base).asRelativeIdeal := by
  intro hpred
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hpred
  obtain ⟨t, htH, htEq⟩ := hpred
  have haH : normalizedA R ∈ normalizedH P.M.base :=
    branchB_actual_normalizedA_mem R
  have hsum : t + normalizedA R ∈ normalizedH P.M.base :=
    (normalizedH P.M.base).add_mem htH haH
  have hkm : k * normalizedM P.M.base = t + normalizedA R := by
    exact_mod_cast (show
      ((k * normalizedM P.M.base : ℕ) : ℤ) =
        (t + normalizedA R : ℕ) by omega)
  have hmem : k * normalizedM P.M.base ∈ normalizedH P.M.base := by
    rw [hkm]
    exact hsum
  have hqle := principalIndex_min (normalizedH P.M.base)
    (normalizedM P.M.base) P.M.base.q_positive hkpos hmem
  exact (Nat.not_le_of_gt hklt) hqle

/-- Once the principal endpoint is known to be Apéry, the strict-prefix
barrier above closes the complete finite return window.  This helper does not
assume any classifier or transport conclusion; its single premise is exactly
the still-missing `k = q0` endpoint. -/
theorem branchB_return_window_a_predecessor_excluded_of_principal
    (R : SectorBCriticalRoleBranchB P)
    (hprincipal :
      (((actualPrincipalIndex P.M.base * normalizedM P.M.base : ℕ) : ℤ) -
          normalizedA R) ∉ (normalizedH P.M.base).asRelativeIdeal) :
    ∀ k : ℕ, 0 < k → k ≤ actualPrincipalIndex P.M.base →
      ((k * normalizedM P.M.base : ℕ) : ℤ) - normalizedA R ∉
        (normalizedH P.M.base).asRelativeIdeal := by
  intro k hkpos hkle
  rcases lt_or_eq_of_le hkle with hklt | rfl
  · exact branchB_preprincipal_return_window_a_predecessor_excluded
      R k hkpos hklt
  · exact hprincipal

/-- Event-specialized strict-prefix window checkpoint for the B52 high
axis-`c` packet.  The extra event arguments are retained so downstream code
can use this theorem without replacing the actual source by the selected
anchor. -/
theorem branchB_actualZeroEdgeBirth_axisC_high_seam_preprincipal_window
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (_hbirth : IsActualZeroEdgeBirth R x hsx)
    (haxis :
      let A := branchB_actual_selected_return_anchor_v2 R hB hsx
      A.coordinate.i = 0 ∧
      qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R) :
    (let A := branchB_actual_selected_return_anchor_v2 R hB hsx;
      A.coordinate.i = 0 ∧
      qH R < A.coordinate.j ∧
      A.coordinate.j < qH R + vH R ∧
      A.beta = A.coordinate.j * normalizedC R ∧
      (A.n : ℤ) + normalizedA R * A.depth =
        A.coordinate.j * normalizedC R) ∧
    ∀ k : ℕ, 0 < k → k < actualPrincipalIndex P.M.base →
      ((k * normalizedM P.M.base : ℕ) : ℤ) - normalizedA R ∉
        (normalizedH P.M.base).asRelativeIdeal := by
  refine ⟨haxis, ?_⟩
  intro k hkpos hklt
  exact branchB_preprincipal_return_window_a_predecessor_excluded
    R k hkpos hklt

end NS25Lean.L5A2B4AR5B

