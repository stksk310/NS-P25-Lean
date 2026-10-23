import NS25Lean.P2Sectors

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C

/--
The final integer accounting step for the symmetric Sector-C zero-slack DAG.

`u` is the number of positive source images, `H0` the missing-zero-corner
deficit, and `X` the number of free merges beyond the baseline ZERO-CROSS
matching.  The hypotheses expose, rather than assume opaquely, the two
load-bearing conclusions of the return analysis: two positive packets are
incompatible, while a sole positive packet in the uncharged Type-A pattern
must create a fresh payment.
-/
theorem sectorC_branch_sub_merge_le_one
    (B M u H0 X : ℕ)
    (haccount : (B : ℤ) - (M : ℤ) = (u : ℤ) - (H0 : ℤ) - (X : ℤ) + 1)
    (hu : u ≤ 2)
    (hincompatible : u ≠ 2)
    (hpayment : u = 1 → H0 = 0 → X = 0 → False) :
    (B : ℤ) - (M : ℤ) ≤ 1 := by
  by_cases hu0 : u = 0
  · omega
  have hu1 : u = 1 := by omega
  by_cases hH0 : H0 = 0
  · by_cases hX : X = 0
    · exact (hpayment hu1 hH0 hX).elim
    · omega
  · omega

/-- Convert `B_C - M_C ≤ 1` through the exact symmetric identity to `t ≤ S`. -/
theorem sectorC_type_le_sourceCount_of_symmetric_accounting
    (S t B M : ℕ)
    (hdeficit : (B : ℤ) - (M : ℤ) ≤ 1)
    (hsymmetric : (S : ℤ) - (t : ℤ) = 1 + ((M : ℤ) - (B : ℤ))) :
    t ≤ S := by
  omega

/-- The complete numerical endgame of the Sector C proof.  All geometric content
is exposed as hypotheses: the branch accounting identity, the two obstructions
to its exceptional cases, and the symmetric source/type identity. -/
theorem sectorC_accounting_endgame
    (S t B M u H0 X : ℕ)
    (haccount : (B : ℤ) - (M : ℤ) = (u : ℤ) - (H0 : ℤ) - (X : ℤ) + 1)
    (hu : u ≤ 2)
    (hincompatible : u ≠ 2)
    (hpayment : u = 1 → H0 = 0 → X = 0 → False)
    (hsymmetric : (S : ℤ) - (t : ℤ) = 1 + ((M : ℤ) - (B : ℤ))) :
    t ≤ S := by
  apply sectorC_type_le_sourceCount_of_symmetric_accounting S t B M
  · exact sectorC_branch_sub_merge_le_one B M u H0 X haccount hu hincompatible hpayment
  · exact hsymmetric

end NS25Lean.L5A2C
