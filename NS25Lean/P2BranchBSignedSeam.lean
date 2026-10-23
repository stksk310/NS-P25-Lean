import NS25Lean.P2BranchBPrincipalSeamProfile
import NS25Lean.P2BranchBFOXYV2
import NS25Lean.P2BranchBOldPrefixAperyDiamond

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L5A1 L5A2B4AR1
open L5A2B L5A2B4AR4R1 L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR5 L5A2C4OR6

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- A strict-prefix multiple cannot already lie in the normalized tail.
This is exactly the defining minimality of the first principal return. -/
theorem branchB_nonprincipal_multiple_not_mem
    (R : SectorBCriticalRoleBranchB P) {j : ℕ}
    (hjpos : 1 ≤ j) (hjlt : j < actualPrincipalIndex P.M.base) :
    j * routingM P.M.base (branchBInactiveReindex R) ∉
      routingH P.M.base (branchBInactiveReindex R) := by
  intro hjmem
  have hjmem' : j * normalizedM P.M.base ∈ normalizedH P.M.base := by
    rw [← branchBRoutingH_eq_normalizedH R]
    simpa [routingM] using hjmem
  have hqle := principalIndex_min (normalizedH P.M.base)
    (normalizedM P.M.base) P.M.base.q_positive hjpos hjmem'
  exact (Nat.not_le_of_gt hjlt) hqle

/-- The Apéry representative attached to a return level in the inactive
Branch-B residue system. -/
noncomputable def branchBNonprincipalAperyAnchor
    (R : SectorBCriticalRoleBranchB P) (j : ℕ) : ℤ := by
  let a := routingA P.M.base (branchBInactiveReindex R)
  letI : NeZero a := ⟨(routingA_pos P.M.base (branchBInactiveReindex R)).ne'⟩
  exact (routingH P.M.base (branchBInactiveReindex R)).asRelativeIdeal.aperyRepresentative a
      (j * routingM P.M.base (branchBInactiveReindex R) : ZMod a)

/-- The source-exact data available for every strict-prefix return level.
It deliberately records no chart classification: first-return minimality
gives the positive Apéry defect, but not exclusion of the CENTER chart. -/
structure BranchBNonprincipalAperyAnchorPacket
    (R : SectorBCriticalRoleBranchB P) (j : ℕ) where
  beta : ℤ
  defect : ℕ
  beta_eq_apery : beta = branchBNonprincipalAperyAnchor R j
  beta_mem :
    beta ∈ (routingH P.M.base (branchBInactiveReindex R)).asRelativeIdeal
  beta_mod :
    (beta : ZMod (routingA P.M.base (branchBInactiveReindex R))) =
      (j * routingM P.M.base (branchBInactiveReindex R) :
        ZMod (routingA P.M.base (branchBInactiveReindex R)))
  anchor_eq :
    beta = (j * routingM P.M.base (branchBInactiveReindex R) : ℕ) +
      routingA P.M.base (branchBInactiveReindex R) * defect
  defect_pos : 0 < defect

/-- Every strict-prefix level has an Apéry representative strictly above
the corresponding multiple, by a positive multiple of the inactive modulus.
No strict-arm assertion is hidden in this packet. -/
noncomputable def branchB_nonprincipal_apery_anchor_packet
    (R : SectorBCriticalRoleBranchB P) {j : ℕ}
    (hjpos : 1 ≤ j) (hjlt : j < actualPrincipalIndex P.M.base) :
    BranchBNonprincipalAperyAnchorPacket R j := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let H := routingH B e
  let a := routingA B e
  let m := routingM B e
  let n := j * m
  letI : NeZero a := ⟨(routingA_pos B e).ne'⟩
  let beta := branchBNonprincipalAperyAnchor R j
  have hn_not_mem : n ∉ H := by
    dsimp only [n, m, H, B, e]
    exact branchB_nonprincipal_multiple_not_mem R hjpos hjlt
  have hbeta_mem : beta ∈ H.asRelativeIdeal := by
    dsimp only [beta, branchBNonprincipalAperyAnchor]
    exact H.asRelativeIdeal.aperyRepresentative_mem a _
  have hbeta_mod : (beta : ZMod a) = (n : ZMod a) := by
    have h := H.asRelativeIdeal.aperyRepresentative_mod a (n : ZMod a)
    simpa [beta, branchBNonprincipalAperyAnchor, n, m, H, a, B, e,
      Nat.cast_mul] using h
  have hbeta_mod_int : (beta : ZMod a) = ((n : ℤ) : ZMod a) := by
    simpa using hbeta_mod
  have hn_lt_beta : (n : ℤ) < beta := by
    by_contra hnot
    have hbeta_le : beta ≤ (n : ℤ) := le_of_not_gt hnot
    obtain ⟨k, hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
      a hbeta_le hbeta_mod_int.symm
    rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hbeta_mem
    obtain ⟨b, hbH, hbeta_b⟩ := hbeta_mem
    have hn_eq : n = b + a * k := by
      exact_mod_cast (show (n : ℤ) = (b : ℤ) + (a * k : ℕ) by
        rw [hk, hbeta_b]
        norm_num)
    have haH : a ∈ H := by
      dsimp only [a, H, B, e]
      rw [branchBRoutingH_eq_normalizedH R,
        branchB_inactive_routingA_eq_normalizedC R]
      exact branchB_actual_normalizedC_mem R
    have hakH : a * k ∈ H := by
      simpa [nsmul_eq_mul, Nat.mul_comm] using H.toAddSubmonoid.nsmul_mem haH k
    apply hn_not_mem
    rw [hn_eq]
    exact H.add_mem hbH hakH
  let hdefectExists := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
    a (le_of_lt hn_lt_beta) hbeta_mod_int
  let defect := Classical.choose hdefectExists
  have hdefect := Classical.choose_spec hdefectExists
  have hdefect_pos : 0 < defect := by
    by_contra hnot
    have hd0 : defect = 0 := Nat.eq_zero_of_not_pos hnot
    change beta = (n : ℤ) + (a : ℤ) * (defect : ℤ) at hdefect
    rw [hd0, Nat.cast_zero, mul_zero, add_zero] at hdefect
    omega
  exact {
    beta := beta
    defect := defect
    beta_eq_apery := rfl
    beta_mem := hbeta_mem
    beta_mod := by
      dsimp only [beta, n, m, a, B, e] at hbeta_mod ⊢
      simpa [Nat.cast_mul] using hbeta_mod
    anchor_eq := hdefect
    defect_pos := hdefect_pos
  }

/-- Current kernel-exact localization of the nonprincipal Apéry anchor.
The three alternatives are exhaustive, and the CENTER alternative is kept
explicit because first-return minimality alone does not eliminate it. -/
theorem branchB_nonprincipal_apery_anchor_lShape_trichotomy
    (R : SectorBCriticalRoleBranchB P) {j : ℕ}
    (hjpos : 1 ≤ j) (hjlt : j < actualPrincipalIndex P.M.base) :
    let e := branchBInactiveReindex R
    let D := branchB_inactive_coherentHerzogData R
    let A := branchB_nonprincipal_apery_anchor_packet R hjpos hjlt
    ∃ i k : ℤ,
      InLShape (cr12 D) (cr13 D) (cr32 D) (cr23 D) i k ∧
      Int.ModEq (routingA P.M.base e)
        (i * routingB P.M.base e + k * routingC P.M.base e) A.beta ∧
      ((i < cr12 D ∧ k < cr13 D) ∨
        ((cr12 D : ℤ) ≤ i ∧ k < cr13 D) ∨
        (i < cr12 D ∧ (cr13 D : ℤ) ≤ k)) := by
  dsimp only
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  let A := branchB_nonprincipal_apery_anchor_packet R hjpos hjlt
  obtain ⟨ik, hik, _hunique⟩ :=
    coherent_lShape_unique_coordinate P.M.base e D A.beta
  refine ⟨ik.1, ik.2, hik.1, hik.2, ?_⟩
  rcases hik.1 with ⟨_hi0, _hk0, _hibound, _hkbound, hcorner⟩
  by_cases hi : ik.1 < (cr12 D : ℤ)
  · by_cases hk : ik.2 < (cr13 D : ℤ)
    · exact Or.inl ⟨hi, hk⟩
    · exact Or.inr (Or.inr ⟨hi, le_of_not_gt hk⟩)
  · exact Or.inr (Or.inl ⟨le_of_not_gt hi, hcorner.resolve_left hi⟩)

end NS25Lean.L5A2B4AR5B
