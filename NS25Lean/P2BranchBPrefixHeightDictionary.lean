import NS25Lean.P2BranchBOldPrefixAperyDiamond

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B L2B2A2 L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2C4H CombinatorialCore

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The ambient normalized-semigroup Apéry value in the inactive
Branch-B residue chart.  This is deliberately distinct from both prefix
and final routing heights. -/
noncomputable def branchBPrefixAlpha
    (R : SectorBCriticalRoleBranchB P)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) : ℤ := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  exact (routingH P.M.base e).asRelativeIdeal.aperyRepresentative
    (routingA P.M.base e) r

/-- Every prefix Apéry value is an actual element of the ambient
normalized semigroup.  The proof opens the prefix return level and uses
the first component of `J_(ell*m) = H ∩ (ell*m + H)`. -/
theorem branchB_prefix_aperyRepresentative_mem_ambient
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    (branchBActualPrefixIdeal R x hsx).aperyRepresentative
        (routingA P.M.base e) r ∈ (routingH P.M.base e).asRelativeIdeal := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Iminus := branchBActualPrefixIdeal R x hsx
  have hp := Iminus.aperyRepresentative_mem (routingA P.M.base e) r
  change ∃ ell : ℕ, 0 < ell ∧ ell < actualPrincipalIndex P.M.base ∧
    Iminus.aperyRepresentative (routingA P.M.base e) r ∈
      returnIdeal (routingH P.M.base e) (ell * normalizedM P.M.base) at hp
  obtain ⟨ell, hellpos, helllt, hreturn⟩ := hp
  exact hreturn.1

/-- Ambient Apéry minimality places `alpha` below the prefix Apéry value
in the same residue. -/
theorem branchB_prefix_alpha_le
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    branchBPrefixAlpha R r ≤
      (branchBActualPrefixIdeal R x hsx).aperyRepresentative
        (routingA P.M.base e) r := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  apply (routingH P.M.base e).asRelativeIdeal.aperyRepresentative_le
    (routingA P.M.base e) r
  · exact branchB_prefix_aperyRepresentative_mem_ambient R x hsx r
  · exact (branchBActualPrefixIdeal R x hsx).aperyRepresentative_mod
      (routingA P.M.base e) r

private theorem existsUnique_branchBPrefixHeight
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    ∃! eta : ℕ,
      (branchBActualPrefixIdeal R x hsx).aperyRepresentative
          (routingA P.M.base e) r =
        branchBPrefixAlpha R r + routingA P.M.base e * eta := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Iminus := branchBActualPrefixIdeal R x hsx
  let alpha := branchBPrefixAlpha R r
  let lambda := Iminus.aperyRepresentative (routingA P.M.base e) r
  have hle : alpha ≤ lambda := branchB_prefix_alpha_le R x hsx r
  have hmod : (lambda : ZMod (routingA P.M.base e)) =
      (alpha : ZMod (routingA P.M.base e)) := by
    change
      ((Iminus.aperyRepresentative (routingA P.M.base e) r : ℤ) :
          ZMod (routingA P.M.base e)) =
        (((routingH P.M.base e).asRelativeIdeal.aperyRepresentative
            (routingA P.M.base e) r : ℤ) : ZMod (routingA P.M.base e))
    rw [Iminus.aperyRepresentative_mod,
      (routingH P.M.base e).asRelativeIdeal.aperyRepresentative_mod]
  obtain ⟨eta, heta⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
    (routingA P.M.base e) hle hmod
  refine ⟨eta, heta, ?_⟩
  intro k hk
  have ha : (0 : ℤ) < routingA P.M.base e := by
    exact_mod_cast routingA_pos P.M.base e
  change lambda = alpha + (routingA P.M.base e : ℤ) * k at hk
  rw [heta] at hk
  have hmul : (routingA P.M.base e : ℤ) * eta =
      (routingA P.M.base e : ℤ) * k := by omega
  have hcast : (eta : ℤ) = k := mul_left_cancel₀ (ne_of_gt ha) hmul
  exact_mod_cast hcast.symm

/-- The exact nonnegative quotient between the prefix and ambient Apéry
representatives in one residue. -/
noncomputable def branchBPrefixHeight
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) : ℕ := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  exact Classical.choose (existsUnique_branchBPrefixHeight R x hsx r)

/-- B31 prefix height dictionary:
`lambdaMinus(r) = alpha(r) + a * etaMinus(r)`. -/
theorem branchB_prefix_apery_eq_ambient_apery_add_height_mul
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    (branchBActualPrefixIdeal R x hsx).aperyRepresentative
        (routingA P.M.base e) r =
      branchBPrefixAlpha R r +
        routingA P.M.base e * branchBPrefixHeight R x hsx r :=
  (Classical.choose_spec (existsUnique_branchBPrefixHeight R x hsx r)).1

/-- The ambient carry in the inactive chart's `b` direction. -/
noncomputable def branchBPrefixAmbientU
    (R : SectorBCriticalRoleBranchB P)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) : ℕ := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  exact (routingH P.M.base e).asRelativeIdeal.aperyStepQuotient
    (routingA P.M.base e) (routingB P.M.base e)
      (routingHB P.M.base e) r

/-- The ambient carry in the inactive chart's `c` direction. -/
noncomputable def branchBPrefixAmbientV
    (R : SectorBCriticalRoleBranchB P)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) : ℕ := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  exact (routingH P.M.base e).asRelativeIdeal.aperyStepQuotient
    (routingA P.M.base e) (routingC P.M.base e)
      (routingHC P.M.base e) r

/-- Exact change-of-height equation in the inactive `b` direction.  It
retains the ambient carry instead of assuming a no-wrap law. -/
theorem branchB_prefix_height_step_b_with_ambient_carry
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Iminus := branchBActualPrefixIdeal R x hsx
    branchBPrefixHeight R x hsx r + branchBPrefixAmbientU R r =
      branchBPrefixHeight R x hsx (r + routingB P.M.base e) +
        Iminus.aperyStepQuotient (routingA P.M.base e)
          (routingB P.M.base e) (routingHB P.M.base e) r := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Iminus := branchBActualPrefixIdeal R x hsx
  have hl0 := branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx r
  have hl1 := branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx
    (r + routingB P.M.base e)
  have hprefix := Iminus.apery_step_eq (routingA P.M.base e)
    (routingB P.M.base e) (routingHB P.M.base e) r
  have hambient := (routingH P.M.base e).asRelativeIdeal.apery_step_eq
    (routingA P.M.base e) (routingB P.M.base e)
      (routingHB P.M.base e) r
  change Iminus.aperyRepresentative (routingA P.M.base e) r =
    branchBPrefixAlpha R r + (routingA P.M.base e : ℤ) *
      branchBPrefixHeight R x hsx r at hl0
  change Iminus.aperyRepresentative (routingA P.M.base e)
      (r + routingB P.M.base e) =
    branchBPrefixAlpha R (r + routingB P.M.base e) +
      (routingA P.M.base e : ℤ) *
        branchBPrefixHeight R x hsx (r + routingB P.M.base e) at hl1
  change branchBPrefixAlpha R r + routingB P.M.base e =
    branchBPrefixAlpha R (r + routingB P.M.base e) +
      (routingA P.M.base e : ℤ) * branchBPrefixAmbientU R r at hambient
  have ha : (0 : ℤ) < routingA P.M.base e := by
    exact_mod_cast routingA_pos P.M.base e
  have hprod :
      (routingA P.M.base e : ℤ) *
          ((branchBPrefixHeight R x hsx r : ℤ) + branchBPrefixAmbientU R r) =
        (routingA P.M.base e : ℤ) *
          (branchBPrefixHeight R x hsx (r + routingB P.M.base e) +
            Iminus.aperyStepQuotient (routingA P.M.base e)
              (routingB P.M.base e) (routingHB P.M.base e) r) := by
    linear_combination hprefix - hl0 + hl1 - hambient
  have hcast :
      (branchBPrefixHeight R x hsx r : ℤ) + branchBPrefixAmbientU R r =
        branchBPrefixHeight R x hsx (r + routingB P.M.base e) +
          Iminus.aperyStepQuotient (routingA P.M.base e)
            (routingB P.M.base e) (routingHB P.M.base e) r :=
    mul_left_cancel₀ (ne_of_gt ha) hprod
  exact_mod_cast hcast

/-- Exact change-of-height equation in the inactive `c` direction. -/
theorem branchB_prefix_height_step_c_with_ambient_carry
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Iminus := branchBActualPrefixIdeal R x hsx
    branchBPrefixHeight R x hsx r + branchBPrefixAmbientV R r =
      branchBPrefixHeight R x hsx (r + routingC P.M.base e) +
        Iminus.aperyStepQuotient (routingA P.M.base e)
          (routingC P.M.base e) (routingHC P.M.base e) r := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Iminus := branchBActualPrefixIdeal R x hsx
  have hl0 := branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx r
  have hl1 := branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx
    (r + routingC P.M.base e)
  have hprefix := Iminus.apery_step_eq (routingA P.M.base e)
    (routingC P.M.base e) (routingHC P.M.base e) r
  have hambient := (routingH P.M.base e).asRelativeIdeal.apery_step_eq
    (routingA P.M.base e) (routingC P.M.base e)
      (routingHC P.M.base e) r
  change Iminus.aperyRepresentative (routingA P.M.base e) r =
    branchBPrefixAlpha R r + (routingA P.M.base e : ℤ) *
      branchBPrefixHeight R x hsx r at hl0
  change Iminus.aperyRepresentative (routingA P.M.base e)
      (r + routingC P.M.base e) =
    branchBPrefixAlpha R (r + routingC P.M.base e) +
      (routingA P.M.base e : ℤ) *
        branchBPrefixHeight R x hsx (r + routingC P.M.base e) at hl1
  change branchBPrefixAlpha R r + routingC P.M.base e =
    branchBPrefixAlpha R (r + routingC P.M.base e) +
      (routingA P.M.base e : ℤ) * branchBPrefixAmbientV R r at hambient
  have ha : (0 : ℤ) < routingA P.M.base e := by
    exact_mod_cast routingA_pos P.M.base e
  have hprod :
      (routingA P.M.base e : ℤ) *
          ((branchBPrefixHeight R x hsx r : ℤ) + branchBPrefixAmbientV R r) =
        (routingA P.M.base e : ℤ) *
          (branchBPrefixHeight R x hsx (r + routingC P.M.base e) +
            Iminus.aperyStepQuotient (routingA P.M.base e)
              (routingC P.M.base e) (routingHC P.M.base e) r) := by
    linear_combination hprefix - hl0 + hl1 - hambient
  have hcast :
      (branchBPrefixHeight R x hsx r : ℤ) + branchBPrefixAmbientV R r =
        branchBPrefixHeight R x hsx (r + routingC P.M.base e) +
          Iminus.aperyStepQuotient (routingA P.M.base e)
            (routingC P.M.base e) (routingHC P.M.base e) r :=
    mul_left_cancel₀ (ne_of_gt ha) hprod
  exact_mod_cast hcast

/-- The sound height dictionary specialized to the four residues of the
actual OLD same-diamond packet.  This records no F/O tag and assumes no
ambient no-wrap law. -/
theorem branchB_positive_center_pureB_reverseX_old_prefix_height_dictionary
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = i ∧ S.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hOld : IsOldActualBranch R x hsx) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Iminus := branchBActualPrefixIdeal R x hsx
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    let r := branchBActualExceptionalRoutingSource P R x
    let alpha := branchBPrefixAlpha R
    let etaMinus := branchBPrefixHeight R x hsx
    Iminus.aperyRepresentative (routingA P.M.base e) A =
        alpha A + routingA P.M.base e * etaMinus A ∧
      Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.b A) =
        alpha (Gminus.b A) + routingA P.M.base e * etaMinus (Gminus.b A) ∧
      Iminus.aperyRepresentative (routingA P.M.base e) (Gminus.c A) =
        alpha (Gminus.c A) + routingA P.M.base e * etaMinus (Gminus.c A) ∧
      Iminus.aperyRepresentative (routingA P.M.base e) r.val =
        alpha r.val + routingA P.M.base e * etaMinus r.val := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Iminus := branchBActualPrefixIdeal R x hsx
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let alpha := branchBPrefixAlpha R
  let etaMinus := branchBPrefixHeight R x hsx
  exact ⟨branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx A,
    branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx (Gminus.b A),
    branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx (Gminus.c A),
    branchB_prefix_apery_eq_ambient_apery_add_height_mul R x hsx r.val⟩

/-- The strongest four-cell height stencil available before proving any
ambient no-wrap statement.  The residual terms are exactly the four
ambient Apéry carries, so this theorem isolates the remaining semantic
frontier without importing a historical F/O label. -/
theorem branchB_positive_center_pureB_reverseX_old_prefix_height_carry_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = i ∧ S.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hOld : IsOldActualBranch R x hsx) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    let r := branchBActualExceptionalRoutingSource P R x
    let etaMinus := branchBPrefixHeight R x hsx
    let ambientU := branchBPrefixAmbientU R
    let ambientV := branchBPrefixAmbientV R
    let h := Gminus.u (Gminus.c A)
    0 < h ∧
      etaMinus A + ambientU A = etaMinus (Gminus.b A) ∧
      etaMinus A + ambientV A = etaMinus (Gminus.c A) ∧
      etaMinus (Gminus.c A) + ambientU (Gminus.c A) = etaMinus r.val + h ∧
      etaMinus (Gminus.b A) + ambientV (Gminus.b A) = etaMinus r.val + h := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let etaMinus := branchBPrefixHeight R x hsx
  let ambientU := branchBPrefixAmbientU R
  let ambientV := branchBPrefixAmbientV R
  let h := Gminus.u (Gminus.c A)
  have hold := hOld
  change _ ∧ _ ∧ _ ∧ Gminus.IsBranch A ∧
    Gminus.branchTarget A = r.val ∧ _ at hold
  have hbranch : Gminus.IsBranch A := hold.2.2.2.1
  have htarget : Gminus.branchTarget A = r.val := hold.2.2.2.2.1
  have hp :=
    branchB_positive_center_pureB_reverseX_old_prefix_apery_diamond_packet
      R hB x hsx i j hcenter hroute hOld
  change 0 < h ∧ Gminus.v (Gminus.b A) = h ∧ _ at hp
  have hpos : 0 < h := hp.1
  have hcross : Gminus.v (Gminus.b A) = h := hp.2.1
  have hbA := branchB_prefix_height_step_b_with_ambient_carry R x hsx A
  have hcA := branchB_prefix_height_step_c_with_ambient_carry R x hsx A
  have hbC := branchB_prefix_height_step_b_with_ambient_carry R x hsx (Gminus.c A)
  have hcB := branchB_prefix_height_step_c_with_ambient_carry R x hsx (Gminus.b A)
  change etaMinus A + ambientU A = etaMinus (Gminus.b A) + Gminus.u A at hbA
  change etaMinus A + ambientV A = etaMinus (Gminus.c A) + Gminus.v A at hcA
  change etaMinus (Gminus.c A) + ambientU (Gminus.c A) =
    etaMinus (Gminus.b (Gminus.c A)) + h at hbC
  change etaMinus (Gminus.b A) + ambientV (Gminus.b A) =
    etaMinus (Gminus.c (Gminus.b A)) + Gminus.v (Gminus.b A) at hcB
  have hb0 : Gminus.u A = 0 := hbranch.1
  have hc0 : Gminus.v A = 0 := hbranch.2
  have hbBase : etaMinus A + ambientU A = etaMinus (Gminus.b A) := by
    simpa [hb0] using hbA
  have hcBase : etaMinus A + ambientV A = etaMinus (Gminus.c A) := by
    simpa [hc0] using hcA
  have hbTop : etaMinus (Gminus.c A) + ambientU (Gminus.c A) =
      etaMinus r.val + h := by
    rw [← htarget]
    simpa [ResidueData.branchTarget, Gminus.commute A] using hbC
  have hcTop : etaMinus (Gminus.b A) + ambientV (Gminus.b A) =
      etaMinus r.val + h := by
    rw [← htarget]
    simpa [ResidueData.branchTarget, hcross] using hcB
  exact ⟨hpos, hbBase, hcBase, hbTop, hcTop⟩

/-- A pure `normalizedB` value below its actual critical exponent is the
ambient Apéry representative modulo `normalizedC`.  This is the
source-exact critical-minimality argument needed at the reverse-X target. -/
theorem branchB_prefix_alpha_pureB_below_c2
    (R : SectorBCriticalRoleBranchB P) (k : ℕ)
    (hk : k < L5A2B4AR4R2B.c2 R) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    branchBPrefixAlpha R
        (((k * normalizedB R : ℕ) : ℤ) : ZMod (routingA P.M.base e)) =
      (k * normalizedB R : ℕ) := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let H := routingH P.M.base e
  let residue : ZMod (routingA P.M.base e) :=
    (((k * normalizedB R : ℕ) : ℤ) : ZMod (routingA P.M.base e))
  let alpha := branchBPrefixAlpha R residue
  have hrA : routingA P.M.base e = normalizedC R := by
    simpa [e] using branchB_inactive_routingA_eq_normalizedC R
  have hrB : routingB P.M.base e = normalizedA R := by
    simpa [e] using branchB_inactive_routingB_eq_normalizedA R
  have hrC : routingC P.M.base e = normalizedB R := by
    simpa [e] using branchB_inactive_routingC_eq_normalizedB R
  have hsourceH : k * normalizedB R ∈ H := by
    have hm := H.toAddSubmonoid.nsmul_mem (routingHC P.M.base e) k
    simpa [H, hrC, nsmul_eq_mul, Nat.mul_comm] using hm
  have hsourceMem : ((k * normalizedB R : ℕ) : ℤ) ∈ H.asRelativeIdeal :=
    ⟨k * normalizedB R, hsourceH, rfl⟩
  have hle : alpha ≤ (k * normalizedB R : ℕ) := by
    apply H.asRelativeIdeal.aperyRepresentative_le
      (routingA P.M.base e) residue hsourceMem
    rfl
  have hmod : ((((k * normalizedB R : ℕ) : ℤ) :
      ZMod (routingA P.M.base e))) =
      (alpha : ZMod (routingA P.M.base e)) := by
    change residue =
      (((H.asRelativeIdeal.aperyRepresentative
        (routingA P.M.base e) residue : ℤ)) : ZMod (routingA P.M.base e))
    rw [H.asRelativeIdeal.aperyRepresentative_mod]
  obtain ⟨t, ht⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
    (routingA P.M.base e) hle hmod
  by_cases ht0 : t = 0
  · subst t
    change branchBPrefixAlpha R residue = (k * normalizedB R : ℕ)
    simpa [alpha] using ht.symm
  have htpos : 0 < t := Nat.pos_of_ne_zero ht0
  have halphaMem : alpha ∈ H.asRelativeIdeal := by
    exact H.asRelativeIdeal.aperyRepresentative_mem (routingA P.M.base e) residue
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at halphaMem
  obtain ⟨n, hnH, halphaEq⟩ := halphaMem
  have hnClosure : n ∈ AddSubmonoid.closure
      {routingA P.M.base e, routingB P.M.base e, routingC P.M.base e} :=
    (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base e)).1).1 hnH
  have hnGen : n ∈ generatedThree (routingA P.M.base e)
      (routingB P.M.base e) (routingC P.M.base e) := hnClosure
  obtain ⟨p, q, z, hn⟩ :=
    (FourGeneratedBridge.mem_generatedThree_iff
      (routingA P.M.base e) (routingB P.M.base e)
        (routingC P.M.base e) n).mp hnGen
  have heqNat : k * normalizedB R = n + normalizedC R * t := by
    have ht' := ht
    rw [halphaEq, hrA] at ht'
    exact_mod_cast ht'
  have heq : k * normalizedB R =
      p * normalizedC R + q * normalizedA R + z * normalizedB R +
        normalizedC R * t := by
    rw [hn, hrA, hrB, hrC] at heqNat
    exact heqNat
  have hbpos : 0 < normalizedB R := by
    have hs := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex 1)
    have hw := L2B.weights_positive P.M.base (R.reindex 1)
    change 0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex 1)
    nlinarith
  have hcpos : 0 < normalizedC R := by
    have hs := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex 2)
    have hw := L2B.weights_positive P.M.base (R.reindex 2)
    change 0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex 2)
    nlinarith
  have hzlt : z < k := by
    by_contra hnot
    have hzk : k ≤ z := by omega
    have hctpos : 0 < normalizedC R * t := Nat.mul_pos hcpos htpos
    have hzb_lt : z * normalizedB R <
        p * normalizedC R + q * normalizedA R + z * normalizedB R +
          normalizedC R * t := by omega
    have hkb_le : k * normalizedB R ≤ z * normalizedB R :=
      Nat.mul_le_mul_right (normalizedB R) hzk
    omega
  have hqpos : 0 < k - z := by omega
  have hsplit : (k - z) * normalizedB R + z * normalizedB R =
      k * normalizedB R := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hzlt)]
  have hrel0 : (k - z) * normalizedB R =
      p * normalizedC R + q * normalizedA R + normalizedC R * t := by
    omega
  have hrel : (k - z) * normalizedB R =
      q * normalizedA R + (p + t) * normalizedC R := by
    rw [hrel0]
    ring
  have hmin := branchB_normalizedB_relation_min R (k - z) q (p + t) hqpos hrel
  exfalso
  omega

/-- At the actual reverse-X target, the prefix envelope height is zero.
This uses the legal actual prefix source equality and the subcritical
pure-`b` ambient Apéry theorem, not a sign heuristic for a candidate. -/
theorem branchB_positive_center_pureB_reverseX_prefix_height_target_eq_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = i ∧ S.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let r := branchBActualExceptionalRoutingSource P R x
    branchBPrefixHeight R x hsx r.val = 0 := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let r := branchBActualExceptionalRoutingSource P R x
  let s := branchBActualExceptionalNormalizedSource P R x
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  have hiLt := branchB_positive_center_pureB_anchor_i_lt_pH
    R hB hsx i j hcenter hroute
  have hsource := branchB_positive_center_pureB_reverseX_value_packet
    R hB hsx i j hcenter hroute
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    C.data.sourceValue = (i + zH R) * normalizedB R ∧ _ at hsource
  have hik : i + zH R < L5A2B4AR4R2B.c2 R := by
    let HC := branchB_actual_herzog_coordinates R
    obtain ⟨_hs1, hs2, _hs3⟩ := HC.coefficient_sums
    omega
  have halpha := branchB_prefix_alpha_pureB_below_c2 R (i + zH R) hik
  have hprefix := branchB_actualExceptional_prefix_source_packet R x hsx
  change _ ∧
    (branchBActualPrefixIdeal R x hsx).aperyRepresentative
      (routingA P.M.base e) r.val = s.val ∧ _ at hprefix
  have hsvalue : s.val = ((i + zH R) * normalizedB R : ℕ) := by
    calc
      s.val = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
      _ = ((i + zH R) * normalizedB R : ℕ) := by
        exact_mod_cast hsource.2.2.2.2.2.2.1
  have hresidue : r.val =
      ((((i + zH R) * normalizedB R : ℕ) : ℤ) :
        ZMod (routingA P.M.base e)) := by
    calc
      r.val = (s.val : ZMod (routingA P.M.base e)) := hprefix.2.2.symm
      _ = _ := by rw [hsvalue]
  have hdict := branchB_prefix_apery_eq_ambient_apery_add_height_mul
    R x hsx r.val
  rw [hresidue] at hdict
  rw [halpha] at hdict
  rw [hresidue] at hprefix
  rw [hsvalue] at hprefix
  have ha : (0 : ℤ) < routingA P.M.base e := by
    exact_mod_cast routingA_pos P.M.base e
  have hzeroCast : (branchBPrefixHeight R x hsx r.val : ℤ) = 0 := by
    rw [hresidue]
    nlinarith [hdict, hprefix.2.1]
  exact_mod_cast hzeroCast

/-- The other predecessor of a subcritical pure-`b` ambient Apéry value
cannot be obtained by subtracting `normalizedA`.  Otherwise its ambient
factorization would give a positive `b`-critical relation below `c2`. -/
theorem branchB_pureB_below_c2_sub_normalizedA_not_mem
    (R : SectorBCriticalRoleBranchB P) (k : ℕ)
    (hk : k < L5A2B4AR4R2B.c2 R) :
    let e := branchBInactiveReindex R
    ((k * normalizedB R : ℕ) : ℤ) - normalizedA R ∉
      (routingH P.M.base e).asRelativeIdeal := by
  let e := branchBInactiveReindex R
  let H := routingH P.M.base e
  have hrA : routingA P.M.base e = normalizedC R := by
    simpa [e] using branchB_inactive_routingA_eq_normalizedC R
  have hrB : routingB P.M.base e = normalizedA R := by
    simpa [e] using branchB_inactive_routingB_eq_normalizedA R
  have hrC : routingC P.M.base e = normalizedB R := by
    simpa [e] using branchB_inactive_routingC_eq_normalizedB R
  change ((k * normalizedB R : ℕ) : ℤ) - normalizedA R ∉ H.asRelativeIdeal
  intro hmem
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hmem
  obtain ⟨n, hnH, heqInt⟩ := hmem
  have hnClosure : n ∈ AddSubmonoid.closure
      {routingA P.M.base e, routingB P.M.base e, routingC P.M.base e} :=
    (NumericalSemigroup.mem_generatedByThree_iff
      (normalizedSemigroup_minimal (chosenBase_minimalFour P.M.base e)).1).1 hnH
  have hnGen : n ∈ generatedThree (routingA P.M.base e)
      (routingB P.M.base e) (routingC P.M.base e) := hnClosure
  obtain ⟨p, q, z, hn⟩ :=
    (FourGeneratedBridge.mem_generatedThree_iff
      (routingA P.M.base e) (routingB P.M.base e)
        (routingC P.M.base e) n).mp hnGen
  have heqNat : k * normalizedB R = normalizedA R + n := by
    exact_mod_cast (show
      ((k * normalizedB R : ℕ) : ℤ) = normalizedA R + n by omega)
  have heq : k * normalizedB R =
      normalizedA R +
        (p * normalizedC R + q * normalizedA R + z * normalizedB R) := by
    rw [hn, hrA, hrB, hrC] at heqNat
    exact heqNat
  have hapos : 0 < normalizedA R := branchB_actual_normalizedA_pos R
  have hbpos : 0 < normalizedB R := by
    have hs := L5A2B4AR3.normalizedWeight_scale P.M.base (R.reindex 1)
    have hw := L2B.weights_positive P.M.base (R.reindex 1)
    change 0 < L5A2B4AR3.normalizedWeight P.M.base (R.reindex 1)
    nlinarith
  have hzlt : z < k := by
    by_contra hnot
    have hzk : k ≤ z := by omega
    have hazpos : 0 < normalizedA R + p * normalizedC R +
        q * normalizedA R := by omega
    have hzb_lt : z * normalizedB R <
        normalizedA R +
          (p * normalizedC R + q * normalizedA R + z * normalizedB R) := by
      omega
    have hkb_le : k * normalizedB R ≤ z * normalizedB R :=
      Nat.mul_le_mul_right (normalizedB R) hzk
    omega
  have hqpos : 0 < k - z := by omega
  have hsplit : (k - z) * normalizedB R + z * normalizedB R =
      k * normalizedB R := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hzlt)]
  have hrel0 : (k - z) * normalizedB R =
      normalizedA R + p * normalizedC R + q * normalizedA R := by
    omega
  have hrel : (k - z) * normalizedB R =
      (q + 1) * normalizedA R + p * normalizedC R := by
    rw [hrel0]
    ring
  have hmin := branchB_normalizedB_relation_min R
    (k - z) (q + 1) p hqpos hrel
  omega

/-- In an OLD reverse-X diamond, the ambient carry on the `b`-edge from
`c A` to the actual target is strictly nonzero.  Thus the historical
all-equal positive height stencil cannot be obtained by silently dropping
ambient carries. -/
theorem branchB_positive_center_pureB_reverseX_old_top_ambientU_ne_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = i ∧ S.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hOld : IsOldActualBranch R x hsx) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    branchBPrefixAmbientU R (Gminus.c A) ≠ 0 := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let s := branchBActualExceptionalNormalizedSource P R x
  let H := routingH P.M.base e
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  have hiLt := branchB_positive_center_pureB_anchor_i_lt_pH
    R hB hsx i j hcenter hroute
  have hsource := branchB_positive_center_pureB_reverseX_value_packet
    R hB hsx i j hcenter hroute
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    C.data.sourceValue = (i + zH R) * normalizedB R ∧ _ at hsource
  have hik : i + zH R < L5A2B4AR4R2B.c2 R := by
    let HC := branchB_actual_herzog_coordinates R
    obtain ⟨_hs1, hs2, _hs3⟩ := HC.coefficient_sums
    omega
  have hnotmem := branchB_pureB_below_c2_sub_normalizedA_not_mem
    R (i + zH R) hik
  have halpha := branchB_prefix_alpha_pureB_below_c2 R (i + zH R) hik
  have hprefix := branchB_actualExceptional_prefix_source_packet R x hsx
  have hsvalue : s.val = ((i + zH R) * normalizedB R : ℕ) := by
    calc
      s.val = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
      _ = ((i + zH R) * normalizedB R : ℕ) := by
        exact_mod_cast hsource.2.2.2.2.2.2.1
  have hresidue : r.val =
      ((((i + zH R) * normalizedB R : ℕ) : ℤ) :
        ZMod (routingA P.M.base e)) := by
    calc
      r.val = (s.val : ZMod (routingA P.M.base e)) := hprefix.2.2.symm
      _ = _ := by rw [hsvalue]
  have htarget : Gminus.branchTarget A = r.val := hOld.2.2.2.2.1
  change H.asRelativeIdeal.aperyStepQuotient
    (routingA P.M.base e) (routingB P.M.base e)
      (routingHB P.M.base e) (Gminus.c A) ≠ 0
  intro hzero
  have hbad := (H.asRelativeIdeal.aperyStepQuotient_eq_zero_iff_sub_mem
    (routingA P.M.base e) (routingB P.M.base e)
      (routingHB P.M.base e) (Gminus.c A)).mp hzero
  change branchBPrefixAlpha R (Gminus.b (Gminus.c A)) -
      routingB P.M.base e ∈ H.asRelativeIdeal at hbad
  rw [Gminus.commute A] at hbad
  rw [show Gminus.c (Gminus.b A) = r.val by
    simpa [ResidueData.branchTarget] using htarget] at hbad
  rw [hresidue, halpha] at hbad
  have hrB : routingB P.M.base e = normalizedA R := by
    simpa [e] using branchB_inactive_routingB_eq_normalizedA R
  rw [hrB] at hbad
  exact hnotmem hbad

/-- The cyclic top edge has zero ambient carry: the actual pure-`b`
target can be moved back by one `normalizedB` because its coefficient is
positive. -/
theorem branchB_positive_center_pureB_reverseX_old_top_ambientV_eq_zero
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = i ∧ S.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hOld : IsOldActualBranch R x hsx) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    branchBPrefixAmbientV R (Gminus.b A) = 0 := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let s := branchBActualExceptionalNormalizedSource P R x
  let H := routingH P.M.base e
  let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
  have hiLt := branchB_positive_center_pureB_anchor_i_lt_pH
    R hB hsx i j hcenter hroute
  have hsource := branchB_positive_center_pureB_reverseX_value_packet
    R hB hsx i j hcenter hroute
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    C.data.sourceValue = (i + zH R) * normalizedB R ∧ _ at hsource
  have hik : i + zH R < L5A2B4AR4R2B.c2 R := by
    let HC := branchB_actual_herzog_coordinates R
    obtain ⟨_hs1, hs2, _hs3⟩ := HC.coefficient_sums
    omega
  have halpha := branchB_prefix_alpha_pureB_below_c2 R (i + zH R) hik
  have hprefix := branchB_actualExceptional_prefix_source_packet R x hsx
  have hsvalue : s.val = ((i + zH R) * normalizedB R : ℕ) := by
    calc
      s.val = (C.data.sourceValue : ℤ) := C.data.source_eq.symm
      _ = ((i + zH R) * normalizedB R : ℕ) := by
        exact_mod_cast hsource.2.2.2.2.2.2.1
  have hresidue : r.val =
      ((((i + zH R) * normalizedB R : ℕ) : ℤ) :
        ZMod (routingA P.M.base e)) := by
    calc
      r.val = (s.val : ZMod (routingA P.M.base e)) := hprefix.2.2.symm
      _ = _ := by rw [hsvalue]
  have htarget : Gminus.branchTarget A = r.val := hOld.2.2.2.2.1
  change H.asRelativeIdeal.aperyStepQuotient
    (routingA P.M.base e) (routingC P.M.base e)
      (routingHC P.M.base e) (Gminus.b A) = 0
  apply (H.asRelativeIdeal.aperyStepQuotient_eq_zero_iff_sub_mem
    (routingA P.M.base e) (routingC P.M.base e)
      (routingHC P.M.base e) (Gminus.b A)).2
  change branchBPrefixAlpha R (Gminus.c (Gminus.b A)) -
      routingC P.M.base e ∈ H.asRelativeIdeal
  rw [show Gminus.c (Gminus.b A) = r.val by
    simpa [ResidueData.branchTarget] using htarget]
  rw [hresidue, halpha]
  have hrC : routingC P.M.base e = normalizedB R := by
    simpa [e] using branchB_inactive_routingC_eq_normalizedB R
  rw [hrC, NumericalSemigroup.mem_asRelativeIdeal_iff]
  refine ⟨(i + zH R - 1) * normalizedB R, ?_, ?_⟩
  · have hm := H.toAddSubmonoid.nsmul_mem (routingHC P.M.base e)
      (i + zH R - 1)
    simpa [H, hrC, nsmul_eq_mul, Nat.mul_comm] using hm
  · have hcenter' := hcenter
    change _ ∧ _ ∧ 1 ≤ i ∧ _ at hcenter'
    have hkpos : 0 < i + zH R := by omega
    have hmul : (i + zH R - 1) * normalizedB R + normalizedB R =
        (i + zH R) * normalizedB R := by
      calc
        (i + zH R - 1) * normalizedB R + normalizedB R =
            (i + zH R - 1 + 1) * normalizedB R := by ring
        _ = (i + zH R) * normalizedB R := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ i + zH R)]
    have hmulZ := congrArg (fun n : ℕ => (n : ℤ)) hmul
    push_cast at hmulZ ⊢
    omega

/-- Corrected top-row OLD height packet.  One top height is exactly `h`,
whereas the other is strictly below `h` by the positive ambient carry. -/
theorem branchB_positive_center_pureB_reverseX_old_corrected_top_height_packet
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = i ∧ S.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hOld : IsOldActualBranch R x hsx) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    let r := branchBActualExceptionalRoutingSource P R x
    let etaMinus := branchBPrefixHeight R x hsx
    let h := Gminus.u (Gminus.c A)
    etaMinus r.val = 0 ∧
      etaMinus (Gminus.b A) = h ∧
      etaMinus (Gminus.c A) + branchBPrefixAmbientU R (Gminus.c A) = h ∧
      etaMinus (Gminus.c A) < h := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let etaMinus := branchBPrefixHeight R x hsx
  let h := Gminus.u (Gminus.c A)
  change branchBPrefixHeight R x hsx r.val = 0 ∧
    branchBPrefixHeight R x hsx (Gminus.b A) = h ∧
    branchBPrefixHeight R x hsx (Gminus.c A) +
        branchBPrefixAmbientU R (Gminus.c A) = h ∧
    branchBPrefixHeight R x hsx (Gminus.c A) < h
  have hD := branchB_positive_center_pureB_reverseX_prefix_height_target_eq_zero
    R hB x hsx i j hcenter hroute
  have hcarries :=
    branchB_positive_center_pureB_reverseX_old_prefix_height_carry_packet
      R hB x hsx i j hcenter hroute hOld
  have hUne :=
    branchB_positive_center_pureB_reverseX_old_top_ambientU_ne_zero
      R hB x hsx i j hcenter hroute hOld
  have hVzero :=
    branchB_positive_center_pureB_reverseX_old_top_ambientV_eq_zero
      R hB x hsx i j hcenter hroute hOld
  change branchBPrefixHeight R x hsx r.val = 0 at hD
  change 0 < h ∧ _ ∧ _ ∧
    branchBPrefixHeight R x hsx (Gminus.c A) +
        branchBPrefixAmbientU R (Gminus.c A) =
      branchBPrefixHeight R x hsx r.val + h ∧
    branchBPrefixHeight R x hsx (Gminus.b A) +
        branchBPrefixAmbientV R (Gminus.b A) =
      branchBPrefixHeight R x hsx r.val + h at hcarries
  change branchBPrefixAmbientU R (Gminus.c A) ≠ 0 at hUne
  change branchBPrefixAmbientV R (Gminus.b A) = 0 at hVzero
  have htopU := hcarries.2.2.2.1
  have htopV := hcarries.2.2.2.2
  constructor
  · exact hD
  constructor
  · omega
  constructor <;> omega

/-- The recovered current height object also excludes the historical
O-shaped zero triple on the OLD base and its two successors. -/
theorem branchB_positive_center_pureB_reverseX_old_not_O_height_stencil
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = i ∧ S.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hOld : IsOldActualBranch R x hsx) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    let etaMinus := branchBPrefixHeight R x hsx
    ¬(etaMinus A = 0 ∧ etaMinus (Gminus.b A) = 0 ∧
      etaMinus (Gminus.c A) = 0) := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  let etaMinus := branchBPrefixHeight R x hsx
  change ¬(branchBPrefixHeight R x hsx A = 0 ∧
    branchBPrefixHeight R x hsx (Gminus.b A) = 0 ∧
    branchBPrefixHeight R x hsx (Gminus.c A) = 0)
  intro hO
  have hp :=
    branchB_positive_center_pureB_reverseX_old_corrected_top_height_packet
      R hB x hsx i j hcenter hroute hOld
  let h := Gminus.u (Gminus.c A)
  change _ ∧ branchBPrefixHeight R x hsx (Gminus.b A) = h ∧ _ at hp
  have hpos :=
    (branchB_positive_center_pureB_reverseX_old_prefix_height_carry_packet
      R hB x hsx i j hcenter hroute hOld).1
  change 0 < h at hpos
  omega

/-- Red-team result: the historical `(h,h,h,0)` tuple is not the current
OLD reverse-X height stencil.  The exact top ambient carry is nonzero. -/
theorem branchB_positive_center_pureB_reverseX_old_not_all_equal_F_height_stencil
    (R : SectorBCriticalRoleBranchB P) (hB : SectorB P.M)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (i j : ℕ)
    (hcenter :
      let S := branchB_actual_selected_return_anchor_v2 R hB hsx
      S.coordinate.i = i ∧ S.coordinate.j = j ∧
        1 ≤ i ∧ i ≤ pH R ∧ 1 ≤ j ∧ j ≤ qH R ∧
        (i, j) ≠ (pH R, qH R))
    (hroute :
      let C := branchB_actual_prefix_canonical_lShape_coordinates R hB hsx
      ActualSourceSupportRoute.Matches ActualSourceSupportRoute.pureB
        C.data.sourceX C.data.sourceY C.data.sourceZ)
    (hOld : IsOldActualBranch R x hsx) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let A := x.val.val.val
    let r := branchBActualExceptionalRoutingSource P R x
    let etaMinus := branchBPrefixHeight R x hsx
    let h := Gminus.u (Gminus.c A)
    ¬(etaMinus A = h ∧ etaMinus (Gminus.b A) = h ∧
      etaMinus (Gminus.c A) = h ∧ etaMinus r.val = 0) := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let etaMinus := branchBPrefixHeight R x hsx
  let h := Gminus.u (Gminus.c A)
  change ¬(branchBPrefixHeight R x hsx A = h ∧
    branchBPrefixHeight R x hsx (Gminus.b A) = h ∧
    branchBPrefixHeight R x hsx (Gminus.c A) = h ∧
    branchBPrefixHeight R x hsx r.val = 0)
  intro hF
  have hcarries :=
    branchB_positive_center_pureB_reverseX_old_prefix_height_carry_packet
      R hB x hsx i j hcenter hroute hOld
  change 0 < h ∧ _ ∧ _ ∧
    etaMinus (Gminus.c A) + branchBPrefixAmbientU R (Gminus.c A) =
      etaMinus r.val + h ∧ _ at hcarries
  have hUne :=
    branchB_positive_center_pureB_reverseX_old_top_ambientU_ne_zero
      R hB x hsx i j hcenter hroute hOld
  have htop := hcarries.2.2.2.1
  change branchBPrefixHeight R x hsx (Gminus.c A) +
      branchBPrefixAmbientU R (Gminus.c A) =
    branchBPrefixHeight R x hsx r.val + h at htop
  change branchBPrefixAmbientU R (Gminus.c A) ≠ 0 at hUne
  omega

end NS25Lean.L5A2B4AR5B
