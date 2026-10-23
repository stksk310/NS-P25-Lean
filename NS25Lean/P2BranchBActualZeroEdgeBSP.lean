import NS25Lean.P2BranchBPrincipalSurgeryChannel
import NS25Lean.P2BranchBCorrectedM2M3

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open FourGeneratedBridge ChosenBase L2B2A2 L5A1 L5A2B4AR1
open L5A2B4AR4R1 L5A2C4H CombinatorialCore

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The exact lowering used by BSP FINAL, kept local to the actual prefix
and final ideals.  No family tag or BSP conclusion is stored in this
definition. -/
noncomputable def branchBActualZeroEdgeLowering
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (r : ZMod (routingA P.M.base (branchBInactiveReindex R))) : ℤ := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  exact ((branchBActualPrefixIdeal R x hsx).aperyRepresentative
      (routingA P.M.base e) r -
    (routingI P.M.base e).aperyRepresentative
      (routingA P.M.base e) r) / routingA P.M.base e

/-- Kernel checkpoint immediately before family-local BSP transport.

The actual event supplies one common base and target residue, the same
actual source as prefix and final Apéry representative, a prefix non-branch,
and a final branch.  Consequently the fourth lowering is exactly zero and
at least one prefix edge at the base is nonzero.  This theorem deliberately
does not classify that nonzero edge as X or Y: that is the remaining
source-complete family theorem, not a routing-formal consequence. -/
theorem branchB_actualZeroEdgeBirth_same_diamond_source_packet
    (R : SectorBCriticalRoleBranchB P)
    (x : BranchBActualExceptionalBranches P R)
    (hsx : IsBranchBirth (normalizedH P.M.base) (normalizedM P.M.base)
      (actualPrincipalIndex P.M.base)
      (branchBActualExceptionalNormalizedSource P R x).val)
    (hbirth : IsActualZeroEdgeBirth R x hsx) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let Gminus := branchBActualPrefixRoutingData R x hsx
    let G := routingData P.M.base e
    let Iminus := branchBActualPrefixIdeal R x hsx
    let Ifinal := routingI P.M.base e
    let A := x.val.val.val
    let r := branchBActualExceptionalRoutingSource P R x
    let s := branchBActualExceptionalNormalizedSource P R x
    let L := branchBActualZeroEdgeLowering R x hsx
    Gminus.IsSource r.val ∧
      Gminus.branchTarget A = r.val ∧
      G.branchTarget A = r.val ∧
      ¬ Gminus.IsBranch A ∧ G.IsBranch A ∧
      (Gminus.u A ≠ 0 ∨ Gminus.v A ≠ 0) ∧
      Iminus.aperyRepresentative (routingA P.M.base e) r.val = s.val ∧
      Ifinal.aperyRepresentative (routingA P.M.base e) r.val = s.val ∧
      G.b (G.c A) = r.val ∧ L (G.b (G.c A)) = 0 := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  let Gminus := branchBActualPrefixRoutingData R x hsx
  let G := routingData P.M.base e
  let Iminus := branchBActualPrefixIdeal R x hsx
  let Ifinal := routingI P.M.base e
  let A := x.val.val.val
  let r := branchBActualExceptionalRoutingSource P R x
  let s := branchBActualExceptionalNormalizedSource P R x
  let L := branchBActualZeroEdgeLowering R x hsx
  have hpref := branchB_actualExceptional_prefix_source_packet R x hsx
  have hfinal := branchB_actualExceptional_source_packet P R x
  have hedge := branchB_actualZeroEdgeBirth_edge_nonzero R x hsx hbirth
  have hrGminus : Gminus.branchTarget A = r.val := hbirth.2.2.2.2.1
  have hrG : G.branchTarget A = r.val := hbirth.2.2.2.2.2.2
  have hdiamond : G.b (G.c A) = r.val := by
    rw [G.commute A]
    simpa [ResidueData.branchTarget] using hrG
  refine ⟨hpref.1, hrGminus, hrG, hbirth.2.2.2.1,
    hbirth.2.2.2.2.2.1, hedge, hpref.2.1, ?_, hdiamond, ?_⟩
  · exact hfinal.2.2.2.1.symm
  · rw [hdiamond]
    change (Iminus.aperyRepresentative (routingA P.M.base e) r.val -
      Ifinal.aperyRepresentative (routingA P.M.base e) r.val) /
        routingA P.M.base e = 0
    rw [hpref.2.1, hfinal.2.2.2.1.symm]
    simp

end NS25Lean.L5A2B4AR5B
