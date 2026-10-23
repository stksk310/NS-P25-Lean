import NS25Lean.P2BranchBExceptionalResource

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open L5A1 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The complete topology-free Branch-B checkpoint immediately before the
missing exposed-PF selector.  It combines the actual raw accounting identity,
the inactive Gate/RECORD inequalities, the ENTRY `+1` equality, and the
existence of an actual exceptional endpoint.  It deliberately does not call
an arbitrary actual endpoint an OX/OY escape. -/
theorem branchB_topology_free_entry_pre_escape_kernel
    (hB : SectorB P.M) (R : SectorBCriticalRoleBranchB P)
    (hentry : P.W = 1) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    let D := L5A2C4H.routingData P.M.base e
    P.W = (L5A2C4M.ResidueData.Cbr D : ℤ) -
        (L5A2C4M.ResidueData.U D : ℤ) - (L5A2C4N.E P.M.base e : ℤ) ∧
      L5A2C4C.eta P.M.base e 0 0 < L5A2B4AR4R2B.c3 R ∧
      (L5A2C4C.eta P.M.base e
            (L5A2B4AR4R2B.r31 R - 1) (L5A2B4AR4R2B.r32 R) = 0 ∨
        L5A2C4C.eta P.M.base e
            (L5A2B4AR4R2B.r31 R) (L5A2B4AR4R2B.r32 R - 1) = 0) ∧
      (L5A2C4M.ResidueData.Cbr D : ℤ) =
        L5A2C4M.ResidueData.U D + L5A2C4N.E P.M.base e + 1 ∧
      Nonempty (BranchBActualExceptionalBranches P R) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  let D := L5A2C4H.routingData P.M.base e
  have hgate := branchB_actual_inactive_gate hB R
  exact ⟨branchB_actual_raw_routing_identity R, hgate.1, hgate.2,
    branchB_entry_unpaid_channel R hentry,
    branchB_entry_exists_actual_exceptional R hentry⟩

/-- ENTRY supplies an actual exceptional endpoint together with every
source-exact endpoint fact currently available before OX/OY orientation:
sinkhood, actual integrality, positive endpoint height, terminal B-zero, and
exceptional C-cross positivity.  The missing next theorem must identify the
distinguished seam-exposed channel; this packet does not assume that
identification. -/
theorem branchB_topology_free_entry_endpoint_packet
    (R : SectorBCriticalRoleBranchB P) (hentry : P.W = 1) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    let D := L5A2C4H.routingData P.M.base e
    ∃ x : BranchBActualExceptionalBranches P R,
      let p := L5A2C4I.ResidueData.canonicalBEndpoint D x.val.val
      D.IsSink p ∧
        (L5A2C4H.routingI P.M.base e).aperyRepresentative
            (L5A2C4H.routingA P.M.base e) p -
          L5A2C4H.routingA P.M.base e ∈
            (L5A2C4H.routingH P.M.base e).asRelativeIdeal ∧
        0 < D.v p ∧ D.v (D.b p) = 0 ∧ 0 < D.u (D.c p) := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  let D := L5A2C4H.routingData P.M.base e
  obtain ⟨x⟩ := branchB_entry_exists_actual_exceptional R hentry
  exact ⟨x, branchB_actualExceptional_endpoint_kernel P R x⟩

end NS25Lean.L5A2B4AR5B

