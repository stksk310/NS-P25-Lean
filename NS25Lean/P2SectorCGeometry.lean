import NS25Lean.P2SectorCBranchBridge

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C3G

open L2B L5A1

variable {Gamma : NumericalSemigroup}

/-- Actual contribution-level Sector-C fibers.  Every proof field is an
equality about the existing factorization objects; there is no gate, branch,
payment, or terminal premise in this record. -/
structure SectorCActualFibers (P : P2Data Gamma) where
  internalDegree : ℕ
  boundaryDegree : ℕ
  degree_ne : internalDegree ≠ boundaryDegree
  positiveDegrees_eq : positiveDegrees P.M = {internalDegree, boundaryDegree}
  internalSignature : LocalSignature P.M internalDegree 2 0
  boundarySignature : LocalSignature P.M boundaryDegree 2 1
  internalContribution : fiberContribution P.M internalDegree = 1
  boundaryContribution : fiberContribution P.M boundaryDegree = 1
  contribution_zero_elsewhere : ∀ x : ℕ,
    x ≠ internalDegree → x ≠ boundaryDegree → fiberContribution P.M x = 0

/-- The actual connected components of the internal `(2,0)` fiber. -/
abbrev internalComponents {P : P2Data Gamma} (G : SectorCActualFibers P) :=
  FiberComponent P.M.base G.internalDegree

/-- The actual connected components of the boundary `(2,1)` fiber. -/
abbrev boundaryComponents {P : P2Data Gamma} (G : SectorCActualFibers P) :=
  FiberComponent P.M.base G.boundaryDegree

/-- The actually boundary-killed components of the internal fiber. -/
abbrev internalKilledComponents {P : P2Data Gamma} (G : SectorCActualFibers P) :=
  {C : internalComponents G // BoundaryKilled P.M G.internalDegree C}

/-- The actually boundary-killed components of the boundary fiber. -/
abbrev boundaryKilledComponents {P : P2Data Gamma} (G : SectorCActualFibers P) :=
  {C : boundaryComponents G // BoundaryKilled P.M G.boundaryDegree C}

/-- Sector C really supplies two finite factorization-component objects.  The
first has two components and no killed component; the second has two
components and exactly one killed component.  Every component support is
nonempty.  This is the strongest source-free actual-geometry checkpoint
available before a Herzog gate/RECORD construction is proved. -/
theorem sectorC_actual_fibers (P : P2Data Gamma) (hC : SectorC P.M) :
    ∃ G : SectorCActualFibers P,
      Nat.card (internalComponents G) = 2 ∧
      Nat.card (boundaryComponents G) = 2 ∧
      Nat.card (internalKilledComponents G) = 0 ∧
      Nat.card (boundaryKilledComponents G) = 1 ∧
      (∀ C : internalComponents G,
        (componentSupport P.M.base G.internalDegree C).Nonempty) ∧
      (∀ C : boundaryComponents G,
        (componentSupport P.M.base G.boundaryDegree C).Nonempty) := by
  obtain ⟨h, g, hne, hpositive, hh, hg, hcontrib, gcontrib, hzero⟩ :=
    L5A2C2.sectorC_actual_signature_data P hC
  let G : SectorCActualFibers P :=
    { internalDegree := h
      boundaryDegree := g
      degree_ne := hne
      positiveDegrees_eq := hpositive
      internalSignature := hh
      boundarySignature := hg
      internalContribution := hcontrib
      boundaryContribution := gcontrib
      contribution_zero_elsewhere := hzero }
  have hhpos : 0 < h := (positive_contribution_active P.M h (by omega)).1
  have hgpos : 0 < g := (positive_contribution_active P.M g (by omega)).1
  refine ⟨G, hh.1, hg.1, hh.2, hg.2, ?_, ?_⟩
  · intro C
    exact componentSupport_nonempty P.M.base h hhpos C
  · intro C
    exact componentSupport_nonempty P.M.base g hgpos C

end NS25Lean.L5A2C3G
