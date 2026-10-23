import NS25Lean.P2SectorCActualDispatcherAssemblyR38
import NS25Lean.P2BranchARectangleLocalization

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR39

open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A

variable {Gamma : NumericalSemigroup}

private theorem pair_of_all_pure (B : Data Gamma) (h : ℕ)
    (hpos : 0 < h) (hcount : componentCount B h = 2)
    (hall : ∀ C : FiberComponent B h, (componentSupport B h C).card = 1) :
    Nonempty (PurePureCriticalPair B h) := by
  obtain ⟨C, D, hne, _⟩ := Nat.card_eq_two_iff.mp hcount
  exact purePureCriticalPair_of_components B h hpos hcount C D hne (hall C) (hall D)

private theorem two_pure_pairs_impossible (B : Data Gamma) {h g : ℕ}
    (hne : h ≠ g) (A : PurePureCriticalPair B h)
    (T : PurePureCriticalPair B g) : False := by
  classical
  have hll := pure_roles_ne_of_degree_ne B h g hne A.degree_pos T.degree_pos
    A.componentCount_eq_two T.componentCount_eq_two A.leftComponent T.leftComponent
    A.leftRole T.leftRole A.leftSupport T.leftSupport
  have hlr := pure_roles_ne_of_degree_ne B h g hne A.degree_pos T.degree_pos
    A.componentCount_eq_two T.componentCount_eq_two A.leftComponent T.rightComponent
    A.leftRole T.rightRole A.leftSupport T.rightSupport
  have hrl := pure_roles_ne_of_degree_ne B h g hne A.degree_pos T.degree_pos
    A.componentCount_eq_two T.componentCount_eq_two A.rightComponent T.leftComponent
    A.rightRole T.leftRole A.rightSupport T.leftSupport
  have hrr := pure_roles_ne_of_degree_ne B h g hne A.degree_pos T.degree_pos
    A.componentCount_eq_two T.componentCount_eq_two A.rightComponent T.rightComponent
    A.rightRole T.rightRole A.rightSupport T.rightSupport
  have hc : ({A.leftRole, A.rightRole, T.leftRole, T.rightRole} : Finset (Fin 3)).card = 4 := by
    simp [A.roles_ne, T.roles_ne, hll, hlr, hrl, hrr]
  have hb := Finset.card_le_univ
    ({A.leftRole, A.rightRole, T.leftRole, T.rightRole} : Finset (Fin 3))
  simp only [Fintype.card_fin] at hb
  omega

private def pairSwap {B : Data Gamma} {h : ℕ} (A : PurePureCriticalPair B h) :
    PurePureCriticalPair B h :=
  { A with
    leftComponent := A.rightComponent
    rightComponent := A.leftComponent
    components_ne := A.components_ne.symm
    leftRole := A.rightRole
    rightRole := A.leftRole
    roles_ne := A.roles_ne.symm
    leftSupport := A.rightSupport
    rightSupport := A.leftSupport
    left_degree_eq_critical := A.right_degree_eq_critical
    right_degree_eq_critical := A.left_degree_eq_critical
    leftWitness := A.rightWitness
    rightWitness := A.leftWitness
    leftWitness_component := A.rightWitness_component
    rightWitness_component := A.leftWitness_component
    leftWitness_pure := A.rightWitness_pure
    rightWitness_pure := A.leftWitness_pure }

private def actualPairMixedPackage (P : P2Data Gamma) {h g : ℕ}
    (hne : h ≠ g) (hdegrees : positiveDegrees P.M = {h, g})
    (A : PurePureCriticalPair P.M.base h)
    (R : PureMixedCriticalRole P.M.base g) : SectorBCriticalRoleBranchA P := by
  have hRL : R.pureRole ≠ A.leftRole :=
    pure_roles_ne_of_degree_ne P.M.base g h hne.symm
      R.degree_pos A.degree_pos R.componentCount_eq_two A.componentCount_eq_two
      R.pureComponent A.leftComponent R.pureRole A.leftRole R.pureSupport A.leftSupport
  have hRR : R.pureRole ≠ A.rightRole :=
    pure_roles_ne_of_degree_ne P.M.base g h hne.symm
      R.degree_pos A.degree_pos R.componentCount_eq_two A.componentCount_eq_two
      R.pureComponent A.rightComponent R.pureRole A.rightRole R.pureSupport A.rightSupport
  let f : Fin 3 → Fin 3 := ![A.leftRole, A.rightRole, R.pureRole]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, A.roles_ne, Ne.symm A.roles_ne, Ne.symm hRL, Ne.symm hRR]
  let e := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  exact {
    pairDegree := h
    mixedDegree := g
    degree_ne := hne
    positiveDegrees_eq := hdegrees
    pair := A
    mixed := R
    mixed_ne_left := hRL
    mixed_ne_right := hRR
    reindex := e
    reindex_zero := rfl
    reindex_one := rfl
    reindex_two := rfl }

private theorem pair_exhausts {B : Data Gamma} {h : ℕ}
    (A : PurePureCriticalPair B h) (E : FiberComponent B h) :
    E = A.leftComponent ∨ E = A.rightComponent := by
  obtain ⟨C, D, hne, hset⟩ := Nat.card_eq_two_iff.mp A.componentCount_eq_two
  have hall (F : FiberComponent B h) : F = C ∨ F = D := by
    have hh : F ∈ ({C, D} : Set (FiberComponent B h)) := hset.symm ▸ Set.mem_univ F
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  have := A.components_ne
  rcases hall E with he | he <;> rcases hall A.leftComponent with hl | hl <;>
    rcases hall A.rightComponent with hr | hr <;> grind

/-- Boundary all-pure geometry on the original physical `P`.  The pair is
oriented killed/live before reindexing; no Sector-B hypothesis is used. -/
theorem boundary_all_pure_geometry (P : P2Data Gamma) (G : SectorCActualFibers P)
    (h : ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree = G.boundaryDegree ∧ A.mixedDegree = G.internalDegree ∧
      BoundaryKilled P.M A.pairDegree A.pair.leftComponent ∧
      ¬ BoundaryKilled P.M A.pairDegree A.pair.rightComponent ∧
      BranchASymmetricTailData A := by
  classical
  have hbpos := (positive_contribution_active P.M G.boundaryDegree (by
    rw [G.boundaryContribution]; omega)).1
  have hipos := (positive_contribution_active P.M G.internalDegree (by
    rw [G.internalContribution]; omega)).1
  obtain ⟨A⟩ := pair_of_all_pure P.M.base G.boundaryDegree hbpos G.boundarySignature.1 h
  have hn : ¬ ∀ C : internalComponents G,
      (componentSupport P.M.base G.internalDegree C).card = 1 := by
    intro hi
    obtain ⟨T⟩ := pair_of_all_pure P.M.base G.internalDegree hipos G.internalSignature.1 hi
    exact two_pure_pairs_impossible P.M.base G.degree_ne.symm A T
  rcases L5A2C4A.sectorC_internal_support_shape_exhaustion G with hi | hm
  · exact (hn hi).elim
  obtain ⟨C, D, hne, hshape, _⟩ := hm
  have hex : Nonempty (PureMixedCriticalRole P.M.base G.internalDegree) := by
    rcases hshape with hCD | hDC
    · exact pureMixedCriticalRole_of_components P.M.base G.internalDegree hipos
        G.internalSignature.1 C D hne hCD.1 hCD.2
    · exact pureMixedCriticalRole_of_components P.M.base G.internalDegree hipos
        G.internalSignature.1 D C hne.symm hDC.2 hDC.1
  obtain ⟨R⟩ := hex
  have hor := (boundary_orientation_exhaustion G A.leftComponent A.rightComponent
    A.components_ne (pair_exhausts A) G.boundarySignature.2).1
  have hd : positiveDegrees P.M = {G.boundaryDegree, G.internalDegree} := by
    simpa only [Finset.pair_comm] using G.positiveDegrees_eq
  rcases hor with hk | hk
  · let T := actualPairMixedPackage P G.degree_ne.symm hd A R
    exact ⟨T, rfl, rfl, hk.1, hk.2, branchA_symmetricTailData T⟩
  · let T := actualPairMixedPackage P G.degree_ne.symm hd (pairSwap A) R
    exact ⟨T, rfl, rfl, hk.2, hk.1, branchA_symmetricTailData T⟩

/-- Internal all-pure geometry, retaining the original `Gamma`, `P` and both
actual critical degrees.  The boundary mixed witness is an actual vertex. -/
theorem internal_all_pure_geometry (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp ≠ bm)
    (hp : IsPureBoundaryComponent G bp) (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,
      (componentSupport P.M.base G.internalDegree C).card = 1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree = G.internalDegree ∧ A.mixedDegree = G.boundaryDegree ∧
      BranchASymmetricTailData A := by
  have hbpos := (positive_contribution_active P.M G.boundaryDegree (by
    rw [G.boundaryContribution]; omega)).1
  have hipos := (positive_contribution_active P.M G.internalDegree (by
    rw [G.internalContribution]; omega)).1
  obtain ⟨A⟩ := pair_of_all_pure P.M.base G.internalDegree hipos G.internalSignature.1 hi
  obtain ⟨R⟩ := pureMixedCriticalRole_of_components P.M.base G.boundaryDegree hbpos
    G.boundarySignature.1 bp bm hne hp hm
  let T := actualPairMixedPackage P G.degree_ne G.positiveDegrees_eq A R
  exact ⟨T, rfl, rfl, branchA_symmetricTailData T⟩

end NS25Lean.L5A2C4OR39
