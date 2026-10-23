import NS25Lean.P2NonsymmetricHerzogCompletion
import NS25Lean.P2SectorCEtaKappaStencil
import NS25Lean.P2SectorCFakeTerminalResourceBridge
import NS25Lean.P2SectorCLocalCollisionAccounting

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2B4AR5B

open L2B L5A1 L5A2C4B L5A2C4C ChosenBase Classical
open L5A2B4AR4R1 L5A2B4AR4R2B

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The cyclic Branch-B reindexing used by the inactive-gate argument:
the completed third critical role becomes the `a`-coordinate. -/
def branchBInactiveReindex (R : SectorBCriticalRoleBranchB P) : Fin 3 ≃ Fin 3 :=
  ((Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 2)).trans R.reindex

@[simp] theorem branchBInactiveReindex_zero (R : SectorBCriticalRoleBranchB P) :
    branchBInactiveReindex R 0 = R.reindex 2 := by
  change R.reindex ((Equiv.swap 0 2) ((Equiv.swap 1 2) 0)) = R.reindex 2
  congr 1

@[simp] theorem branchBInactiveReindex_one (R : SectorBCriticalRoleBranchB P) :
    branchBInactiveReindex R 1 = R.reindex 0 := by
  change R.reindex ((Equiv.swap 0 2) ((Equiv.swap 1 2) 1)) = R.reindex 0
  congr 1

@[simp] theorem branchBInactiveReindex_two (R : SectorBCriticalRoleBranchB P) :
    branchBInactiveReindex R 2 = R.reindex 1 := by
  change R.reindex ((Equiv.swap 0 2) ((Equiv.swap 1 2) 2)) = R.reindex 1
  congr 1

abbrev branchBInactiveDegree (R : SectorBCriticalRoleBranchB P) : ℕ :=
  criticalExponent P.M.base (branchBInactiveReindex R 0) *
    weights P.M.base (branchBInactiveReindex R 0)

theorem branchBInactiveDegree_eq (R : SectorBCriticalRoleBranchB P) :
    branchBInactiveDegree R = c3 R * weights P.M.base (R.reindex 2) := by
  simp [branchBInactiveDegree, branchB_third_criticalExponent]

def branchBInactiveMixedFactorization (R : SectorBCriticalRoleBranchB P) :
    FactorizationFiber P.M.base (branchBInactiveDegree R) :=
  ⟨thirdWitness R, by
    simpa [branchBInactiveDegree] using thirdWitness_weight R⟩

def branchBInactiveMixedComponent (R : SectorBCriticalRoleBranchB P) :
    FiberComponent P.M.base (branchBInactiveDegree R) :=
  (fiberGraph P.M.base _).connectedComponentMk (branchBInactiveMixedFactorization R)

theorem branchB_inactive_mixed_coordinate_zero
    (R : SectorBCriticalRoleBranchB P) :
    (branchBInactiveMixedFactorization R).val (branchBInactiveReindex R 0) = 0 := by
  simp [branchBInactiveMixedFactorization, thirdWitness,
    R.reindex.injective.eq_iff]

theorem branchB_inactive_mixed_coordinate_one_pos
    (R : SectorBCriticalRoleBranchB P) :
    0 < (branchBInactiveMixedFactorization R).val (branchBInactiveReindex R 1) := by
  simpa [branchBInactiveMixedFactorization, thirdWitness,
    R.reindex.injective.eq_iff] using
      (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.2.2.1

theorem branchB_inactive_mixed_coordinate_two_pos
    (R : SectorBCriticalRoleBranchB P) :
    0 < (branchBInactiveMixedFactorization R).val (branchBInactiveReindex R 2) := by
  simpa [branchBInactiveMixedFactorization, thirdWitness,
    R.reindex.injective.eq_iff] using
      (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.2.2.2

/-- The actual completed third witness, viewed in the inactive cyclic chart,
has precisely the two non-pivot coordinates in its component support. -/
theorem branchB_inactive_nonpure_component_support
    (R : SectorBCriticalRoleBranchB P) :
    componentSupport P.M.base (branchBInactiveDegree R)
      (branchBInactiveMixedComponent R) =
        {branchBInactiveReindex R 1, branchBInactiveReindex R 2} := by
  classical
  let e := branchBInactiveReindex R
  let C := branchBInactiveMixedComponent R
  apply Finset.Subset.antisymm
  · intro j hj
    obtain ⟨k, rfl⟩ := e.surjective j
    fin_cases k
    ·
      have hp : e 0 ∈ componentSupport P.M.base (branchBInactiveDegree R)
          (critical_pure_component P.M.base (e 0)) := by
        simpa [branchBInactiveDegree] using
          congrArg (fun s : Finset (Fin 3) ↦ e 0 ∈ s)
            (critical_component_support_eq_singleton P.M.base (e 0))
      have heq := components_eq_of_shared_support P.M.base (branchBInactiveDegree R)
        C (critical_pure_component P.M.base (e 0)) (e 0) hj hp
      have hmix1 : e 1 ∈ componentSupport P.M.base (branchBInactiveDegree R) C :=
        (mem_componentSupport P.M.base _ C (e 1)).mpr
          ⟨branchBInactiveMixedFactorization R, rfl,
            branchB_inactive_mixed_coordinate_one_pos R⟩
      rw [heq, critical_component_support_eq_singleton] at hmix1
      have he10 : e 1 = e 0 := Finset.mem_singleton.mp hmix1
      exact ((by omega : (1 : Fin 3) ≠ 0) (e.injective he10)).elim
    · simp [e]
    · simp [e]
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact (mem_componentSupport P.M.base _ C (e 1)).mpr
        ⟨branchBInactiveMixedFactorization R, rfl,
          branchB_inactive_mixed_coordinate_one_pos R⟩
    · exact (mem_componentSupport P.M.base _ C (e 2)).mpr
        ⟨branchBInactiveMixedFactorization R, rfl,
          branchB_inactive_mixed_coordinate_two_pos R⟩

private theorem two_components_exhaust (B : Data Gamma) (h : ℕ)
    (C D : FiberComponent B h) (hne : C ≠ D) (hc : componentCount B h = 2)
    (E : FiberComponent B h) : E = C ∨ E = D := by
  classical
  letI := Fintype.ofFinite (FiberComponent B h)
  have hcard : Fintype.card (FiberComponent B h) = 2 := by
    simpa [componentCount, Nat.card_eq_fintype_card] using hc
  have hall : ({C, D} : Finset (FiberComponent B h)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simp [hne, hcard])
  have hmem : E ∈ ({C, D} : Finset (FiberComponent B h)) := by
    rw [hall]
    simp
  simpa using hmem

private theorem critical_degree_ne_of_two_supports (B : Data Gamma) (j : Fin 3)
    (h : ℕ) (C D : FiberComponent B h) (hne : C ≠ D)
    (hc : componentCount B h = 2)
    (hCne : ({j} : Finset (Fin 3)) ≠ componentSupport B h C)
    (hDne : ({j} : Finset (Fin 3)) ≠ componentSupport B h D) :
    criticalExponent B j * weights B j ≠ h := by
  intro heq
  cases heq
  have hcrit := critical_component_support_eq_singleton B j
  rcases two_components_exhaust B _ C D hne hc (critical_pure_component B j) with hE | hE
  · subst hE
    exact hCne hcrit.symm
  · subst hE
    exact hDne hcrit.symm

/-- The completed third critical degree is outside the two actual positive
Branch-B degrees.  This is proved from their frozen component supports. -/
theorem branchB_inactive_distinct_degrees (R : SectorBCriticalRoleBranchB P) :
    branchBInactiveDegree R ≠ R.firstDegree ∧
      branchBInactiveDegree R ≠ R.secondDegree := by
  let e := branchBInactiveReindex R
  constructor
  · apply critical_degree_ne_of_two_supports P.M.base (e 0) R.firstDegree
      R.first.pureComponent R.first.mixedComponent R.first.components_ne
      R.first.componentCount_eq_two
    · rw [R.first.pureSupport]
      intro hs
      have he : e 0 = R.first.pureRole := Finset.singleton_inj.mp hs
      rw [← R.reindex_zero] at he
      exact (by omega : (2 : Fin 3) ≠ 0) (R.reindex.injective (by simpa [e] using he))
    · rw [R.first_mixed_support]
      intro hs
      have hc := congrArg Finset.card hs
      simp [R.reindex.injective.eq_iff] at hc

  · apply critical_degree_ne_of_two_supports P.M.base (e 0) R.secondDegree
      R.second.pureComponent R.second.mixedComponent R.second.components_ne
      R.second.componentCount_eq_two
    · rw [R.second.pureSupport]
      intro hs
      have he : e 0 = R.second.pureRole := Finset.singleton_inj.mp hs
      rw [← R.reindex_one] at he
      exact (by omega : (2 : Fin 3) ≠ 1) (R.reindex.injective (by simpa [e] using he))
    · rw [R.second_mixed_support]
      intro hs
      have hc := congrArg Finset.card hs
      simp [R.reindex.injective.eq_iff] at hc

theorem branchB_inactive_degree_ne_first (R : SectorBCriticalRoleBranchB P) :
    branchBInactiveDegree R ≠ R.firstDegree :=
  (branchB_inactive_distinct_degrees R).1

theorem branchB_inactive_degree_ne_second (R : SectorBCriticalRoleBranchB P) :
    branchBInactiveDegree R ≠ R.secondDegree :=
  (branchB_inactive_distinct_degrees R).2

theorem branchB_inactive_componentCount (R : SectorBCriticalRoleBranchB P) :
    componentCount P.M.base (branchBInactiveDegree R) = 2 := by
  let e := branchBInactiveReindex R
  have hlow : 2 ≤ componentCount P.M.base (branchBInactiveDegree R) := by
    change 2 ≤ componentCount P.M.base
      (criticalExponent P.M.base (e 0) * weights P.M.base (e 0))
    exact critical_fiber_componentCount_ge_two P.M.base (e 0)
  have hpos : 0 < branchBInactiveDegree R := by
    have hc := (criticalExponent_spec P.M.base (e 0)).1
    have hw := weights_positive P.M.base (e 0)
    dsimp [branchBInactiveDegree]
    positivity
  have hupp := componentCount_le_three P.M.base (branchBInactiveDegree R) hpos
  by_cases hthree : componentCount P.M.base (branchBInactiveDegree R) = 3
  · have hactive : R.firstDegree ∈ activeDegreeFinset P.M :=
      (mem_activeDegreeFinset P.M R.firstDegree).mpr
        (positive_contribution_active P.M R.firstDegree
          ((mem_positiveDegrees P.M R.firstDegree).mp (by
            rw [R.positiveDegrees_eq]
            simp)))
    have heq := three_components_unique_active P.M
      (branchBInactiveDegree R) R.firstDegree hpos hthree hactive
    exact ((branchB_inactive_distinct_degrees R).1 heq.symm).elim
  · omega

theorem branchB_inactive_contribution_zero (R : SectorBCriticalRoleBranchB P) :
    fiberContribution P.M (branchBInactiveDegree R) = 0 := by
  apply contribution_zero_outside_positive
  rw [R.positiveDegrees_eq]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  push_neg
  exact branchB_inactive_distinct_degrees R

theorem branchB_inactive_killedCount (R : SectorBCriticalRoleBranchB P) :
    killedCount P.M (branchBInactiveDegree R) = 2 := by
  have hc := branchB_inactive_componentCount R
  have hz := branchB_inactive_contribution_zero R
  have hle := killedCount_le_componentCount P.M (branchBInactiveDegree R)
  unfold fiberContribution at hz
  split_ifs at hz <;> omega

theorem branchB_inactive_localSignature
    (hB : SectorB P.M) (R : SectorBCriticalRoleBranchB P) :
    LocalSignature P.M (branchBInactiveDegree R) 2 2 := by
  exact ⟨branchB_inactive_componentCount R, branchB_inactive_killedCount R⟩

def branchBInactivePureComponent (R : SectorBCriticalRoleBranchB P) :
    FiberComponent P.M.base (branchBInactiveDegree R) :=
  critical_pure_component P.M.base (branchBInactiveReindex R 0)

theorem branchB_inactive_components_ne (R : SectorBCriticalRoleBranchB P) :
    branchBInactivePureComponent R ≠ branchBInactiveMixedComponent R := by
  intro heq
  have hs := critical_component_support_eq_singleton P.M.base
    (branchBInactiveReindex R 0)
  have hm := branchB_inactive_nonpure_component_support R
  have hs' : componentSupport P.M.base (branchBInactiveDegree R)
      (branchBInactiveMixedComponent R) = {(branchBInactiveReindex R) 0} := by
    rw [← heq]
    simpa [branchBInactivePureComponent, branchBInactiveDegree] using hs
  rw [hm] at hs'
  have hc := congrArg Finset.card hs'
  simp [(branchBInactiveReindex R).injective.eq_iff] at hc

private theorem both_boundaryKilled_of_two
    (M : MultiplicityBase Gamma) (h : ℕ)
    (C D : FiberComponent M.base h) (hne : C ≠ D)
    (hc : componentCount M.base h = 2) (hk : killedCount M h = 2) :
    BoundaryKilled M h C ∧ BoundaryKilled M h D := by
  classical
  have hexhaust := two_components_exhaust M.base h C D hne hc
  constructor
  · by_contra hnC
    letI := Fintype.ofFinite {E : FiberComponent M.base h // BoundaryKilled M h E}
    have hsub : Subsingleton {E : FiberComponent M.base h // BoundaryKilled M h E} := by
      refine ⟨fun E F => Subtype.ext ?_⟩
      rcases hexhaust E.val with hEC | hED
      · exact (hnC (hEC ▸ E.property)).elim
      rcases hexhaust F.val with hFC | hFD
      · exact (hnC (hFC ▸ F.property)).elim
      exact hED.trans hFD.symm
    have hle : killedCount M h ≤ 1 := by
      simpa [killedCount, Nat.card_eq_fintype_card] using
        (Fintype.card_le_one_iff_subsingleton.mpr hsub)
    omega
  · by_contra hnD
    letI := Fintype.ofFinite {E : FiberComponent M.base h // BoundaryKilled M h E}
    have hsub : Subsingleton {E : FiberComponent M.base h // BoundaryKilled M h E} := by
      refine ⟨fun E F => Subtype.ext ?_⟩
      rcases hexhaust E.val with hEC | hED
      · rcases hexhaust F.val with hFC | hFD
        · exact hEC.trans hFC.symm
        · exact (hnD (hFD ▸ F.property)).elim
      · exact (hnD (hED ▸ E.property)).elim
    have hle : killedCount M h ≤ 1 := by
      simpa [killedCount, Nat.card_eq_fintype_card] using
        (Fintype.card_le_one_iff_subsingleton.mpr hsub)
    omega

/-- At the Branch-B inactive critical degree the isolated pure component and
the actual completed mixed component are both boundary-killed. -/
theorem branchB_inactive_components_killed (R : SectorBCriticalRoleBranchB P) :
    BoundaryKilled P.M (branchBInactiveDegree R) (branchBInactivePureComponent R) ∧
      BoundaryKilled P.M (branchBInactiveDegree R) (branchBInactiveMixedComponent R) :=
  both_boundaryKilled_of_two P.M (branchBInactiveDegree R)
    (branchBInactivePureComponent R) (branchBInactiveMixedComponent R)
    (branchB_inactive_components_ne R) (branchB_inactive_componentCount R)
    (branchB_inactive_killedCount R)

/-- Killing the actual pure third-critical component forces the strict
inactive-height inequality at the origin. -/
theorem branchB_inactive_H0_lt (R : SectorBCriticalRoleBranchB P) :
    eta P.M.base (branchBInactiveReindex R) 0 0 < c3 R := by
  let e := branchBInactiveReindex R
  change eta P.M.base e 0 0 < c3 R
  obtain ⟨u, huC, j, huj, hK⟩ := (branchB_inactive_components_killed R).1
  have hjmem : j ∈ componentSupport P.M.base (branchBInactiveDegree R)
      (branchBInactivePureComponent R) :=
    (mem_componentSupport P.M.base _ _ j).mpr ⟨u, huC, huj⟩
  have hj : j = e 0 := by
    change j ∈ componentSupport P.M.base
      (criticalExponent P.M.base (e 0) * weights P.M.base (e 0))
      (critical_pure_component P.M.base (e 0)) at hjmem
    rw [critical_component_support_eq_singleton] at hjmem
    exact Finset.mem_singleton.mp hjmem
  subst j
  have hcpos : 0 < c3 R := by
    have h := (branchB_nonsymmetric_herzog_completion R).cross_positive
    have hc := (branchB_nonsymmetric_herzog_completion R).coefficient_sums.2.2
    omega
  have hdegree : branchBInactiveDegree R - weights P.M.base (e 0) =
      gridDegree P.M.base e (c3 R - 1) 0 0 := by
    rw [branchBInactiveDegree_eq]
    simp only [gridDegree, zero_mul, add_zero]
    change c3 R * weights P.M.base (e 0) - weights P.M.base (e 0) =
      (c3 R - 1) * weights P.M.base (e 0)
    rw [Nat.sub_mul]
    simp
  have heta : eta P.M.base e 0 0 ≤ c3 R - 1 :=
    (gridDegree_mem_K_iff_eta_le P.M.base e 0 0 (c3 R - 1)).mp
      (hdegree ▸ hK)
  omega

/-- Killing the actual completed mixed component forces one of the two
source-exact seam values to vanish. -/
theorem branchB_inactive_seam_zero (R : SectorBCriticalRoleBranchB P) :
    eta P.M.base (branchBInactiveReindex R) (r31 R - 1) (r32 R) = 0 ∨
      eta P.M.base (branchBInactiveReindex R) (r31 R) (r32 R - 1) = 0 := by
  let e := branchBInactiveReindex R
  obtain ⟨u, huC, j, huj, hK⟩ := (branchB_inactive_components_killed R).2
  have hjmem : j ∈ componentSupport P.M.base (branchBInactiveDegree R)
      (branchBInactiveMixedComponent R) :=
    (mem_componentSupport P.M.base _ _ j).mpr ⟨u, huC, huj⟩
  rw [branchB_inactive_nonpure_component_support] at hjmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem
  have hrel : branchBInactiveDegree R =
      r31 R * weights P.M.base (e 1) + r32 R * weights P.M.base (e 2) := by
    simpa [branchBInactiveDegree_eq, e] using
      (branchB_nonsymmetric_herzog_completion R).weighted_relations.2.2
  obtain ⟨hr31, hr32⟩ :=
    (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.2.2
  rcases hjmem with rfl | rfl
  · left
    apply (eta_eq_zero_iff P.M.base e (r31 R - 1) (r32 R)).mpr
    have hK' : branchBInactiveDegree R - weights P.M.base (e 1) ∈ P.M.base.K := by
      simpa [e] using hK
    have hr : r31 R = 1 + (r31 R - 1) := by omega
    rw [hrel, hr, Nat.add_mul] at hK'
    simpa [gridDegree, Nat.add_assoc] using hK'
  · right
    apply (eta_eq_zero_iff P.M.base e (r31 R) (r32 R - 1)).mpr
    have hK' : branchBInactiveDegree R - weights P.M.base (e 2) ∈ P.M.base.K := by
      simpa [e] using hK
    have hr : r32 R = 1 + (r32 R - 1) := by omega
    rw [hrel, hr, Nat.add_mul] at hK'
    have hs :
        r31 R * weights P.M.base (e 1) +
            (weights P.M.base (e 2) + (r32 R - 1) * weights P.M.base (e 2)) -
              weights P.M.base (e 2) =
          r31 R * weights P.M.base (e 1) +
            (r32 R - 1) * weights P.M.base (e 2) := by
      omega
    simp only [one_mul] at hK'
    rw [hs] at hK'
    simpa [gridDegree] using hK'

/-- Source-exact Branch-B inactive gate: strict origin height together with
one of the two actual Herzog seam zeros. -/
theorem branchB_actual_inactive_gate
    (hB : SectorB P.M) (R : SectorBCriticalRoleBranchB P) :
    let e := branchBInactiveReindex R
    eta P.M.base e 0 0 < c3 R ∧
      (eta P.M.base e (r31 R - 1) (r32 R) = 0 ∨
        eta P.M.base e (r31 R) (r32 R - 1) = 0) := by
  exact ⟨branchB_inactive_H0_lt R, branchB_inactive_seam_zero R⟩

/-- The actual raw routing identity in the inactive Branch-B chart.  The
paired zero diamonds cancel between the raw branch and merge counts, leaving
the source-target branches, exact unused merges, and fake terminals. -/
theorem branchB_actual_raw_routing_identity (R : SectorBCriticalRoleBranchB P) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    let D := L5A2C4H.routingData P.M.base e
    P.W = (L5A2C4M.ResidueData.Cbr D : ℤ) -
      (L5A2C4M.ResidueData.U D : ℤ) - (L5A2C4N.E P.M.base e : ℤ) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA B e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos B e)⟩
  let D := L5A2C4H.routingData B e
  change P.W = (L5A2C4M.ResidueData.Cbr D : ℤ) -
    (L5A2C4M.ResidueData.U D : ℤ) - (L5A2C4N.E B e : ℤ)
  obtain ⟨_ha, hsource, _hsink, hout, hin⟩ :=
    L5A2C4H.exists_actualRoutingCore P e
  obtain ⟨_ha', hactual, _hsink'⟩ :=
    L5A2C4H.exists_actualRouting_with_exact_actualSinkCount P e
  have hpartition := L5A2C4H.fullSinkCount_eq_actual_add_fake
    (L5A2C4H.routingI B e) (L5A2C4H.routingA B e)
      (L5A2C4H.routingB B e) (L5A2C4H.routingC B e)
      (L5A2C4H.routingHB B e) (L5A2C4H.routingHC B e)
  have hbalance := CombinatorialCore.ResidueData.edge_count_balance hout hin
  obtain ⟨hbranch, hmerge⟩ := L5A2C4J.actual_raw_decomposition B e
  change D.sourceCount = P.sourceCount at hsource
  change L5A2C4H.actualSinkCount (L5A2C4H.routingI B e)
      (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
      (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
      (L5A2C4H.routingHC B e) = Gamma.asRelativeIdeal.idealType at hactual
  change D.sinkCount = L5A2C4H.actualSinkCount (L5A2C4H.routingI B e)
      (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
      (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
      (L5A2C4H.routingHC B e) +
        L5A2C4H.fakeSinkCount (L5A2C4H.routingI B e)
          (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
          (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
          (L5A2C4H.routingHC B e) at hpartition
  change D.branchCount = L5A2C4J.ResidueData.pairedZeroDiamondCount D +
      L5A2C4I.ResidueData.sourceTargetBranchCount D at hbranch
  change D.mergeCount = L5A2C4J.ResidueData.pairedZeroDiamondCount D +
      L5A2C4J.ResidueData.exactUnusedMergeCount D at hmerge
  change D.sinkCount + D.mergeCount = D.sourceCount + D.branchCount at hbalance
  unfold P2Data.W L5A2C4M.ResidueData.Cbr L5A2C4M.ResidueData.U L5A2C4N.E
  change _ = _ - (Nat.card (L5A2C4I.ResidueData.ExactUnusedMergeBases D) : ℤ) -
    (L5A2C4H.fakeSinkCount (L5A2C4H.routingI B e)
      (L5A2C4H.routingA B e) (L5A2C4H.routingB B e)
      (L5A2C4H.routingC B e) (L5A2C4H.routingHB B e)
      (L5A2C4H.routingHC B e) : ℤ)
  unfold L5A2C4J.ResidueData.exactUnusedMergeCount at hmerge
  omega

/-- ENTRY leaves one more actual source-target branch than the combined exact
unused-merge and fake-terminal seats in the inactive Branch-B routing chart. -/
theorem branchB_entry_unpaid_channel
    (R : SectorBCriticalRoleBranchB P) (hentry : P.W = 1) :
    let e := branchBInactiveReindex R
    letI : NeZero (L5A2C4H.routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
    let D := L5A2C4H.routingData P.M.base e
    (L5A2C4M.ResidueData.Cbr D : ℤ) =
      L5A2C4M.ResidueData.U D + L5A2C4N.E P.M.base e + 1 := by
  let e := branchBInactiveReindex R
  letI : NeZero (L5A2C4H.routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (L5A2C4H.routingA_pos P.M.base e)⟩
  let D := L5A2C4H.routingData P.M.base e
  exact L5A2B.entry_unpaid_channel
    (L5A2C4M.ResidueData.Cbr D) (L5A2C4M.ResidueData.U D)
      (L5A2C4N.E P.M.base e) P.W (branchB_actual_raw_routing_identity R) hentry

end NS25Lean.L5A2B4AR5B
