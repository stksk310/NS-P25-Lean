import NS25Lean.P2BranchBTopologyFreeEntryKernel
import NS25Lean.P2SectorCHerzogCanonicalityOwnerReentryR6
import NS25Lean.P2SectorCFakeTerminalResourceBridge

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR5B

open L2B L5A1 L5A2C4B L5A2C4C L5A2C4H ChosenBase Classical
open L5A2B4AR4R1 L5A2B4AR4R2B

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The three frozen actual mixed critical witnesses, cyclically viewed in
the inactive Branch-B chart.  No relation or coefficient identity is stored
as additional data. -/
noncomputable def branchB_inactive_coherentHerzogData
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4D.CoherentHerzogData P.M.base (branchBInactiveReindex R) := by
  let e := branchBInactiveReindex R
  let w1 : FactorizationFiber P.M.base
      (L5A2C4A.c1 P.M.base e * weights P.M.base (e 0)) :=
    ⟨thirdWitness R, by
      simpa [e, L5A2C4A.c1, L5A2C4A.herzogC] using thirdWitness_weight R⟩
  let w2 : FactorizationFiber P.M.base
      (L5A2C4A.c2 P.M.base e * weights P.M.base (e 1)) :=
    ⟨R.first.witness.val, by
      calc
        weight P.M.base R.first.witness.val = R.firstDegree :=
          R.first.witness.property
        _ = L5A2C4A.c2 P.M.base e * weights P.M.base (e 1) := by
          simpa [e, L5A2C4A.c2, L5A2C4A.herzogC, R.reindex_zero] using
            R.first.degree_eq_critical⟩
  let w3 : FactorizationFiber P.M.base
      (L5A2C4A.c3 P.M.base e * weights P.M.base (e 2)) :=
    ⟨R.second.witness.val, by
      calc
        weight P.M.base R.second.witness.val = R.secondDegree :=
          R.second.witness.property
        _ = L5A2C4A.c3 P.M.base e * weights P.M.base (e 2) := by
          simpa [e, L5A2C4A.c3, L5A2C4A.herzogC, R.reindex_one] using
            R.second.degree_eq_critical⟩
  exact {
    witness1 := w1
    witness2 := w2
    witness3 := w3
    witness1_self_zero := by
      simp [w1, thirdWitness, R.reindex.injective.eq_iff]
    witness2_self_zero := by
      simpa [w2, e, R.reindex_zero] using R.first.witness_pure_zero
    witness3_self_zero := by
      simpa [w3, e, R.reindex_one] using R.second.witness_pure_zero
    witness1_left_pos := by
      simpa [w1, e, thirdWitness, R.reindex.injective.eq_iff] using
        (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.2.2.1
    witness1_right_pos := by
      simpa [w1, e, thirdWitness, R.reindex.injective.eq_iff] using
        (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.2.2.2
    witness2_left_pos := by
      simpa [w2, e] using R.first_witness_two_pos
    witness2_right_pos := by
      simpa [w2, e] using R.first_witness_one_pos
    witness3_left_pos := by
      simpa [w3, e] using R.second_witness_two_pos
    witness3_right_pos := by
      simpa [w3, e] using R.second_witness_zero_pos
  }

@[simp] theorem branchB_inactive_coherent_c1
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4A.c1 P.M.base (branchBInactiveReindex R) = c3 R := by
  simp [L5A2C4A.c1, L5A2C4A.herzogC, branchB_third_criticalExponent]

@[simp] theorem branchB_inactive_coherent_c2
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4A.c2 P.M.base (branchBInactiveReindex R) = c1 R := by
  simp [L5A2C4A.c2, L5A2C4A.herzogC, c1]

@[simp] theorem branchB_inactive_coherent_c3
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4A.c3 P.M.base (branchBInactiveReindex R) = c2 R := by
  simp [L5A2C4A.c3, L5A2C4A.herzogC, c2]

@[simp] theorem branchB_inactive_coherent_coefficients
    (R : SectorBCriticalRoleBranchB P) :
    let D := branchB_inactive_coherentHerzogData R
    L5A2C4D.cr12 D = r31 R ∧ L5A2C4D.cr13 D = r32 R ∧
      L5A2C4D.cr21 D = r13 R ∧ L5A2C4D.cr23 D = r12 R ∧
      L5A2C4D.cr31 D = r23 R ∧ L5A2C4D.cr32 D = r21 R := by
  simp [branchB_inactive_coherentHerzogData, L5A2C4D.cr12,
    L5A2C4D.cr13, L5A2C4D.cr21, L5A2C4D.cr23, L5A2C4D.cr31,
    L5A2C4D.cr32, thirdWitness, r12, r13, r21, r23, r31, r32,
    R.reindex.injective.eq_iff]

@[simp] theorem branchB_inactive_coherent_cr12
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4D.cr12 (branchB_inactive_coherentHerzogData R) = r31 R :=
  (branchB_inactive_coherent_coefficients R).1

@[simp] theorem branchB_inactive_coherent_cr13
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4D.cr13 (branchB_inactive_coherentHerzogData R) = r32 R :=
  (branchB_inactive_coherent_coefficients R).2.1

@[simp] theorem branchB_inactive_coherent_cr21
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4D.cr21 (branchB_inactive_coherentHerzogData R) = r13 R :=
  (branchB_inactive_coherent_coefficients R).2.2.1

@[simp] theorem branchB_inactive_coherent_cr23
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4D.cr23 (branchB_inactive_coherentHerzogData R) = r12 R :=
  (branchB_inactive_coherent_coefficients R).2.2.2.1

@[simp] theorem branchB_inactive_coherent_cr31
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4D.cr31 (branchB_inactive_coherentHerzogData R) = r23 R :=
  (branchB_inactive_coherent_coefficients R).2.2.2.2.1

@[simp] theorem branchB_inactive_coherent_cr32
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4D.cr32 (branchB_inactive_coherentHerzogData R) = r21 R :=
  (branchB_inactive_coherent_coefficients R).2.2.2.2.2

/-!
The paper's `x2` and `y3` are threshold states, not exceptional-run
endpoints.  These definitions deliberately keep the lattice coordinate, its
residue state, and its eta value separate.
-/

def branchBOXThresholdCoordinates (R : SectorBCriticalRoleBranchB P) : ℕ × ℕ :=
  (c1 R - 1, 0)

def branchBOYThresholdCoordinates (R : SectorBCriticalRoleBranchB P) : ℕ × ℕ :=
  (0, c2 R - 1)

def branchBOXThresholdState (R : SectorBCriticalRoleBranchB P) :
    ZMod (routingA P.M.base (branchBInactiveReindex R)) :=
  gridResidue P.M.base (branchBInactiveReindex R)
    (branchBOXThresholdCoordinates R).1 (branchBOXThresholdCoordinates R).2

def branchBOYThresholdState (R : SectorBCriticalRoleBranchB P) :
    ZMod (routingA P.M.base (branchBInactiveReindex R)) :=
  gridResidue P.M.base (branchBInactiveReindex R)
    (branchBOYThresholdCoordinates R).1 (branchBOYThresholdCoordinates R).2

abbrev branchBOXThreshold (R : SectorBCriticalRoleBranchB P) : ℕ :=
  eta P.M.base (branchBInactiveReindex R)
    (branchBOXThresholdCoordinates R).1 (branchBOXThresholdCoordinates R).2

abbrev branchBOYThreshold (R : SectorBCriticalRoleBranchB P) : ℕ :=
  eta P.M.base (branchBInactiveReindex R)
    (branchBOYThresholdCoordinates R).1 (branchBOYThresholdCoordinates R).2

/-- The adjacent OX fake-corner coordinate (`kappa2`) in the inactive chart.
It is not definitionally identified with the OX threshold state. -/
def branchBOXKappaCoordinates (R : SectorBCriticalRoleBranchB P) : ℕ × ℕ :=
  (r31 R - 1, c2 R - 1)

/-- The adjacent OY fake-corner coordinate (`kappa1`) in the inactive chart.
It is not definitionally identified with the OY threshold state. -/
def branchBOYKappaCoordinates (R : SectorBCriticalRoleBranchB P) : ℕ × ℕ :=
  (c1 R - 1, r32 R - 1)

theorem branchB_ox_kappa_canonical
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4OR4.IsCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
      (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2 := by
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  apply L5A2C4OR6.herzogLShapeCanonicality P.M.base e D
  have hp := L5A2C4D.coherent_coefficients_positive P.M.base e D
  have hb := L5A2C4D.coherent_strict_bounds P.M.base e D
  have hc := L5A2C4D.coherent_coefficients P.M.base e D
  simp only [L5A2C4OR5.HerzogLShapeDomain]
  change r31 R - 1 < L5A2C4A.c2 P.M.base e ∧
    c2 R - 1 < L5A2C4A.c3 P.M.base e ∧
      (r31 R - 1 < L5A2C4D.cr12 D ∨ c2 R - 1 < L5A2C4D.cr13 D)
  dsimp only [e]
  rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
  have hmap := branchB_inactive_coherent_coefficients R
  dsimp only [D, e] at hp hb hc hmap
  obtain ⟨h12, h13, h21, h23, h31, h32⟩ := hmap
  rw [h12, h13, h21, h23, h31, h32] at hp hb hc
  rw [branchB_inactive_coherent_c1, branchB_inactive_coherent_c2,
    branchB_inactive_coherent_c3] at hb hc
  dsimp only [D]
  omega

private theorem branchB_ox_kappa_reduced_b_canonical
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4OR4.IsCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
      0 (r12 R - 1) := by
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  apply L5A2C4OR6.herzogLShapeCanonicality P.M.base e D
  have hp := L5A2C4D.coherent_coefficients_positive P.M.base e D
  have hb := L5A2C4D.coherent_strict_bounds P.M.base e D
  simp only [L5A2C4OR5.HerzogLShapeDomain]
  change 0 < L5A2C4A.c2 P.M.base e ∧
    r12 R - 1 < L5A2C4A.c3 P.M.base e ∧
      (0 < L5A2C4D.cr12 D ∨ r12 R - 1 < L5A2C4D.cr13 D)
  dsimp only [e]
  rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
  have hmap := branchB_inactive_coherent_coefficients R
  dsimp only [D, e] at hp hb hmap
  obtain ⟨h12, h13, h21, h23, h31, h32⟩ := hmap
  rw [h12, h13, h21, h23, h31, h32] at hp hb
  rw [branchB_inactive_coherent_c1, branchB_inactive_coherent_c2,
    branchB_inactive_coherent_c3] at hb
  dsimp only [D]
  omega

private theorem branchB_ox_kappa_reduced_c_canonical
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4OR4.IsCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
      (c1 R - 1) 0 := by
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  apply L5A2C4OR6.herzogLShapeCanonicality P.M.base e D
  have hp := L5A2C4D.coherent_coefficients_positive P.M.base e D
  simp only [L5A2C4OR5.HerzogLShapeDomain]
  change c1 R - 1 < L5A2C4A.c2 P.M.base e ∧
    0 < L5A2C4A.c3 P.M.base e ∧
      (c1 R - 1 < L5A2C4D.cr12 D ∨ 0 < L5A2C4D.cr13 D)
  dsimp only [e]
  rw [branchB_inactive_coherent_c2, branchB_inactive_coherent_c3]
  have hc1pos : 0 < c1 R := (criticalExponent_spec P.M.base (R.reindex 0)).1
  have hc2pos : 0 < c2 R := (criticalExponent_spec P.M.base (R.reindex 1)).1
  exact ⟨by omega, hc2pos, Or.inr hp.2.1⟩

theorem branchB_ox_kappa_gridLift_zero
    (R : SectorBCriticalRoleBranchB P) :
    gridLift P.M.base (branchBInactiveReindex R)
      (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2 = 0 :=
  L5A2C4OR4.gridLift_eq_zero_of_isCanonical P.M.base
    (branchBInactiveReindex R) _ _ (branchB_ox_kappa_canonical R)

private theorem coherent_kappa2_add_b_normalized_transport
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : L5A2C4D.CoherentHerzogData B e) (n : ℕ) :
    normalizedGrid B e n (L5A2C4D.cr12 D) (L5A2C4A.c3 B e - 1) =
      normalizedGrid B e (n + L5A2C4A.c1 B e) 0 (L5A2C4D.cr23 D - 1) := by
  have hr := L5A2C4OR5.coherent_normalized_relations B e D
  have hc := L5A2C4D.coherent_coefficients B e D
  have hp := L5A2C4D.coherent_coefficients_positive B e D
  have hs3 : L5A2C4A.c3 B e - 1 + 1 = L5A2C4A.c3 B e := by omega
  have hs23 : L5A2C4D.cr23 D - 1 + 1 = L5A2C4D.cr23 D := by omega
  have hc3sub : L5A2C4A.c3 B e - 1 =
      L5A2C4D.cr13 D + (L5A2C4D.cr23 D - 1) := by omega
  simp only [normalizedGrid, zero_mul, add_zero]
  rw [hc3sub, Nat.add_mul]
  calc
    n * routingA B e + L5A2C4D.cr12 D * routingB B e +
          (L5A2C4D.cr13 D * routingC B e +
            (L5A2C4D.cr23 D - 1) * routingC B e) =
        n * routingA B e +
          (L5A2C4D.cr12 D * routingB B e +
            L5A2C4D.cr13 D * routingC B e) +
          (L5A2C4D.cr23 D - 1) * routingC B e := by ring
    _ = n * routingA B e + L5A2C4A.c1 B e * routingA B e +
          (L5A2C4D.cr23 D - 1) * routingC B e := by rw [hr.1]
    _ = (n + L5A2C4A.c1 B e) * routingA B e +
          (L5A2C4D.cr23 D - 1) * routingC B e := by ring

private theorem coherent_kappa2_add_c_normalized_transport
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : L5A2C4D.CoherentHerzogData B e) (n : ℕ) :
    normalizedGrid B e n (L5A2C4D.cr12 D - 1) (L5A2C4A.c3 B e) =
      normalizedGrid B e (n + L5A2C4D.cr31 D) (L5A2C4A.c2 B e - 1) 0 := by
  have hr := L5A2C4OR5.coherent_normalized_relations B e D
  have hc := L5A2C4D.coherent_coefficients B e D
  have hp := L5A2C4D.coherent_coefficients_positive B e D
  have hs12 : L5A2C4D.cr12 D - 1 + 1 = L5A2C4D.cr12 D := by omega
  have hs2 : L5A2C4A.c2 B e - 1 + 1 = L5A2C4A.c2 B e := by omega
  have hc2sub : L5A2C4A.c2 B e - 1 =
      (L5A2C4D.cr12 D - 1) + L5A2C4D.cr32 D := by omega
  simp only [normalizedGrid, zero_mul, add_zero]
  rw [hr.2.2, hc2sub, Nat.add_mul]
  ring

private theorem routing_apery_eq_normalizedGrid_of_canonical
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) [NeZero (routingA B e)]
    (i j : ℕ)
    (h : L5A2C4OR4.IsCanonicalTailGridPoint B e i j) :
    (routingI B e).aperyRepresentative (routingA B e) (gridResidue B e i j) =
      (normalizedGrid B e (eta B e i j) i j : ℤ) := by
  have hs := gridLift_spec B e i j
  have hz := L5A2C4OR4.gridLift_eq_zero_of_isCanonical B e i j h
  simpa [hz] using hs.symm

private theorem branchB_ox_kappa_add_b_normalized_transport
    (R : SectorBCriticalRoleBranchB P) (n : ℕ) :
    normalizedGrid P.M.base (branchBInactiveReindex R) n
        (r31 R) (c2 R - 1) =
      normalizedGrid P.M.base (branchBInactiveReindex R) (n + c3 R)
        0 (r12 R - 1) := by
  simpa using coherent_kappa2_add_b_normalized_transport P.M.base
    (branchBInactiveReindex R) (branchB_inactive_coherentHerzogData R) n

private theorem branchB_ox_kappa_add_c_normalized_transport
    (R : SectorBCriticalRoleBranchB P) (n : ℕ) :
    normalizedGrid P.M.base (branchBInactiveReindex R) n
        (r31 R - 1) (c2 R) =
      normalizedGrid P.M.base (branchBInactiveReindex R) (n + r23 R)
        (c1 R - 1) 0 := by
  simpa using coherent_kappa2_add_c_normalized_transport P.M.base
    (branchBInactiveReindex R) (branchB_inactive_coherentHerzogData R) n

private theorem branchB_ox_kappa_add_b_residue
    (R : SectorBCriticalRoleBranchB P) :
    gridResidue P.M.base (branchBInactiveReindex R) (r31 R - 1) (c2 R - 1) +
        routingB P.M.base (branchBInactiveReindex R) =
      gridResidue P.M.base (branchBInactiveReindex R) 0 (r12 R - 1) := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  have hr31 := (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.2.2.1
  rw [← gridResidue_add_b P.M.base e (r31 R - 1) (c2 R - 1)]
  have hstep : r31 R - 1 + 1 = r31 R := Nat.sub_add_cancel hr31
  rw [hstep]
  have ht := branchB_ox_kappa_add_b_normalized_transport R 0
  have hraw := normalizedGrid_mod P.M.base e 0 (r31 R) (c2 R - 1)
  have hred := normalizedGrid_mod P.M.base e (c3 R) 0 (r12 R - 1)
  rw [← hraw, ← hred]
  simpa [e] using
    congrArg (fun n : ℕ => (n : ZMod (routingA P.M.base e))) ht

private theorem branchB_ox_kappa_add_c_residue
    (R : SectorBCriticalRoleBranchB P) :
    gridResidue P.M.base (branchBInactiveReindex R) (r31 R - 1) (c2 R - 1) +
        routingC P.M.base (branchBInactiveReindex R) =
      gridResidue P.M.base (branchBInactiveReindex R) (c1 R - 1) 0 := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  have hc2 : 0 < c2 R := (criticalExponent_spec P.M.base (R.reindex 1)).1
  rw [← gridResidue_add_c P.M.base e (r31 R - 1) (c2 R - 1)]
  have hstep : c2 R - 1 + 1 = c2 R := Nat.sub_add_cancel hc2
  rw [hstep]
  have ht := branchB_ox_kappa_add_c_normalized_transport R 0
  have hraw := normalizedGrid_mod P.M.base e 0 (r31 R - 1) (c2 R)
  have hred := normalizedGrid_mod P.M.base e (r23 R) (c1 R - 1) 0
  rw [← hraw, ← hred]
  simpa [e] using
    congrArg (fun n : ℕ => (n : ZMod (routingA P.M.base e))) ht

theorem branchB_ox_kappa_v_eq_r23_sub_threshold
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0) :
    (routingData P.M.base (branchBInactiveReindex R)).v
        (gridResidue P.M.base (branchBInactiveReindex R)
          (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2) =
      r23 R - branchBOXThreshold R := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let I := routingI B e
  let a := routingA B e
  let c := routingC B e
  let r := gridResidue B e (r31 R - 1) (c2 R - 1)
  let t := gridResidue B e (c1 R - 1) 0
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hr12 := (branchB_nonsymmetric_herzog_completion R).cross_positive.1
  have hc2sum := (branchB_nonsymmetric_herzog_completion R).coefficient_sums.2.1
  have hm := eta_antitone_right B e (r31 R - 1) (r32 R) (r12 R - 1)
  have hcoord : r32 R + (r12 R - 1) = c2 R - 1 := by omega
  rw [hcoord] at hm
  have heta : eta B e (r31 R - 1) (c2 R - 1) = 0 := by
    change eta B e (r31 R - 1) (r32 R) = 0 at hP1
    omega
  have hbase := routing_apery_eq_normalizedGrid_of_canonical B e
    (r31 R - 1) (c2 R - 1) (branchB_ox_kappa_canonical R)
  rw [heta] at hbase
  have htarget := routing_apery_eq_normalizedGrid_of_canonical B e
    (c1 R - 1) 0 (branchB_ox_kappa_reduced_c_canonical R)
  have hres : r + c = t := by
    simpa [r, c, t, e, B] using branchB_ox_kappa_add_c_residue R
  have hstep := I.apery_step_eq a c (routingHC B e) r
  change I.aperyRepresentative a r + c =
    I.aperyRepresentative a (r + c) +
      a * (routingData B e).v r at hstep
  rw [hres, hbase, htarget] at hstep
  have ht := congrArg (fun n : ℕ => (n : ℤ))
    (branchB_ox_kappa_add_c_normalized_transport R 0)
  have hc2 : 0 < c2 R := (criticalExponent_spec B (R.reindex 1)).1
  have hraw :
      ((normalizedGrid B e 0 (r31 R - 1) (c2 R - 1) : ℕ) : ℤ) + c =
        normalizedGrid B e 0 (r31 R - 1) (c2 R) := by
    have hnat :
        normalizedGrid B e 0 (r31 R - 1) (c2 R - 1) + c =
          normalizedGrid B e 0 (r31 R - 1) (c2 R) := by
      simp only [normalizedGrid, zero_mul, zero_add]
      have hj : (c2 R - 1) * routingC B e + routingC B e =
          c2 R * routingC B e := by
        calc
          (c2 R - 1) * routingC B e + routingC B e =
              ((c2 R - 1) + 1) * routingC B e := by ring
          _ = c2 R * routingC B e := by rw [Nat.sub_add_cancel hc2]
      dsimp only [c]
      omega
    exact_mod_cast hnat
  change (routingData B e).v r = r23 R - eta B e (c1 R - 1) 0
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul] at hstep ht
  dsimp only [a, c, B, e] at hstep hraw
  have hcstepZ :
      ((c2 R - 1 : ℕ) : ℤ) * routingC P.M.base (branchBInactiveReindex R) +
          routingC P.M.base (branchBInactiveReindex R) =
        (c2 R : ℤ) * routingC P.M.base (branchBInactiveReindex R) := by
    have hcstep : (c2 R - 1) + 1 = c2 R := Nat.sub_add_cancel hc2
    have hcstep' : ((c2 R - 1 : ℕ) : ℤ) + 1 = (c2 R : ℤ) := by
      exact_mod_cast hcstep
    calc
      ((c2 R - 1 : ℕ) : ℤ) * routingC P.M.base (branchBInactiveReindex R) +
          routingC P.M.base (branchBInactiveReindex R) =
        (((c2 R - 1 : ℕ) : ℤ) + 1) *
          routingC P.M.base (branchBInactiveReindex R) := by ring
      _ = (c2 R : ℤ) * routingC P.M.base (branchBInactiveReindex R) := by
        rw [hcstep']
  have hsum : eta B e (c1 R - 1) 0 + (routingData B e).v r = r23 R := by
    nlinarith [hstep, ht, hcstepZ]
  omega

private theorem branchB_ox_kappa_u_eq_c3_sub_reduced_eta
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0) :
    (routingData P.M.base (branchBInactiveReindex R)).u
        (gridResidue P.M.base (branchBInactiveReindex R)
          (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2) =
      c3 R - eta P.M.base (branchBInactiveReindex R) 0 (r12 R - 1) := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let I := routingI B e
  let a := routingA B e
  let b := routingB B e
  let r := gridResidue B e (r31 R - 1) (c2 R - 1)
  let t := gridResidue B e 0 (r12 R - 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hr12 := (branchB_nonsymmetric_herzog_completion R).cross_positive.1
  have hm := eta_antitone_right B e (r31 R - 1) (r32 R) (r12 R - 1)
  have hcoord : r32 R + (r12 R - 1) = c2 R - 1 := by
    have hc2sum := (branchB_nonsymmetric_herzog_completion R).coefficient_sums.2.1
    omega
  rw [hcoord] at hm
  have heta : eta B e (r31 R - 1) (c2 R - 1) = 0 := by
    change eta B e (r31 R - 1) (r32 R) = 0 at hP1
    omega
  have hbase := routing_apery_eq_normalizedGrid_of_canonical B e
    (r31 R - 1) (c2 R - 1) (branchB_ox_kappa_canonical R)
  rw [heta] at hbase
  have htarget := routing_apery_eq_normalizedGrid_of_canonical B e
    0 (r12 R - 1) (branchB_ox_kappa_reduced_b_canonical R)
  have hres : r + b = t := by
    simpa [r, b, t, e, B] using branchB_ox_kappa_add_b_residue R
  have hstep := I.apery_step_eq a b (routingHB B e) r
  change I.aperyRepresentative a r + b =
    I.aperyRepresentative a (r + b) + a * (routingData B e).u r at hstep
  rw [hres, hbase, htarget] at hstep
  have ht := congrArg (fun n : ℕ => (n : ℤ))
    (branchB_ox_kappa_add_b_normalized_transport R 0)
  have hr31 : 0 < r31 R :=
    (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.2.2.1
  have hbStepZ :
      ((r31 R - 1 : ℕ) : ℤ) * routingB P.M.base (branchBInactiveReindex R) +
          routingB P.M.base (branchBInactiveReindex R) =
        (r31 R : ℤ) * routingB P.M.base (branchBInactiveReindex R) := by
    have hs : (r31 R - 1) + 1 = r31 R := Nat.sub_add_cancel hr31
    have hs' : ((r31 R - 1 : ℕ) : ℤ) + 1 = (r31 R : ℤ) := by
      exact_mod_cast hs
    calc
      ((r31 R - 1 : ℕ) : ℤ) * routingB P.M.base (branchBInactiveReindex R) +
          routingB P.M.base (branchBInactiveReindex R) =
        (((r31 R - 1 : ℕ) : ℤ) + 1) *
          routingB P.M.base (branchBInactiveReindex R) := by ring
      _ = (r31 R : ℤ) * routingB P.M.base (branchBInactiveReindex R) := by
        rw [hs']
  change (routingData B e).u r =
    c3 R - eta B e 0 (r12 R - 1)
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul] at hstep ht
  dsimp only [a, b, B, e] at hstep
  have hsum : eta B e 0 (r12 R - 1) + (routingData B e).u r = c3 R := by
    nlinarith [hstep, ht, hbStepZ]
  omega

theorem branchB_ox_kappa_u_pos_of_P1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0) :
    0 < (routingData P.M.base (branchBInactiveReindex R)).u
      (gridResidue P.M.base (branchBInactiveReindex R)
        (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2) := by
  rw [branchB_ox_kappa_u_eq_c3_sub_reduced_eta R hP1]
  have heta := eta_antitone_right P.M.base (branchBInactiveReindex R)
    0 0 (r12 R - 1)
  have heta' : eta P.M.base (branchBInactiveReindex R) 0 (r12 R - 1) ≤
      eta P.M.base (branchBInactiveReindex R) 0 0 := by
    simpa using heta
  have hH0 := branchB_inactive_H0_lt R
  change eta P.M.base (branchBInactiveReindex R) 0 0 < c3 R at hH0
  omega

theorem branchB_ox_kappa_v_pos_of_P1_zero_lt
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0)
    (hX : branchBOXThreshold R < r23 R) :
    0 < (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R)
        (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2) := by
  rw [branchB_ox_kappa_v_eq_r23_sub_threshold R hP1]
  omega

private theorem branchB_ox_kappa_not_integral_of_P1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let r := gridResidue P.M.base e
      (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2
    (routingI P.M.base e).aperyRepresentative (routingA P.M.base e) r -
        routingA P.M.base e ∉ (routingH P.M.base e).asRelativeIdeal := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let r := gridResidue B e (r31 R - 1) (c2 R - 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hr12 := (branchB_nonsymmetric_herzog_completion R).cross_positive.1
  have hm := eta_antitone_right B e (r31 R - 1) (r32 R) (r12 R - 1)
  have hcoord : r32 R + (r12 R - 1) = c2 R - 1 := by
    have hc2sum := (branchB_nonsymmetric_herzog_completion R).coefficient_sums.2.1
    omega
  rw [hcoord] at hm
  have heta : eta B e (r31 R - 1) (c2 R - 1) = 0 := by
    change eta B e (r31 R - 1) (r32 R) = 0 at hP1
    omega
  have hI := routing_apery_eq_normalizedGrid_of_canonical B e
    (r31 R - 1) (c2 R - 1) (branchB_ox_kappa_canonical R)
  rw [heta] at hI
  have hcanonical := branchB_ox_kappa_canonical R
  change (normalizedGrid B e 0 (r31 R - 1) (c2 R - 1) : ℤ) =
    L5A2C4OR3.physicalAlpha B e r at hcanonical
  have heq : (routingI B e).aperyRepresentative a r =
      (routingH B e).asRelativeIdeal.aperyRepresentative a r := by
    calc
      (routingI B e).aperyRepresentative a r =
          (normalizedGrid B e 0 (r31 R - 1) (c2 R - 1) : ℤ) := hI
      _ = L5A2C4OR3.physicalAlpha B e r := hcanonical
      _ = (routingH B e).asRelativeIdeal.aperyRepresentative a r := rfl
  change (routingI B e).aperyRepresentative a r - a ∉
    (routingH B e).asRelativeIdeal
  rw [heq]
  exact (routingH B e).asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem a r

theorem branchB_ox_kappa_fake_terminal_of_P1_zero_lt
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0)
    (hX : branchBOXThreshold R < r23 R) :
    ∃ x : L5A2C4N.ActualFakeTerminalSeats P.M.base (branchBInactiveReindex R),
      x.val = gridResidue P.M.base (branchBInactiveReindex R)
        (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let r := gridResidue B e (r31 R - 1) (c2 R - 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hu := branchB_ox_kappa_u_pos_of_P1_zero R hP1
  have hv := branchB_ox_kappa_v_pos_of_P1_zero_lt R hP1 hX
  have hn := branchB_ox_kappa_not_integral_of_P1_zero R hP1
  refine ⟨⟨r, ?_⟩, rfl⟩
  change (routingData B e).IsSink r ∧
    (routingI B e).aperyRepresentative a r - a ∉
      (routingH B e).asRelativeIdeal
  exact ⟨⟨Nat.ne_of_gt hu, Nat.ne_of_gt hv⟩, hn⟩

theorem branchB_oy_kappa_canonical
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4OR4.IsCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
      (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2 := by
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  have h := L5A2C4OR6.loadBearingCoordinates_canonical P.M.base e D
  simpa [branchBOYKappaCoordinates, L5A2C4D.coherentKappa1, e, D] using
    h.2.2.2.2.2.2

private theorem branchB_oy_kappa_reduced_b_canonical
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4OR4.IsCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
      0 (c2 R - 1) := by
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  have h := L5A2C4OR6.loadBearingCoordinates_canonical P.M.base e D
  simpa [e, D, branchB_inactive_coherent_c3] using h.2.2.2.1

private theorem branchB_oy_kappa_reduced_c_canonical
    (R : SectorBCriticalRoleBranchB P) :
    L5A2C4OR4.IsCanonicalTailGridPoint P.M.base (branchBInactiveReindex R)
      (r21 R - 1) 0 := by
  let e := branchBInactiveReindex R
  let D := branchB_inactive_coherentHerzogData R
  have h := L5A2C4OR6.loadBearingCoordinates_canonical P.M.base e D
  simpa [e, D] using h.2.2.2.2.2.1

theorem branchB_oy_kappa_gridLift_zero
    (R : SectorBCriticalRoleBranchB P) :
    gridLift P.M.base (branchBInactiveReindex R)
      (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2 = 0 :=
  L5A2C4OR4.gridLift_eq_zero_of_isCanonical P.M.base
    (branchBInactiveReindex R) _ _ (branchB_oy_kappa_canonical R)

private theorem coherent_kappa1_add_b_normalized_transport
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : L5A2C4D.CoherentHerzogData B e) (n : ℕ) :
    normalizedGrid B e n (L5A2C4A.c2 B e) (L5A2C4D.cr13 D - 1) =
      normalizedGrid B e (n + L5A2C4D.cr21 D) 0
        (L5A2C4A.c3 B e - 1) := by
  have hr := L5A2C4OR5.coherent_normalized_relations B e D
  have hc := L5A2C4D.coherent_coefficients B e D
  have hp := L5A2C4D.coherent_coefficients_positive B e D
  have hc3sub : L5A2C4A.c3 B e - 1 =
      (L5A2C4D.cr13 D - 1) + L5A2C4D.cr23 D := by omega
  simp only [normalizedGrid, zero_mul, add_zero]
  rw [hr.2.1, hc3sub, Nat.add_mul]
  ring

private theorem coherent_kappa1_add_c_normalized_transport
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : L5A2C4D.CoherentHerzogData B e) (n : ℕ) :
    normalizedGrid B e n (L5A2C4A.c2 B e - 1) (L5A2C4D.cr13 D) =
      normalizedGrid B e (n + L5A2C4A.c1 B e)
        (L5A2C4D.cr32 D - 1) 0 := by
  have hr := L5A2C4OR5.coherent_normalized_relations B e D
  have hc := L5A2C4D.coherent_coefficients B e D
  have hp := L5A2C4D.coherent_coefficients_positive B e D
  have hc2sub : L5A2C4A.c2 B e - 1 =
      L5A2C4D.cr12 D + (L5A2C4D.cr32 D - 1) := by omega
  simp only [normalizedGrid, zero_mul, add_zero]
  rw [hc2sub, Nat.add_mul]
  calc
    n * routingA B e +
          (L5A2C4D.cr12 D * routingB B e +
            (L5A2C4D.cr32 D - 1) * routingB B e) +
          L5A2C4D.cr13 D * routingC B e =
        n * routingA B e +
          (L5A2C4D.cr12 D * routingB B e +
            L5A2C4D.cr13 D * routingC B e) +
          (L5A2C4D.cr32 D - 1) * routingB B e := by ring
    _ = n * routingA B e + L5A2C4A.c1 B e * routingA B e +
          (L5A2C4D.cr32 D - 1) * routingB B e := by rw [hr.1]
    _ = (n + L5A2C4A.c1 B e) * routingA B e +
          (L5A2C4D.cr32 D - 1) * routingB B e := by ring

private theorem branchB_oy_kappa_add_b_normalized_transport
    (R : SectorBCriticalRoleBranchB P) (n : ℕ) :
    normalizedGrid P.M.base (branchBInactiveReindex R) n
        (c1 R) (r32 R - 1) =
      normalizedGrid P.M.base (branchBInactiveReindex R) (n + r13 R)
        0 (c2 R - 1) := by
  simpa using coherent_kappa1_add_b_normalized_transport P.M.base
    (branchBInactiveReindex R) (branchB_inactive_coherentHerzogData R) n

private theorem branchB_oy_kappa_add_c_normalized_transport
    (R : SectorBCriticalRoleBranchB P) (n : ℕ) :
    normalizedGrid P.M.base (branchBInactiveReindex R) n
        (c1 R - 1) (r32 R) =
      normalizedGrid P.M.base (branchBInactiveReindex R) (n + c3 R)
        (r21 R - 1) 0 := by
  simpa using coherent_kappa1_add_c_normalized_transport P.M.base
    (branchBInactiveReindex R) (branchB_inactive_coherentHerzogData R) n

private theorem branchB_oy_kappa_add_b_residue
    (R : SectorBCriticalRoleBranchB P) :
    gridResidue P.M.base (branchBInactiveReindex R) (c1 R - 1) (r32 R - 1) +
        routingB P.M.base (branchBInactiveReindex R) =
      gridResidue P.M.base (branchBInactiveReindex R) 0 (c2 R - 1) := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  have hc1 : 0 < c1 R := (criticalExponent_spec P.M.base (R.reindex 0)).1
  rw [← gridResidue_add_b P.M.base e (c1 R - 1) (r32 R - 1)]
  rw [Nat.sub_add_cancel hc1]
  have ht := branchB_oy_kappa_add_b_normalized_transport R 0
  have hraw := normalizedGrid_mod P.M.base e 0 (c1 R) (r32 R - 1)
  have hred := normalizedGrid_mod P.M.base e (r13 R) 0 (c2 R - 1)
  rw [← hraw, ← hred]
  simpa [e] using
    congrArg (fun n : ℕ => (n : ZMod (routingA P.M.base e))) ht

private theorem branchB_oy_kappa_add_c_residue
    (R : SectorBCriticalRoleBranchB P) :
    gridResidue P.M.base (branchBInactiveReindex R) (c1 R - 1) (r32 R - 1) +
        routingC P.M.base (branchBInactiveReindex R) =
      gridResidue P.M.base (branchBInactiveReindex R) (r21 R - 1) 0 := by
  let e := branchBInactiveReindex R
  letI : NeZero (routingA P.M.base e) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
  have hr32 := (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.2.2.2
  rw [← gridResidue_add_c P.M.base e (c1 R - 1) (r32 R - 1)]
  rw [Nat.sub_add_cancel hr32]
  have ht := branchB_oy_kappa_add_c_normalized_transport R 0
  have hraw := normalizedGrid_mod P.M.base e 0 (c1 R - 1) (r32 R)
  have hred := normalizedGrid_mod P.M.base e (c3 R) (r21 R - 1) 0
  rw [← hraw, ← hred]
  simpa [e] using
    congrArg (fun n : ℕ => (n : ZMod (routingA P.M.base e))) ht

private theorem branchB_oy_kappa_u_eq_r13_sub_threshold
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0) :
    (routingData P.M.base (branchBInactiveReindex R)).u
        (gridResidue P.M.base (branchBInactiveReindex R)
          (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2) =
      r13 R - branchBOYThreshold R := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let I := routingI B e
  let a := routingA B e
  let b := routingB B e
  let r := gridResidue B e (c1 R - 1) (r32 R - 1)
  let t := gridResidue B e 0 (c2 R - 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hr21 := (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.1
  have hm := eta_antitone_left B e (r31 R) (r32 R - 1) (r21 R - 1)
  have hcoord : r31 R + (r21 R - 1) = c1 R - 1 := by
    have hc1sum := (branchB_nonsymmetric_herzog_completion R).coefficient_sums.1
    omega
  rw [hcoord] at hm
  have heta : eta B e (c1 R - 1) (r32 R - 1) = 0 := by
    change eta B e (r31 R) (r32 R - 1) = 0 at hQ1
    omega
  have hbase := routing_apery_eq_normalizedGrid_of_canonical B e
    (c1 R - 1) (r32 R - 1) (branchB_oy_kappa_canonical R)
  rw [heta] at hbase
  have htarget := routing_apery_eq_normalizedGrid_of_canonical B e
    0 (c2 R - 1) (branchB_oy_kappa_reduced_b_canonical R)
  have hres : r + b = t := by
    simpa [r, b, t, e, B] using branchB_oy_kappa_add_b_residue R
  have hstep := I.apery_step_eq a b (routingHB B e) r
  change I.aperyRepresentative a r + b =
    I.aperyRepresentative a (r + b) + a * (routingData B e).u r at hstep
  rw [hres, hbase, htarget] at hstep
  have ht := congrArg (fun n : ℕ => (n : ℤ))
    (branchB_oy_kappa_add_b_normalized_transport R 0)
  have hc1 : 0 < c1 R := (criticalExponent_spec B (R.reindex 0)).1
  have hbStepZ :
      ((c1 R - 1 : ℕ) : ℤ) * routingB P.M.base (branchBInactiveReindex R) +
          routingB P.M.base (branchBInactiveReindex R) =
        (c1 R : ℤ) * routingB P.M.base (branchBInactiveReindex R) := by
    have hs : (c1 R - 1) + 1 = c1 R := Nat.sub_add_cancel hc1
    have hs' : ((c1 R - 1 : ℕ) : ℤ) + 1 = (c1 R : ℤ) := by exact_mod_cast hs
    calc
      ((c1 R - 1 : ℕ) : ℤ) * routingB P.M.base (branchBInactiveReindex R) +
          routingB P.M.base (branchBInactiveReindex R) =
        (((c1 R - 1 : ℕ) : ℤ) + 1) *
          routingB P.M.base (branchBInactiveReindex R) := by ring
      _ = (c1 R : ℤ) * routingB P.M.base (branchBInactiveReindex R) := by rw [hs']
  change (routingData B e).u r = r13 R - eta B e 0 (c2 R - 1)
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul] at hstep ht
  dsimp only [a, b, B, e] at hstep
  have hsum : eta B e 0 (c2 R - 1) + (routingData B e).u r = r13 R := by
    nlinarith [hstep, ht, hbStepZ]
  omega

private theorem branchB_oy_kappa_v_eq_c3_sub_reduced_eta
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0) :
    (routingData P.M.base (branchBInactiveReindex R)).v
        (gridResidue P.M.base (branchBInactiveReindex R)
          (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2) =
      c3 R - eta P.M.base (branchBInactiveReindex R) (r21 R - 1) 0 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let I := routingI B e
  let a := routingA B e
  let c := routingC B e
  let r := gridResidue B e (c1 R - 1) (r32 R - 1)
  let t := gridResidue B e (r21 R - 1) 0
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hr21 := (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.1
  have hm := eta_antitone_left B e (r31 R) (r32 R - 1) (r21 R - 1)
  have hcoord : r31 R + (r21 R - 1) = c1 R - 1 := by
    have hc1sum := (branchB_nonsymmetric_herzog_completion R).coefficient_sums.1
    omega
  rw [hcoord] at hm
  have heta : eta B e (c1 R - 1) (r32 R - 1) = 0 := by
    change eta B e (r31 R) (r32 R - 1) = 0 at hQ1
    omega
  have hbase := routing_apery_eq_normalizedGrid_of_canonical B e
    (c1 R - 1) (r32 R - 1) (branchB_oy_kappa_canonical R)
  rw [heta] at hbase
  have htarget := routing_apery_eq_normalizedGrid_of_canonical B e
    (r21 R - 1) 0 (branchB_oy_kappa_reduced_c_canonical R)
  have hres : r + c = t := by
    simpa [r, c, t, e, B] using branchB_oy_kappa_add_c_residue R
  have hstep := I.apery_step_eq a c (routingHC B e) r
  change I.aperyRepresentative a r + c =
    I.aperyRepresentative a (r + c) + a * (routingData B e).v r at hstep
  rw [hres, hbase, htarget] at hstep
  have ht := congrArg (fun n : ℕ => (n : ℤ))
    (branchB_oy_kappa_add_c_normalized_transport R 0)
  have hr32 := (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.2.2.2
  have hcStepZ :
      ((r32 R - 1 : ℕ) : ℤ) * routingC P.M.base (branchBInactiveReindex R) +
          routingC P.M.base (branchBInactiveReindex R) =
        (r32 R : ℤ) * routingC P.M.base (branchBInactiveReindex R) := by
    have hs : (r32 R - 1) + 1 = r32 R := Nat.sub_add_cancel hr32
    have hs' : ((r32 R - 1 : ℕ) : ℤ) + 1 = (r32 R : ℤ) := by exact_mod_cast hs
    calc
      ((r32 R - 1 : ℕ) : ℤ) * routingC P.M.base (branchBInactiveReindex R) +
          routingC P.M.base (branchBInactiveReindex R) =
        (((r32 R - 1 : ℕ) : ℤ) + 1) *
          routingC P.M.base (branchBInactiveReindex R) := by ring
      _ = (r32 R : ℤ) * routingC P.M.base (branchBInactiveReindex R) := by rw [hs']
  change (routingData B e).v r = c3 R - eta B e (r21 R - 1) 0
  have ha : (0 : ℤ) < a := by exact_mod_cast routingA_pos B e
  have hc3sum := (branchB_nonsymmetric_herzog_completion R).coefficient_sums.2.2
  have hc3sumZ : (c3 R : ℤ) = (r13 R : ℤ) + r23 R := by
    exact_mod_cast hc3sum
  simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul] at hstep ht
  dsimp only [a, c, B, e] at hstep
  have hsum : eta B e (r21 R - 1) 0 + (routingData B e).v r = c3 R := by
    nlinarith [hstep, ht, hcStepZ, hc3sumZ]
  omega

theorem branchB_oy_kappa_u_pos_of_Q1_zero_lt
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0)
    (hY : branchBOYThreshold R < r13 R) :
    0 < (routingData P.M.base (branchBInactiveReindex R)).u
      (gridResidue P.M.base (branchBInactiveReindex R)
        (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2) := by
  rw [branchB_oy_kappa_u_eq_r13_sub_threshold R hQ1]
  omega

theorem branchB_oy_kappa_v_pos_of_Q1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0) :
    0 < (routingData P.M.base (branchBInactiveReindex R)).v
      (gridResidue P.M.base (branchBInactiveReindex R)
        (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2) := by
  rw [branchB_oy_kappa_v_eq_c3_sub_reduced_eta R hQ1]
  have heta := eta_antitone_left P.M.base (branchBInactiveReindex R)
    0 0 (r21 R - 1)
  have heta' : eta P.M.base (branchBInactiveReindex R) (r21 R - 1) 0 ≤
      eta P.M.base (branchBInactiveReindex R) 0 0 := by
    simpa using heta
  have hH0 := branchB_inactive_H0_lt R
  change eta P.M.base (branchBInactiveReindex R) 0 0 < c3 R at hH0
  omega

private theorem branchB_oy_kappa_not_integral_of_Q1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0) :
    let e := branchBInactiveReindex R
    letI : NeZero (routingA P.M.base e) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
    let r := gridResidue P.M.base e
      (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2
    (routingI P.M.base e).aperyRepresentative (routingA P.M.base e) r -
        routingA P.M.base e ∉ (routingH P.M.base e).asRelativeIdeal := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let r := gridResidue B e (c1 R - 1) (r32 R - 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hr21 := (branchB_nonsymmetric_herzog_completion R).cross_positive.2.2.1
  have hm := eta_antitone_left B e (r31 R) (r32 R - 1) (r21 R - 1)
  have hcoord : r31 R + (r21 R - 1) = c1 R - 1 := by
    have hc1sum := (branchB_nonsymmetric_herzog_completion R).coefficient_sums.1
    omega
  rw [hcoord] at hm
  have heta : eta B e (c1 R - 1) (r32 R - 1) = 0 := by
    change eta B e (r31 R) (r32 R - 1) = 0 at hQ1
    omega
  have hI := routing_apery_eq_normalizedGrid_of_canonical B e
    (c1 R - 1) (r32 R - 1) (branchB_oy_kappa_canonical R)
  rw [heta] at hI
  have hcanonical := branchB_oy_kappa_canonical R
  change (normalizedGrid B e 0 (c1 R - 1) (r32 R - 1) : ℤ) =
    L5A2C4OR3.physicalAlpha B e r at hcanonical
  have heq : (routingI B e).aperyRepresentative a r =
      (routingH B e).asRelativeIdeal.aperyRepresentative a r := by
    calc
      (routingI B e).aperyRepresentative a r =
          (normalizedGrid B e 0 (c1 R - 1) (r32 R - 1) : ℤ) := hI
      _ = L5A2C4OR3.physicalAlpha B e r := hcanonical
      _ = (routingH B e).asRelativeIdeal.aperyRepresentative a r := rfl
  change (routingI B e).aperyRepresentative a r - a ∉
    (routingH B e).asRelativeIdeal
  rw [heq]
  exact (routingH B e).asRelativeIdeal.aperyRepresentative_sub_modulus_not_mem a r

theorem branchB_oy_kappa_fake_terminal_of_Q1_zero_lt
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0)
    (hY : branchBOYThreshold R < r13 R) :
    ∃ x : L5A2C4N.ActualFakeTerminalSeats P.M.base (branchBInactiveReindex R),
      x.val = gridResidue P.M.base (branchBInactiveReindex R)
        (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2 := by
  let B := P.M.base
  let e := branchBInactiveReindex R
  let a := routingA B e
  let r := gridResidue B e (c1 R - 1) (r32 R - 1)
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hu := branchB_oy_kappa_u_pos_of_Q1_zero_lt R hQ1 hY
  have hv := branchB_oy_kappa_v_pos_of_Q1_zero R hQ1
  have hn := branchB_oy_kappa_not_integral_of_Q1_zero R hQ1
  refine ⟨⟨r, ?_⟩, rfl⟩
  change (routingData B e).IsSink r ∧
    (routingI B e).aperyRepresentative a r - a ∉
      (routingH B e).asRelativeIdeal
  exact ⟨⟨Nat.ne_of_gt hu, Nat.ne_of_gt hv⟩, hn⟩

@[simp] theorem branchB_ox_threshold_coordinates
    (R : SectorBCriticalRoleBranchB P) :
    branchBOXThresholdCoordinates R = (c1 R - 1, 0) := rfl

@[simp] theorem branchB_oy_threshold_coordinates
    (R : SectorBCriticalRoleBranchB P) :
    branchBOYThresholdCoordinates R = (0, c2 R - 1) := rfl

theorem branchB_ox_endpoint_threshold_eq
    (R : SectorBCriticalRoleBranchB P) :
    branchBOXThreshold R =
      eta P.M.base (branchBInactiveReindex R) (c1 R - 1) 0 := rfl

theorem branchB_oy_endpoint_threshold_eq
    (R : SectorBCriticalRoleBranchB P) :
    branchBOYThreshold R =
      eta P.M.base (branchBInactiveReindex R) 0 (c2 R - 1) := rfl

theorem branchB_ox_kappa_eta_zero_of_P1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0) :
    eta P.M.base (branchBInactiveReindex R)
      (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2 = 0 := by
  let e := branchBInactiveReindex R
  let C := branchB_nonsymmetric_herzog_completion R
  have hr12 := C.cross_positive.1
  have hc2 := C.coefficient_sums.2.1
  have hm := eta_antitone_right P.M.base e (r31 R - 1) (r32 R) (r12 R - 1)
  have hcoord : r32 R + (r12 R - 1) = c2 R - 1 := by omega
  rw [hcoord] at hm
  change eta P.M.base e (r31 R - 1) (c2 R - 1) = 0
  change eta P.M.base e (r31 R - 1) (r32 R) = 0 at hP1
  omega

theorem branchB_oy_kappa_eta_zero_of_Q1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0) :
    eta P.M.base (branchBInactiveReindex R)
      (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2 = 0 := by
  let e := branchBInactiveReindex R
  let C := branchB_nonsymmetric_herzog_completion R
  have hr21 := C.cross_positive.2.2.1
  have hc1 := C.coefficient_sums.1
  have hm := eta_antitone_left P.M.base e (r31 R) (r32 R - 1) (r21 R - 1)
  have hcoord : r31 R + (r21 R - 1) = c1 R - 1 := by omega
  rw [hcoord] at hm
  change eta P.M.base e (c1 R - 1) (r32 R - 1) = 0
  change eta P.M.base e (r31 R) (r32 R - 1) = 0 at hQ1
  omega

/-- In the inactive cyclic chart, the first seam zero transports to the OX
threshold state and gives the exact paper bound `X2 <= local r31`.  Here the
local `r31` is the frozen Branch-B coefficient `r23` after cyclic reindexing.
-/
theorem branchB_ox_threshold_le_r23_of_P1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0) :
    branchBOXThreshold R ≤ r23 R := by
  let e := branchBInactiveReindex R
  let C := branchB_nonsymmetric_herzog_completion R
  obtain ⟨hr12, _, _, hr23, hr31, _⟩ := C.cross_positive
  obtain ⟨hc1, hc2, _⟩ := C.coefficient_sums
  obtain ⟨_, hrel2, _⟩ := C.weighted_relations
  have hm := eta_antitone_right P.M.base e (r31 R - 1) (r32 R) (r12 R - 1)
  have hcoord : r32 R + (r12 R - 1) = c2 R - 1 := by omega
  have hkappa : eta P.M.base e (r31 R - 1) (c2 R - 1) = 0 := by
    rw [hcoord] at hm
    change eta P.M.base e (r31 R - 1) (r32 R) = 0 at hP1
    omega
  have hm1 := eta_antitone_right P.M.base e (r31 R - 1) (c2 R - 1) 1
  have hc2pos : 0 < c2 R := by omega
  have hc2step : c2 R - 1 + 1 = c2 R := Nat.sub_add_cancel hc2pos
  have hrawzero : eta P.M.base e (r31 R - 1) (c2 R) = 0 := by
    rw [hc2step] at hm1
    omega
  have hK : gridDegree P.M.base e 0 (r31 R - 1) (c2 R) ∈ P.M.base.K :=
    (eta_eq_zero_iff P.M.base e _ _).mp hrawzero
  have htransport :
      gridDegree P.M.base e 0 (r31 R - 1) (c2 R) =
        gridDegree P.M.base e (r23 R) (c1 R - 1) 0 := by
    dsimp [e]
    simp only [gridDegree, branchBInactiveReindex_zero,
      branchBInactiveReindex_one, branchBInactiveReindex_two,
      zero_mul, add_zero]
    have hsub : (r31 R - 1) + r21 R = c1 R - 1 := by omega
    calc
      0 + (r31 R - 1) * weights P.M.base (R.reindex 0) +
          c2 R * weights P.M.base (R.reindex 1) =
        ((r31 R - 1) + r21 R) * weights P.M.base (R.reindex 0) +
          r23 R * weights P.M.base (R.reindex 2) := by rw [hrel2]; ring
      _ = (c1 R - 1) * weights P.M.base (R.reindex 0) +
          r23 R * weights P.M.base (R.reindex 2) := by rw [hsub]
      _ = r23 R * weights P.M.base (R.reindex 2) +
          (c1 R - 1) * weights P.M.base (R.reindex 0) := by ac_rfl
  rw [htransport] at hK
  exact eta_le_of_mem P.M.base e (c1 R - 1) 0 (r23 R) hK

/-- Cyclic dual of `branchB_ox_threshold_le_r23_of_P1_zero`.  In the inactive
chart the local `r21` is the frozen Branch-B coefficient `r13`.
-/
theorem branchB_oy_threshold_le_r13_of_Q1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0) :
    branchBOYThreshold R ≤ r13 R := by
  let e := branchBInactiveReindex R
  let C := branchB_nonsymmetric_herzog_completion R
  obtain ⟨_, _, hr21, _, _, hr32⟩ := C.cross_positive
  obtain ⟨hc1, hc2, _⟩ := C.coefficient_sums
  obtain ⟨hrel1, _, _⟩ := C.weighted_relations
  have hm := eta_antitone_left P.M.base e (r31 R) (r32 R - 1) (r21 R - 1)
  have hcoord : r31 R + (r21 R - 1) = c1 R - 1 := by omega
  have hkappa : eta P.M.base e (c1 R - 1) (r32 R - 1) = 0 := by
    rw [hcoord] at hm
    change eta P.M.base e (r31 R) (r32 R - 1) = 0 at hQ1
    omega
  have hm1 := eta_antitone_left P.M.base e (c1 R - 1) (r32 R - 1) 1
  have hc1pos : 0 < c1 R := by omega
  have hc1step : c1 R - 1 + 1 = c1 R := Nat.sub_add_cancel hc1pos
  have hrawzero : eta P.M.base e (c1 R) (r32 R - 1) = 0 := by
    rw [hc1step] at hm1
    omega
  have hK : gridDegree P.M.base e 0 (c1 R) (r32 R - 1) ∈ P.M.base.K :=
    (eta_eq_zero_iff P.M.base e _ _).mp hrawzero
  have htransport :
      gridDegree P.M.base e 0 (c1 R) (r32 R - 1) =
        gridDegree P.M.base e (r13 R) 0 (c2 R - 1) := by
    dsimp [e]
    simp only [gridDegree, branchBInactiveReindex_zero,
      branchBInactiveReindex_one, branchBInactiveReindex_two,
      zero_mul, add_zero]
    have hsub : r12 R + (r32 R - 1) = c2 R - 1 := by omega
    calc
      0 + c1 R * weights P.M.base (R.reindex 0) +
          (r32 R - 1) * weights P.M.base (R.reindex 1) =
        r13 R * weights P.M.base (R.reindex 2) +
          (r12 R + (r32 R - 1)) * weights P.M.base (R.reindex 1) := by
            rw [hrel1]
            ring
      _ = r13 R * weights P.M.base (R.reindex 2) +
          (c2 R - 1) * weights P.M.base (R.reindex 1) := by rw [hsub]
  rw [htransport] at hK
  exact eta_le_of_mem P.M.base e 0 (c2 R - 1) (r13 R) hK

theorem branchB_ox_threshold_lt_or_eq_of_P1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0) :
    branchBOXThreshold R < r23 R ∨ branchBOXThreshold R = r23 R := by
  have hle := branchB_ox_threshold_le_r23_of_P1_zero R hP1
  omega

theorem branchB_oy_threshold_lt_or_eq_of_Q1_zero
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0) :
    branchBOYThreshold R < r13 R ∨ branchBOYThreshold R = r13 R := by
  have hle := branchB_oy_threshold_le_r13_of_Q1_zero R hQ1
  omega

/-- The complete source-exact numerical conclusion currently justified by the
inactive gate.  It intentionally does not identify `x2`/`y3` with a canonical
exceptional-run endpoint: the audited stencil identifies the fake terminal
with the adjacent kappa corner, not with these threshold states.
-/
theorem branchB_inactive_gate_exposed_pf_numerical_frontier
    (R : SectorBCriticalRoleBranchB P) :
    (branchBOXThreshold R < r23 R ∨ branchBOXThreshold R = r23 R) ∨
      (branchBOYThreshold R < r13 R ∨ branchBOYThreshold R = r13 R) := by
  rcases branchB_inactive_seam_zero R with hP | hQ
  · exact Or.inl (branchB_ox_threshold_lt_or_eq_of_P1_zero R hP)
  · exact Or.inr (branchB_oy_threshold_lt_or_eq_of_Q1_zero R hQ)

/-- The OX seam is either represented by the actual fake terminal at the
adjacent `kappa2` corner, or it is the exact escape equality.  No endpoint or
owner identification is included. -/
theorem branchB_ox_exposed_pf_fake_or_escape
    (R : SectorBCriticalRoleBranchB P)
    (hP1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R - 1) (r32 R) = 0) :
    (∃ x : L5A2C4N.ActualFakeTerminalSeats P.M.base (branchBInactiveReindex R),
        x.val = gridResidue P.M.base (branchBInactiveReindex R)
          (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2) ∨
      branchBOXThreshold R = r23 R := by
  rcases branchB_ox_threshold_lt_or_eq_of_P1_zero R hP1 with hlt | heq
  · exact Or.inl (branchB_ox_kappa_fake_terminal_of_P1_zero_lt R hP1 hlt)
  · exact Or.inr heq

/-- Exact cyclic dual of the OX fake-or-escape classification. -/
theorem branchB_oy_exposed_pf_fake_or_escape
    (R : SectorBCriticalRoleBranchB P)
    (hQ1 : eta P.M.base (branchBInactiveReindex R)
      (r31 R) (r32 R - 1) = 0) :
    (∃ x : L5A2C4N.ActualFakeTerminalSeats P.M.base (branchBInactiveReindex R),
        x.val = gridResidue P.M.base (branchBInactiveReindex R)
          (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2) ∨
      branchBOYThreshold R = r13 R := by
  rcases branchB_oy_threshold_lt_or_eq_of_Q1_zero R hQ1 with hlt | heq
  · exact Or.inl (branchB_oy_kappa_fake_terminal_of_Q1_zero_lt R hQ1 hlt)
  · exact Or.inr heq

/-- A3.3: the inactive gate exposes one of the two actual PF channels.  In a
strict channel the adjacent canonical corner occupies an actual fake terminal
seat; in the boundary channel the corresponding source-exact escape equality
holds. -/
theorem branchB_inactive_gate_exposed_pf_channel
    (R : SectorBCriticalRoleBranchB P) :
    ((∃ x : L5A2C4N.ActualFakeTerminalSeats P.M.base (branchBInactiveReindex R),
          x.val = gridResidue P.M.base (branchBInactiveReindex R)
            (branchBOXKappaCoordinates R).1 (branchBOXKappaCoordinates R).2) ∨
        branchBOXThreshold R = r23 R) ∨
      ((∃ x : L5A2C4N.ActualFakeTerminalSeats P.M.base (branchBInactiveReindex R),
          x.val = gridResidue P.M.base (branchBInactiveReindex R)
            (branchBOYKappaCoordinates R).1 (branchBOYKappaCoordinates R).2) ∨
        branchBOYThreshold R = r13 R) := by
  rcases branchB_inactive_seam_zero R with hP | hQ
  · exact Or.inl (branchB_ox_exposed_pf_fake_or_escape R hP)
  · exact Or.inr (branchB_oy_exposed_pf_fake_or_escape R hQ)

end NS25Lean.L5A2B4AR5B

