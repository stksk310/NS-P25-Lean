import NS25Lean.P2BranchAEntryClosure
import NS25Lean.P2SectorCGridPhysicalOffsetDictionary

noncomputable section
namespace NS25Lean.L5A2B4AR5A

open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR3 L5A2B4AR4R1 L5A2C4C L5A2C4H
  L5A2B4AR4R2A L5A2C4OR3 L5A2C4OR4

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

private theorem routingD_eq_tailGcd (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B e = tailGcd (B.tailDegrees 0).val
      (B.tailDegrees 1).val (B.tailDegrees 2).val := by
  apply Nat.dvd_antisymm
  · have hall (i : Fin 3) : routingD B e ∣ (B.tailDegrees i).val := by
      obtain ⟨j, hj⟩ := e.surjective i
      rw [← hj]
      fin_cases j
      · exact (tailGcd_dvd _ _ _).1
      · exact (tailGcd_dvd _ _ _).2.1
      · exact (tailGcd_dvd _ _ _).2.2
    exact Nat.dvd_gcd (hall 0) (Nat.dvd_gcd (hall 1) (hall 2))
  · obtain ⟨h0, h1, h2⟩ := tailGcd_dvd
      (B.tailDegrees 0).val (B.tailDegrees 1).val (B.tailDegrees 2).val
    have hall (i : Fin 3) :
        tailGcd (B.tailDegrees 0).val (B.tailDegrees 1).val
          (B.tailDegrees 2).val ∣ (B.tailDegrees (e i)).val := by
      have he : e i = 0 ∨ e i = 1 ∨ e i = 2 := by omega
      rcases he with he | he | he
      · simpa [he] using h0
      · simpa [he] using h1
      · simpa [he] using h2
    exact Nat.dvd_gcd (hall 0) (Nat.dvd_gcd (hall 1) (hall 2))

theorem routingA_eq_n0 (A : SectorBCriticalRoleBranchA P) :
    routingA P.M.base A.reindex = n0 A := by
  simp only [routingA, routingN1, tailValue, n0, normalizedWeight, weights]
  rw [routingD_eq_tailGcd]

theorem routingB_eq_n1 (A : SectorBCriticalRoleBranchA P) :
    routingB P.M.base A.reindex = n1 A := by
  simp only [routingB, routingN2, tailValue, n1, normalizedWeight, weights]
  rw [routingD_eq_tailGcd]

theorem routingC_eq_n2 (A : SectorBCriticalRoleBranchA P) :
    routingC P.M.base A.reindex = n2 A := by
  simp only [routingC, routingN3, tailValue, n2, normalizedWeight, weights]
  rw [routingD_eq_tailGcd]

theorem branchA_routingH_rectangle_factorization
    (A : SectorBCriticalRoleBranchA P) {n : ℕ}
    (hn : n ∈ routingH P.M.base A.reindex) :
    ∃ k i j : ℕ,
      i < alpha A ∧ j < d A ∧
      n = k * routingA P.M.base A.reindex +
        i * routingB P.M.base A.reindex +
        j * routingC P.M.base A.reindex := by
  let S := branchA_symmetricTailData A
  have hd : 0 < d A := by
    have := S.n0_pos
    rw [S.n0_eq] at this
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at this)
  have ha : 0 < alpha A := by
    have := S.n0_pos
    rw [S.n0_eq] at this
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at this)
  change n ∈ generatedThree (routingA P.M.base A.reindex)
    (routingB P.M.base A.reindex) (routingC P.M.base A.reindex) at hn
  obtain ⟨x, y, z, hn⟩ := (mem_generatedThree_iff _ _ _ _).mp hn
  let q := z / d A
  let j := z % d A
  let Y := y + q * s A
  let t := Y / alpha A
  let i := Y % alpha A
  refine ⟨x + q * r A + t * beta A, i, j, Nat.mod_lt _ ha,
    Nat.mod_lt _ hd, ?_⟩
  have hz : j + d A * q = z := by
    simpa [j, q] using Nat.mod_add_div z (d A)
  have hY : i + alpha A * t = Y := by
    simpa [i, t] using Nat.mod_add_div Y (alpha A)
  change i + alpha A * t = y + q * s A at hY
  rw [routingA_eq_n0 A, routingB_eq_n1 A, routingC_eq_n2 A] at hn ⊢
  rw [S.n0_eq, S.n1_eq, S.n2_eq] at hn ⊢
  calc
    n = x * (d A * alpha A) + y * (d A * beta A) +
        z * (r A * alpha A + s A * beta A) := hn
    _ = (x + q * r A) * (d A * alpha A) +
        (y + q * s A) * (d A * beta A) +
        j * (r A * alpha A + s A * beta A) := by rw [← hz]; ring
    _ = (x + q * r A + t * beta A) * (d A * alpha A) +
        i * (d A * beta A) + j * (r A * alpha A + s A * beta A) := by
      rw [← hY]
      ring

theorem branchA_rectangle_modEq_unique
    (A : SectorBCriticalRoleBranchA P) {i j i' j' : ℕ}
    (hi : i < alpha A) (hj : j < d A)
    (hi' : i' < alpha A) (hj' : j' < d A)
    (hmod :
      i * routingB P.M.base A.reindex + j * routingC P.M.base A.reindex
        ≡ i' * routingB P.M.base A.reindex +
          j' * routingC P.M.base A.reindex
        [MOD routingA P.M.base A.reindex]) :
    i = i' ∧ j = j' := by
  let S := branchA_symmetricTailData A
  have hd : 0 < d A := by
    have h := S.n0_pos
    rw [S.n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  rw [routingA_eq_n0 A, routingB_eq_n1 A, routingC_eq_n2 A,
    S.n0_eq, S.n1_eq] at hmod
  have hmodd :
      i * (d A * beta A) + j * n2 A ≡
        i' * (d A * beta A) + j' * n2 A [MOD d A] :=
    hmod.of_mul_right (alpha A)
  have hib : i * (d A * beta A) ≡ i' * (d A * beta A) [MOD d A] := by
    have hz : i * (d A * beta A) ≡ 0 [MOD d A] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact ⟨i * beta A, by ring⟩
    have hz' : i' * (d A * beta A) ≡ 0 [MOD d A] := by
      rw [Nat.modEq_zero_iff_dvd]
      exact ⟨i' * beta A, by ring⟩
    exact hz.trans hz'.symm
  have hjc : j * n2 A ≡ j' * n2 A [MOD d A] :=
    hib.add_left_cancel hmodd
  have hjmod : j ≡ j' [MOD d A] :=
    hjc.cancel_right_of_coprime S.d_n2_coprime
  have hjEq : j = j' := hjmod.eq_of_lt_of_lt hj hj'
  subst j'
  have himul : i * (d A * beta A) ≡ i' * (d A * beta A)
      [MOD d A * alpha A] :=
    (Nat.ModEq.refl (j * n2 A)).add_right_cancel hmod
  have hid : d A * (i * beta A) ≡ d A * (i' * beta A)
      [MOD d A * alpha A] := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using himul
  have hibeta : i * beta A ≡ i' * beta A [MOD alpha A] :=
    hid.mul_left_cancel' (Nat.ne_of_gt hd)
  have himod : i ≡ i' [MOD alpha A] :=
    hibeta.cancel_right_of_coprime S.alpha_beta_coprime
  exact ⟨himod.eq_of_lt_of_lt hi hi', rfl⟩

theorem branchA_rectangle_canonicality
    (A : SectorBCriticalRoleBranchA P) {i j : ℕ}
    (hi : i < alpha A) (hj : j < d A) :
    IsCanonicalTailGridPoint P.M.base A.reindex i j := by
  let B := P.M.base
  let e := A.reindex
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let beta0 : ℤ := normalizedGrid B e 0 i j
  let residue := gridResidue B e i j
  let alpha0 : ℤ := physicalAlpha B e residue
  have halphaMem : alpha0 ∈ (routingH B e).asRelativeIdeal := by
    dsimp [alpha0, physicalAlpha]
    exact (routingH B e).asRelativeIdeal.aperyRepresentative_mem
      (routingA B e) residue
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at halphaMem
  obtain ⟨n, hnH, hnalpha⟩ := halphaMem
  obtain ⟨k, i', j', hi', hj', hnfac⟩ :=
    branchA_routingH_rectangle_factorization A hnH
  have hnResidue : (n : ZMod (routingA B e)) = residue := by
    have h := (routingH B e).asRelativeIdeal.aperyRepresentative_mod
      (routingA B e) residue
    change (alpha0 : ZMod (routingA B e)) = residue at h
    rw [hnalpha] at h
    exact_mod_cast h
  have hterminalResidue :
      ((i' * routingB B e + j' * routingC B e : ℕ) :
        ZMod (routingA B e)) = residue := by
    calc
      ((i' * routingB B e + j' * routingC B e : ℕ) :
          ZMod (routingA B e)) = (n : ZMod (routingA B e)) := by
            rw [hnfac]
            push_cast
            simp
            ring
      _ = residue := hnResidue
  have hinputResidue :
      ((i * routingB B e + j * routingC B e : ℕ) :
        ZMod (routingA B e)) = residue := by
    simpa [residue, normalizedGrid] using normalizedGrid_mod B e 0 i j
  have hmod :
      i' * routingB B e + j' * routingC B e ≡
        i * routingB B e + j * routingC B e [MOD routingA B e] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    exact hterminalResidue.trans hinputResidue.symm
  have hcoords := branchA_rectangle_modEq_unique A hi' hj' hi hj hmod
  have hiEq : i' = i := hcoords.1
  have hjEq : j' = j := hcoords.2
  subst i'
  subst j'
  have hbetaMem : beta0 ∈ (routingH B e).asRelativeIdeal := by
    simpa [beta0] using normalizedGrid_zero_mem_routingH B e i j
  have hbetaMod : (beta0 : ZMod (routingA B e)) = residue := by
    simpa [beta0, residue] using normalizedGrid_mod B e 0 i j
  have halphaLe : alpha0 ≤ beta0 := by
    apply (routingH B e).asRelativeIdeal.aperyRepresentative_le
      (routingA B e) residue hbetaMem hbetaMod
  have hbetaLe : beta0 ≤ alpha0 := by
    have heq : alpha0 = beta0 + (k * routingA B e : ℕ) := by
      calc
        alpha0 = (n : ℤ) := hnalpha
        _ = (k * routingA B e + i * routingB B e +
            j * routingC B e : ℕ) := by rw [hnfac]
        _ = beta0 + (k * routingA B e : ℕ) := by
          simp [beta0, normalizedGrid]
          ring
    rw [heq]
    exact le_add_of_nonneg_right (by positivity)
  exact le_antisymm hbetaLe halphaLe

theorem branchA_residue_rectangle_localization
    (A : SectorBCriticalRoleBranchA P)
    (z : ZMod (routingA P.M.base A.reindex)) :
    ∃ i j : ℕ, i < alpha A ∧ j < d A ∧
      z = gridResidue P.M.base A.reindex i j := by
  let B := P.M.base
  let e := A.reindex
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmem : physicalAlpha B e z ∈ (routingH B e).asRelativeIdeal :=
    (routingH B e).asRelativeIdeal.aperyRepresentative_mem (routingA B e) z
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hmem
  obtain ⟨n, hnH, hnalpha⟩ := hmem
  obtain ⟨k, i, j, hi, hj, hnfac⟩ :=
    branchA_routingH_rectangle_factorization A hnH
  refine ⟨i, j, hi, hj, ?_⟩
  have hmod := (routingH B e).asRelativeIdeal.aperyRepresentative_mod
    (routingA B e) z
  change (physicalAlpha B e z : ZMod (routingA B e)) = z at hmod
  have hnmod : (n : ZMod (routingA B e)) = z := by
    simpa only [Int.cast_natCast] using
      (congrArg (fun t : ℤ => (t : ZMod (routingA B e))) hnalpha).symm.trans hmod
  calc
    z = (n : ZMod (routingA B e)) := hnmod.symm
    _ = gridResidue B e i j := by
      rw [hnfac]
      push_cast
      simp [gridResidue]
      ring

theorem branchA_actualExceptional_cEndpoint_rectangle
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P)
    (x : BranchAActualExceptionalBranches P A) :
    letI : NeZero (routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
    let D := routingData P.M.base A.reindex
    ∃ i j : ℕ, i < alpha A ∧ j < d A ∧
      L5A2C4I.ResidueData.canonicalCEndpoint D
          ⟨x.val.val.val, x.val.val.property⟩ =
        gridResidue P.M.base A.reindex i j := by
  letI : NeZero (routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
  exact branchA_residue_rectangle_localization A _

/-! ### R9: actual B-endpoint transport into the rectangle -/

theorem branchA_actualExceptionalSink_val_eq_bEndpoint
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P)
    (x : BranchAActualExceptionalBranches P A) :
    letI : NeZero (routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
    (branchAActualExceptionalSink P A x).val =
      L5A2C4I.ResidueData.canonicalBEndpoint
        (routingData P.M.base A.reindex) x.val.val := by
  letI : NeZero (routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
  have h := branchAActualExceptionalSink_spec P A x
  let E := L5A2C4N.fullSinkEquivActualSumFake_sourceExact
    (routingI P.M.base A.reindex) (routingA P.M.base A.reindex)
    (routingB P.M.base A.reindex) (routingC P.M.base A.reindex)
    (routingHB P.M.base A.reindex) (routingHC P.M.base A.reindex)
  change E (exceptionalEndpointFullSink P.M.base A.reindex x.val) =
    Sum.inl (branchAActualExceptionalSink P A x) at h
  have hinv := congrArg E.symm h
  rw [E.symm_apply_apply] at hinv
  have hv := congrArg Subtype.val hinv
  have hs : (E.symm (Sum.inl (branchAActualExceptionalSink P A x))).val =
      (branchAActualExceptionalSink P A x).val := by
    rfl
  rw [hs] at hv
  simpa [exceptionalEndpointFullSink] using hv.symm

theorem branchA_actualSink_physicalHeight_pos
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P)
    [NeZero (routingA P.M.base A.reindex)]
    (y : L5A2C4H.ActualSink
      (routingI P.M.base A.reindex)
      (routingA P.M.base A.reindex)
      (routingB P.M.base A.reindex)
      (routingC P.M.base A.reindex)
      (routingHB P.M.base A.reindex)
      (routingHC P.M.base A.reindex)) :
    0 < physicalHeight P.M.base A.reindex y.val := by
  let B := P.M.base
  let e := A.reindex
  letI : NeZero (routingA B e) :=
    ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hmem := y.property.2
  have hmod : (((routingI B e).aperyRepresentative (routingA B e) y.val -
      routingA B e : ℤ) : ZMod (routingA B e)) = y.val := by
    rw [Int.cast_sub, (routingI B e).aperyRepresentative_mod]
    change y.val - (((routingA B e : ℕ) : ℤ) : ZMod (routingA B e)) = y.val
    rw [Int.cast_natCast, ZMod.natCast_self, sub_zero]
  have hle := (routingH B e).asRelativeIdeal.aperyRepresentative_le
    (routingA B e) y.val hmem hmod
  by_contra hn
  have hz : physicalHeight B e y.val = 0 := Nat.eq_zero_of_not_pos hn
  have hspec := physicalHeight_spec B e y.val
  rw [hz] at hspec
  simp only [Nat.cast_zero, mul_zero, add_zero] at hspec
  have haZ : (0 : ℤ) < routingA B e := by
    exact_mod_cast routingA_pos B e
  change physicalAlpha B e y.val ≤
    (routingI B e).aperyRepresentative (routingA B e) y.val -
      routingA B e at hle
  change (routingI B e).aperyRepresentative (routingA B e) y.val =
    physicalAlpha B e y.val at hspec
  omega

theorem branchA_actualExceptional_bEndpoint_rectangle_eta_pos
    (P : P2Data Gamma) (A : SectorBCriticalRoleBranchA P)
    (x : BranchAActualExceptionalBranches P A) :
    letI : NeZero (routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
    let D := routingData P.M.base A.reindex
    ∃ i j : ℕ, i < alpha A ∧ j < d A ∧
      L5A2C4I.ResidueData.canonicalBEndpoint D x.val.val =
        gridResidue P.M.base A.reindex i j ∧
      0 < eta P.M.base A.reindex i j := by
  letI : NeZero (routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
  obtain ⟨i, j, hi, hj, heq⟩ := branchA_residue_rectangle_localization A
    (L5A2C4I.ResidueData.canonicalBEndpoint
      (routingData P.M.base A.reindex) x.val.val)
  refine ⟨i, j, hi, hj, heq, ?_⟩
  have hyval := branchA_actualExceptionalSink_val_eq_bEndpoint P A x
  have hypos := branchA_actualSink_physicalHeight_pos P A
    (branchAActualExceptionalSink P A x)
  have heta := eta_eq_physicalHeight_of_isCanonical P.M.base A.reindex i j
    (branchA_rectangle_canonicality A hi hj)
  rw [heta]
  rw [← heq, ← hyval]
  exact hypos

theorem branchA_rectangle_gridLift_zero
    (A : SectorBCriticalRoleBranchA P) {i j : ℕ}
    (hi : i < alpha A) (hj : j < d A) :
    gridLift P.M.base A.reindex i j = 0 :=
  gridLift_eq_zero_of_isCanonical P.M.base A.reindex i j
    (branchA_rectangle_canonicality A hi hj)

theorem branchA_gridResidue_b_wrap
    (A : SectorBCriticalRoleBranchA P) (j : ℕ) :
    letI : NeZero (routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
    gridResidue P.M.base A.reindex (alpha A) j =
      gridResidue P.M.base A.reindex 0 j := by
  letI : NeZero (routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
  let S := branchA_symmetricTailData A
  have hrel : alpha A * routingB P.M.base A.reindex =
      beta A * routingA P.M.base A.reindex := by
    rw [routingA_eq_n0 A, routingB_eq_n1 A]
    exact S.pure_relation.symm
  have hz : ((alpha A * routingB P.M.base A.reindex : ℕ) :
      ZMod (routingA P.M.base A.reindex)) = 0 := by
    rw [hrel]
    simp
  simp only [gridResidue, Nat.cast_zero, zero_mul, zero_add]
  push_cast at hz
  rw [hz, zero_add]

theorem branchA_gridResidue_c_wrap
    (A : SectorBCriticalRoleBranchA P) (i : ℕ) :
    letI : NeZero (routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
    gridResidue P.M.base A.reindex i (d A) =
      gridResidue P.M.base A.reindex (i + s A) 0 := by
  letI : NeZero (routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
  let S := branchA_symmetricTailData A
  have hrel : d A * routingC P.M.base A.reindex =
      r A * routingA P.M.base A.reindex +
        s A * routingB P.M.base A.reindex := by
    rw [routingA_eq_n0 A, routingB_eq_n1 A, routingC_eq_n2 A]
    exact S.mixed_relation
  have heq : ((d A * routingC P.M.base A.reindex : ℕ) :
      ZMod (routingA P.M.base A.reindex)) =
      ((s A * routingB P.M.base A.reindex : ℕ) :
        ZMod (routingA P.M.base A.reindex)) := by
    rw [hrel]
    push_cast
    simp
  simp only [gridResidue, Nat.cast_zero, mul_zero, add_zero, Nat.cast_add, add_mul]
  push_cast at heq
  rw [heq]
  simp

/-! ### R9: boundary-aware physical-height transport -/

theorem branchA_tailGridLift_b_boundary
    (A : SectorBCriticalRoleBranchA P) {j : ℕ} (hj : j < d A) :
    tailGridLift P.M.base A.reindex (alpha A) j = beta A := by
  let B := P.M.base
  let e := A.reindex
  let S := branchA_symmetricTailData A
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have haAlpha : 0 < alpha A := by
    have h := S.n0_pos
    rw [S.n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have hrel : alpha A * routingB B e = beta A * routingA B e := by
    rw [routingA_eq_n0 A, routingB_eq_n1 A]
    exact S.pure_relation.symm
  have hl0 : tailGridLift B e 0 j = 0 :=
    (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e 0 j).mp
      (branchA_rectangle_canonicality A haAlpha hj)
  have hspec0 := tailGridLift_spec B e 0 j
  have hspecA := tailGridLift_spec B e (alpha A) j
  have hres := branchA_gridResidue_b_wrap A j
  rw [hres] at hspecA
  simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul]
    at hspec0 hspecA
  rw [hl0] at hspec0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hspec0
  have hrelZ : (alpha A : ℤ) * routingB B e =
      (beta A : ℤ) * routingA B e := by exact_mod_cast hrel
  have haZ : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hcast : (tailGridLift B e (alpha A) j : ℤ) = beta A := by
    nlinarith
  exact_mod_cast hcast

theorem branchA_eta_b_boundary
    (A : SectorBCriticalRoleBranchA P) {j : ℕ} (hj : j < d A) :
    eta P.M.base A.reindex (alpha A) j =
      eta P.M.base A.reindex 0 j - beta A := by
  let B := P.M.base
  let e := A.reindex
  let S := branchA_symmetricTailData A
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have haAlpha : 0 < alpha A := by
    have h := S.n0_pos
    rw [S.n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have hl0 : tailGridLift B e 0 j = 0 :=
    (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e 0 j).mp
      (branchA_rectangle_canonicality A haAlpha hj)
  rw [eta_eq_physicalHeight_sub_tailGridLift,
    eta_eq_physicalHeight_sub_tailGridLift,
    branchA_tailGridLift_b_boundary A hj, hl0,
    branchA_gridResidue_b_wrap A j]
  simp

theorem branchA_normalizedGrid_c_boundary
    (A : SectorBCriticalRoleBranchA P) (i : ℕ) :
    normalizedGrid P.M.base A.reindex 0 i (d A) =
      normalizedGrid P.M.base A.reindex 0
          ((i + s A) % alpha A) 0 +
        routingA P.M.base A.reindex *
          (r A + ((i + s A) / alpha A) * beta A) := by
  let B := P.M.base
  let e := A.reindex
  let S := branchA_symmetricTailData A
  have haAlpha : 0 < alpha A := by
    have h := S.n0_pos
    rw [S.n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have hpure : alpha A * routingB B e = beta A * routingA B e := by
    rw [routingA_eq_n0 A, routingB_eq_n1 A]
    exact S.pure_relation.symm
  have hmixed : d A * routingC B e =
      r A * routingA B e + s A * routingB B e := by
    rw [routingA_eq_n0 A, routingB_eq_n1 A, routingC_eq_n2 A]
    exact S.mixed_relation
  have hsplit := Nat.mod_add_div (i + s A) (alpha A)
  simp only [normalizedGrid, zero_mul, zero_add, mul_zero, add_zero]
  rw [hmixed]
  calc
    i * routingB B e +
          (r A * routingA B e + s A * routingB B e) =
        (i + s A) * routingB B e + r A * routingA B e := by ring
    _ = (((i + s A) % alpha A) +
          alpha A * ((i + s A) / alpha A)) * routingB B e +
        r A * routingA B e := by rw [hsplit]
    _ = ((i + s A) % alpha A) * routingB B e +
        ((i + s A) / alpha A) * (alpha A * routingB B e) +
          r A * routingA B e := by ring
    _ = ((i + s A) % alpha A) * routingB B e +
        routingA B e * (r A + ((i + s A) / alpha A) * beta A) := by
          rw [hpure]
          ring

theorem branchA_gridResidue_c_boundary
    (A : SectorBCriticalRoleBranchA P) (i : ℕ) :
    letI : NeZero (routingA P.M.base A.reindex) :=
      ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
    gridResidue P.M.base A.reindex i (d A) =
      gridResidue P.M.base A.reindex ((i + s A) % alpha A) 0 := by
  letI : NeZero (routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
  have hcast := congrArg
    (fun n : ℕ => (n : ZMod (routingA P.M.base A.reindex)))
      (branchA_normalizedGrid_c_boundary A i)
  rw [normalizedGrid_mod P.M.base A.reindex 0 i (d A),
    Nat.cast_add, Nat.cast_mul,
    normalizedGrid_mod P.M.base A.reindex 0 ((i + s A) % alpha A) 0]
    at hcast
  simpa using hcast

theorem branchA_tailGridLift_c_boundary
    (A : SectorBCriticalRoleBranchA P) {i : ℕ} (_hi : i < alpha A) :
    tailGridLift P.M.base A.reindex i (d A) =
      r A + ((i + s A) / alpha A) * beta A := by
  let B := P.M.base
  let e := A.reindex
  let S := branchA_symmetricTailData A
  let k := r A + ((i + s A) / alpha A) * beta A
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have haAlpha : 0 < alpha A := by
    have h := S.n0_pos
    rw [S.n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have hd : 0 < d A := by
    have h := S.n0_pos
    rw [S.n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have ht : (i + s A) % alpha A < alpha A := Nat.mod_lt _ haAlpha
  have hl0 : tailGridLift B e ((i + s A) % alpha A) 0 = 0 :=
    (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e _ _).mp
      (branchA_rectangle_canonicality A ht hd)
  have hspec0 := tailGridLift_spec B e ((i + s A) % alpha A) 0
  have hspecI := tailGridLift_spec B e i (d A)
  have hres := branchA_gridResidue_c_boundary A i
  change gridResidue B e i (d A) =
    gridResidue B e ((i + s A) % alpha A) 0 at hres
  rw [hres] at hspecI
  simp only [normalizedGrid, zero_mul, zero_add, Nat.cast_add, Nat.cast_mul]
    at hspec0 hspecI
  rw [hl0] at hspec0
  simp only [Nat.cast_zero, mul_zero, add_zero] at hspec0
  rw [← hspec0] at hspecI
  have hnorm := branchA_normalizedGrid_c_boundary A i
  change normalizedGrid B e 0 i (d A) =
    normalizedGrid B e 0 ((i + s A) % alpha A) 0 + routingA B e * k at hnorm
  have hnormZ := congrArg (fun n : ℕ => (n : ℤ)) hnorm
  simp only [normalizedGrid, zero_mul, zero_add, mul_zero, add_zero,
    Nat.cast_add, Nat.cast_mul] at hnormZ
  have haZ : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hcast : (tailGridLift B e i (d A) : ℤ) = (k : ℤ) := by
    nlinarith
  have hnat : tailGridLift B e i (d A) = k := by exact_mod_cast hcast
  simpa [k] using hnat

theorem branchA_eta_c_boundary
    (A : SectorBCriticalRoleBranchA P) {i : ℕ} (hi : i < alpha A) :
    eta P.M.base A.reindex i (d A) =
      eta P.M.base A.reindex ((i + s A) % alpha A) 0 -
        (r A + ((i + s A) / alpha A) * beta A) := by
  let B := P.M.base
  let e := A.reindex
  let S := branchA_symmetricTailData A
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have haAlpha : 0 < alpha A := by
    have h := S.n0_pos
    rw [S.n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have hd : 0 < d A := by
    have h := S.n0_pos
    rw [S.n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have ht : (i + s A) % alpha A < alpha A := Nat.mod_lt _ haAlpha
  have hl0 : tailGridLift B e ((i + s A) % alpha A) 0 = 0 :=
    (isCanonicalTailGridPoint_iff_tailGridLift_eq_zero B e _ _).mp
      (branchA_rectangle_canonicality A ht hd)
  rw [eta_eq_physicalHeight_sub_tailGridLift,
    eta_eq_physicalHeight_sub_tailGridLift,
    branchA_tailGridLift_c_boundary A hi, hl0,
    branchA_gridResidue_c_boundary A i]
  simp

theorem branchA_interior_transverse_plateau_gives_carry_zero
    (A : SectorBCriticalRoleBranchA P) {i j : ℕ}
    (hi : i + 1 < alpha A) (hj : j + 1 < d A)
    (hplateau :
      eta P.M.base A.reindex (i + 1) j =
        eta P.M.base A.reindex (i + 1) (j + 1)) :
    let D := routingData P.M.base A.reindex
    D.v (D.b (gridResidue P.M.base A.reindex i j)) = 0 := by
  letI : NeZero (routingA P.M.base A.reindex) :=
    ⟨Nat.ne_of_gt (routingA_pos P.M.base A.reindex)⟩
  have hshift := gridResidue_add_b P.M.base A.reindex i j
  have hcarry := eta_c_carry_transition P.M.base A.reindex (i + 1) j
  have hl1 : gridLift P.M.base A.reindex (i + 1) (j + 1) = 0 :=
    branchA_rectangle_gridLift_zero A hi hj
  have hl0 : gridLift P.M.base A.reindex (i + 1) j = 0 :=
    branchA_rectangle_gridLift_zero A hi (by omega)
  rw [hl1, hl0] at hcarry
  rw [hplateau] at hcarry
  have hz : (routingData P.M.base A.reindex).v
      (gridResidue P.M.base A.reindex (i + 1) j) = 0 := by omega
  have hb : (routingData P.M.base A.reindex).b
      (gridResidue P.M.base A.reindex i j) =
        gridResidue P.M.base A.reindex (i + 1) j := by
    change gridResidue P.M.base A.reindex i j +
      routingB P.M.base A.reindex = _
    exact hshift.symm
  dsimp only
  rw [hb]
  exact hz

end NS25Lean.L5A2B4AR5A
