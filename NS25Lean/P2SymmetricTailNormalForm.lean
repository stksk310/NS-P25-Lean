import NS25Lean.P2CriticalRoleDichotomy
import NS25Lean.AppendixBTwoGenerator

set_option linter.style.header false

noncomputable section
namespace NS25Lean.L5A2B4AR4R2A

open ChosenBase FourGeneratedBridge L2B L4A L5A1 L5A2B4AR3 L5A2B4AR4R1

variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

abbrev n0 (A : SectorBCriticalRoleBranchA P) : ℕ :=
  normalizedWeight P.M.base (A.reindex 0)

abbrev n1 (A : SectorBCriticalRoleBranchA P) : ℕ :=
  normalizedWeight P.M.base (A.reindex 1)

abbrev n2 (A : SectorBCriticalRoleBranchA P) : ℕ :=
  normalizedWeight P.M.base (A.reindex 2)

abbrev c0 (A : SectorBCriticalRoleBranchA P) : ℕ :=
  criticalExponent P.M.base (A.reindex 0)

abbrev c1 (A : SectorBCriticalRoleBranchA P) : ℕ :=
  criticalExponent P.M.base (A.reindex 1)

abbrev c2 (A : SectorBCriticalRoleBranchA P) : ℕ :=
  criticalExponent P.M.base (A.reindex 2)

abbrev r (A : SectorBCriticalRoleBranchA P) : ℕ :=
  A.mixed.witness.val (A.reindex 0)

abbrev s (A : SectorBCriticalRoleBranchA P) : ℕ :=
  A.mixed.witness.val (A.reindex 1)

abbrev d (A : SectorBCriticalRoleBranchA P) : ℕ := Nat.gcd (n0 A) (n1 A)
abbrev alpha (A : SectorBCriticalRoleBranchA P) : ℕ := n0 A / d A
abbrev beta (A : SectorBCriticalRoleBranchA P) : ℕ := n1 A / d A

/-- The source-exact normalized-tail normal form attached to an actual
Branch-A critical-role package.  It makes no assertion about the ambient
four-generated semigroup. -/
structure BranchASymmetricTailData (A : SectorBCriticalRoleBranchA P) : Prop where
  n0_pos : 0 < n0 A
  n1_pos : 0 < n1 A
  n2_pos : 0 < n2 A
  r_pos : 0 < r A
  s_pos : 0 < s A
  alpha_beta_coprime : Nat.Coprime (alpha A) (beta A)
  c0_eq_beta : c0 A = beta A
  c1_eq_alpha : c1 A = alpha A
  d_n2_coprime : Nat.Coprime (d A) (n2 A)
  c2_eq_d : c2 A = d A
  n0_eq : n0 A = d A * alpha A
  n1_eq : n1 A = d A * beta A
  n2_eq : n2 A = r A * alpha A + s A * beta A
  pure_relation : beta A * n0 A = alpha A * n1 A
  mixed_relation : d A * n2 A = r A * n0 A + s A * n1 A

private theorem normalizedWeight_pos (B : Data Gamma) (i : Fin 3) :
    0 < normalizedWeight B i := by
  have hs := normalizedWeight_scale B i
  have hw := weights_positive B i
  nlinarith

private theorem normalized_gcd_reindexed_eq_one (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Nat.gcd (normalizedWeight B (e 0))
      (Nat.gcd (normalizedWeight B (e 1)) (normalizedWeight B (e 2))) = 1 := by
  let g := Nat.gcd (normalizedWeight B (e 0))
    (Nat.gcd (normalizedWeight B (e 1)) (normalizedWeight B (e 2)))
  have hall (i : Fin 3) : g ∣ normalizedWeight B i := by
    obtain ⟨j, rfl⟩ := e.surjective i
    fin_cases j
    · exact Nat.gcd_dvd_left _ _
    · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
    · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hfixed : g ∣ Nat.gcd (normalizedWeight B 0)
      (Nat.gcd (normalizedWeight B 1) (normalizedWeight B 2)) :=
    Nat.dvd_gcd (hall 0) (Nat.dvd_gcd (hall 1) (hall 2))
  have hone := normalized_gcd_eq_one
    (n₁ := (B.tailDegrees 0).val) (n₂ := (B.tailDegrees 1).val)
    (n₃ := (B.tailDegrees 2).val) (B.degrees_positive 1)
  change g = 1
  apply Nat.eq_one_of_dvd_one
  rw [← hone]
  simpa [normalizedWeight, weights] using hfixed

private theorem support_pair_eq_first_two (B : Data Gamma) (h : ℕ)
    (C : FiberComponent B h) (e : Fin 3 ≃ Fin 3)
    (hcard : (componentSupport B h C).card = 2)
    (htwo : e 2 ∉ componentSupport B h C) :
    componentSupport B h C = {e 0, e 1} := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    obtain ⟨i, rfl⟩ := e.surjective j
    fin_cases i
    · simp
    · simp
    · exact (htwo hj).elim
  · simp [hcard, e.injective.eq_iff]

private theorem branchA_mixed_support (A : SectorBCriticalRoleBranchA P) :
    componentSupport P.M.base A.mixedDegree A.mixed.mixedComponent =
      {A.reindex 0, A.reindex 1} := by
  apply support_pair_eq_first_two P.M.base A.mixedDegree A.mixed.mixedComponent A.reindex
  · rw [A.mixed.mixedSupport]
    simp [A.mixed.other_ne]
  · rw [A.reindex_two, A.mixed.mixedSupport]
    simp [A.mixed.pure_ne_left, A.mixed.pure_ne_right]

private theorem branchA_r_pos (A : SectorBCriticalRoleBranchA P) : 0 < r A := by
  apply A.mixed.witness_pos_of_mem_mixedSupport
  rw [branchA_mixed_support A]
  simp

private theorem branchA_s_pos (A : SectorBCriticalRoleBranchA P) : 0 < s A := by
  apply A.mixed.witness_pos_of_mem_mixedSupport
  rw [branchA_mixed_support A]
  simp

private theorem branchA_n0_scale (A : SectorBCriticalRoleBranchA P) :
    n0 A = d A * alpha A := by
  exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left (n0 A) (n1 A))).symm

private theorem branchA_n1_scale (A : SectorBCriticalRoleBranchA P) :
    n1 A = d A * beta A := by
  exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right (n0 A) (n1 A))).symm

private theorem branchA_alpha_beta_coprime (A : SectorBCriticalRoleBranchA P) :
    Nat.Coprime (alpha A) (beta A) := by
  exact Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left (n1 A) (normalizedWeight_pos P.M.base (A.reindex 0)))

private theorem branchA_d_n2_coprime (A : SectorBCriticalRoleBranchA P) :
    Nat.Coprime (d A) (n2 A) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  simpa [Nat.gcd_assoc] using normalized_gcd_reindexed_eq_one P.M.base A.reindex

private theorem branchA_pair_relation (A : SectorBCriticalRoleBranchA P) :
    c0 A * n0 A = c1 A * n1 A := by
  let D := tailGcd (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val
    (P.M.base.tailDegrees 2).val
  have hD : 0 < D := tailGcd_pos (P.M.base.degrees_positive 1)
  have hraw : c0 A * weights P.M.base (A.reindex 0) =
      c1 A * weights P.M.base (A.reindex 1) := by
    change criticalExponent P.M.base (A.reindex 0) * weights P.M.base (A.reindex 0) =
      criticalExponent P.M.base (A.reindex 1) * weights P.M.base (A.reindex 1)
    simpa only [A.reindex_zero, A.reindex_one] using
      A.pair.left_degree_eq_critical.symm.trans A.pair.right_degree_eq_critical
  apply Nat.eq_of_mul_eq_mul_left hD
  calc
    D * (c0 A * n0 A) = c0 A * weights P.M.base (A.reindex 0) := by
      rw [← normalizedWeight_scale P.M.base (A.reindex 0)]
      ring
    _ = c1 A * weights P.M.base (A.reindex 1) := hraw
    _ = D * (c1 A * n1 A) := by
      rw [← normalizedWeight_scale P.M.base (A.reindex 1)]
      ring

private theorem branchA_mixed_relation (A : SectorBCriticalRoleBranchA P) :
    c2 A * n2 A = r A * n0 A + s A * n1 A := by
  let D := tailGcd (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val
    (P.M.base.tailDegrees 2).val
  have hD : 0 < D := tailGcd_pos (P.M.base.degrees_positive 1)
  have hraw : c2 A * weights P.M.base (A.reindex 2) =
      r A * weights P.M.base (A.reindex 0) +
        s A * weights P.M.base (A.reindex 1) := by
    have hdegree : c2 A * weights P.M.base (A.reindex 2) =
        weight P.M.base A.mixed.witness.val := by
      change criticalExponent P.M.base (A.reindex 2) * weights P.M.base (A.reindex 2) =
        weight P.M.base A.mixed.witness.val
      simpa only [A.reindex_two] using
        A.mixed.degree_eq_critical.symm.trans A.mixed.witness.property.symm
    rw [weight_three_coordinates P.M.base A.reindex] at hdegree
    have hz : A.mixed.witness.val (A.reindex 2) = 0 := by
      rw [A.reindex_two]
      exact A.mixed.witness_pure_zero
    rw [hz, zero_mul, add_zero] at hdegree
    exact hdegree
  apply Nat.eq_of_mul_eq_mul_left hD
  calc
    D * (c2 A * n2 A) = c2 A * weights P.M.base (A.reindex 2) := by
      rw [← normalizedWeight_scale P.M.base (A.reindex 2)]
      ring
    _ = r A * weights P.M.base (A.reindex 0) +
        s A * weights P.M.base (A.reindex 1) := hraw
    _ = D * (r A * n0 A + s A * n1 A) := by
      rw [← normalizedWeight_scale P.M.base (A.reindex 0),
        ← normalizedWeight_scale P.M.base (A.reindex 1)]
      ring

private theorem branchA_pure_exponents (A : SectorBCriticalRoleBranchA P) :
    c0 A = beta A ∧ c1 A = alpha A := by
  have hn0 := branchA_n0_scale A
  have hn1 := branchA_n1_scale A
  have hd : 0 < d A := Nat.gcd_pos_of_pos_left (n1 A)
    (normalizedWeight_pos P.M.base (A.reindex 0))
  have ha : 0 < alpha A := by nlinarith [normalizedWeight_pos P.M.base (A.reindex 0)]
  have hb : 0 < beta A := by nlinarith [normalizedWeight_pos P.M.base (A.reindex 1)]
  have hab := branchA_alpha_beta_coprime A
  have hp := branchA_pair_relation A
  have hp' : c0 A * alpha A = c1 A * beta A := by
    apply Nat.eq_of_mul_eq_mul_left hd
    calc
      d A * (c0 A * alpha A) = c0 A * n0 A := by rw [hn0]; ring
      _ = c1 A * n1 A := hp
      _ = d A * (c1 A * beta A) := by rw [hn1]; ring
  have hbeta_dvd : beta A ∣ c0 A := by
    apply hab.symm.dvd_of_dvd_mul_right
    rw [hp']
    exact dvd_mul_left (beta A) (c1 A)
  have halpha_dvd : alpha A ∣ c1 A := by
    apply hab.dvd_of_dvd_mul_right
    rw [← hp']
    exact dvd_mul_left (alpha A) (c0 A)
  have hpure : beta A * n0 A = alpha A * n1 A := by rw [hn0, hn1]; ring
  have hout0 : OutsideExponent P.M.base (A.reindex 0) (beta A) := by
    refine ⟨hb, Finsupp.single (A.reindex 1) (alpha A), ?_, ?_⟩
    · simp [A.reindex.injective.ne (by decide : (0 : Fin 3) ≠ 1)]
    · rw [weight_single]
      let D := tailGcd (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val
        (P.M.base.tailDegrees 2).val
      calc
        alpha A * weights P.M.base (A.reindex 1) = D * (alpha A * n1 A) := by
          rw [← normalizedWeight_scale P.M.base (A.reindex 1)]
          ring
        _ = D * (beta A * n0 A) := by rw [hpure]
        _ = beta A * weights P.M.base (A.reindex 0) := by
          rw [← normalizedWeight_scale P.M.base (A.reindex 0)]
          ring
  have hout1 : OutsideExponent P.M.base (A.reindex 1) (alpha A) := by
    refine ⟨ha, Finsupp.single (A.reindex 0) (beta A), ?_, ?_⟩
    · simp [A.reindex.injective.ne (by decide : (1 : Fin 3) ≠ 0)]
    · rw [weight_single]
      let D := tailGcd (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val
        (P.M.base.tailDegrees 2).val
      calc
        beta A * weights P.M.base (A.reindex 0) = D * (beta A * n0 A) := by
          rw [← normalizedWeight_scale P.M.base (A.reindex 0)]
          ring
        _ = D * (alpha A * n1 A) := by rw [hpure]
        _ = alpha A * weights P.M.base (A.reindex 1) := by
          rw [← normalizedWeight_scale P.M.base (A.reindex 1)]
          ring
  have hc0le : c0 A ≤ beta A :=
    criticalExponent_min P.M.base (A.reindex 0) (beta A) hout0
  have hc1le : c1 A ≤ alpha A :=
    criticalExponent_min P.M.base (A.reindex 1) (alpha A) hout1
  have hc0pos : 0 < c0 A := (criticalExponent_spec P.M.base (A.reindex 0)).1
  have hc1pos : 0 < c1 A := (criticalExponent_spec P.M.base (A.reindex 1)).1
  have hbetale := Nat.le_of_dvd hc0pos hbeta_dvd
  have halphale := Nat.le_of_dvd hc1pos halpha_dvd
  omega

/-- The component separation at the actual pure/pure critical degree forces
the third normalized weight into the coprime two-generator monoid. -/
private theorem branchA_n2_mem_twoGenerator (A : SectorBCriticalRoleBranchA P) :
    n2 A ∈ twoGenerator (alpha A) (beta A) := by
  classical
  have hn0 := branchA_n0_scale A
  have hn1 := branchA_n1_scale A
  have ha : 0 < alpha A := by nlinarith [normalizedWeight_pos P.M.base (A.reindex 0)]
  have hb : 0 < beta A := by nlinarith [normalizedWeight_pos P.M.base (A.reindex 1)]
  have hd : 0 < d A := Nat.gcd_pos_of_pos_left (n1 A)
    (normalizedWeight_pos P.M.base (A.reindex 0))
  have hab := branchA_alpha_beta_coprime A
  have hc0 := (branchA_pure_exponents A).1
  have he01 : A.reindex 0 ≠ A.reindex 1 := A.reindex.injective.ne (by decide)
  have he02 : A.reindex 0 ≠ A.reindex 2 := A.reindex.injective.ne (by decide)
  have he12 : A.reindex 1 ≠ A.reindex 2 := A.reindex.injective.ne (by decide)
  by_contra hnot
  have hnint : ¬ twoGeneratorInt (alpha A) (beta A) (n2 A : ℤ) := by
    intro hz
    exact hnot ((twoGeneratorInt_nat (alpha A) (beta A) (n2 A)).mp hz)
  obtain ⟨u, v, huv⟩ :=
    (two_generator_symmetry (alpha A) (beta A) ha hb hab (n2 A : ℤ)).mp hnint
  have hsumInt : (alpha A * beta A : ℕ) =
      alpha A * (u + 1) + beta A * (v + 1) + n2 A := by
    exact_mod_cast (show (alpha A * beta A : ℤ) =
      alpha A * ((u : ℤ) + 1) + beta A * ((v : ℤ) + 1) + n2 A by
        nlinarith [huv])
  let zval : Fin 3 →₀ ℕ :=
    Finsupp.single (A.reindex 0) (u + 1) +
      Finsupp.single (A.reindex 1) (v + 1) +
        Finsupp.single (A.reindex 2) (d A)
  have hnorm : (u + 1) * n0 A + (v + 1) * n1 A + d A * n2 A =
      beta A * n0 A := by
    calc
      (u + 1) * n0 A + (v + 1) * n1 A + d A * n2 A =
          d A * (alpha A * (u + 1) + beta A * (v + 1) + n2 A) := by
            rw [hn0, hn1]
            ring
      _ = d A * (alpha A * beta A) := by rw [← hsumInt]
      _ = beta A * n0 A := by rw [hn0]; ring
  let D := tailGcd (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val
    (P.M.base.tailDegrees 2).val
  have hraw : (u + 1) * weights P.M.base (A.reindex 0) +
      (v + 1) * weights P.M.base (A.reindex 1) +
        d A * weights P.M.base (A.reindex 2) =
      beta A * weights P.M.base (A.reindex 0) := by
    calc
      (u + 1) * weights P.M.base (A.reindex 0) +
          (v + 1) * weights P.M.base (A.reindex 1) +
            d A * weights P.M.base (A.reindex 2) =
          D * ((u + 1) * n0 A + (v + 1) * n1 A + d A * n2 A) := by
            rw [← normalizedWeight_scale P.M.base (A.reindex 0),
              ← normalizedWeight_scale P.M.base (A.reindex 1),
              ← normalizedWeight_scale P.M.base (A.reindex 2)]
            ring
      _ = D * (beta A * n0 A) := by rw [hnorm]
      _ = beta A * weights P.M.base (A.reindex 0) := by
        rw [← normalizedWeight_scale P.M.base (A.reindex 0)]
        ring
  have hpair : A.pairDegree = beta A * weights P.M.base (A.reindex 0) := by
    calc
      A.pairDegree = c0 A * weights P.M.base (A.reindex 0) := by
        change A.pairDegree =
          criticalExponent P.M.base (A.reindex 0) * weights P.M.base (A.reindex 0)
        simpa only [A.reindex_zero] using A.pair.left_degree_eq_critical
      _ = beta A * weights P.M.base (A.reindex 0) := by rw [hc0]
  let z : FactorizationFiber P.M.base A.pairDegree := ⟨zval, by
    rw [weight_three_coordinates P.M.base A.reindex]
    simp only [zval, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne he01, Finsupp.single_eq_of_ne he02,
      Finsupp.single_eq_of_ne he01.symm, Finsupp.single_eq_of_ne he12,
      Finsupp.single_eq_of_ne he02.symm, Finsupp.single_eq_of_ne he12.symm,
      zero_add, add_zero]
    exact hraw.trans hpair.symm⟩
  have hz0 : 0 < z.val (A.reindex 0) := by
    simp [z, zval, he01, he02]
  have hz1 : 0 < z.val (A.reindex 1) := by
    simp [z, zval, he12]
  have hleft0 : 0 < A.pair.leftWitness.val (A.reindex 0) := by
    rw [A.reindex_zero]
    by_contra hn
    have hz : A.pair.leftWitness.val A.pair.leftRole = 0 := Nat.eq_zero_of_not_pos hn
    have hval : A.pair.leftWitness.val = 0 := by
      rw [A.pair.leftWitness_pure, hz]
      simp
    have hdegree := A.pair.leftWitness.property
    rw [hval, map_zero] at hdegree
    exact (Nat.ne_of_gt A.pair.degree_pos) hdegree.symm
  have hright1 : 0 < A.pair.rightWitness.val (A.reindex 1) := by
    rw [A.reindex_one]
    by_contra hn
    have hz : A.pair.rightWitness.val A.pair.rightRole = 0 := Nat.eq_zero_of_not_pos hn
    have hval : A.pair.rightWitness.val = 0 := by
      rw [A.pair.rightWitness_pure, hz]
      simp
    have hdegree := A.pair.rightWitness.property
    rw [hval, map_zero] at hdegree
    exact (Nat.ne_of_gt A.pair.degree_pos) hdegree.symm
  have hzleft : (fiberGraph P.M.base A.pairDegree).connectedComponentMk z =
      A.pair.leftComponent := by
    by_cases heq : z = A.pair.leftWitness
    · exact heq ▸ A.pair.leftWitness_component
    · exact (SimpleGraph.ConnectedComponent.sound
        (show (fiberGraph P.M.base A.pairDegree).Adj z A.pair.leftWitness from
          ⟨heq, A.reindex 0, hz0, hleft0⟩).reachable).trans
        A.pair.leftWitness_component
  have hzright : (fiberGraph P.M.base A.pairDegree).connectedComponentMk z =
      A.pair.rightComponent := by
    by_cases heq : z = A.pair.rightWitness
    · exact heq ▸ A.pair.rightWitness_component
    · exact (SimpleGraph.ConnectedComponent.sound
        (show (fiberGraph P.M.base A.pairDegree).Adj z A.pair.rightWitness from
          ⟨heq, A.reindex 1, hz1, hright1⟩).reachable).trans
        A.pair.rightWitness_component
  exact A.pair.components_ne (hzleft.symm.trans hzright)

private theorem branchA_d_outsideExponent (A : SectorBCriticalRoleBranchA P) :
    OutsideExponent P.M.base (A.reindex 2) (d A) := by
  classical
  have hn0 := branchA_n0_scale A
  have hn1 := branchA_n1_scale A
  have hd : 0 < d A := Nat.gcd_pos_of_pos_left (n1 A)
    (normalizedWeight_pos P.M.base (A.reindex 0))
  obtain ⟨u, v, huv⟩ :=
    (mem_twoGenerator (alpha A) (beta A) (n2 A)).mp (branchA_n2_mem_twoGenerator A)
  have hnorm : u * n0 A + v * n1 A = d A * n2 A := by
    calc
      u * n0 A + v * n1 A = d A * (alpha A * u + beta A * v) := by
        rw [hn0, hn1]
        ring
      _ = d A * n2 A := by rw [← huv]
  let w : Fin 3 →₀ ℕ :=
    Finsupp.single (A.reindex 0) u + Finsupp.single (A.reindex 1) v
  refine ⟨hd, w, ?_, ?_⟩
  · simp [w, A.reindex.injective.ne (by decide : (2 : Fin 3) ≠ 0),
      A.reindex.injective.ne (by decide : (2 : Fin 3) ≠ 1)]
  · rw [weight_three_coordinates P.M.base A.reindex]
    simp only [w, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (A.reindex.injective.ne (by decide : (0 : Fin 3) ≠ 1)),
      Finsupp.single_eq_of_ne (A.reindex.injective.ne (by decide : (1 : Fin 3) ≠ 0)),
      Finsupp.single_eq_of_ne (A.reindex.injective.ne (by decide : (2 : Fin 3) ≠ 0)),
      Finsupp.single_eq_of_ne (A.reindex.injective.ne (by decide : (2 : Fin 3) ≠ 1)),
      zero_add, add_zero, zero_mul]
    let D := tailGcd (P.M.base.tailDegrees 0).val (P.M.base.tailDegrees 1).val
      (P.M.base.tailDegrees 2).val
    calc
      u * weights P.M.base (A.reindex 0) + v * weights P.M.base (A.reindex 1) =
          D * (u * n0 A + v * n1 A) := by
            rw [← normalizedWeight_scale P.M.base (A.reindex 0),
              ← normalizedWeight_scale P.M.base (A.reindex 1)]
            ring
      _ = D * (d A * n2 A) := by rw [hnorm]
      _ = d A * weights P.M.base (A.reindex 2) := by
        rw [← normalizedWeight_scale P.M.base (A.reindex 2)]
        ring

/-- Integrality comes first: the actual mixed relation and `Coprime d n2`
give `c2 = d*t`.  If `t > 1`, the actual exponent-`d` outside factorization
above contradicts critical-exponent minimality. -/
private theorem branchA_c2_eq_d (A : SectorBCriticalRoleBranchA P) : c2 A = d A := by
  have hn0 := branchA_n0_scale A
  have hn1 := branchA_n1_scale A
  have hd : 0 < d A := Nat.gcd_pos_of_pos_left (n1 A)
    (normalizedWeight_pos P.M.base (A.reindex 0))
  have hcop := branchA_d_n2_coprime A
  have hmix := branchA_mixed_relation A
  have hdprod : d A ∣ c2 A * n2 A := by
    rw [hmix]
    refine ⟨r A * alpha A + s A * beta A, ?_⟩
    rw [hn0, hn1]
    ring
  have hdc2 : d A ∣ c2 A := hcop.dvd_of_dvd_mul_right hdprod
  obtain ⟨t, hct⟩ := hdc2
  have hc2pos : 0 < c2 A := (criticalExponent_spec P.M.base (A.reindex 2)).1
  have htpos : 0 < t := by
    by_contra ht
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
    rw [hct, ht0, Nat.mul_zero] at hc2pos
    omega
  have hc2le : c2 A ≤ d A :=
    criticalExponent_min P.M.base (A.reindex 2) (d A) (branchA_d_outsideExponent A)
  have htle : t ≤ 1 := by
    by_contra ht
    have htt : 1 < t := by omega
    have hdc : d A < c2 A := by rw [hct]; nlinarith
    omega
  have ht : t = 1 := by omega
  rw [hct, ht, Nat.mul_one]

private theorem branchA_n2_normal_form (A : SectorBCriticalRoleBranchA P) :
    n2 A = r A * alpha A + s A * beta A := by
  have hn0 := branchA_n0_scale A
  have hn1 := branchA_n1_scale A
  have hd : 0 < d A := Nat.gcd_pos_of_pos_left (n1 A)
    (normalizedWeight_pos P.M.base (A.reindex 0))
  apply Nat.eq_of_mul_eq_mul_left hd
  calc
    d A * n2 A = c2 A * n2 A := by rw [branchA_c2_eq_d A]
    _ = r A * n0 A + s A * n1 A := branchA_mixed_relation A
    _ = d A * (r A * alpha A + s A * beta A) := by rw [hn0, hn1]; ring

/-- The complete source-exact Branch-A normalized-tail package. -/
theorem branchA_symmetricTailData (A : SectorBCriticalRoleBranchA P) :
    BranchASymmetricTailData A := by
  have hn0 := branchA_n0_scale A
  have hn1 := branchA_n1_scale A
  have hc := branchA_pure_exponents A
  have hc2 := branchA_c2_eq_d A
  have hn2 := branchA_n2_normal_form A
  refine {
    n0_pos := normalizedWeight_pos P.M.base (A.reindex 0)
    n1_pos := normalizedWeight_pos P.M.base (A.reindex 1)
    n2_pos := normalizedWeight_pos P.M.base (A.reindex 2)
    r_pos := branchA_r_pos A
    s_pos := branchA_s_pos A
    alpha_beta_coprime := branchA_alpha_beta_coprime A
    c0_eq_beta := hc.1
    c1_eq_alpha := hc.2
    d_n2_coprime := branchA_d_n2_coprime A
    c2_eq_d := hc2
    n0_eq := hn0
    n1_eq := hn1
    n2_eq := hn2
    pure_relation := ?_
    mixed_relation := ?_
  }
  · rw [hn0, hn1]
    ring
  · rw [← hc2]
    exact branchA_mixed_relation A

/-- Sector-B-facing specialization, still conditional on the actual Branch-A
side of the frozen dichotomy and still asserting only a tail normal form. -/
theorem sectorB_branchA_symmetricTailData (P : P2Data Gamma)
    (_hB : SectorB P.M) (A : SectorBCriticalRoleBranchA P) :
    BranchASymmetricTailData A :=
  branchA_symmetricTailData A

end NS25Lean.L5A2B4AR4R2A
