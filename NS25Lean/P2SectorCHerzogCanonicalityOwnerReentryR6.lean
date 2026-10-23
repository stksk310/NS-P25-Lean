import NS25Lean.GenericLShapeCompleteness
import NS25Lean.P2SectorCHerzogCanonicalityOwnerReentry

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR6

open ChosenBase FourGeneratedBridge GenericLShape
open L2B L5A2B L5A2C4A L5A2C4C L5A2C4D L5A2C4H
open L5A2C4OR3 L5A2C4OR4 L5A2C4OR5

variable {Gamma : NumericalSemigroup}

private theorem routing_scale_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B e * routingA B e = weights B (e 0) := by
  simpa [normalizedGrid, gridDegree] using normalizedGrid_scale B e 1 0 0

private theorem routing_scale_one (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B e * routingB B e = weights B (e 1) := by
  simpa [normalizedGrid, gridDegree] using normalizedGrid_scale B e 0 1 0

private theorem routing_scale_two (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B e * routingC B e = weights B (e 2) := by
  simpa [normalizedGrid, gridDegree] using normalizedGrid_scale B e 0 0 1

private theorem outside_one_of_normalized_relation (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3) {n x y : ℕ} (hn : 0 < n)
    (h : n * routingB B e = x * routingA B e + y * routingC B e) :
    OutsideExponent B (e 1) n := by
  refine ⟨hn, Finsupp.single (e 0) x + Finsupp.single (e 2) y, ?_, ?_⟩
  · simp
  · have hs0 := routing_scale_zero B e
    have hs1 := routing_scale_one B e
    have hs2 := routing_scale_two B e
    have hr : n * weights B (e 1) =
        x * weights B (e 0) + y * weights B (e 2) := by
      nlinarith only [h, hs0, hs1, hs2]
    simpa [map_add, weight_single] using hr.symm

private theorem outside_two_of_normalized_relation (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3) {n x y : ℕ} (hn : 0 < n)
    (h : n * routingC B e = x * routingA B e + y * routingB B e) :
    OutsideExponent B (e 2) n := by
  refine ⟨hn, Finsupp.single (e 0) x + Finsupp.single (e 1) y, ?_, ?_⟩
  · simp
  · have hs0 := routing_scale_zero B e
    have hs1 := routing_scale_one B e
    have hs2 := routing_scale_two B e
    have hr : n * weights B (e 2) =
        x * weights B (e 0) + y * weights B (e 1) := by
      nlinarith only [h, hs0, hs1, hs2]
    simpa [map_add, weight_single] using hr.symm

theorem coherent_second_minimality (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    ∀ n x y : ℕ, 0 < n →
      n * routingB B e = x * routingA B e + y * routingC B e →
      c2 B e ≤ n := by
  intro n x y hn hrel
  exact criticalExponent_min B (e 1) n
    (outside_one_of_normalized_relation B e hn hrel)

theorem coherent_third_minimality (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    ∀ n x y : ℕ, 0 < n →
      n * routingC B e = x * routingA B e + y * routingB B e →
      c3 B e ≤ n := by
  intro n x y hn hrel
  exact criticalExponent_min B (e 2) n
    (outside_two_of_normalized_relation B e hn hrel)

/-- Phase 1: the generic finite-coordinate theorem instantiated only with
actual coherent Sector-C data. -/
theorem coherent_lShape_residue_bijective
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    Function.Bijective
      (GenericLShape.residue (routingA B e) (routingB B e) (routingC B e)
        (cr12 D) (cr13 D) (cr32 D) (cr23 D)) := by
  have hp := coherent_coefficients_positive B e D
  have hs := coherent_coefficients B e D
  have hr := coherent_normalized_relations B e D
  apply GenericLShape.residue_bijective
    (routingA B e) (routingB B e) (routingC B e)
    (c1 B e) (c2 B e) (c3 B e)
    (cr12 D) (cr13 D) (cr32 D) (cr23 D) (cr21 D) (cr31 D)
  · exact routingA_pos B e
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.2.2.2
  · exact hp.2.2.2.1
  · exact hs.2.1
  · exact hs.2.2
  · exact hr.1
  · exact hr.2.1
  · exact hr.2.2
  · exact coherent_second_minimality B e D
  · exact coherent_third_minimality B e D
  · exact coherent_uniqueZeroInLShape B e D
  · simpa [routingA, routingB, routingC, routingD, routingN1, routingN2,
      routingN3] using normalized_gcd_eq_one (chosenBase_minimalFour B e).n₁_pos

theorem coherent_lShape_unique_coordinate
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (n : ℤ) :
    ∃! ij : ℤ × ℤ,
      InLShape (cr12 D) (cr13 D) (cr32 D) (cr23 D) ij.1 ij.2 ∧
        Int.ModEq (routingA B e)
          (ij.1 * routingB B e + ij.2 * routingC B e) n := by
  have hp := coherent_coefficients_positive B e D
  have hs := coherent_coefficients B e D
  have hr := coherent_normalized_relations B e D
  apply GenericLShape.existsUnique_pair
    (routingA B e) (routingB B e) (routingC B e)
    (c1 B e) (c2 B e) (c3 B e)
    (cr12 D) (cr13 D) (cr32 D) (cr23 D) (cr21 D) (cr31 D)
  · exact routingA_pos B e
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2.2.2.2
  · exact hp.2.2.2.1
  · exact hs.2.1
  · exact hs.2.2
  · exact hr.1
  · exact hr.2.1
  · exact hr.2.2
  · exact coherent_second_minimality B e D
  · exact coherent_third_minimality B e D
  · exact coherent_uniqueZeroInLShape B e D
  · simpa [routingA, routingB, routingC, routingD, routingN1, routingN2,
      routingN3] using normalized_gcd_eq_one (chosenBase_minimalFour B e).n₁_pos

/-- Phase 2, actual specialization of the terminating reduction. -/
theorem coherent_exists_reduction
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) (x y : ℕ) :
    ∃ i j k : ℕ,
      HerzogLShapeDomain D i j ∧
        x * routingB B e + y * routingC B e =
          i * routingB B e + j * routingC B e + k * routingA B e := by
  have hp := coherent_coefficients_positive B e D
  have hs := coherent_coefficients B e D
  have hr := coherent_normalized_relations B e D
  simpa [HerzogLShapeDomain, GenericLShape.NatDomain] using
    (GenericLShape.exists_reduction
      (routingA B e) (routingB B e) (routingC B e)
      (c1 B e) (c2 B e) (c3 B e)
      (cr12 D) (cr13 D) (cr32 D) (cr23 D) (cr21 D) (cr31 D)
      (routingA_pos B e) (criticalExponent_spec B (e 0)).1
      hp.2.2.1 hp.2.2.2.2.1 hs.2.1 hs.2.2 hr.1 hr.2.1 hr.2.2 x y)

theorem inLShape_of_herzogDomain
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) {i j : ℕ}
    (h : HerzogLShapeDomain D i j) :
    InLShape (cr12 D) (cr13 D) (cr32 D) (cr23 D) i j := by
  have hs := coherent_coefficients B e D
  rcases h with ⟨hi, hj, hcorner⟩
  unfold InLShape
  constructor
  · exact_mod_cast Nat.zero_le i
  constructor
  · exact_mod_cast Nat.zero_le j
  constructor
  · have hi' : i < cr12 D + cr32 D := by omega
    exact_mod_cast hi'
  constructor
  · have hj' : j < cr13 D + cr23 D := by omega
    exact_mod_cast hj'
  · rcases hcorner with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)

theorem routingH_factorization
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3) {n : ℕ}
    (hn : n ∈ routingH B e) :
    ∃ x y z : ℕ,
      n = x * routingA B e + y * routingB B e + z * routingC B e := by
  change n ∈ generatedThree (routingA B e) (routingB B e) (routingC B e) at hn
  exact (mem_generatedThree_iff _ _ _ _).mp hn

/-- Whole-domain canonicality, obtained from finite residue completeness,
terminating reduction, and the actual Apéry minimality theorem. -/
theorem herzogLShapeCanonicality
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    ∀ i j, HerzogLShapeDomain D i j →
      IsCanonicalTailGridPoint B e i j := by
  intro i j hdomain
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let beta : ℤ := normalizedGrid B e 0 i j
  let s := gridResidue B e i j
  let alpha : ℤ := physicalAlpha B e s
  have halphaMem : alpha ∈ (routingH B e).asRelativeIdeal := by
    dsimp [alpha, physicalAlpha]
    exact (routingH B e).asRelativeIdeal.aperyRepresentative_mem
      (routingA B e) s
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at halphaMem
  obtain ⟨n, hnH, hnalpha⟩ := halphaMem
  obtain ⟨x, y, z, hnfac⟩ := routingH_factorization B e hnH
  obtain ⟨i', j', k, hdomain', hreduce⟩ :=
    coherent_exists_reduction B e D y z
  have hnterminal :
      n = i' * routingB B e + j' * routingC B e +
        (x + k) * routingA B e := by
    nlinarith only [hnfac, hreduce]
  have hnResidue : (n : ZMod (routingA B e)) = s := by
    have halphaMod := (routingH B e).asRelativeIdeal.aperyRepresentative_mod
      (routingA B e) s
    change (alpha : ZMod (routingA B e)) = s at halphaMod
    rw [hnalpha] at halphaMod
    exact_mod_cast halphaMod
  have hinputResidue :
      ((i * routingB B e + j * routingC B e : ℕ) :
        ZMod (routingA B e)) = s := by
    simpa [s, normalizedGrid] using normalizedGrid_mod B e 0 i j
  have hmod : Int.ModEq (routingA B e)
      ((i' : ℤ) * routingB B e + (j' : ℤ) * routingC B e)
      ((i : ℤ) * routingB B e + (j : ℤ) * routingC B e) := by
    have htermN : Int.ModEq (routingA B e)
        ((i' : ℤ) * routingB B e + (j' : ℤ) * routingC B e) n := by
      rw [Int.modEq_iff_dvd]
      refine ⟨(x + k : ℤ), ?_⟩
      push_cast
      nlinarith only [hnterminal]
    have hnInput : Int.ModEq (routingA B e) (n : ℤ)
        ((i : ℤ) * routingB B e + (j : ℤ) * routingC B e) := by
      apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
      exact_mod_cast hnResidue.trans hinputResidue.symm
    exact htermN.trans hnInput
  have hcoords := GenericLShape.modEq_unique
    (routingA B e) (routingB B e) (routingC B e)
    (c2 B e) (c3 B e) (cr12 D) (cr13 D) (cr32 D) (cr23 D)
    (coherent_coefficients_positive B e D).1
    (coherent_coefficients_positive B e D).2.1
    (coherent_coefficients_positive B e D).2.2.2.2.2
    (coherent_coefficients_positive B e D).2.2.2.1
    (coherent_coefficients B e D).2.1
    (coherent_coefficients B e D).2.2
    (coherent_second_minimality B e D)
    (coherent_third_minimality B e D)
    (coherent_uniqueZeroInLShape B e D)
    (inLShape_of_herzogDomain B e D hdomain')
    (inLShape_of_herzogDomain B e D hdomain) hmod
  have hiEq : i' = i := by exact_mod_cast hcoords.1
  have hjEq : j' = j := by exact_mod_cast hcoords.2
  subst i'
  subst j'
  have hbetaMem : beta ∈ (routingH B e).asRelativeIdeal := by
    simpa [beta] using normalizedGrid_zero_mem_routingH B e i j
  have hbetaMod : (beta : ZMod (routingA B e)) = s := by
    simpa [beta, s] using normalizedGrid_mod B e 0 i j
  have halphaLe : alpha ≤ beta := by
    apply (routingH B e).asRelativeIdeal.aperyRepresentative_le
      (routingA B e) s hbetaMem hbetaMod
  have hbetaLe : beta ≤ alpha := by
    have halphaEq : alpha = beta + ((x + k) * routingA B e : ℕ) := by
      calc
        alpha = (n : ℤ) := hnalpha
        _ = (i * routingB B e + j * routingC B e +
            (x + k) * routingA B e : ℕ) := by rw [hnterminal]
        _ = beta + ((x + k) * routingA B e : ℕ) := by
          simp [beta, normalizedGrid]
    rw [halphaEq]
    exact le_add_of_nonneg_right (by positivity)
  exact le_antisymm hbetaLe halphaLe

theorem eta_eq_physicalHeight_on_herzogDomain
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) {i j : ℕ}
    (h : HerzogLShapeDomain D i j) :
    eta B e i j = physicalHeight B e (gridResidue B e i j) :=
  eta_eq_physicalHeight_of_isCanonical B e i j
    (herzogLShapeCanonicality B e D i j h)

theorem gridLift_eq_zero_on_herzogDomain
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) {i j : ℕ}
    (h : HerzogLShapeDomain D i j) :
    gridLift B e i j = 0 :=
  gridLift_eq_zero_of_isCanonical B e i j
    (herzogLShapeCanonicality B e D i j h)

/-- Phase 3 entry point: every paper load-bearing coordinate is now an actual
canonical tail-grid point. -/
theorem loadBearingCoordinates_canonical
    (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    IsCanonicalTailGridPoint B e 0 0 ∧
      IsCanonicalTailGridPoint B e (cr12 D - 1) (cr13 D) ∧
      IsCanonicalTailGridPoint B e (cr12 D) (cr13 D - 1) ∧
      IsCanonicalTailGridPoint B e 0 (c3 B e - 1) ∧
      IsCanonicalTailGridPoint B e (cr32 D) 0 ∧
      IsCanonicalTailGridPoint B e (cr32 D - 1) 0 ∧
      IsCanonicalTailGridPoint B e (coherentKappa1 B e D).1
        (coherentKappa1 B e D).2 := by
  have h := loadBearingCoordinates_in_domain B e D
  exact ⟨herzogLShapeCanonicality B e D 0 0 h.1,
    herzogLShapeCanonicality B e D _ _ h.2.1,
    herzogLShapeCanonicality B e D _ _ h.2.2.1,
    herzogLShapeCanonicality B e D _ _ h.2.2.2.1,
    herzogLShapeCanonicality B e D _ _ h.2.2.2.2.1,
    herzogLShapeCanonicality B e D _ _ h.2.2.2.2.2.1,
    herzogLShapeCanonicality B e D _ _ h.2.2.2.2.2.2⟩

end NS25Lean.L5A2C4OR6
