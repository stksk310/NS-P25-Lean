import NS25Lean.MonomialSetup

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3A
open MvPolynomial
variable {k : Type*} [Field k]

def standardExponents (I : Ideal (Polynomial k)) : Set Exponent :=
  {a | monomial a (1 : k) ∉ I}

def socleExponents (I : Ideal (Polynomial k)) : Set Exponent :=
  {a | a ∈ standardExponents I ∧ ∀ i, monomial (a + Finsupp.single i 1) (1 : k) ∈ I}

def monomialClass (I : Ideal (Polynomial k)) (a : Exponent) : Polynomial k ⧸ I :=
  Ideal.Quotient.mkₐ k I (monomial a 1)

theorem standard_coefficient_zero (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I)
    (f : Polynomial k) (hf : f ∈ I) (a : Exponent) (ha : a ∈ standardExponents I) :
    coeff a f = 0 := by
  by_contra hn
  obtain ⟨S, rfl⟩ := hI
  have h := mem_ideal_span_monomial_image.mp hf a (mem_support_iff.mpr hn)
  exact ha ((monomial_mem_span_iff S a).mpr h)

theorem standard_linearIndependent (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I) :
    LinearIndependent k (fun a : standardExponents I => monomialClass I a.val) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hc a ha
  let f : Polynomial k := ∑ b ∈ s, c b • monomial b.val 1
  have hf : f ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ k I f = 0
    simpa only [f, map_sum, map_smul, monomialClass] using hc
  have hz := standard_coefficient_zero I hI f hf a.val a.property
  have he : coeff a.val f = c a := by
    simp only [f, coeff_sum, coeff_smul, coeff_monomial]
    simp [Subtype.val_injective.eq_iff, ha]
  exact he.symm.trans hz

theorem standard_span (I : Ideal (Polynomial k)) :
    Submodule.span k (Set.range (fun a : standardExponents I => monomialClass I a.val)) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mkₐ k I f ∈ _
  induction f using MvPolynomial.induction_on' with
  | monomial a c =>
    have he : monomial a c = c • monomial a (1 : k) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [he, map_smul]
    apply Submodule.smul_mem
    by_cases ha : monomial a (1 : k) ∈ I
    · have hz : Ideal.Quotient.mkₐ k I (monomial a (1 : k)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr ha
      rw [hz]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg

def standardBasis (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I) :
    Module.Basis (standardExponents I) k (Polynomial k ⧸ I) :=
  Module.Basis.mk (standard_linearIndependent I hI) (by rw [standard_span I])

theorem standardExponents_finite (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I)
    [IsArtinianRing (Polynomial k ⧸ I)] : (standardExponents I).Finite := by
  letI := quotient_finite_of_artinian I
  letI := (standard_linearIndependent I hI).finite
  exact Set.toFinite _

theorem socleExponents_finite (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I)
    [IsArtinianRing (Polynomial k ⧸ I)] : (socleExponents I).Finite :=
  (standardExponents_finite I hI).subset (fun _ ha => ha.1)

theorem X_mul_monomialClass (I : Ideal (Polynomial k)) (a : Exponent) (i : Fin 3) :
    Ideal.Quotient.mk I (X i) * monomialClass I a =
      monomialClass I (a + Finsupp.single i 1) := by
  change Ideal.Quotient.mkₐ k I (X i) * Ideal.Quotient.mkₐ k I (monomial a 1) = _
  rw [← map_mul]
  congr 1
  simp [X, monomial_mul, add_comm]

theorem socleMonomial_mem (I : Ideal (Polynomial k)) (a : socleExponents I) :
    monomialClass I a.val ∈ socle I := by
  intro i
  rw [X_mul_monomialClass]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (a.property.2 i)

def socleMonomial (I : Ideal (Polynomial k)) (a : socleExponents I) : socle I :=
  ⟨monomialClass I a.val, socleMonomial_mem I a⟩

theorem socle_support (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I)
    (f : Polynomial k) (hf : Ideal.Quotient.mkₐ k I f ∈ socle I)
    (a : Exponent) (ha : a ∈ standardExponents I) (hc : coeff a f ≠ 0) :
    a ∈ socleExponents I := by
  refine ⟨ha, fun i => ?_⟩
  by_contra hn
  have hm : X i * f ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ k I (X i * f) = 0
    rw [map_mul]
    exact hf i
  have hz := standard_coefficient_zero I hI (X i * f) hm (a + Finsupp.single i 1) hn
  exact hc (by simpa only [add_comm a, coeff_X_mul] using hz)

theorem socle_eq_span (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I) :
    socle I = Submodule.span k (Set.range (fun a : socleExponents I => monomialClass I a.val)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mkₐ k I f ∈ _
    rw [← support_sum_monomial_coeff f, map_sum]
    apply Submodule.sum_mem
    intro a ha
    have he : monomial a (coeff a f) = coeff a f • monomial a (1 : k) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [he, map_smul]
    apply Submodule.smul_mem
    by_cases hm : monomial a (1 : k) ∈ I
    · have hz : Ideal.Quotient.mkₐ k I (monomial a (1 : k)) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hm
      rw [hz]; exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨a, socle_support I hI f hx a hm (mem_support_iff.mp ha)⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact socleMonomial_mem I a

theorem socle_linearIndependent (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I) :
    LinearIndependent k (fun a : socleExponents I => monomialClass I a.val) := by
  let f : socleExponents I → standardExponents I := fun a => ⟨a.val, a.property.1⟩
  apply (standard_linearIndependent I hI).comp f
  intro a b he
  apply Subtype.ext
  exact congrArg (fun u : standardExponents I => u.val) he

def socleBasis (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I) :
    Module.Basis (socleExponents I) k (socle I) :=
  (Module.Basis.span (socle_linearIndependent I hI)).map
    (LinearEquiv.ofEq _ _ (socle_eq_span I hI).symm)

/-- The type is the number of maximal surviving monomials, not a surrogate definition. -/
theorem quotientType_eq_socle_count (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I) :
    quotientType I = (socleExponents I).ncard := by
  exact Module.finrank_eq_nat_card_basis (socleBasis I hI)

/-- Exact reduction of M2 to the three-dimensional staircase counting problem. -/
theorem support_refined_iff_staircase_count (I : Ideal (Polynomial k))
    (hI : L2B.IsMonomialIdeal k I) :
    (quotientType I ≤ mu I + q_fs I - 2) ↔
      (socleExponents I).ncard ≤ (minimalExponents I).ncard + (fullSupportGenerators I).ncard - 2 := by
  rw [quotientType_eq_socle_count I hI, mu_eq_minimal_count I hI]
  rfl

theorem exists_purePower_mem (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I)
    [IsArtinianRing (Polynomial k ⧸ I)] (i : Fin 3) :
    ∃ n : ℕ, monomial (Finsupp.single i n) (1 : k) ∈ I := by
  classical
  by_contra! hn
  letI : Finite (standardExponents I) := (standardExponents_finite I hI).to_subtype
  let f : ℕ → standardExponents I := fun n => ⟨Finsupp.single i n, hn n⟩
  have hi : Function.Injective f := by
    intro a b he
    have h := congrArg (fun u : standardExponents I => u.val i) he
    simpa [f] using h
  letI : Finite ℕ := Finite.of_injective f hi
  exact Set.infinite_univ (Set.toFinite (Set.univ : Set ℕ))

theorem mu_positive_of_artinian (I : Ideal (Polynomial k)) (hI : L2B.IsMonomialIdeal k I)
    [IsArtinianRing (Polynomial k ⧸ I)] : 0 < mu I := by
  by_contra! hz
  have he : I.spanFinrank = 0 := Nat.eq_zero_of_le_zero hz
  have hb := (Submodule.spanFinrank_eq_zero_iff_eq_bot (Ideal.fg_of_isNoetherianRing I)).mp he
  obtain ⟨n, hn⟩ := exists_purePower_mem I hI 0
  rw [hb] at hn
  simpa using hn

end NS25Lean.L3A
