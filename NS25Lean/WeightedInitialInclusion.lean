import NS25Lean.DilationIdeals

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase Presentation MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem weightedDegree_binomial_of_lt (k : Type*) [Field k] (B : Data Gamma)
    (u v : Fin 3 →₀ ℕ) (h : weight B v < weight B u) :
    weightedTotalDegree (weights B) (monomial u (1 : k) - monomial v 1) = weight B u := by
  classical
  have huv : u ≠ v := by intro he; subst v; omega
  apply le_antisymm
  · unfold weightedTotalDegree
    apply Finset.sup_le
    intro d hd
    by_cases hdu : d = u
    · subst d; exact le_rfl
    by_cases hdv : d = v
    · subst d; exact le_of_lt h
    have hc := mem_support_iff.mp hd
    simp [coeff_sub, coeff_monomial, hdu, hdv, Ne.symm hdu, Ne.symm hdv] at hc
  · apply le_weightedTotalDegree
    simp [mem_support_iff, coeff_sub, coeff_monomial, huv, Ne.symm huv]

theorem weightInitial_binomial_of_lt (k : Type*) [Field k] (B : Data Gamma)
    (u v : Fin 3 →₀ ℕ) (h : weight B v < weight B u) :
    weightInitial k B (monomial u (1 : k) - monomial v 1) = monomial u 1 := by
  classical
  have huv : u ≠ v := by intro he; subst v; omega
  ext d
  rw [coeff_weightInitial, weightedDegree_binomial_of_lt k B u v h]
  by_cases hdu : d = u
  · subst d; simp [huv, Ne.symm huv]
  by_cases hdv : d = v
  · subst d; simp [huv, Ne.symm huv, ne_of_lt h]
  · simp [coeff_sub, coeff_monomial, hdu, hdv, Ne.symm hdu, Ne.symm hdv]

theorem boundary_lattice_partner (B : Data Gamma) (u : Fin 3 →₀ ℕ)
    (hu : weight B u ∈ B.K) :
    ∃ v : Fin 3 →₀ ℕ, weight B v < weight B u ∧
      exponentDifference u v ∈ residueLattice B := by
  obtain ⟨r, g, hg, he⟩ := B.generatedOver (weight B u - B.q.val) hu.2.2
  obtain ⟨v, hv⟩ := factorizationMap_surjective B.tailDegrees B.tailDegrees_generate ⟨g, hg⟩
  have hv' : weight B v = g := by rw [weight_eq_degree, hv]
  have hu' : weight B u = (r + 1) * B.q.val + weight B v := by
    rw [hv']
    have hq := hu.2.1
    have hsub := Nat.sub_add_cancel hq
    nlinarith
  refine ⟨v, ?_, ?_⟩
  · have hp := B.q_positive
    nlinarith
  · change (B.q.val : ℤ) ∣ integerWeight B (exponentDifference u v)
    rw [integerWeight_difference, hu']
    refine ⟨(r : ℤ) + 1, ?_⟩
    push_cast
    ring

/-- Both types of generators of the actual J are initials of lattice binomials. -/
theorem J_le_weightInitial_latticeIdeal (k : Type*) [Field k] (B : Data Gamma) :
    B.J k ≤ weightInitialIdeal k B (latticeIdeal k B) := by
  rw [B.J_eq_IH_sup_MK k]
  apply sup_le
  · rw [IH_eq_relationIdeal, relationIdeal]
    apply Ideal.span_le.mpr
    rintro f ⟨⟨u, v⟩, huv, rfl⟩
    change weight B u = weight B v at huv
    have hmem : monomial u (1 : k) - monomial v 1 ∈ latticeIdeal k B := by
      apply Ideal.subset_span
      refine ⟨(u, v), ?_, rfl⟩
      change (B.q.val : ℤ) ∣ integerWeight B (exponentDifference u v)
      rw [integerWeight_difference, huv, sub_self]
      exact dvd_zero _
    have hf : (monomial u (1 : k) - monomial v 1).IsWeightedHomogeneous
        (weights B) (weight B u) :=
      (isWeightedHomogeneous_monomial _ _ _ rfl).sub
        (isWeightedHomogeneous_monomial _ _ _ huv.symm)
    apply Ideal.subset_span
    exact ⟨_, hmem, weightInitial_of_homogeneous k B _ _ hf⟩
  · unfold Data.MK
    apply Ideal.span_le.mpr
    rintro f ⟨u, hu, rfl⟩
    have hu' : weight B u ∈ B.K := by rwa [weight_eq_degree]
    obtain ⟨v, hv, hl⟩ := boundary_lattice_partner B u hu'
    apply Ideal.subset_span
    refine ⟨monomial u (1 : k) - monomial v 1, ?_, weightInitial_binomial_of_lt k B u v hv⟩
    exact Ideal.subset_span ⟨(u, v), hl, rfl⟩

theorem larger_lattice_weight_mem_K (B : Data Gamma) (u v : Fin 3 →₀ ℕ)
    (hl : exponentDifference u v ∈ residueLattice B) (hlt : weight B v < weight B u) :
    weight B u ∈ B.K := by
  have hdivZ : (B.q.val : ℤ) ∣ ((weight B u - weight B v : ℕ) : ℤ) := by
    rw [Int.natCast_sub (le_of_lt hlt)]
    change (B.q.val : ℤ) ∣ integerWeight B (exponentDifference u v) at hl
    rwa [integerWeight_difference] at hl
  have hdiv : B.q.val ∣ weight B u - weight B v := Int.natCast_dvd_natCast.mp hdivZ
  obtain ⟨r, hr⟩ := hdiv
  have hsub := Nat.sub_add_cancel (le_of_lt hlt)
  have hrpos : 0 < r := by
    have hdpos := Nat.sub_pos_of_lt hlt
    by_contra hn
    have hz : r = 0 := by omega
    simp only [hz, mul_zero] at hr
    omega
  have hrsub := Nat.sub_add_cancel hrpos
  have hq := B.q_positive
  have hbound : B.q.val ≤ weight B u := by nlinarith
  have he : weight B u - B.q.val = weight B v + (r - 1) * B.q.val := by
    have hs := Nat.sub_add_cancel hbound
    nlinarith
  refine ⟨?_, hbound, ?_⟩
  · rw [weight_eq_degree]
    exact (factorizationMap B.tailDegrees u).property
  · rw [he]
    apply Gamma.toAddSubmonoid.add_mem
    · apply B.H_le
      rw [weight_eq_degree]
      exact (factorizationMap B.tailDegrees v).property
    · simpa [nsmul_eq_mul] using Gamma.toAddSubmonoid.nsmul_mem B.q.property (r - 1)

theorem weightInitial_neg (k : Type*) [Field k] (B : Data Gamma) (f : MvPolynomial (Fin 3) k) :
    weightInitial k B (-f) = -weightInitial k B f := by
  simp only [weightInitial, weightedTotalDegree, support_neg, map_neg]

theorem lattice_binomial_initial_mem_J (k : Type*) [Field k] (B : Data Gamma)
    (u v : Fin 3 →₀ ℕ) (hl : exponentDifference u v ∈ residueLattice B) :
    weightInitial k B (monomial u (1 : k) - monomial v 1) ∈ B.J k := by
  have hIH : B.IH k ≤ B.J k := by rw [B.J_eq_IH_sup_MK k]; exact le_sup_left
  have hMK : B.MK k ≤ B.J k := by rw [B.J_eq_IH_sup_MK k]; exact le_sup_right
  have mon_mem (a : Fin 3 →₀ ℕ) (ha : weight B a ∈ B.K) : monomial a (1 : k) ∈ B.J k := by
    apply hMK
    apply Ideal.subset_span
    refine ⟨a, ?_, rfl⟩
    change (factorizationMap B.tailDegrees a).val ∈ B.K
    rwa [← weight_eq_degree]
  rcases lt_trichotomy (weight B v) (weight B u) with hlt | heq | hgt
  · rw [weightInitial_binomial_of_lt k B u v hlt]
    exact mon_mem u (larger_lattice_weight_mem_K B u v hl hlt)
  · have hf : (monomial u (1 : k) - monomial v 1).IsWeightedHomogeneous
        (weights B) (weight B u) :=
      (isWeightedHomogeneous_monomial _ _ _ rfl).sub
        (isWeightedHomogeneous_monomial _ _ _ heq)
    rw [weightInitial_of_homogeneous k B _ _ hf]
    apply hIH
    rw [IH_eq_relationIdeal, relationIdeal]
    exact Ideal.subset_span ⟨(u, v), heq.symm, rfl⟩
  · have hl' : exponentDifference v u ∈ residueLattice B := by
      rw [difference_mem_lattice_iff] at hl ⊢
      exact hl.symm
    rw [show monomial u (1 : k) - monomial v 1 = -(monomial v 1 - monomial u 1) by abel,
      weightInitial_neg, weightInitial_binomial_of_lt k B v u hgt]
    exact (B.J k).neg_mem (mon_mem v (larger_lattice_weight_mem_K B v u hl' hgt))

end NS25Lean.L2B
