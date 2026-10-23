import NS25Lean.WeightedInitialInclusion

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase Presentation MvPolynomial ToricPresentation
variable {Gamma : NumericalSemigroup}

def residueWeights (B : Data Gamma) : Fin 3 → ZMod B.q.val :=
  fun i => (weights B i : ZMod B.q.val)

theorem residue_factorization (B : Data Gamma) (u : Fin 3 →₀ ℕ) :
    factorizationMap (residueWeights B) u = (weight B u : ZMod B.q.val) := by
  have he : factorizationMap (residueWeights B) =
      (Nat.castAddMonoidHom (ZMod B.q.val)).comp (weight B) := by
    apply Finsupp.addHom_ext
    intro i n
    simp [residueWeights, weight, Finsupp.weight_single, nsmul_eq_mul]
  exact DFunLike.congr_fun he u

theorem lattice_iff_residue (B : Data Gamma) (u v : Fin 3 →₀ ℕ) :
    exponentDifference u v ∈ residueLattice B ↔
      factorizationMap (residueWeights B) u = factorizationMap (residueWeights B) v := by
  rw [difference_mem_lattice_iff, residue_factorization, residue_factorization]
  simpa only [Int.cast_natCast] using
    (ZMod.intCast_eq_intCast_iff (weight B u) (weight B v) B.q.val).symm

def residueMap (k : Type*) [Field k] (B : Data Gamma) :
    MvPolynomial (Fin 3) k →ₐ[k] AddMonoidAlgebra k (ZMod B.q.val) :=
  factorizationAlgebraMap k (residueWeights B)

/-- The actual lattice ideal is the kernel of the residue map. -/
theorem latticeIdeal_eq_ker_residueMap (k : Type*) [Field k] (B : Data Gamma) :
    latticeIdeal k B = RingHom.ker (residueMap k B).toRingHom := by
  rw [residueMap, ← relationIdeal_factorization_eq_ker]
  unfold latticeIdeal relationIdeal
  congr 1
  congr 1
  ext p
  exact lattice_iff_residue B p.1 p.2

open Classical in
theorem factorization_coeff_sum (k : Type*) [Field k] {H : Type*} [AddCommMonoid H]
    (w : Fin 3 → H) (f : MvPolynomial (Fin 3) k) (h : H) :
    (factorizationAlgebraMap k w f).coeff h =
      ∑ u ∈ f.support, if factorizationMap w u = h then coeff u f else 0 := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff f]
  simp only [map_sum, factorizationAlgebraMap_monomial, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem tail_coeff_sum (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (h : B.H) :
    (toricMap k B.H B.tailDegrees f).coeff h =
      ∑ u ∈ f.support, if weight B u = h.val then coeff u f else 0 := by
  rw [← factorizationAlgebraMap_eq_toricMap, factorization_coeff_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [weight_eq_degree]
  simp only [Subtype.ext_iff]

theorem tail_component_coeff (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (d : ℕ) (h : B.H) :
    (toricMap k B.H B.tailDegrees (weightedHomogeneousComponent (weights B) d f)).coeff h =
      if h.val = d then (toricMap k B.H B.tailDegrees f).coeff h else 0 := by
  classical
  rw [tail_coeff_sum, support_weightedHomogeneousComponent, Finset.sum_filter,
    tail_coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  by_cases hd : h.val = d
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro u hu
    by_cases he : weight B u = h.val <;> simp_all [weight, eq_comm]
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro u hu
    by_cases he : weight B u = h.val <;> simp_all [weight, eq_comm]

/-- Coefficients in an un-killed maximal degree equal residue-fiber coefficients.
This statement applies to every polynomial, so cancellations have already been combined. -/
theorem top_tail_coeff_eq_residue (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (h : B.H)
    (ht : h.val = weightedTotalDegree (weights B) f) (hk : h.val ∉ B.K) :
    (toricMap k B.H B.tailDegrees f).coeff h =
      (residueMap k B f).coeff (h.val : ZMod B.q.val) := by
  classical
  rw [tail_coeff_sum, residueMap, factorization_coeff_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [residue_factorization]
  have he : weight B u = h.val ↔
      (weight B u : ZMod B.q.val) = (h.val : ZMod B.q.val) := by
    constructor
    · intro he; rw [he]
    · intro he
      have hle : weight B u ≤ h.val := ht ▸ le_weightedTotalDegree (weights B) hu
      by_contra hn
      have hlt : weight B u < h.val := lt_of_le_of_ne hle hn
      obtain ⟨v, hv⟩ := factorizationMap_surjective B.tailDegrees B.tailDegrees_generate h
      have hvw : weight B v = h.val := by rw [weight_eq_degree, hv]
      have hl : exponentDifference v u ∈ residueLattice B := by
        rw [lattice_iff_residue, residue_factorization, residue_factorization, hvw]
        exact he.symm
      exact hk (hvw ▸ larger_lattice_weight_mem_K B v u hl (hvw ▸ hlt))
  by_cases h : weight B u = h.val
  · simp only [h, ite_true]
  · simp only [h, not_congr he |>.mp h, ite_false]

/-- W4: arbitrary ideal elements, via exact coefficient fibers, not generator initials. -/
theorem weightInitial_mem_J (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (hf : f ∈ latticeIdeal k B) :
    weightInitial k B f ∈ B.J k := by
  have hz : residueMap k B f = 0 := by
    have := hf
    rw [latticeIdeal_eq_ker_residueMap] at this
    exact this
  rw [B.J_eq_comap_tail k]
  apply (mem_tailMonomialIdeal_iff k _ _ _ B.H_le _).mpr
  intro h hh
  have hc := Finsupp.mem_support_iff.mp hh
  change (toricMap k B.H B.tailDegrees (weightInitial k B f)).coeff h ≠ 0 at hc
  rw [weightInitial, tail_component_coeff] at hc
  by_cases ht : h.val = weightedTotalDegree (weights B) f
  · rw [ite_eq_left ht] at hc
    by_contra hk
    have he := top_tail_coeff_eq_residue k B f h ht hk
    rw [hz] at he
    exact hc he
  · simp [ht] at hc

theorem weightInitial_latticeIdeal_le_J (k : Type*) [Field k] (B : Data Gamma) :
    weightInitialIdeal k B (latticeIdeal k B) ≤ B.J k := by
  apply Ideal.span_le.mpr
  rintro _ ⟨f, hf, rfl⟩
  exact weightInitial_mem_J k B f hf

/-- Paper Proposition weighted-initial, first boxed equality. -/
theorem J_eq_weightInitial_latticeIdeal (k : Type*) [Field k] (B : Data Gamma) :
    B.J k = weightInitialIdeal k B (latticeIdeal k B) :=
  le_antisymm (J_le_weightInitial_latticeIdeal k B) (weightInitial_latticeIdeal_le_J k B)

end NS25Lean.L2B
