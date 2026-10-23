import NS25Lean.OneDefectGenerators

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3B
open ChosenBase L2B L2B2A L2B2A2 MvPolynomial
variable {Gamma : NumericalSemigroup}

def actualInitial (k : Type*) [Field k] (B : Data Gamma) (m : MonomialOrder (Fin 3)) :
    Ideal (ToricPresentation.Poly k 3) := monomialInitialIdeal k m (B.J k)

theorem actualInitial_lattice (k : Type*) [Field k] (B : Data Gamma)
    (m : MonomialOrder (Fin 3)) :
    actualInitial k B m = monomialInitialIdeal k (weightRefinement B m)
      (L3A.latticeIdeal (residueLattice B)) := J_monomialInitial_eq_refinement k B m

theorem actualInitial_q_fs (k : Type*) [Field k] (B : Data Gamma)
    (m : MonomialOrder (Fin 3)) : L3A.q_fs (actualInitial k B m) ≤ 1 := by
  rw [actualInitial_lattice]
  exact L3A.q_fs_lattice_initial_le_one _ _

theorem actualInitial_purePower (k : Type*) [Field k] (B : Data Gamma)
    (m : MonomialOrder (Fin 3)) (j : Fin 3) :
    monomial (Finsupp.single j B.q.val) (1 : k) ∈ actualInitial k B m := by
  have hl : exponentDifference (Finsupp.single j B.q.val) 0 ∈ residueLattice B := by
    change (B.q.val : ℤ) ∣ integerWeight B _
    rw [integerWeight_difference, weight_single, map_zero, Nat.cast_mul, Nat.cast_zero, sub_zero]
    exact dvd_mul_right _ _
  have hp : weight B 0 < weight B (Finsupp.single j B.q.val) := by
    rw [map_zero, weight_single]
    exact Nat.mul_pos B.q_positive (weights_positive B j)
  have hK := larger_lattice_weight_mem_K B _ _ hl hp
  exact Ideal.subset_span ⟨monomial (Finsupp.single j B.q.val) 1,
    boundary_monomial_mem_J k B _ hK, m.leadingTerm_monomial _ _⟩

theorem actualInitial_standard_bound (k : Type*) [Field k] (B : Data Gamma)
    (m : MonomialOrder (Fin 3)) (u : L3A.standardExponents (actualInitial k B m)) (j : Fin 3) :
    u.val j < B.q.val := by
  by_contra hn
  have hle : Finsupp.single j B.q.val ≤ u.val := Finsupp.single_le_iff.mpr (by omega)
  have hd : monomial (Finsupp.single j B.q.val) (1 : k) ∣ monomial u.val 1 :=
    monomial_one_dvd_monomial_one.mpr hle
  exact u.property ((actualInitial k B m).mem_of_dvd hd (actualInitial_purePower k B m j))

theorem actualInitial_standard_finite (k : Type*) [Field k] (B : Data Gamma)
    (m : MonomialOrder (Fin 3)) : (L3A.standardExponents (actualInitial k B m)).Finite := by
  let f : L3A.standardExponents (actualInitial k B m) → (Fin 3 → Fin B.q.val) :=
    fun u j => ⟨u.val j, actualInitial_standard_bound k B m u j⟩
  have hi : Function.Injective f := by
    intro u v he
    apply Subtype.ext
    ext j
    exact congrArg Fin.val (congrFun he j)
  haveI := Finite.of_injective f hi
  exact Set.toFinite _

instance actualInitial_artinian (k : Type*) [Field k] (B : Data Gamma)
    (m : MonomialOrder (Fin 3)) :
    IsArtinianRing (ToricPresentation.Poly k 3 ⧸ actualInitial k B m) := by
  letI : FiniteDimensional k (ToricPresentation.Poly k 3 ⧸ actualInitial k B m) :=
    FiniteDimensional.of_finite_basis
      (L3A.standardBasis _ (L3A.initial_isMonomial m (B.J k)))
      (actualInitial_standard_finite k B m)
  exact IsArtinianRing.of_finite k _

def actualInitialArtinianMonomial (k : Type*) [Field k] (B : Data Gamma)
    (m : MonomialOrder (Fin 3)) : L3A.ArtinianMonomial k where
  ideal := actualInitial k B m
  monomial := L3A.initial_isMonomial m (B.J k)
  proper := by rw [actualInitial_lattice]; exact L3A.lattice_initial_proper _ _
  artinian := inferInstance

end NS25Lean.L3B
