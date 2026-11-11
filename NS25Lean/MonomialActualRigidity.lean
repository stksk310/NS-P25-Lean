import NS25Lean.P2DAFirstReturnR49

set_option linter.style.header false
noncomputable section
namespace NS25Lean.MonomialPivotStrictness
open ChosenBase L2B L2B2A L2B2A2 L3A L3B L3C L5A1 L5A2R49First
open MvPolynomial
variable {Gamma : NumericalSemigroup}

/-- Actual monomiality excludes every relation between distinct standard
factorizations. This works at every original pivot and over every field. -/
theorem monomial_apery_unique (k : Type*) [Field k] (B : Data Gamma)
    (hJ : IsMonomialIdeal k (B.J k)) (d : ℕ) (hd : d ∈ B.apery) :
    Subsingleton (FactorizationFiber B d) := by
  refine ⟨fun u v => ?_⟩
  apply Subtype.ext
  by_contra hne
  have hu : u.val ∈ standardExponents (B.J k) :=
    (standard_iff_chosen_apery k B u.val).mpr (u.property.symm ▸ hd)
  have hrel : monomial u.val (1 : k) - monomial v.val 1 ∈ B.J k := by
    have hle : B.IH k ≤ B.J k := by rw [B.J_eq_IH_sup_MK k]; exact le_sup_left
    exact hle (binomial_mem_IH k B _ _ (u.property.trans v.property.symm))
  have hz := standard_coefficient_zero (B.J k) hJ _ hrel u.val hu
  simp [coeff_sub, coeff_monomial, hne, Ne.symm hne] at hz

theorem monomial_eq_MK (k : Type*) [Field k] (B : Data Gamma)
    (hJ : IsMonomialIdeal k (B.J k)) : B.J k = B.MK k :=
  L5A2R49.J_eq_MK_of_apery_unique B (monomial_apery_unique k B hJ) k

/-- Cancellation at a standard predecessor separates any distinct
factorization from a minimal excluded exponent. -/
theorem minimal_factorization_disjoint (k : Type*) [Field k] (B : Data Gamma)
    (hJ : IsMonomialIdeal k (B.J k)) (u v : Exponent)
    (hu : u ∈ minimalExponents (B.J k)) (hv : weight B v = weight B u)
    (hne : v ≠ u) (j : Fin 3) (hj : 0 < u j) : v j = 0 := by
  by_contra hn
  have hvj := Nat.pos_of_ne_zero hn
  have ha := minimal_boundary_remove_apery k B (monomial_eq_MK k B hJ) u hu j hj
  have hu' := removed_weight B (weight B u) ⟨u,rfl⟩ j hj
  have hv' := removed_weight B (weight B u) ⟨v,hv⟩ j hvj
  change weights B j + weight B (u - Finsupp.single j 1) = weight B u at hu'
  change weights B j + weight B (v - Finsupp.single j 1) = weight B u at hv'
  let a : FactorizationFiber B (weight B u - weights B j) :=
    ⟨u - Finsupp.single j 1, by omega⟩
  let b : FactorizationFiber B (weight B u - weights B j) :=
    ⟨v - Finsupp.single j 1, by omega⟩
  have he := congrArg Subtype.val ((monomial_apery_unique k B hJ _ ha).elim a b)
  have he' := congrArg (fun w => Finsupp.single j 1 + w) he
  exact hne (by simpa only [a,b,remove_variable_add u j hj,
    remove_variable_add v j hvj] using he'.symm)

end NS25Lean.MonomialPivotStrictness
