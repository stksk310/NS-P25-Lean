import NS25Lean.WeightedInitialEquality

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase Presentation MvPolynomial ToricPresentation
variable {Gamma : NumericalSemigroup}

def coefficientSum (k : Type*) [Field k] (f : MvPolynomial (Fin 3) k) : k :=
  ∑ u ∈ f.support, coeff u f

theorem factorization_image_single (k : Type*) [Field k] {H : Type*} [AddCommMonoid H]
    (w : Fin 3 → H) (f : MvPolynomial (Fin 3) k) (h : H)
    (hf : ∀ u ∈ f.support, factorizationMap w u = h) :
    factorizationAlgebraMap k w f = AddMonoidAlgebra.single h (coefficientSum k f) := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff f]
  rw [map_sum]
  change _ = (AddMonoidAlgebra.singleAddHom h) (∑ u ∈ f.support, coeff u f)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [factorizationAlgebraMap_monomial, hf u hu]
  rfl

theorem homogeneous_residue_image (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (d : ℕ) (hf : f.IsWeightedHomogeneous (weights B) d) :
    residueMap k B f = AddMonoidAlgebra.single (d : ZMod B.q.val) (coefficientSum k f) := by
  apply factorization_image_single
  intro u hu
  rw [residue_factorization, show weight B u = d from hf (mem_support_iff.mp hu)]

theorem homogeneous_tail_image (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (h : B.H)
    (hf : f.IsWeightedHomogeneous (weights B) h.val) :
    toricMap k B.H B.tailDegrees f = AddMonoidAlgebra.single h (coefficientSum k f) := by
  rw [← factorizationAlgebraMap_eq_toricMap]
  apply factorization_image_single
  intro u hu
  apply Subtype.ext
  rw [← weight_eq_degree]
  exact hf (mem_support_iff.mp hu)

theorem homogeneous_J_sum_zero (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (h : B.H)
    (hf : f.IsWeightedHomogeneous (weights B) h.val)
    (hJ : f ∈ B.J k) (hk : h.val ∉ B.K) : coefficientSum k f = 0 := by
  rw [B.J_eq_comap_tail k] at hJ
  have hm := (mem_tailMonomialIdeal_iff k _ _ _ B.H_le _).mp hJ
  change ∀ x ∈ (toricMap k B.H B.tailDegrees f).coeff.support, x.val ∈ B.K at hm
  rw [homogeneous_tail_image k B f h hf] at hm
  by_contra hn
  exact hk (hm h (by simpa [AddMonoidAlgebra.coeff_single] using hn))

/-- Subtracting one strictly lower-weight monomial preserves the whole top form. -/
theorem weightInitial_sub_lower_monomial (k : Type*) [Field k] (B : Data Gamma)
    (f : MvPolynomial (Fin 3) k) (d : ℕ) (hf : f.IsWeightedHomogeneous (weights B) d)
    (hn : f ≠ 0) (v : Fin 3 →₀ ℕ) (hv : weight B v < d) (a : k) :
    weightInitial k B (f - monomial v a) = f := by
  classical
  obtain ⟨u, hu⟩ := support_nonempty.mpr hn
  have hud : weight B u = d := hf (mem_support_iff.mp hu)
  have huv : u ≠ v := by intro he; subst u; omega
  have hdeg : weightedTotalDegree (weights B) (f - monomial v a) = d := by
    apply le_antisymm
    · apply Finset.sup_le
      intro x hx
      by_cases hxv : x = v
      · subst x; exact le_of_lt hv
      · have hxf : x ∈ f.support := by
          simpa [mem_support_iff, coeff_sub, coeff_monomial, Ne.symm hxv] using hx
        exact le_of_eq (hf (mem_support_iff.mp hxf))
    · rw [← hud]
      apply le_weightedTotalDegree
      simpa [mem_support_iff, coeff_sub, coeff_monomial, Ne.symm huv] using hu
  unfold weightInitial
  rw [hdeg, map_sub, hf.weightedHomogeneousComponent_same]
  have hmono := isWeightedHomogeneous_monomial (weights B) v a rfl
  rw [hmono.weightedHomogeneousComponent_ne d (ne_of_gt hv), sub_zero]

/-- Every nonzero homogeneous element of actual J is exactly the top form of an
element of the actual lattice ideal. The boundary case supplies a lower partner. -/
theorem homogeneous_J_lift (k : Type*) [Field k] (B : Data Gamma)
    (g : MvPolynomial (Fin 3) k) (d : ℕ) (hg : g.IsWeightedHomogeneous (weights B) d)
    (hJ : g ∈ B.J k) (hn : g ≠ 0) :
    ∃ f ∈ latticeIdeal k B, weightInitial k B f = g := by
  classical
  obtain ⟨u, hu⟩ := support_nonempty.mpr hn
  have hud : weight B u = d := hg (mem_support_iff.mp hu)
  by_cases hd : d ∈ B.K
  · obtain ⟨v, hv, hl⟩ := boundary_lattice_partner B u (hud ▸ hd)
    refine ⟨g - monomial v (coefficientSum k g), ?_, ?_⟩
    · rw [latticeIdeal_eq_ker_residueMap]
      change residueMap k B (g - monomial v (coefficientSum k g)) = 0
      rw [map_sub, homogeneous_residue_image k B g d hg]
      change _ - factorizationAlgebraMap k (residueWeights B)
        (monomial v (coefficientSum k g)) = 0
      rw [factorizationAlgebraMap_monomial, residue_factorization]
      have he := (lattice_iff_residue B u v).mp hl
      rw [residue_factorization, residue_factorization, hud] at he
      rw [he, sub_self]
    · exact weightInitial_sub_lower_monomial k B g d hg hn v (hud ▸ hv) _
  · have hs := homogeneous_J_sum_zero k B g (factorizationMap B.tailDegrees u)
      (by simpa [← weight_eq_degree, hud] using hg) hJ
      (by simpa [← weight_eq_degree, hud] using hd)
    refine ⟨g, ?_, weightInitial_of_homogeneous k B g d hg⟩
    rw [latticeIdeal_eq_ker_residueMap]
    change residueMap k B g = 0
    rw [homogeneous_residue_image k B g d hg, hs]
    exact AddMonoidAlgebra.single_zero _

theorem J_component_mem (k : Type*) [Field k] (B : Data Gamma)
    (g : MvPolynomial (Fin 3) k) (hg : g ∈ B.J k) (d : ℕ) :
    weightedHomogeneousComponent (weights B) d g ∈ B.J k := by
  rw [J_eq_weightInitial_latticeIdeal] at hg ⊢
  apply PositivePresentation.component_mem_span (weights B) _ _ g hg d
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨_, weightedHomogeneousComponent_isWeightedHomogeneous _ _⟩

end NS25Lean.L2B
