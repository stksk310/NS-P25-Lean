import NS25Lean.AppendixBCongruence

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C Presentation
variable {Gamma : NumericalSemigroup} {B : Data Gamma}
namespace NormalizedPairs

theorem exponent_expansion (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) :
    f = ((f (N.perm 0)) • Finsupp.single (N.perm 0) 1 +
      (f (N.perm 1)) • Finsupp.single (N.perm 1) 1) +
      ((f (N.perm 2)) • Finsupp.single (N.perm 2) 1 +
      (f (N.perm 3)) • Finsupp.single (N.perm 3) 1) := by
  ext i
  obtain ⟨j, rfl⟩ := N.perm.surjective i
  fin_cases j <;> simp [Finsupp.single_apply, N.perm.injective.eq_iff]

theorem weight_expansion (N : NormalizedPairs B) (f : Fin 4 →₀ ℕ) :
    weight B f = N.u * (N.alpha * f (N.perm 0) + N.beta * f (N.perm 1)) +
      N.v * (N.gamma * f (N.perm 2) + N.delta * f (N.perm 3)) := by
  rw [weight_eq_sum, ← Equiv.sum_comp N.perm]
  rw [Fin.sum_univ_four]
  simp only [N.weight0, N.weight1, N.weight2, N.weight3]
  ring

def sourceRelations (N : NormalizedPairs B) (r s k l : ℕ) :
    Finset ((Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ)) :=
  {(Finsupp.single (N.perm 0) N.beta, Finsupp.single (N.perm 1) N.alpha),
   (Finsupp.single (N.perm 2) N.delta, Finsupp.single (N.perm 3) N.gamma),
   (Finsupp.single (N.perm 0) r + Finsupp.single (N.perm 1) s,
    Finsupp.single (N.perm 2) k + Finsupp.single (N.perm 3) l)}

theorem sourceRelations_presentation (N : NormalizedPairs B) (r s k l : ℕ)
    (hvr : N.v = N.alpha * r + N.beta * s)
    (huk : N.u = N.gamma * k + N.delta * l) :
    IsPresentation B.family (N.sourceRelations r s k l) := by
  classical
  let q := generatedCongruence (↑(N.sourceRelations r s k l) : Set ((Fin 4 →₀ ℕ) × (Fin 4 →₀ ℕ)))
  apply le_antisymm
  · apply AddCon.addConGen_le.mpr
    intro x y h
    change (x, y) ∈ N.sourceRelations r s k l at h
    simp only [sourceRelations, Finset.mem_insert, Finset.mem_singleton] at h
    change factorizationMap B.family x = factorizationMap B.family y
    apply Subtype.ext
    change (factorizationMap B.family x).val = (factorizationMap B.family y).val
    rw [← weight_eq_degree, ← weight_eq_degree]
    rcases h with h | h | h
    · cases h
      rw [weight_single, weight_single, N.weight0, N.weight1]; ring
    · cases h
      rw [weight_single, weight_single, N.weight2, N.weight3]; ring
    · cases h
      simp only [map_add, weight_single, N.weight0, N.weight1, N.weight2, N.weight3]
      calc
        r * (N.u * N.alpha) + s * (N.u * N.beta) = N.u * (N.alpha * r + N.beta * s) := by ring
        _ = N.v * (N.gamma * k + N.delta * l) := by rw [← hvr, ← huk, mul_comm]
        _ = k * (N.v * N.gamma) + l * (N.v * N.delta) := by ring
  · intro x y h
    have he : weight B x = weight B y := by
      rw [weight_eq_degree, weight_eq_degree]
      exact congrArg Subtype.val h
    rw [N.weight_expansion x, N.weight_expansion y] at he
    have hfirst : q (N.beta • Finsupp.single (N.perm 0) 1)
        (N.alpha • Finsupp.single (N.perm 1) 1) := by
      apply AddConGen.Rel.of
      simp [sourceRelations, Finsupp.smul_single]
    have hsecond : q (N.delta • Finsupp.single (N.perm 2) 1)
        (N.gamma • Finsupp.single (N.perm 3) 1) := by
      apply AddConGen.Rel.of
      simp [sourceRelations, Finsupp.smul_single]
    have hcross : q (r • Finsupp.single (N.perm 0) 1 + s • Finsupp.single (N.perm 1) 1)
        (k • Finsupp.single (N.perm 2) 1 + l • Finsupp.single (N.perm 3) 1) := by
      apply AddConGen.Rel.of
      simp [sourceRelations, Finsupp.smul_single]
    have hg := gluing_congruence q (Finsupp.single (N.perm 0) 1) (Finsupp.single (N.perm 1) 1)
      (Finsupp.single (N.perm 2) 1) (Finsupp.single (N.perm 3) 1)
      N.u N.v N.alpha N.beta N.gamma N.delta r s k l N.v_pos
      (by have := N.beta_ge; omega) (by have := N.delta_ge; omega)
      N.ab_coprime N.cd_coprime N.uv_coprime hvr huk hfirst hsecond hcross
      (x (N.perm 0)) (x (N.perm 1)) (x (N.perm 2)) (x (N.perm 3))
      (y (N.perm 0)) (y (N.perm 1)) (y (N.perm 2)) (y (N.perm 3)) he
    simpa only [← N.exponent_expansion x, ← N.exponent_expansion y] using hg

theorem sourceRelations_generate_toricIdeal (N : NormalizedPairs B)
    (K : Type*) [Field K] (r s k l : ℕ)
    (hvr : N.v = N.alpha * r + N.beta * s)
    (huk : N.u = N.gamma * k + N.delta * l) :
    relationIdeal K (N.sourceRelations r s k l : Set _) =
      ToricPresentation.toricIdeal K Gamma.toAddSubmonoid B.family := by
  have h := (isPresentation_iff_relationIdeal_eq_ker K B.family (N.sourceRelations r s k l)).mp
    (N.sourceRelations_presentation r s k l hvr huk)
  rw [factorizationAlgebraMap_eq_toricMap] at h
  exact h

theorem symmetric_cross_representations (N : NormalizedPairs B) (he : N.a = N.b) :
    ∃ r s k l : ℕ, N.v = N.alpha * r + N.beta * s ∧ N.u = N.gamma * k + N.delta * l := by
  have hc : N.a.Coprime N.b := reduced_generators_coprime _ _ _ N.ab_coprime
  have hb : N.b = 1 := by simpa [he] using hc
  have ha : N.a = 1 := he.trans hb
  have h1 : 1 ∈ N.T := by
    rw [N.reduced_T]
    apply (mem_twoGenerator _ _ _).mpr
    exact ⟨N.w, 0, by simp [ha, hb]⟩
  obtain ⟨⟨r, s, _, _, hvr⟩, ⟨k, l, _, _, huk⟩⟩ := N.positive_representations 1 h1 (by omega)
  exact ⟨r, s, k, l, by simpa using hvr, by simpa using huk⟩

end NormalizedPairs
end NS25Lean.L4A
