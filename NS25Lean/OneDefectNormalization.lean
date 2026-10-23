import NS25Lean.OneDefectNormalForm

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3B
open ChosenBase L2B L2B2A L2B2A2 MvPolynomial
open scoped MonomialOrder
variable {Gamma : NumericalSemigroup}

def permutationOrder (e : Fin 3 ≃ Fin 3) : MonomialOrder (Fin 3) where
  syn := (MonomialOrder.lex (σ := Fin 3)).syn
  toSyn := (Finsupp.domCongr e.symm).trans MonomialOrder.lex.toSyn
  toSyn_monotone := by
    intro u v huv
    change toLex (Finsupp.domCongr e.symm u) ≤ toLex (Finsupp.domCongr e.symm v)
    apply Finsupp.toLex_monotone
    intro i
    change u (e i) ≤ v (e i)
    exact huv (e i)

theorem TieNormalForm.order_tie {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) :
    N.beta.val ≺[permutationOrder N.perm] N.alpha.val := by
  change toLex (Finsupp.domCongr N.perm.symm N.beta.val) <
    toLex (Finsupp.domCongr N.perm.symm N.alpha.val)
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    exact (Fin.not_lt_zero j hj).elim
  · change N.beta.val (N.perm 0) < N.alpha.val (N.perm 0)
    rw [N.alpha_eq, N.beta_eq]
    simpa [N.perm.injective.eq_iff] using lt_of_lt_of_le (by decide : 0 < 2) N.a_ge_two

def permutedJ (k : Type*) [Field k] (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Ideal (ToricPresentation.Poly k 3) := (B.J k).map (renameEquiv k e.symm).toRingHom

def permutationQuotientEquiv (k : Type*) [Field k] (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    (ToricPresentation.Poly k 3 ⧸ B.J k) ≃ₐ[k]
      (ToricPresentation.Poly k 3 ⧸ permutedJ k B e) :=
  Ideal.quotientEquivAlg _ _ (renameEquiv k e.symm) rfl

theorem permutation_tail_semigroup (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    AddSubmonoid.closure (Set.range (fun i => weights B (e i))) = B.H := by
  have he : Set.range (fun i => weights B (e i)) = Set.range (weights B) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨e.symm i, by simp⟩
  rw [he]
  rfl

/-- Repeated substitution of the actual tie. This is only division with remainder,
and makes no assertion about excess initial generators or wrap terms. -/
theorem TieNormalForm.normalize_monomial {B : Data Gamma} {h : ℕ}
    (N : TieNormalForm B h) (k : Type*) [Field k] (u : Fin 3 →₀ ℕ) :
    ∃ v : Fin 3 →₀ ℕ, v (N.perm 0) < N.a ∧ weight B v = weight B u ∧
      monomial u (1 : k) - monomial v 1 ∈
        Ideal.span {monomial N.alpha.val (1 : k) - monomial N.beta.val 1} := by
  classical
  generalize he : u (N.perm 0) = n
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
    by_cases hlt : n < N.a
    · exact ⟨u, by omega, rfl, by simp⟩
    · have ha : N.alpha.val ≤ u := by
        rw [N.alpha_eq]
        exact Finsupp.single_le_iff.mpr (by omega)
      let w := u - N.alpha.val
      let v₁ := w + N.beta.val
      have hu : w + N.alpha.val = u := tsub_add_cancel_of_le ha
      have hβx : N.beta.val (N.perm 0) = 0 := by
        rw [N.beta_eq]
        simp [N.perm.injective.eq_iff]
      have hαx : N.alpha.val (N.perm 0) = N.a := by rw [N.alpha_eq]; simp
      have hvx : v₁ (N.perm 0) = n - N.a := by
        simp only [v₁, w, Finsupp.add_apply, Finsupp.tsub_apply, hβx, add_zero, hαx, he]
      have hsmall : n - N.a < n := by have := N.a_ge_two; omega
      have hvdeg : weight B v₁ = weight B u := by
        have hu' := congrArg (weight B) hu
        simp only [map_add, N.alpha.property] at hu'
        simpa only [v₁, map_add, N.beta.property] using hu'
      have hdiff : monomial u (1 : k) - monomial v₁ 1 ∈
          Ideal.span {monomial N.alpha.val (1 : k) - monomial N.beta.val 1} := by
        have hm := (Ideal.span {monomial N.alpha.val (1 : k) - monomial N.beta.val 1}).mul_mem_left
          (monomial w 1) (Ideal.subset_span (Set.mem_singleton _))
        simpa only [mul_sub, monomial_mul, one_mul, hu, v₁] using hm
      obtain ⟨v, hv, hdeg, hrel⟩ := ih _ hsmall v₁ hvx
      refine ⟨v, hv, hdeg.trans hvdeg, ?_⟩
      simpa only [sub_add_sub_cancel] using
        (Ideal.span {monomial N.alpha.val (1 : k) - monomial N.beta.val 1}).add_mem hdiff hrel

theorem exponent_three_coordinates (e : Fin 3 ≃ Fin 3) (v : Fin 3 →₀ ℕ) :
    v = Finsupp.single (e 0) (v (e 0)) + Finsupp.single (e 1) (v (e 1)) +
      Finsupp.single (e 2) (v (e 2)) := by
  ext j
  obtain ⟨i, rfl⟩ := e.surjective j
  fin_cases i <;> simp [Finsupp.add_apply, e.injective.eq_iff]

/-- Source degree is preserved, and the x exponent is strictly less than a. -/
theorem TieNormalForm.source_normalization {B : Data Gamma} {h : ℕ}
    (N : TieNormalForm B h) (k : Type*) [Field k] (s : Source B) :
    ∃ r b c : ℕ, r < N.a ∧
      weight B (Finsupp.single (N.perm 0) r + Finsupp.single (N.perm 1) b +
        Finsupp.single (N.perm 2) c) = s.val ∧
      sourcePolynomial k B s -
        (X (N.perm 0) ^ r * (X (N.perm 1) ^ b * X (N.perm 2) ^ c)) ∈
        Ideal.span {monomial N.alpha.val (1 : k) - monomial N.beta.val 1} := by
  obtain ⟨v, hv, hd, hr⟩ := N.normalize_monomial k (sourceRepresentative B s).val
  refine ⟨v (N.perm 0), v (N.perm 1), v (N.perm 2), hv, ?_, ?_⟩
  · rw [← exponent_three_coordinates N.perm v]
    exact hd.trans (sourceRepresentative B s).property
  · have hm : X (N.perm 0) ^ v (N.perm 0) *
        (X (N.perm 1) ^ v (N.perm 1) * X (N.perm 2) ^ v (N.perm 2)) = monomial v (1 : k) := by
      simp only [X_pow_eq_monomial, monomial_mul, one_mul]
      rw [← add_assoc, ← exponent_three_coordinates N.perm v]
    rw [hm]
    exact hr

end NS25Lean.L3B

