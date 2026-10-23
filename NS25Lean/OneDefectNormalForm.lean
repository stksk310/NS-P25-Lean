import NS25Lean.OneDefectInitial

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3B
open ChosenBase L2B L2B2A L2B2A2 MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem tail_weight_ne_of_avoids (B : Data Gamma) (j : Fin 3) (v : Fin 3 →₀ ℕ)
    (hv : v j = 0) : weight B v ≠ weights B j := by
  intro he
  apply B.degrees_minimal j.succ
  change weights B j ∈ _
  rw [← he, weight_eq_sum]
  apply AddSubmonoid.sum_mem
  intro i _
  by_cases hi : i = j
  · subst i; simp only [hv, zero_mul]; exact AddSubmonoid.zero_mem _
  · have hm : weights B i ∈ AddSubmonoid.closure
        ((fun l => (B.degrees l).val) '' {l | l ≠ j.succ}) :=
      AddSubmonoid.subset_closure ⟨i.succ, fun hh => hi (Fin.succ_inj.mp hh), rfl⟩
    exact (AddSubmonoid.closure _).nsmul_mem hm (v i)

structure TieNormalForm (B : Data Gamma) (h : ℕ) where
  perm : Fin 3 ≃ Fin 3
  a : ℕ
  b : ℕ
  c : ℕ
  a_ge_two : 2 ≤ a
  b_positive : 1 ≤ b
  nontrivial_yz : (b, c) ≠ (1, 0)
  alpha : FactorizationFiber B h
  beta : FactorizationFiber B h
  distinct : alpha ≠ beta
  exactly_two : ∀ u : FactorizationFiber B h, u = alpha ∨ u = beta
  alpha_eq : alpha.val = Finsupp.single (perm 0) a
  beta_eq : beta.val = Finsupp.single (perm 1) b + Finsupp.single (perm 2) c
  apery : h ∈ B.apery

def TieNormalForm.TypeI {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) : Prop := N.c = 0
def TieNormalForm.TypeII {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) : Prop := 0 < N.c

theorem TieNormalForm.type_split {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) :
    N.TypeI ∨ N.TypeII := by unfold TieNormalForm.TypeI TieNormalForm.TypeII; omega

theorem TieNormalForm.degree_equality {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h) :
    N.a * weights B (N.perm 0) = h ∧
      N.b * weights B (N.perm 1) + N.c * weights B (N.perm 2) = h := by
  constructor
  · simpa only [N.alpha_eq, weight_single] using N.alpha.property
  · simpa only [N.beta_eq, map_add, weight_single] using N.beta.property

theorem exists_tie_normal_form (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h) :
    Nonempty (TieNormalForm M.base h) := by
  classical
  have hp : 0 < h := by
    have hc := componentCount_zero_le_one M.base
    have hh := ht.2.2
    by_contra hn
    have he : h = 0 := by omega
    rw [he] at hh
    omega
  let C := activeSingletonOver M ⟨h, hp, by rw [ht.2.2]; omega⟩
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp C.property
  let α : FactorizationFiber M.base h := C.val.out
  have ha : α.val = Finsupp.single j (α.val j) :=
    fiber_eq_single_of_componentSupport M.base h C.val j hj α C.val.out_eq
  obtain ⟨β, hβ, huniq⟩ := (Nat.card_eq_two_iff' α).mp (internal_tie_fiber_card M h hz ht)
  have htwo (u : FactorizationFiber M.base h) : u = α ∨ u = β := by
    by_cases hu : u = α
    · exact Or.inl hu
    · exact Or.inr (huniq u hu)
  have hapos : 0 < α.val j := by
    have hd := α.property
    rw [ha, weight_single] at hd
    nlinarith
  have hβj : β.val j = 0 := by
    rcases internal_tie_disjoint_exponents M h hz ht α β hβ.symm j with hh | hh
    · omega
    · exact hh
  let e₀ : Fin 3 ≃ Fin 3 := Equiv.swap 0 j
  have he0 : e₀ 0 = j := by simp [e₀]
  have hβ0 : β.val (e₀ 0) = 0 := by rwa [he0]
  have hβnonzero : β.val ≠ 0 := by
    intro he
    have hd := β.property
    rw [he, map_zero] at hd
    change 0 = h at hd
    omega
  have hpos : 0 < β.val (e₀ 1) ∨ 0 < β.val (e₀ 2) := by
    by_contra hn
    push Not at hn
    apply hβnonzero
    ext i
    obtain ⟨l, rfl⟩ := e₀.surjective i
    fin_cases l
    · exact hβ0
    · exact Nat.eq_zero_of_le_zero hn.1
    · exact Nat.eq_zero_of_le_zero hn.2
  have hex : ∃ e : Fin 3 ≃ Fin 3, e 0 = j ∧ 0 < β.val (e 1) := by
    rcases hpos with h1 | h2
    · exact ⟨e₀, he0, h1⟩
    · refine ⟨(Equiv.swap 1 2).trans e₀, ?_, ?_⟩
      · simpa [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne] using he0
      · simpa [Equiv.trans_apply] using h2
  obtain ⟨e, he, hb⟩ := hex
  have hbe : β.val = Finsupp.single (e 1) (β.val (e 1)) +
      Finsupp.single (e 2) (β.val (e 2)) := by
    ext i
    obtain ⟨l, rfl⟩ := e.surjective i
    have hβe0 : β.val (e 0) = 0 := by rwa [he]
    fin_cases l <;> simp [Finsupp.add_apply, e.injective.eq_iff, hβe0]
  have haa : 2 ≤ α.val j := by
    have hn := tail_weight_ne_of_avoids M.base j β.val hβj
    have hd := α.property
    rw [ha, weight_single] at hd
    have hdβ := β.property
    by_contra hn2
    have hone : α.val j = 1 := by omega
    rw [hone, one_mul] at hd
    exact hn (hdβ.trans hd.symm)
  have hnt : (β.val (e 1), β.val (e 2)) ≠ (1, 0) := by
    intro hh
    have hb1 := congrArg Prod.fst hh
    have hc0 := congrArg Prod.snd hh
    change β.val (e 1) = 1 at hb1
    change β.val (e 2) = 0 at hc0
    have hα1 : α.val (e 1) = 0 := by
      rw [ha, ← he]
      simp [e.injective.eq_iff]
    have hn := tail_weight_ne_of_avoids M.base (e 1) α.val hα1
    have hd := β.property
    rw [hbe, map_add, weight_single, weight_single, hb1, hc0] at hd
    simp only [one_mul, zero_mul, add_zero] at hd
    exact hn (α.property.trans hd.symm)
  exact ⟨⟨e, α.val j, β.val (e 1), β.val (e 2), haa, hb, hnt,
    α, β, hβ.symm, htwo, by rwa [he], hbe, ht.1⟩⟩

/-- An explicit permutation of polynomial variables realizes the displayed normal form. -/
theorem TieNormalForm.polynomial {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (k : Type*) [Field k] :
    monomial N.alpha.val (1 : k) - monomial N.beta.val 1 =
      rename N.perm (X (0 : Fin 3) ^ N.a - X 1 ^ N.b * X 2 ^ N.c) := by
  rw [N.alpha_eq, N.beta_eq]
  simp [X_pow_eq_monomial, monomial_mul, rename_monomial, Finsupp.mapDomain_add, Finsupp.mapDomain_single]

end NS25Lean.L3B

