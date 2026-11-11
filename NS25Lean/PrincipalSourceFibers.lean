import NS25Lean.AppendixASources
import NS25Lean.AppendixAChains

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- All components of a minimal-source fiber survive. The unique active
Apéry degree is different, so the whole source fiber is connected. -/
theorem source_component_le_one (F : InternalFrontend k M h) (s : Source M.base) :
    componentCount M.base s.val ≤ 1 := by
  have hne : s.val ≠ h := by
    intro he
    have ha := F.normal.apery
    rw [M.base.apery_eq_compl] at ha
    exact ha.2 (he ▸ s.property.1)
  have hz := F.unique_degree.2 s.val hne
  rw [fiberContribution, ite_eq_left (minimalSource_killedCount_zero M s.val s.property)] at hz
  omega

/-- No shared-coordinate premise: a whole minimal-source fiber is one tie path.
Each graph edge removes a positive generator and lands in actual Apéry. -/
theorem source_presentation_paths (F : InternalFrontend k M h) (s : Source M.base)
    (u v : FactorizationFiber M.base s.val) : TiePath F.normal u.val v.val := by
  classical
  let := Fintype.ofFinite (FiberComponent M.base s.val)
  have : Subsingleton (FiberComponent M.base s.val) :=
    Fintype.card_le_one_iff_subsingleton.mp (by
      simpa only [componentCount, Nat.card_eq_fintype_card] using source_component_le_one F s)
  have hr : (fiberGraph M.base s.val).Reachable u v :=
    SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _)
  have hp := (SimpleGraph.reachable_iff_reflTransGen u v).mp hr
  apply hp.lift' Subtype.val
  intro a b hab
  rcases hab with ⟨_, j, ha, hb⟩
  have hea := removed_weight M.base s.val a j ha
  have heb := removed_weight M.base s.val b j hb
  let a' : FactorizationFiber M.base (s.val - weights M.base j) :=
    ⟨a.val - Finsupp.single j 1, by omega⟩
  let b' : FactorizationFiber M.base (s.val - weights M.base j) :=
    ⟨b.val - Finsupp.single j 1, by omega⟩
  have hi := apery_presentation_paths F _ (source_remove_apery F s a j ha) a' b'
  have hl := tiePath_add F.normal hi (Finsupp.single j 1)
  simpa only [a', b', remove_variable_add a.val j ha,
    remove_variable_add b.val j hb] using hl

theorem source_factorization_difference (F : InternalFrontend k M h)
    (s : Source M.base) (u v : FactorizationFiber M.base s.val) :
    ∃ j : ℤ, ∀ i, (v.val i : ℤ) = (u.val i : ℤ) + j * tieDelta F.normal i :=
  tiePath_integer_difference F.normal (source_presentation_paths F s u v)

def principalTieIdeal {B : Data Gamma} {d : ℕ} (N : TieNormalForm B d) :
    Ideal (ToricPresentation.Poly k 3) :=
  Ideal.span {MvPolynomial.monomial N.alpha.val (1 : k) - MvPolynomial.monomial N.beta.val 1}

theorem tieStep_binomial_mem_principal {B : Data Gamma} {d : ℕ} (N : TieNormalForm B d)
    {u v : Fin 3 →₀ ℕ} (huv : TieStep N u v) :
    MvPolynomial.monomial u (1 : k) - MvPolynomial.monomial v 1 ∈
      principalTieIdeal (k := k) N := by
  have hf : MvPolynomial.monomial N.alpha.val (1 : k) - MvPolynomial.monomial N.beta.val 1 ∈
      principalTieIdeal (k := k) N := Ideal.subset_span rfl
  rcases huv with ⟨t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simpa only [mul_sub, MvPolynomial.monomial_mul, one_mul] using
      (principalTieIdeal (k := k) N).mul_mem_left (MvPolynomial.monomial t (1 : k)) hf
  · simpa only [mul_sub, MvPolynomial.monomial_mul, one_mul, neg_sub] using
      (principalTieIdeal (k := k) N).neg_mem
        ((principalTieIdeal (k := k) N).mul_mem_left (MvPolynomial.monomial t (1 : k)) hf)

theorem tiePath_binomial_mem_principal {B : Data Gamma} {d : ℕ} (N : TieNormalForm B d)
    {u v : Fin 3 →₀ ℕ} (huv : TiePath N u v) :
    MvPolynomial.monomial u (1 : k) - MvPolynomial.monomial v 1 ∈
      principalTieIdeal (k := k) N := by
  induction huv with
  | refl => simp
  | @tail v w _ hvw ih =>
      simpa only [sub_add_sub_cancel] using
        (principalTieIdeal (k := k) N).add_mem ih (tieStep_binomial_mem_principal N hvw)

/-- A whole minimal-source fiber is governed by the principal binomial,
without requiring the two factorizations to share a variable. -/
theorem source_binomial_mem_principal (F : InternalFrontend k M h) (s : Source M.base)
    (u v : FactorizationFiber M.base s.val) :
    MvPolynomial.monomial u.val (1 : k) - MvPolynomial.monomial v.val 1 ∈
      principalTieIdeal (k := k) F.normal :=
  tiePath_binomial_mem_principal F.normal (source_presentation_paths F s u v)

/-- Source fibers have every nonnegative point of one finite integer interval. -/
theorem source_factorization_chain (F : InternalFrontend k M h) (s : Source M.base) :
    ∃ u₀ : FactorizationFiber M.base s.val, ∃ l r : ℤ, l ≤ r ∧
      (∀ v : FactorizationFiber M.base s.val,
        ∃ j : ℤ, l ≤ j ∧ j ≤ r ∧
          ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ) + j * tieDelta F.normal i) ∧
      (∀ j : ℤ, l ≤ j → j ≤ r →
        ∃ v : FactorizationFiber M.base s.val,
          ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ) + j * tieDelta F.normal i) := by
  exact fiber_chain_of_difference F.normal s.val s.property.1.1
    (fun u v=>source_factorization_difference F s u v)

/-- A complete normalized source chain, including zero transverse coordinates. -/
theorem source_normalized_factorization_chain (F : InternalFrontend k M h)
    (s : Source M.base) :
    ∃ u₀ : FactorizationFiber M.base s.val, u₀.val (F.normal.perm 0) < F.normal.a ∧
      ∃ r : ℤ, 0 ≤ r ∧
        (∀ v : FactorizationFiber M.base s.val,
          ∃! j : ℤ, 0 ≤ j ∧ j ≤ r ∧
            ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ) + j * tieDelta F.normal i) ∧
        (∀ j : ℤ, 0 ≤ j → j ≤ r →
          ∃ v : FactorizationFiber M.base s.val,
            ∀ i, (v.val i : ℤ) = (u₀.val i : ℤ) + j * tieDelta F.normal i) := by
  exact normalized_fiber_chain_of_difference k F.normal s.val s.property.1.1
    (fun u v=>source_factorization_difference F s u v)

theorem source_slab_factorization_unique (F : InternalFrontend k M h)
    (s : Source M.base) (u v : FactorizationFiber M.base s.val)
    (hu : u.val (F.normal.perm 0) < F.normal.a)
    (hv : v.val (F.normal.perm 0) < F.normal.a) : u = v := by
  exact slab_unique_of_integer_difference F.normal u v
    (source_factorization_difference F s u v) hu hv

theorem source_unique_normal_form (F : InternalFrontend k M h) (s : Source M.base) :
    ∃! u : FactorizationFiber M.base s.val, u.val (F.normal.perm 0) < F.normal.a := by
  obtain ⟨u, hu, _⟩ := source_normalized_factorization_chain F s
  exact ⟨u, hu, fun v hv => source_slab_factorization_unique F s v u hv hu⟩

end NS25Lean.L3C
