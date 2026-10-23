import NS25Lean.FourBaseBudget
import NS25Lean.WeightedRefinement
import NS25Lean.DilationIdeals

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase FourGeneratedBridge MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem weight_mem (B : Data Gamma) (u : Fin 4 →₀ ℕ) : weight B u ∈ Gamma := by
  rw [weight_eq_degree]
  exact (Presentation.factorizationMap B.family u).property

theorem apery_pivot_coordinate_zero (B : Data Gamma) (d : ℕ) (hd : d ∈ B.apery)
    (u : FactorizationFiber B d) : u.val B.pivot = 0 := by
  by_contra hn
  have he := remove_copies B u.val B.pivot 1 (Nat.pos_of_ne_zero hn)
  rw [one_mul, u.property] at he
  have hq : weights B B.pivot = B.q.val := rfl
  rw [hq] at he
  have hm := weight_mem B (u.val - Finsupp.single B.pivot 1)
  change d ∈ aperySet Gamma.toAddSubmonoid B.q.val at hd
  rcases hd.2 with hlt | hnot
  · omega
  · apply hnot
    have he' : weight B (u.val - Finsupp.single B.pivot 1) = d - B.q.val := by omega
    rw [← he']
    exact hm

theorem apery_avoids_pivot (B : Data Gamma) (d : ℕ) (hd : d ∈ B.apery) :
    B.pivot ∉ fiberVariables B d := by
  intro hi
  obtain ⟨u, hu⟩ := (mem_variables B d B.pivot).mp hi
  rw [apery_pivot_coordinate_zero B d hd u] at hu
  omega

theorem apery_remove_variable (B : Data Gamma) (d : ℕ) (hd : d ∈ B.apery)
    (u : FactorizationFiber B d) (j : Fin 4) (hj : 0 < u.val j) :
    d - weights B j ∈ B.apery := by
  have he := remove_copies B u.val j 1 hj
  rw [one_mul, u.property] at he
  have hm : d - weights B j ∈ Gamma := by
    convert weight_mem B (u.val - Finsupp.single j 1) using 1 <;> omega
  refine ⟨hm, ?_⟩
  by_cases hlt : d - weights B j < B.q.val
  · exact Or.inl hlt
  · right
    intro hn
    have ha := Gamma.toAddSubmonoid.add_mem hn (B.family j).property
    have hd' : d - B.q.val ∈ Gamma := by
      have he' : d - B.q.val = d - weights B j - B.q.val + (B.family j).val := by
        change d - B.q.val = d - weights B j - B.q.val + weights B j
        omega
      rw [he']; exact ha
    rcases hd.2 with hq | hq
    · omega
    · exact hq hd'

/-- Strong induction is the least-bad-Apéry-degree argument: a shared variable
would give two distinct factorizations at a strictly smaller Apéry degree. -/
theorem apery_fiber_subsingleton (B : Data Gamma)
    (hz : internalLoad B B.pivot = 0) (d : ℕ) (hd : d ∈ B.apery) :
    Subsingleton (FactorizationFiber B d) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    have hadj : ∀ u v : FactorizationFiber B d, ¬ (fiberGraph B d).Adj u v := by
      intro u v huv
      obtain ⟨hne, j, hu, hv⟩ := huv
      have heu := remove_copies B u.val j 1 hu
      have hev := remove_copies B v.val j 1 hv
      rw [one_mul, u.property] at heu
      rw [one_mul, v.property] at hev
      let u' : FactorizationFiber B (d - weights B j) :=
        ⟨u.val - Finsupp.single j 1, by omega⟩
      let v' : FactorizationFiber B (d - weights B j) :=
        ⟨v.val - Finsupp.single j 1, by omega⟩
      have hp := weights_positive B j
      have hsub := ih (d - weights B j) (by omega) (apery_remove_variable B d hd u j hu)
      have he : u'.val = v'.val := congrArg Subtype.val (hsub.elim u' v')
      apply hne
      apply Subtype.ext
      ext i
      have hei := DFunLike.congr_fun he i
      simp only [u', v', Finsupp.tsub_apply] at hei
      by_cases hij : i = j
      · subst i; simp only [Finsupp.single_eq_same] at hei; omega
      · simpa [Finsupp.single_eq_of_ne hij] using hei
    have hb := not_betti_of_internalLoad_zero B B.pivot hz d (apery_avoids_pivot B d hd)
    haveI : Subsingleton (FiberComponent B d) :=
      not_nontrivial_iff_subsingleton.mp (fun h => hb ((betti_iff_nontrivial B d).mpr h))
    refine ⟨fun u v => ?_⟩
    have hr : (fiberGraph B d).Reachable u v :=
      SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _)
    have hg : fiberGraph B d = ⊥ := by
      ext a b
      simp only [SimpleGraph.bot_adj, iff_false]
      exact hadj a b
    rw [hg, SimpleGraph.reachable_bot] at hr
    exact hr

def tailLift (B : Data Gamma) : (Fin 3 →₀ ℕ) →+ (Fin 4 →₀ ℕ) :=
  Finsupp.mapDomain.addMonoidHom (fun j : Fin 3 => B.order j.succ)

theorem tailLift_injective (B : Data Gamma) : Function.Injective (tailLift B) :=
  Finsupp.mapDomain_injective (B.order.injective.comp (Fin.succ_injective 3))

theorem weight_tailLift (B : Data Gamma) (u : Fin 3 →₀ ℕ) :
    weight B (tailLift B u) = L2B.weight B u := by
  have he : (weight B).comp (tailLift B) = L2B.weight B := by
    apply Finsupp.addHom_ext
    intro j n
    change weight B (Finsupp.mapDomain _ (Finsupp.single j n)) = _
    rw [Finsupp.mapDomain_single, weight_single]
    simp only [L2B.weight, Finsupp.weight_single, smul_eq_mul]
    rfl
  exact DFunLike.congr_fun he u

theorem apery_tail_unique (B : Data Gamma) (hz : internalLoad B B.pivot = 0)
    (u v : Fin 3 →₀ ℕ) (he : L2B.weight B u = L2B.weight B v)
    (hu : L2B.weight B u ∈ B.apery) : u = v := by
  have hs := apery_fiber_subsingleton B hz (L2B.weight B u) hu
  apply tailLift_injective B
  exact congrArg Subtype.val (hs.elim
    ⟨tailLift B u, weight_tailLift B u⟩
    ⟨tailLift B v, (weight_tailLift B v).trans he.symm⟩)

theorem J_eq_MK_of_internalLoad_zero (k : Type*) [Field k] (B : Data Gamma)
    (hz : internalLoad B B.pivot = 0) : B.J k = B.MK k := by
  rw [B.J_eq_IH_sup_MK k]
  apply sup_eq_right.mpr
  rw [L2B.IH_eq_relationIdeal, Presentation.relationIdeal]
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨u, v⟩, he, rfl⟩
  change L2B.weight B u = L2B.weight B v at he
  change monomial u (1 : k) - monomial v 1 ∈ B.MK k
  by_cases hu : L2B.weight B u ∈ B.K
  · apply (B.MK k).sub_mem
    · exact Ideal.subset_span ⟨u, by simpa only [Set.mem_setOf_eq, ← L2B.weight_eq_degree] using hu, rfl⟩
    · exact Ideal.subset_span ⟨v, by simpa only [Set.mem_setOf_eq, ← L2B.weight_eq_degree, ← he] using hu, rfl⟩
  · have ha : L2B.weight B u ∈ B.apery := by
      rw [B.apery_eq_compl]
      exact ⟨(L2B.weight_eq_degree B u).symm ▸
        (Presentation.factorizationMap B.tailDegrees u).property, hu⟩
    rw [apery_tail_unique B hz u v he ha, sub_self]
    exact Ideal.zero_mem _

/-- Actual monomial generation of the chosen-base ideal, for every coefficient field. -/
theorem monomial_pivot (k : Type*) [Field k] (B : Data Gamma)
    (hz : internalLoad B B.pivot = 0) : L2B.IsMonomialIdeal k (B.J k) := by
  rw [J_eq_MK_of_internalLoad_zero k B hz]
  exact ⟨_, rfl⟩

/-- Direct instantiation of frozen W6 with the proved monomial pivot. -/
theorem monomial_pivot_W6 (k : Type*) [Field k] (B : Data Gamma)
    (hz : internalLoad B B.pivot = 0) (m : MonomialOrder (Fin 3)) :
    B.J k = L2B.monomialInitialIdeal k (L2B.weightRefinement B m) (L2B.latticeIdeal k B) :=
  L2B.monomial_J_eq_refinement k B m (monomial_pivot k B hz)

end NS25Lean.L2C
