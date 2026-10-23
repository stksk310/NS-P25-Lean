import NS25Lean.OneDefectTransfer
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3B
open ChosenBase L2B L2B2A L2B2A2 MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem one_defect_sum (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 1) :
    ∑ h ∈ activeDegreeFinset M, fiberContribution M h = 1 :=
  (chosenDefect_eq_contribution_sum M).symm.trans hp

/-- Uniqueness is over all natural degrees, including degrees outside the finite active set. -/
theorem unique_active_degree (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 1) :
    ∃ h, fiberContribution M h = 1 ∧ ∀ d, d ≠ h → fiberContribution M d = 0 := by
  classical
  have hs := one_defect_sum M hp
  obtain ⟨h, hh, hpos⟩ : ∃ h ∈ activeDegreeFinset M, 0 < fiberContribution M h := by
    by_contra hn
    push Not at hn
    have hz : ∑ h ∈ activeDegreeFinset M, fiberContribution M h = 0 :=
      Finset.sum_eq_zero (fun d hd => Nat.eq_zero_of_le_zero (hn d hd))
    omega
  have hb := Finset.single_le_sum (fun d _ => Nat.zero_le (fiberContribution M d)) hh
  have he : fiberContribution M h = 1 := by omega
  refine ⟨h, he, ?_⟩
  intro d hdh
  by_cases hd : d ∈ activeDegreeFinset M
  · have herase := Finset.sum_erase_add (activeDegreeFinset M) (fiberContribution M) hh
    have hbd := Finset.single_le_sum (fun i _ => Nat.zero_le (fiberContribution M i))
      (Finset.mem_erase.mpr ⟨hdh, hd⟩)
    omega
  · exact contribution_zero_outside_active M d hd

theorem removed_weight (B : Data Gamma) (h : ℕ) (u : FactorizationFiber B h)
    (j : Fin 3) (hj : 0 < u.val j) :
    weights B j + weight B (u.val - Finsupp.single j 1) = h := by
  have he := congrArg (weight B) (remove_variable_add u.val j hj)
  simpa only [map_add, weight_single, one_mul, u.property] using he

theorem killed_mem_K (M : MultiplicityBase Gamma) (h : ℕ)
    (C : FiberComponent M.base h) (hC : BoundaryKilled M h C) : h ∈ M.base.K := by
  obtain ⟨u, _, j, hj, hk⟩ := hC
  have he := removed_weight M.base h u j hj
  have hs : h - weights M.base j + weights M.base j = h := by omega
  rw [← hs]
  exact FourGeneratedBridge.aperyTail_add_mem M.base.H_le hk (M.base.tailDegrees j).property

theorem apery_killedCount_zero (M : MultiplicityBase Gamma) (h : ℕ)
    (ha : h ∈ M.base.apery) : killedCount M h = 0 := by
  have hn : h ∉ M.base.K := ((M.base.apery_eq_compl ▸ ha) :
    h ∈ {d | d ∈ M.base.H ∧ d ∉ M.base.K}).2
  haveI : IsEmpty {C : FiberComponent M.base h // BoundaryKilled M h C} :=
    ⟨fun C => hn (killed_mem_K M h C.val C.property)⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

def MonomializableAt (M : MultiplicityBase Gamma) (h : ℕ) : Prop :=
  (h ∈ M.base.K ∧ killedCount M h = 0 ∧ componentCount M.base h = 2) ∨
    (0 < killedCount M h ∧ componentCount M.base h - killedCount M h = 1)

def InternalTieAt (M : MultiplicityBase Gamma) (h : ℕ) : Prop :=
  h ∈ M.base.apery ∧ killedCount M h = 0 ∧ componentCount M.base h = 2

theorem local_one_defect_split (M : MultiplicityBase Gamma) (h : ℕ)
    (hp : fiberContribution M h = 1) : MonomializableAt M h ∨ InternalTieAt M h := by
  classical
  by_cases hk : killedCount M h = 0
  · have hc : componentCount M.base h = 2 := by
      rw [fiberContribution, if_pos hk] at hp; omega
    by_cases hb : h ∈ M.base.K
    · exact Or.inl (Or.inl ⟨hb, hk, hc⟩)
    · have hpos : 0 < Nat.card (FiberComponent M.base h) := by
        change 0 < componentCount M.base h; omega
      obtain ⟨C⟩ := (Nat.card_pos_iff.mp hpos).1
      have hH : h ∈ M.base.H := by
        rw [← C.out.property, weight_eq_degree]
        exact (Presentation.factorizationMap M.base.tailDegrees C.out.val).property
      exact Or.inr ⟨M.base.apery_eq_compl.symm ▸ ⟨hH, hb⟩, hk, hc⟩
  · exact Or.inl (Or.inr ⟨Nat.pos_of_ne_zero hk, by
      simpa only [fiberContribution, if_neg hk] using hp⟩)

theorem split_disjoint (M : MultiplicityBase Gamma) (h : ℕ) :
    ¬ (MonomializableAt M h ∧ InternalTieAt M h) := by
  rintro ⟨hb, ha, hz, _⟩
  rcases hb with ⟨hk, _, _⟩ | ⟨hd, _⟩
  · rw [M.base.apery_eq_compl] at ha
    exact ha.2 hk
  · omega

theorem apery_remove (B : Data Gamma) (h : ℕ) (ha : h ∈ B.apery)
    (u : FactorizationFiber B h) (j : Fin 3) (hj : 0 < u.val j) :
    h - weights B j ∈ B.apery := by
  have he := removed_weight B h u j hj
  have hw : weight B (u.val - Finsupp.single j 1) = h - weights B j := by omega
  rw [B.apery_eq_compl] at ha ⊢
  refine ⟨?_, ?_⟩
  · rw [← hw, weight_eq_degree]
    exact (Presentation.factorizationMap B.tailDegrees _).property
  · intro hk
    apply ha.2
    have hh := FourGeneratedBridge.aperyTail_add_mem B.H_le hk (B.tailDegrees j).property
    have hs : h - weights B j + weights B j = h := by omega
    change h - weights B j + weights B j ∈ B.K at hh
    rwa [hs] at hh

theorem graph_bot_of_lower_unique (B : Data Gamma) (h : ℕ) (ha : h ∈ B.apery)
    (hl : ∀ d, d < h → d ∈ B.apery → Subsingleton (FactorizationFiber B d)) :
    fiberGraph B h = ⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj, iff_false]
  rintro ⟨hne, j, hu, hv⟩
  have heu := removed_weight B h u j hu
  have hev := removed_weight B h v j hv
  have hp := weights_positive B j
  let u' : FactorizationFiber B (h - weights B j) :=
    ⟨u.val - Finsupp.single j 1, by omega⟩
  let v' : FactorizationFiber B (h - weights B j) :=
    ⟨v.val - Finsupp.single j 1, by omega⟩
  have he := congrArg Subtype.val
    ((hl _ (by omega) (apery_remove B h ha u j hu)).elim u' v')
  apply hne
  apply Subtype.ext
  have he' := congrArg (fun w => Finsupp.single j 1 + w) he
  simpa only [u', v', remove_variable_add u.val j hu, remove_variable_add v.val j hv] using he'

theorem fiber_unique_of_graph_bot_count (B : Data Gamma) (h : ℕ)
    (hg : fiberGraph B h = ⊥) (hc : componentCount B h ≤ 1) :
    Subsingleton (FactorizationFiber B h) := by
  classical
  letI := Fintype.ofFinite (FiberComponent B h)
  haveI : Subsingleton (FiberComponent B h) :=
    Fintype.card_le_one_iff_subsingleton.mp (by
      simpa only [componentCount, Nat.card_eq_fintype_card] using hc)
  refine ⟨fun u v => ?_⟩
  have hr : (fiberGraph B h).Reachable u v :=
    SimpleGraph.ConnectedComponent.exact (Subsingleton.elim _ _)
  simpa only [hg, SimpleGraph.reachable_bot] using hr

theorem apery_fiber_unique_below (B : Data Gamma) (N : ℕ)
    (hc : ∀ d, d < N → d ∈ B.apery → componentCount B d ≤ 1)
    (d : ℕ) (hd : d < N) (ha : d ∈ B.apery) : Subsingleton (FactorizationFiber B d) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    apply fiber_unique_of_graph_bot_count B d
      (graph_bot_of_lower_unique B d ha (fun e he hae => ih e he (by omega) hae)) (hc d hd ha)

theorem monomializable_not_apery (M : MultiplicityBase Gamma) (h : ℕ)
    (hb : MonomializableAt M h) : h ∉ M.base.apery := by
  intro ha
  rcases hb with ⟨hk, _, _⟩ | ⟨hd, _⟩
  · rw [M.base.apery_eq_compl] at ha; exact ha.2 hk
  · have := apery_killedCount_zero M h ha; omega

theorem apery_component_le_one (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : fiberContribution M h = 0) (ha : h ∈ M.base.apery) :
    componentCount M.base h ≤ 1 := by
  rw [fiberContribution, if_pos (apery_killedCount_zero M h ha)] at hz
  omega

/-- The monomializable cases imply actual monomial generation of the kernel J. -/
theorem monomializable_J (k : Type*) [Field k] (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (hb : MonomializableAt M h) :
    IsMonomialIdeal k (M.base.J k) := by
  have hc (d : ℕ) (ha : d ∈ M.base.apery) : componentCount M.base d ≤ 1 :=
    apery_component_le_one M d (hz d (fun he => monomializable_not_apery M h hb (he ▸ ha))) ha
  have hunique (d : ℕ) (ha : d ∈ M.base.apery) : Subsingleton (FactorizationFiber M.base d) :=
    apery_fiber_unique_below M.base (d + 1) (fun e _ => hc e) d (by omega) ha
  have he : M.base.J k = M.base.MK k := by
    rw [M.base.J_eq_IH_sup_MK k]
    apply sup_eq_right.mpr
    rw [IH_eq_relationIdeal, Presentation.relationIdeal]
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨u, v⟩, huv, rfl⟩
    change weight M.base u = weight M.base v at huv
    change monomial u (1 : k) - monomial v 1 ∈ M.base.MK k
    by_cases hu : weight M.base u ∈ M.base.K
    · apply (M.base.MK k).sub_mem
      · exact Ideal.subset_span ⟨u, by simpa only [Set.mem_setOf_eq, ← weight_eq_degree] using hu, rfl⟩
      · exact Ideal.subset_span ⟨v, by simpa only [Set.mem_setOf_eq, ← weight_eq_degree, ← huv] using hu, rfl⟩
    · have ha : weight M.base u ∈ M.base.apery := by
        rw [M.base.apery_eq_compl]
        exact ⟨(weight_eq_degree M.base u).symm ▸
          (Presentation.factorizationMap M.base.tailDegrees u).property, hu⟩
      have heq : u = v := congrArg Subtype.val
        ((hunique _ ha).elim ⟨u, rfl⟩ ⟨v, huv.symm⟩)
      simp only [heq, sub_self, Ideal.zero_mem]
  rw [he]
  exact ⟨_, rfl⟩

theorem transferred_monomializable_bound (k : Type*) [Field k] (B : Data Gamma)
    (hp : chosenDefect B = 1) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution (transferBase B) d = 0)
    (hb : MonomializableAt (transferBase B) h) :
    Gamma.asRelativeIdeal.idealType ≤ sourceCount B ∧
      sourceCount B = Presentation.rho Gamma - 1 := by
  have ht := one_defect_transfer k B hp
  have hbnd := L3A.monomial_pivot_type_bound (transferBase B).base
    (monomializable_J k (transferBase B) h hz hb)
  rw [ht.2.2.2.2.1, ht.2.2.2.1] at hbnd
  exact ⟨(one_defect_sourceCount B hp).symm ▸ hbnd, one_defect_sourceCount B hp⟩

end NS25Lean.L3B

