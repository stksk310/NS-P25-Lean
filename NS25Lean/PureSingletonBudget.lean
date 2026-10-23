import NS25Lean.FiberSupportPartition

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase
variable {Gamma : NumericalSemigroup}

theorem fiber_eq_single_of_componentSupport (B : Data Gamma) (h : ℕ)
    (C : FiberComponent B h) (j : Fin 3) (hs : componentSupport B h C = {j})
    (u : FactorizationFiber B h) (hu : (fiberGraph B h).connectedComponentMk u = C) :
    u.val = Finsupp.single j (u.val j) := by
  classical
  ext i
  by_cases he : i = j
  · subst i; simp
  · rw [Finsupp.single_eq_of_ne he]
    by_contra hn
    have hi := (mem_componentSupport B h C i).mpr ⟨u, hu, Nat.pos_of_ne_zero hn⟩
    rw [hs, Finset.mem_singleton] at hi
    exact he hi

theorem weight_single (B : Data Gamma) (j : Fin 3) (r : ℕ) :
    weight B (Finsupp.single j r) = r * weights B j := by
  simp [weight, Finsupp.weight_single, smul_eq_mul]

theorem singleton_component_degree_not_lt (B : Data Gamma) (h g : ℕ)
    (hh : 0 < h) (hc : 1 < componentCount B h)
    (C : FiberComponent B h) (E : FiberComponent B g) (j : Fin 3)
    (hC : componentSupport B h C = {j}) (hE : componentSupport B g E = {j}) : ¬ h < g := by
  classical
  intro hlt
  obtain ⟨u, hu⟩ := C.exists_rep
  obtain ⟨w, hw⟩ := E.exists_rep
  have hu' := fiber_eq_single_of_componentSupport B h C j hC u hu
  have hw' := fiber_eq_single_of_componentSupport B g E j hE w hw
  have hdeg : h = u.val j * weights B j :=
    u.property.symm.trans ((congrArg (weight B) hu').trans (weight_single B j _))
  have gdeg : g = w.val j * weights B j :=
    w.property.symm.trans ((congrArg (weight B) hw').trans (weight_single B j _))
  have hlt' : u.val j < w.val j := by
    have hp := weights_positive B j
    nlinarith
  haveI : Nontrivial (FiberComponent B h) := by
    by_contra hn
    haveI : Subsingleton (FiberComponent B h) := not_nontrivial_iff_subsingleton.mp hn
    have hz : Nat.card (FiberComponent B h) ≤ 1 := by
      simpa using Nat.card_le_card_of_injective (fun _ : FiberComponent B h => ())
        (fun x y _ => Subsingleton.elim x y)
    change 1 < Nat.card (FiberComponent B h) at hc
    omega
  obtain ⟨F, hF⟩ := exists_ne C
  obtain ⟨v, hv⟩ := F.exists_rep
  have hvj : v.val j = 0 := by
    by_contra hn
    have hjF := (mem_componentSupport B h F j).mpr ⟨v, hv, Nat.pos_of_ne_zero hn⟩
    have hjC : j ∈ componentSupport B h C := by simp [hC]
    exact hF (components_eq_of_shared_support B h F C j hjF hjC)
  have hex : ∃ i : Fin 3, 0 < v.val i := by
    by_contra hn
    push Not at hn
    have hz : v.val = 0 := by ext i; change v.val i = 0; exact Nat.eq_zero_of_le_zero (hn i)
    have he := v.property
    rw [hz, map_zero] at he
    omega
  obtain ⟨i, hi⟩ := hex
  have hij : i ≠ j := by intro he; subst i; omega
  let z : FactorizationFiber B g := ⟨v.val + Finsupp.single j (w.val j - u.val j), by
    rw [map_add, weight_single]
    have hvd := v.property
    have hs := Nat.sub_add_cancel (le_of_lt hlt')
    have hp := weights_positive B j
    nlinarith⟩
  have hzj : 0 < z.val j := by simp only [z, Finsupp.add_apply, Finsupp.single_eq_same]; omega
  have hwj : 0 < w.val j := by omega
  have hzE : (fiberGraph B g).connectedComponentMk z = E := by
    by_cases he : z = w
    · exact he ▸ hw
    · have ha : (fiberGraph B g).Adj z w := ⟨he, j, hzj, hwj⟩
      exact (SimpleGraph.ConnectedComponent.sound ha.reachable).trans hw
  have hzi : 0 < z.val i := by
    simp only [z, Finsupp.add_apply, Finsupp.single_eq_of_ne hij, add_zero]
    exact hi
  have hiE := (mem_componentSupport B g E i).mpr ⟨z, hzE, hzi⟩
  rw [hE, Finset.mem_singleton] at hiE
  exact hij hiE

/-- A tail variable can support a pure component at only one active degree. -/
theorem singleton_active_degree_unique (B : Data Gamma) (h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hc : 1 < componentCount B h) (gc : 1 < componentCount B g)
    (C : FiberComponent B h) (E : FiberComponent B g) (j : Fin 3)
    (hC : componentSupport B h C = {j}) (hE : componentSupport B g E = {j}) : h = g := by
  have h₁ := singleton_component_degree_not_lt B h g hh hc C E j hC hE
  have h₂ := singleton_component_degree_not_lt B g h hg gc E C j hE hC
  omega

def ActiveDegree (B : Data Gamma) := {h : ℕ // 0 < h ∧ 1 < componentCount B h}

def ActiveSingleton (B : Data Gamma) :=
  Sigma (fun h : ActiveDegree B =>
    {C : FiberComponent B h.val // (componentSupport B h.val C).card = 1})

def singletonVariable (B : Data Gamma) (x : ActiveSingleton B) : Fin 3 :=
  Classical.choose (Finset.card_eq_one.mp x.2.property)

theorem singletonVariable_support (B : Data Gamma) (x : ActiveSingleton B) :
    componentSupport B x.1.val x.2.val = {singletonVariable B x} :=
  Classical.choose_spec (Finset.card_eq_one.mp x.2.property)

theorem singletonVariable_injective (B : Data Gamma) : Function.Injective (singletonVariable B) := by
  classical
  rintro ⟨⟨h, hh, hc⟩, C, hC⟩ ⟨⟨g, hg, gc⟩, E, hE⟩ he
  have hsC := singletonVariable_support B ⟨⟨h, hh, hc⟩, C, hC⟩
  have hsE := singletonVariable_support B ⟨⟨g, hg, gc⟩, E, hE⟩
  have hsE' := hsE.trans (congrArg (fun j : Fin 3 => ({j} : Finset (Fin 3))) he.symm)
  have hge := singleton_active_degree_unique B h g hh hg hc gc C E _ hsC hsE'
  subst g
  have hCE : C = E := by
    apply components_eq_of_shared_support B h C E (singletonVariable B ⟨⟨h, hh, hc⟩, C, hC⟩)
    · simp [hsC]
    · simp [hsE']
  subst E
  rfl

instance finiteActiveSingletons (B : Data Gamma) : Finite (ActiveSingleton B) :=
  Finite.of_injective (singletonVariable B) (singletonVariable_injective B)

/-- The total number of pure singleton components across all active degrees is at most three. -/
theorem active_singletons_card_le_three (B : Data Gamma) : Nat.card (ActiveSingleton B) ≤ 3 :=
  (Nat.card_le_card_of_injective _ (singletonVariable_injective B)).trans_eq (by simp)

theorem singleton_sum_le_three (M : MultiplicityBase Gamma) (s : Finset ℕ)
    (hs : ∀ h ∈ s, 0 < h ∧ 1 < componentCount M.base h) :
    ∑ h ∈ s, singletonComponentCount M h ≤ 3 := by
  classical
  let F := Sigma (fun h : s =>
    {C : FiberComponent M.base h.val // (componentSupport M.base h.val C).card = 1})
  letI (h : s) := Fintype.ofFinite
    {C : FiberComponent M.base h.val // (componentSupport M.base h.val C).card = 1}
  let f : F → ActiveSingleton M.base := fun x => ⟨⟨x.1.val, hs x.1.val x.1.property⟩, x.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨h, hh⟩, C⟩ ⟨⟨g, hg⟩, E⟩ he
    have hge : h = g := congrArg (fun x : ActiveSingleton M.base => x.1.val) he
    subst g
    have hCE : C = E := by
      change (⟨⟨h, hs h hh⟩, C⟩ : ActiveSingleton M.base) =
        (⟨⟨h, hs h hg⟩, E⟩ : ActiveSingleton M.base) at he
      exact eq_of_heq (Sigma.mk.inj he).2
    subst E
    rfl
  have hcard := (Nat.card_le_card_of_injective f hf).trans (active_singletons_card_le_three M.base)
  have he : Nat.card F = ∑ h ∈ s, singletonComponentCount M h := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Sigma (fun h : s => _)) = _
    rw [Fintype.card_sigma]
    calc
      _ = ∑ h : s, singletonComponentCount M h.val := by
        apply Finset.sum_congr rfl
        intro h hh
        exact Nat.card_eq_fintype_card.symm
      _ = _ := Finset.sum_coe_sort s _
  rwa [he] at hcard

def activeSingletonOver (M : MultiplicityBase Gamma) (h : ActiveDegree M.base) :
    {C : FiberComponent M.base h.val // (componentSupport M.base h.val C).card = 1} := by
  have hl := componentCount_sub_one_le_singletons M h.val h.property.1
  have hp : 0 < singletonComponentCount M h.val := by have := h.property.2; omega
  exact Classical.choice (Nat.card_pos_iff.mp hp).1

instance finiteActiveDegrees (M : MultiplicityBase Gamma) : Finite (ActiveDegree M.base) := by
  let f : ActiveDegree M.base → ActiveSingleton M.base := fun h => ⟨h, activeSingletonOver M h⟩
  exact Finite.of_injective f (fun _ _ he => congrArg Sigma.fst he)

def activeDegreeFinset (M : MultiplicityBase Gamma) : Finset ℕ := by
  classical
  letI : Fintype (ActiveDegree M.base) := @Fintype.ofFinite _ (finiteActiveDegrees M)
  exact Finset.univ.image (fun h : ActiveDegree M.base => h.val)

@[simp] theorem mem_activeDegreeFinset (M : MultiplicityBase Gamma) (h : ℕ) :
    h ∈ activeDegreeFinset M ↔ 0 < h ∧ 1 < componentCount M.base h := by
  classical
  letI : Fintype (ActiveDegree M.base) := @Fintype.ofFinite _ (finiteActiveDegrees M)
  unfold activeDegreeFinset
  constructor
  · intro hh
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hh
    exact he ▸ x.property
  · intro hh
    exact Finset.mem_image.mpr ⟨⟨h, hh⟩, Finset.mem_univ _, rfl⟩

theorem contribution_sum_le_three (M : MultiplicityBase Gamma) (s : Finset ℕ)
    (hs : ∀ h ∈ s, 0 < h ∧ 1 < componentCount M.base h) :
    ∑ h ∈ s, fiberContribution M h ≤ 3 := by
  apply le_trans _ (singleton_sum_le_three M s hs)
  apply Finset.sum_le_sum
  intro h hh
  exact (fiberContribution_le M h).trans (componentCount_sub_one_le_singletons M h (hs h hh).1)

theorem active_contribution_sum_le_three (M : MultiplicityBase Gamma) :
    ∑ h ∈ activeDegreeFinset M, fiberContribution M h ≤ 3 :=
  contribution_sum_le_three M _ (fun h hh => (mem_activeDegreeFinset M h).mp hh)

theorem componentCount_zero_le_one (B : Data Gamma) : componentCount B 0 ≤ 1 := by
  haveI : Subsingleton (FactorizationFiber B 0) := ⟨by
    intro u v
    apply Subtype.ext
    ext j
    have hu := fiber_coordinate_le B 0 u j
    have hv := fiber_coordinate_le B 0 v j
    omega⟩
  have hc : Nat.card (FiberComponent B 0) ≤ Nat.card (FactorizationFiber B 0) :=
    Nat.card_le_card_of_surjective _ Quot.mk_surjective
  have hf : Nat.card (FactorizationFiber B 0) ≤ 1 := by
    simpa using Nat.card_le_card_of_injective (fun _ : FactorizationFiber B 0 => ())
      (fun u v _ => Subsingleton.elim u v)
  exact hc.trans hf

theorem contribution_zero_outside_active (M : MultiplicityBase Gamma) (h : ℕ)
    (hh : h ∉ activeDegreeFinset M) : fiberContribution M h = 0 := by
  have hp := fiberContribution_le M h
  have hc : componentCount M.base h ≤ 1 := by
    by_cases hz : h = 0
    · subst h; exact componentCount_zero_le_one M.base
    · have hn : ¬(0 < h ∧ 1 < componentCount M.base h) := by rwa [mem_activeDegreeFinset] at hh
      omega
  omega

theorem finite_contribution_support (M : MultiplicityBase Gamma) :
    Set.Finite {h : ℕ | fiberContribution M h ≠ 0} := by
  apply (activeDegreeFinset M).finite_toSet.subset
  intro h hh
  by_contra hn
  exact hh (contribution_zero_outside_active M h hn)

/-- The remaining dependency is explicit: the unproved contribution identity is a hypothesis. -/
theorem defect_range_of_contribution_identity (M : MultiplicityBase Gamma)
    (hidentity : chosenDefect M.base = ∑ h ∈ activeDegreeFinset M, fiberContribution M h) :
    chosenDefect M.base ≤ 3 := by
  rw [hidentity]
  exact active_contribution_sum_le_three M

end NS25Lean.L2B
