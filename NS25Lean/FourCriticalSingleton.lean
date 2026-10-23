import NS25Lean.FourBettiFinite

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase Classical
variable {Gamma : NumericalSemigroup}
theorem fiber_eq_single_of_componentSupport (B : Data Gamma) (h : ℕ)
    (C : FiberComponent B h) (j : Fin 4) (hs : componentSupport B h C = {j})
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

def OutsideExponent (B : Data Gamma) (j : Fin 4) (r : ℕ) : Prop :=
  0 < r ∧ ∃ v : Fin 4 →₀ ℕ, v j = 0 ∧ weight B v = r * weights B j

theorem exists_outsideExponent (B : Data Gamma) (j : Fin 4) : ∃ r, OutsideExponent B j r := by
  classical
  obtain ⟨i, hi⟩ := exists_ne j
  refine ⟨weights B i, weights_positive B i, Finsupp.single i (weights B j), ?_, ?_⟩
  · simp [Ne.symm hi]
  · rw [weight_single, Nat.mul_comm]

def criticalExponent (B : Data Gamma) (j : Fin 4) : ℕ := Nat.find (exists_outsideExponent B j)

theorem criticalExponent_spec (B : Data Gamma) (j : Fin 4) :
    OutsideExponent B j (criticalExponent B j) := Nat.find_spec (exists_outsideExponent B j)

theorem criticalExponent_min (B : Data Gamma) (j : Fin 4) (r : ℕ) (hr : OutsideExponent B j r) :
    criticalExponent B j ≤ r := Nat.find_min' (exists_outsideExponent B j) hr

theorem pure_exponent_le_outside (B : Data Gamma) (g : ℕ) (E : FiberComponent B g)
    (j : Fin 4) (hE : componentSupport B g E = {j})
    (w : FactorizationFiber B g) (hw : (fiberGraph B g).connectedComponentMk w = E)
    (r : ℕ) (hr : OutsideExponent B j r) : w.val j ≤ r := by
  classical
  obtain ⟨hrpos, v, hvj, hvdeg⟩ := hr
  by_contra hn
  have hlt : r < w.val j := by omega
  have hw' := fiber_eq_single_of_componentSupport B g E j hE w hw
  have gdeg : g = w.val j * weights B j :=
    w.property.symm.trans ((congrArg (weight B) hw').trans (weight_single B j _))
  have hex : ∃ i : Fin 4, 0 < v i := by
    by_contra hh
    push Not at hh
    have hz : v = 0 := by ext i; change v i = 0; exact Nat.eq_zero_of_le_zero (hh i)
    have hp := weights_positive B j
    rw [hz, map_zero] at hvdeg
    nlinarith
  obtain ⟨i, hi⟩ := hex
  have hij : i ≠ j := by intro he; subst i; omega
  let z : FactorizationFiber B g := ⟨v + Finsupp.single j (w.val j - r), by
    rw [map_add, weight_single, hvdeg]
    have hs := Nat.sub_add_cancel (le_of_lt hlt)
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

/-- A pure singleton at an active degree occurs exactly at its critical exponent degree. -/
theorem singleton_active_degree_eq_critical (B : Data Gamma) (h : ℕ)
    (hh : 0 < h) (hc : 1 < componentCount B h) (C : FiberComponent B h)
    (j : Fin 4) (hC : componentSupport B h C = {j}) :
    h = criticalExponent B j * weights B j := by
  classical
  obtain ⟨u, hu⟩ := C.exists_rep
  have hu' := fiber_eq_single_of_componentSupport B h C j hC u hu
  have hdeg : h = u.val j * weights B j :=
    u.property.symm.trans ((congrArg (weight B) hu').trans (weight_single B j _))
  have hpos : 0 < u.val j := by nlinarith
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
  have hmin := criticalExponent_min B j (u.val j) ⟨hpos, v.val, hvj, v.property.trans hdeg⟩
  have hmax := pure_exponent_le_outside B h C j hC u hu _ (criticalExponent_spec B j)
  have he : u.val j = criticalExponent B j := by omega
  exact hdeg.trans (congrArg (fun r => r * weights B j) he)


theorem singleton_active_degree_unique (B : Data Gamma) (h g : ℕ)
    (hh : 0 < h) (hg : 0 < g) (hc : 1 < componentCount B h) (gc : 1 < componentCount B g)
    (C : FiberComponent B h) (E : FiberComponent B g) (j : Fin 4)
    (hC : componentSupport B h C = {j}) (hE : componentSupport B g E = {j}) : h = g :=
  (singleton_active_degree_eq_critical B h hh hc C j hC).trans
    (singleton_active_degree_eq_critical B g hg gc E j hE).symm
def singletonComponentCount (B : Data Gamma) (h : ℕ) : ℕ :=
  Nat.card {C : FiberComponent B h // (componentSupport B h C).card = 1}

def ActiveDegree (B : Data Gamma) := {h : ℕ // 0 < h ∧ 1 < componentCount B h}

def ActiveSingleton (B : Data Gamma) :=
  Sigma (fun h : ActiveDegree B =>
    {C : FiberComponent B h.val // (componentSupport B h.val C).card = 1})

def singletonVariable (B : Data Gamma) (x : ActiveSingleton B) : Fin 4 :=
  Classical.choose (Finset.card_eq_one.mp x.2.property)

theorem singletonVariable_support (B : Data Gamma) (x : ActiveSingleton B) :
    componentSupport B x.1.val x.2.val = {singletonVariable B x} :=
  Classical.choose_spec (Finset.card_eq_one.mp x.2.property)

theorem singletonVariable_injective (B : Data Gamma) : Function.Injective (singletonVariable B) := by
  classical
  rintro ⟨⟨h, hh, hc⟩, C, hC⟩ ⟨⟨g, hg, gc⟩, E, hE⟩ he
  have hsC := singletonVariable_support B ⟨⟨h, hh, hc⟩, C, hC⟩
  have hsE := singletonVariable_support B ⟨⟨g, hg, gc⟩, E, hE⟩
  have hsE' := hsE.trans (congrArg (fun j : Fin 4 => ({j} : Finset (Fin 4))) he.symm)
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

/-- The total number of pure singleton components across all active degrees is at most four. -/
theorem active_singletons_card_le_four (B : Data Gamma) : Nat.card (ActiveSingleton B) ≤ 4 :=
  (Nat.card_le_card_of_injective _ (singletonVariable_injective B)).trans_eq (by simp)

theorem singleton_sum_le_four (B : Data Gamma) (s : Finset ℕ)
    (hs : ∀ h ∈ s, 0 < h ∧ 1 < componentCount B h) :
    ∑ h ∈ s, singletonComponentCount B h ≤ 4 := by
  classical
  let F := Sigma (fun h : s =>
    {C : FiberComponent B h.val // (componentSupport B h.val C).card = 1})
  letI (h : s) := Fintype.ofFinite
    {C : FiberComponent B h.val // (componentSupport B h.val C).card = 1}
  let f : F → ActiveSingleton B := fun x => ⟨⟨x.1.val, hs x.1.val x.1.property⟩, x.2⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨h, hh⟩, C⟩ ⟨⟨g, hg⟩, E⟩ he
    have hge : h = g := congrArg (fun x : ActiveSingleton B => x.1.val) he
    subst g
    have hCE : C = E := by
      change (⟨⟨h, hs h hh⟩, C⟩ : ActiveSingleton B) =
        (⟨⟨h, hs h hg⟩, E⟩ : ActiveSingleton B) at he
      exact eq_of_heq (Sigma.mk.inj he).2
    subst E
    rfl
  have hcard := (Nat.card_le_card_of_injective f hf).trans (active_singletons_card_le_four B)
  have he : Nat.card F = ∑ h ∈ s, singletonComponentCount B h := by
    rw [Nat.card_eq_fintype_card]
    change Fintype.card (Sigma (fun h : s => _)) = _
    rw [Fintype.card_sigma]
    calc
      _ = ∑ h : s, singletonComponentCount B h.val := by
        apply Finset.sum_congr rfl
        intro h hh
        exact Nat.card_eq_fintype_card.symm
      _ = _ := Finset.sum_coe_sort s _
  rwa [he] at hcard


end NS25Lean.L2C
