import NS25Lean.ChosenBaseData
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase ToricPresentation MvPolynomial
variable {Gamma : NumericalSemigroup}

def weights (B : Data Gamma) : Fin 4 → ℕ := fun j => (B.family j).val

def weight (B : Data Gamma) : (Fin 4 →₀ ℕ) →+ ℕ := Finsupp.weight (weights B)

theorem weights_positive (B : Data Gamma) (j : Fin 4) : 0 < weights B j := B.positive j

theorem weight_eq_sum (B : Data Gamma) (u : Fin 4 →₀ ℕ) :
    weight B u = ∑ j, u j * weights B j := by
  simp only [weight, Finsupp.weight_eq_sum, smul_eq_mul]

theorem weight_eq_degree (B : Data Gamma) (u : Fin 4 →₀ ℕ) :
    weight B u = (Presentation.factorizationMap B.family u).val :=
  Presentation.weight_factorization_val Gamma.toAddSubmonoid B.family u

theorem weight_single (B : Data Gamma) (j : Fin 4) (r : ℕ) :
    weight B (Finsupp.single j r) = r * weights B j := by
  simp [weight, Finsupp.weight_single, smul_eq_mul]
def FactorizationFiber (B : Data Gamma) (h : ℕ) := {u : Fin 4 →₀ ℕ // weight B u = h}

theorem fiber_coordinate_le (B : Data Gamma) (h : ℕ) (u : FactorizationFiber B h) (j : Fin 4) :
    u.val j ≤ h := by
  have hterm : u.val j * weights B j ≤ ∑ i, u.val i * weights B i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (u.val i * weights B i)) (Finset.mem_univ j)
  rw [← weight_eq_sum, u.property] at hterm
  have hp := weights_positive B j
  nlinarith

instance finiteFactorizationFiber (B : Data Gamma) (h : ℕ) : Finite (FactorizationFiber B h) := by
  let f : FactorizationFiber B h → (Fin 4 → Fin (h + 1)) :=
    fun u j => ⟨u.val j, Nat.lt_succ_of_le (fiber_coordinate_le B h u j)⟩
  apply Finite.of_injective f
  intro u v he
  apply Subtype.ext
  ext j
  exact congrArg Fin.val (congrFun he j)

theorem fiber_nonempty (B : Data Gamma) (h : Gamma.toAddSubmonoid) : Nonempty (FactorizationFiber B h.val) := by
  obtain ⟨u, hu⟩ := Presentation.factorizationMap_surjective B.family (ToricPresentation.subtype_degrees_generate _ _ B.generates.symm) h
  exact ⟨⟨u, (weight_eq_degree B u).trans (congrArg Subtype.val hu)⟩⟩

/-- An edge is exactly a nontrivial shared monomial factor (a shared variable). -/
def fiberGraph (B : Data Gamma) (h : ℕ) : SimpleGraph (FactorizationFiber B h) where
  Adj u v := u ≠ v ∧ ∃ j : Fin 4, 0 < u.val j ∧ 0 < v.val j
  symm := ⟨by rintro u v ⟨hne, j, hu, hv⟩; exact ⟨hne.symm, j, hv, hu⟩⟩
  loopless := ⟨by intro u; exact fun h => h.1 rfl⟩

abbrev FiberComponent (B : Data Gamma) (h : ℕ) := (fiberGraph B h).ConnectedComponent

def componentCount (B : Data Gamma) (h : ℕ) : ℕ := Nat.card (FiberComponent B h)

/-- Graph-theoretic disconnectedness; independent of all presentations. -/
def Betti (B : Data Gamma) (d : ℕ) : Prop := 2 ≤ componentCount B d

def factorizationSupport (u : Fin 4 →₀ ℕ) : Finset (Fin 4) := u.support

open Classical in
def fiberVariables (B : Data Gamma) (d : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => ∃ u : FactorizationFiber B d, 0 < u.val j)

open Classical in
def componentEssential (B : Data Gamma) (d : ℕ) (C : FiberComponent B d) :
    Finset (Fin 4) :=
  Finset.univ.filter (fun j => ∀ u : FactorizationFiber B d,
    (fiberGraph B d).connectedComponentMk u = C → 0 < u.val j)

open Classical in
def essentialVariables (B : Data Gamma) (d : ℕ) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => ∃ C : FiberComponent B d, j ∈ componentEssential B d C)

@[simp] theorem mem_variables (B : Data Gamma) (d : ℕ) (j : Fin 4) :
    j ∈ fiberVariables B d ↔ ∃ u : FactorizationFiber B d, 0 < u.val j := by
  classical
  simp [fiberVariables]

@[simp] theorem mem_componentEssential (B : Data Gamma) (d : ℕ)
    (C : FiberComponent B d) (j : Fin 4) :
    j ∈ componentEssential B d C ↔ ∀ u : FactorizationFiber B d,
      (fiberGraph B d).connectedComponentMk u = C → 0 < u.val j := by
  classical
  simp [componentEssential]

@[simp] theorem mem_essentialVariables (B : Data Gamma) (d : ℕ) (j : Fin 4) :
    j ∈ essentialVariables B d ↔ ∃ C : FiberComponent B d,
      j ∈ componentEssential B d C := by
  classical
  simp [essentialVariables]
open Classical in
def componentSupport (B : Data Gamma) (h : ℕ) (C : FiberComponent B h) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => ∃ u : FactorizationFiber B h,
    (fiberGraph B h).connectedComponentMk u = C ∧ 0 < u.val j)

theorem mem_componentSupport (B : Data Gamma) (h : ℕ) (C : FiberComponent B h) (j : Fin 4) :
    j ∈ componentSupport B h C ↔ ∃ u : FactorizationFiber B h,
      (fiberGraph B h).connectedComponentMk u = C ∧ 0 < u.val j := by
  classical
  simp [componentSupport]

theorem components_eq_of_shared_support (B : Data Gamma) (h : ℕ)
    (C E : FiberComponent B h) (j : Fin 4)
    (hjC : j ∈ componentSupport B h C) (hjE : j ∈ componentSupport B h E) : C = E := by
  obtain ⟨u, hu, hju⟩ := (mem_componentSupport B h C j).mp hjC
  obtain ⟨v, hv, hjv⟩ := (mem_componentSupport B h E j).mp hjE
  by_cases he : u = v
  · exact hu.symm.trans (he ▸ hv)
  · have ha : (fiberGraph B h).Adj u v := ⟨he, j, hju, hjv⟩
    exact hu.symm.trans ((SimpleGraph.ConnectedComponent.sound ha.reachable).trans hv)

theorem componentSupports_disjoint (B : Data Gamma) (h : ℕ)
    (C E : FiberComponent B h) (hne : C ≠ E) :
    Disjoint (componentSupport B h C) (componentSupport B h E) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hjC hjE
  exact hne (components_eq_of_shared_support B h C E j hjC hjE)

theorem componentSupport_nonempty (B : Data Gamma) (h : ℕ) (hh : 0 < h)
    (C : FiberComponent B h) : (componentSupport B h C).Nonempty := by
  classical
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h u =>
    have hex : ∃ j : Fin 4, 0 < u.val j := by
      by_contra hn
      push Not at hn
      have hu : u.val = 0 := by
        ext j
        change u.val j = 0
        have := hn j
        omega
      have hw := u.property
      rw [hu, map_zero] at hw
      omega
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, (mem_componentSupport B h _ j).mpr ⟨u, rfl, hj⟩⟩

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

theorem betti_positive (B : Data Gamma) (d : ℕ) (hd : Betti B d) : 0 < d := by
  have hz := componentCount_zero_le_one B
  unfold Betti at hd
  by_contra hn
  have he : d = 0 := by omega
  subst d
  omega

theorem betti_iff_nontrivial (B : Data Gamma) (d : ℕ) :
    Betti B d ↔ Nontrivial (FiberComponent B d) := by
  classical
  letI := Fintype.ofFinite (FiberComponent B d)
  simp only [Betti, componentCount, Nat.card_eq_fintype_card]
  rw [show (2 ≤ Fintype.card (FiberComponent B d)) ↔
    1 < Fintype.card (FiberComponent B d) by omega]
  exact Fintype.one_lt_card_iff_nontrivial

theorem same_component_of_shared (B : Data Gamma) (d : ℕ)
    (u v : FactorizationFiber B d) (j : Fin 4) (hu : 0 < u.val j) (hv : 0 < v.val j) :
    (fiberGraph B d).connectedComponentMk u = (fiberGraph B d).connectedComponentMk v := by
  by_cases he : u = v
  · exact congrArg _ he
  · exact SimpleGraph.ConnectedComponent.sound (show (fiberGraph B d).Adj u v from
      ⟨he, j, hu, hv⟩).reachable

theorem essential_subset_variables (B : Data Gamma) (d : ℕ) :
    essentialVariables B d ⊆ fiberVariables B d := by
  intro j hj
  obtain ⟨C, hC⟩ := (mem_essentialVariables B d j).mp hj
  obtain ⟨u, hu⟩ := C.exists_rep
  exact (mem_variables B d j).mpr ⟨u, (mem_componentEssential B d C j).mp hC u hu⟩

end NS25Lean.L2C