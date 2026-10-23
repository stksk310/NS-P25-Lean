import NS25Lean.WeightedResidueLattice
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2B
open ChosenBase ToricPresentation MvPolynomial
variable {Gamma : NumericalSemigroup}

structure MultiplicityBase (Gamma : NumericalSemigroup) where
  base : Data Gamma
  isMultiplicity : IsMultiplicity base

def asMultiplicityBase (B : Data Gamma) : MultiplicityBase Gamma :=
  ⟨multiplicityData B, multiplicityData_isMultiplicity B⟩

def FactorizationFiber (B : Data Gamma) (h : ℕ) := {u : Fin 3 →₀ ℕ // weight B u = h}

theorem fiber_coordinate_le (B : Data Gamma) (h : ℕ) (u : FactorizationFiber B h) (j : Fin 3) :
    u.val j ≤ h := by
  have hterm : u.val j * weights B j ≤ ∑ i, u.val i * weights B i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (u.val i * weights B i)) (Finset.mem_univ j)
  rw [← weight_eq_sum, u.property] at hterm
  have hp := weights_positive B j
  nlinarith

instance finiteFactorizationFiber (B : Data Gamma) (h : ℕ) : Finite (FactorizationFiber B h) := by
  let f : FactorizationFiber B h → (Fin 3 → Fin (h + 1)) :=
    fun u j => ⟨u.val j, Nat.lt_succ_of_le (fiber_coordinate_le B h u j)⟩
  apply Finite.of_injective f
  intro u v he
  apply Subtype.ext
  ext j
  exact congrArg Fin.val (congrFun he j)

theorem fiber_nonempty (B : Data Gamma) (h : B.H) : Nonempty (FactorizationFiber B h.val) := by
  obtain ⟨u, hu⟩ := Presentation.factorizationMap_surjective B.tailDegrees B.tailDegrees_generate h
  exact ⟨⟨u, (weight_eq_degree B u).trans (congrArg Subtype.val hu)⟩⟩

/-- An edge is exactly a nontrivial shared monomial factor (a shared variable). -/
def fiberGraph (B : Data Gamma) (h : ℕ) : SimpleGraph (FactorizationFiber B h) where
  Adj u v := u ≠ v ∧ ∃ j : Fin 3, 0 < u.val j ∧ 0 < v.val j
  symm := ⟨by rintro u v ⟨hne, j, hu, hv⟩; exact ⟨hne.symm, j, hv, hu⟩⟩
  loopless := ⟨by intro u; exact fun h => h.1 rfl⟩

abbrev FiberComponent (B : Data Gamma) (h : ℕ) := (fiberGraph B h).ConnectedComponent

def componentCount (B : Data Gamma) (h : ℕ) : ℕ := Nat.card (FiberComponent B h)

def BoundaryKilled (M : MultiplicityBase Gamma) (h : ℕ) (C : FiberComponent M.base h) : Prop :=
  ∃ u : FactorizationFiber M.base h, (fiberGraph M.base h).connectedComponentMk u = C ∧
    ∃ j : Fin 3, 0 < u.val j ∧ h - weights M.base j ∈ M.base.K

def killedCount (M : MultiplicityBase Gamma) (h : ℕ) : ℕ :=
  Nat.card {C : FiberComponent M.base h // BoundaryKilled M h C}

theorem killedCount_le_componentCount (M : MultiplicityBase Gamma) (h : ℕ) :
    killedCount M h ≤ componentCount M.base h :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

open Classical in
/-- Exactly the manuscript's piecewise degree contribution; no MUJ is used. -/
def fiberContribution (M : MultiplicityBase Gamma) (h : ℕ) : ℕ :=
  if killedCount M h = 0 then componentCount M.base h - 1
  else componentCount M.base h - killedCount M h

theorem fiberContribution_le (M : MultiplicityBase Gamma) (h : ℕ) :
    fiberContribution M h ≤ componentCount M.base h - 1 := by
  unfold fiberContribution
  split_ifs with hz
  · exact le_rfl
  · exact Nat.sub_le_sub_left (by omega : 1 ≤ killedCount M h) _

theorem fiberContribution_add_killed (M : MultiplicityBase Gamma) (h : ℕ)
    (hd : killedCount M h ≠ 0) :
    fiberContribution M h + killedCount M h = componentCount M.base h := by
  rw [fiberContribution, ite_eq_right hd]
  exact Nat.sub_add_cancel (killedCount_le_componentCount M h)

def variableIdeal (k : Type*) [Field k] : Ideal (Poly k 3) := Ideal.span (Set.range X)

/-- The actual subspace nJ inside J, with scalars restricted to the coefficient field. -/
def generatorRelations (k : Type*) [Field k] (B : Data Gamma) : Submodule k (B.J k) :=
  ((variableIdeal k * B.J k).restrictScalars k).comap ((B.J k).subtype.restrictScalars k)

abbrev GeneratorQuotient (k : Type*) [Field k] (B : Data Gamma) :=
  (B.J k) ⧸ generatorRelations k B

def tailToGeneratorQuotient (k : Type*) [Field k] (B : Data Gamma) :
    B.IH k →ₗ[k] GeneratorQuotient k B :=
  (generatorRelations k B).mkQ.comp
    ((Submodule.inclusion (show B.IH k ≤ B.J k from by
      rw [B.J_eq_IH_sup_MK k]; exact le_sup_left)).restrictScalars k)

def tailGeneratorImage (k : Type*) [Field k] (B : Data Gamma) :
    Submodule k (GeneratorQuotient k B) := (tailToGeneratorQuotient k B).range

end NS25Lean.L2B
