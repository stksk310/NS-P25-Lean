import NS25Lean.P3R3StaircaseCountR67

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4I L5A2B4AR1 CombinatorialCore
open L5A2C4OR3 L5A2C4OR4
variable {Gamma : NumericalSemigroup}

/-- An occupied rectangular floor provides distinct actual TOTAL merge bases,
with coordinate bounds retained for inter-arm disjointness. -/
theorem rectangular_unused_family (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (Imax Jmax Ylower : ℕ) (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (hI : Imax ≤ criticalExponent M.base (e 1))
    (hJ : Jmax ≤ criticalExponent M.base (e 2))
    (hrect : Imax ≤ P3R57.roleCoefficient M hp e 0 1 ∨ Jmax ≤ P3R57.roleCoefficient M hp e 0 2)
    (hbounds : ∀ p ∈ S, 0<p.1 ∧ p.1<Imax ∧ Ylower<p.2 ∧ p.2<Jmax)
    (hfloor : ∀ i j, i<Imax → j<Jmax →
      ((i : ℤ)*routingB M.base e+j*routingC M.base e ∈ routingI M.base e ↔
        ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j))
    (hcorner :
      letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      ResidueData.ExactUnusedMergeReverseBase (routingData M.base e)
        ((((Imax-1 : ℕ) : ℤ)*routingB M.base e+((Jmax-1 : ℕ) : ℤ)*routingC M.base e : ℤ) : ZMod (routingA M.base e))) :
    letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
    ∃ base : (Fin ((coordinateMinima S).card-1) ⊕ Unit) → ZMod (routingA M.base e),
      Function.Injective base ∧
      (∀ k, ResidueData.ExactUnusedMergeReverseBase (routingData M.base e) (base k)) ∧
      (∀ k, ∃ i j : ℕ, i<Imax ∧ j<Jmax ∧ Ylower≤j ∧
        base k = (((i : ℤ)*routingB M.base e+j*routingC M.base e : ℤ) : ZMod (routingA M.base e))) := by
  classical
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  have hm : 0<Imax ∧ Ylower<Jmax := by
    obtain ⟨p,hpS⟩ := hS
    have := hbounds p hpS
    omega
  let corner : ZMod (routingA M.base e) :=
    ((((Imax-1 : ℕ) : ℤ)*routingB M.base e+((Jmax-1 : ℕ) : ℤ)*routingC M.base e : ℤ) : ZMod (routingA M.base e))
  obtain ⟨f,hf,hfm,hdis,hfg⟩ := rectangular_staircase_merge_family M hp e Imax Jmax S hS hI hJ hrect
    (by intro p hpS; have := hbounds p hpS; omega) hfloor (Jmax-1) (by omega)
    (by rcases hrect with h | h <;> omega) hcorner
  let base : (Fin ((coordinateMinima S).card-1) ⊕ Unit) → ZMod (routingA M.base e) :=
    Sum.elim f (fun _ => corner)
  have hb : Function.Injective base := by
    intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hf he)
      | inr j => exact False.elim (hdis i he)
    | inr i =>
      cases j with
      | inl j => exact False.elim (hdis j he.symm)
      | inr j => cases i; cases j; rfl
  refine ⟨base,hb,?_,?_⟩
  · intro k
    cases k with
    | inl k => exact hfm k
    | inr k => exact hcorner
  · intro k
    cases k with
    | inl k =>
      obtain ⟨p,hpS,q,hqS,_,_,he⟩ := hfg k
      have hpB := hbounds p hpS
      have hqB := hbounds q hqS
      exact ⟨q.1-1,p.2-1,by omega,by omega,by omega,he⟩
    | inr k => exact ⟨Imax-1,Jmax-1,by omega,by omega,by omega,rfl⟩

/-- Two disjoint physical merge families add before any first-stage cancellation. -/
theorem unused_count_two_families {R α β : Type*} [Fintype R] [Finite α] [Finite β]
    (D : ResidueData R) (f : α → R) (g : β → R)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hmf : ∀ i, ResidueData.ExactUnusedMergeReverseBase D (f i))
    (hmg : ∀ j, ResidueData.ExactUnusedMergeReverseBase D (g j))
    (hdis : ∀ i j, f i ≠ g j) :
    Nat.card α+Nat.card β ≤ Nat.card (ResidueData.ExactUnusedMergeBases D) := by
  let h : α ⊕ β → R := Sum.elim f g
  have hh : Function.Injective h := by
    intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hf he)
      | inr j => exact False.elim (hdis i j he)
    | inr i =>
      cases j with
      | inl j => exact False.elim (hdis j i he.symm)
      | inr j => exact congrArg Sum.inr (hg he)
  have hm : ∀ k, ResidueData.ExactUnusedMergeReverseBase D (h k) := by
    intro k
    cases k with
    | inl k => exact hmf k
    | inr k => exact hmg k
  simpa only [Nat.card_sum] using unused_count_of_injective_bases D h hh hm

end NS25Lean.P3R67
