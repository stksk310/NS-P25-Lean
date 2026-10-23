import NS25Lean.P3R3PrincipalR67

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R67
open CombinatorialCore L5A2C4I

variable {H : NumericalSemigroup}

/-- A canonical final-ideal member is its actual final representative. -/
theorem final_rep_of_canonical_mem (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (hsub : ∀ z : ℤ, z ∈ I → z ∈ H.asRelativeIdeal) (x : ℤ)
    (hcan : H.asRelativeIdeal.aperyRepresentative a (x : ZMod a) = x)
    (hx : x ∈ I) : I.aperyRepresentative a (x : ZMod a) = x := by
  apply le_antisymm (I.aperyRepresentative_le a _ hx rfl)
  have h := H.asRelativeIdeal.aperyRepresentative_le a _
    (hsub _ (I.aperyRepresentative_mem a (x : ZMod a))) (I.aperyRepresentative_mod a _)
  simpa only [hcan] using h

/-- Exact representative equations give the actual zero carry. -/
theorem final_step_zero_of_representatives (I : RelativeIdeal H) (a b : ℕ) [NeZero a]
    (hb : b ∈ H) (x : ℤ)
    (h0 : I.aperyRepresentative a (x : ZMod a) = x)
    (h1 : I.aperyRepresentative a ((x+b : ℤ) : ZMod a) = x+b) :
    I.aperyStepQuotient a b hb (x : ZMod a) = 0 := by
  have he := I.apery_step_eq a b hb (x : ZMod a)
  have h1' : I.aperyRepresentative a ((x : ZMod a)+b) = x+b := by simpa using h1
  rw [h0,h1'] at he
  have ha : (0 : ℤ)<a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have hz : (I.aperyStepQuotient a b hb (x : ZMod a) : ℤ)=0 := by nlinarith
  exact_mod_cast hz

/-- TW.10/NF.10 local square: southwest positive height and three final floor
cells give a TOTAL exact unused merge, with no freshness conclusion. -/
theorem unused_merge_of_final_square (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H)
    (hsub : ∀ z : ℤ, z ∈ I → z ∈ H.asRelativeIdeal) (x : ℤ)
    (h0 : H.asRelativeIdeal.aperyRepresentative a (x : ZMod a) = x)
    (h1 : H.asRelativeIdeal.aperyRepresentative a ((x+b : ℤ) : ZMod a) = x+b)
    (h2 : H.asRelativeIdeal.aperyRepresentative a ((x+c : ℤ) : ZMod a) = x+c)
    (h3 : H.asRelativeIdeal.aperyRepresentative a ((x+b+c : ℤ) : ZMod a) = x+b+c)
    (hn : x ∉ I) (he : x+b ∈ I) (hw : x+c ∈ I) (hne : x+b+c ∈ I) :
    ResidueData.ExactUnusedMergeReverseBase (P3R60.idealData I a b c hb hc) (x : ZMod a) := by
  have re := final_rep_of_canonical_mem I a hsub _ h1 he
  have rw' := final_rep_of_canonical_mem I a hsub _ h2 hw
  have rne := final_rep_of_canonical_mem I a hsub _ h3 hne
  have hlow : x < I.aperyRepresentative a (x : ZMod a) := by
    have hl := H.asRelativeIdeal.aperyRepresentative_le a _
      (hsub _ (I.aperyRepresentative_mem a (x : ZMod a))) (I.aperyRepresentative_mod a _)
    rw [h0] at hl
    have hn' : I.aperyRepresentative a (x : ZMod a) ≠ x := by
      intro eq
      exact hn (eq ▸ I.aperyRepresentative_mem a (x : ZMod a))
    omega
  have euc := final_step_zero_of_representatives I a b hb (x+c) rw' (by simpa [add_comm,add_left_comm,add_assoc] using rne)
  have evb := final_step_zero_of_representatives I a c hc (x+b) re rne
  have hu := I.apery_step_eq a b hb (x : ZMod a)
  have hv := I.apery_step_eq a c hc (x : ZMod a)
  have re' : I.aperyRepresentative a ((x : ZMod a)+b)=x+b := by simpa using re
  have rw'' : I.aperyRepresentative a ((x : ZMod a)+c)=x+c := by simpa using rw'
  rw [re'] at hu
  rw [rw''] at hv
  have ha : (0 : ℤ)<a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have huv : I.aperyStepQuotient a b hb (x : ZMod a)=I.aperyStepQuotient a c hc (x : ZMod a) := by
    exact_mod_cast (show (I.aperyStepQuotient a b hb (x : ZMod a) : ℤ)=I.aperyStepQuotient a c hc (x : ZMod a) by nlinarith [hu,hv])
  have hup : 0<I.aperyStepQuotient a b hb (x : ZMod a) := by
    by_contra h
    have hz : I.aperyStepQuotient a b hb (x : ZMod a)=0 := by omega
    rw [hz] at hu
    simp only [Nat.cast_zero,mul_zero,add_zero] at hu
    omega
  refine ⟨huv,hup,?_,?_⟩
  · change I.aperyStepQuotient a b hb ((x : ZMod a)+c)=0
    simpa using euc
  · change I.aperyStepQuotient a c hc ((x : ZMod a)+b)=0
    simpa using evb

/-- Distinct actual staircase bases give a cardinal lower bound on TOTAL UM. -/
theorem unused_count_of_injective_bases {R α : Type*} [Fintype R] [Finite α]
    (D : ResidueData R) (f : α → R) (hf : Function.Injective f)
    (hm : ∀ i, ResidueData.ExactUnusedMergeReverseBase D (f i)) :
    Nat.card α ≤ Nat.card (ResidueData.ExactUnusedMergeBases D) := by
  letI : Finite (ResidueData.ExactUnusedMergeBases D) := Subtype.finite
  let g : α → ResidueData.ExactUnusedMergeBases D := fun i => ⟨f i,hm i⟩
  exact Nat.card_le_card_of_injective g (fun i j h => hf (congrArg Subtype.val h))

/-- A distinct occupied corner adds one TOTAL merge even when baseline-used. -/
theorem unused_count_with_corner {R α : Type*} [Fintype R] [Finite α]
    (D : ResidueData R) (f : α → R) (hf : Function.Injective f)
    (hm : ∀ i, ResidueData.ExactUnusedMergeReverseBase D (f i))
    (corner : R) (hcorner : ResidueData.ExactUnusedMergeReverseBase D corner)
    (hdis : ∀ i, f i ≠ corner) :
    Nat.card α+1 ≤ Nat.card (ResidueData.ExactUnusedMergeBases D) := by
  let g : α ⊕ Unit → R := Sum.elim f (fun _ => corner)
  have hg : Function.Injective g := by
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
  have hm' : ∀ i, ResidueData.ExactUnusedMergeReverseBase D (g i) := by
    intro i; cases i with
    | inl i => exact hm i
    | inr i => exact hcorner
  simpa only [Nat.card_sum,Nat.card_unique] using unused_count_of_injective_bases D g hg hm'

end NS25Lean.P3R67
