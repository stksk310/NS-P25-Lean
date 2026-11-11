import NS25Lean.GenericReturnCommonTheorems
import NS25Lean.P2ErasureActualAdapters

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturn
open SharedTail ErasedSourceScreen ErasureActualAdapters
open ChosenBase L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR3 L5A2C4OR5
open scoped Classical

/-- Numericality of the actual generated H gives primitive tail weights. -/
theorem triple_primitive {H : NumericalSemigroup} (T : Triple H) :
    Nat.gcd (T.g 0) (Nat.gcd (T.g 1) (T.g 2))=1 := by
  let g := Nat.gcd (T.g 0) (Nat.gcd (T.g 1) (T.g 2))
  have h0 : g∣T.g 0 := Nat.gcd_dvd_left _ _
  have h1 : g∣T.g 1 := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
  have h2 : g∣T.g 2 := dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)
  have hall (n : ℕ) (hn : n∈H) : g∣n := by
    obtain ⟨e,he⟩ := T.factor n hn
    rw [←he,T.weight_three]
    dsimp [Triple.grid]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right h0 _) (dvd_mul_of_dvd_right h1 _))
      (dvd_mul_of_dvd_right h2 _)
  obtain ⟨N,hN⟩ := H.exists_conductor
  have hdN := hall N (hN N le_rfl)
  have hdNp := hall (N+1) (hN _ (by omega))
  have hgone : g∣1 := by simpa using Nat.dvd_sub hdNp hdN
  exact Nat.dvd_one.mp hgone

/-- The standalone package is populated from genuine original critical
factorizations. Original normalized carrier and role order are unchanged. -/
def actualPositive {Gamma : NumericalSemigroup} (B : Data Gamma) (e : Fin 3≃Fin 3)
    (HD : CoherentHerzogData B e) : Positive (routingH B e) :=
  let E := actualPositivePresentation B e HD
  { triple := actualTriple B e
    critical := actualCritical B e
    p := E.P
    q := E.Q
    u := E.U
    v := E.V
    w := E.W
    z := E.Z
    p_pos := E.positive.1
    q_pos := E.positive.2.1
    u_pos := E.positive.2.2.1
    v_pos := E.positive.2.2.2.1
    w_pos := E.positive.2.2.2.2.1
    z_pos := E.positive.2.2.2.2.2
    center := E.relationA
    middle := E.relationB
    boundary := E.relationC
    primitive := triple_primitive (actualTriple B e) }

@[simp] theorem actualPositive_a {Gamma : NumericalSemigroup} (B : Data Gamma) (e : Fin 3≃Fin 3)
    (HD : CoherentHerzogData B e) : (actualPositive B e HD).a=routingA B e := actual_g_zero B e
@[simp] theorem actualPositive_b {Gamma : NumericalSemigroup} (B : Data Gamma) (e : Fin 3≃Fin 3)
    (HD : CoherentHerzogData B e) : (actualPositive B e HD).b=routingB B e := actual_g_one B e
@[simp] theorem actualPositive_c {Gamma : NumericalSemigroup} (B : Data Gamma) (e : Fin 3≃Fin 3)
    (HD : CoherentHerzogData B e) : (actualPositive B e HD).c=routingC B e := actual_g_two B e

/-- A concrete original-carrier return tuple feeds the exact shared theorem;
the return degree nu is retained literally. -/
def actualReturn {Gamma : NumericalSemigroup} (B : Data Gamma) (e : Fin 3≃Fin 3)
    (HD : CoherentHerzogData B e) (nu i j d : ℕ)
    (hr : RB (actualPositive B e HD) i j d ∨ LT (actualPositive B e HD) i j d)
    (he : (i : ℤ)*routingB B e+j*routingC B e=(nu : ℤ)+d*routingA B e) :
    Return (actualPositive B e HD) where
  nu := nu
  i := i
  j := j
  depth := d
  strict := hr
  equation := by simpa only [actualPositive_a,actualPositive_b,actualPositive_c] using he

theorem actual_return_exact_generators {Gamma : NumericalSemigroup}
    (B : Data Gamma) (e : Fin 3≃Fin 3) (HD : CoherentHerzogData B e)
    (nu i j d : ℕ)
    (hr : RB (actualPositive B e HD) i j d ∨ LT (actualPositive B e HD) i j d)
    (he : (i : ℤ)*routingB B e+j*routingC B e=(nu : ℤ)+d*routingA B e) (x : ℤ) :
    let R := actualReturn B e HD nu i j d hr he
    x∈L5A2B4AR1.returnIdeal (routingH B e) nu ↔
      x-R.F∈(routingH B e).asRelativeIdeal ∨ x-R.X∈(routingH B e).asRelativeIdeal ∨
        x-R.Y∈(routingH B e).asRelativeIdeal :=
  (actualReturn B e HD nu i j d hr he).exact_generators x

end NS25Lean.GenericReturn
