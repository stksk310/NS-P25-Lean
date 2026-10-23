import NS25Lean.P3R3OmegaR67
set_option linter.style.header false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4OR6 L5A2B4AR1
variable {Gamma : NumericalSemigroup}
/-- Complete factorization classification of the short RB critical strip (TW.07). -/
theorem short_strip_Z_factorization (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (ell x y z : ℕ)
    (hell : ell < criticalExponent M.base (e 0))
    (he : x*routingA M.base e+y*routingB M.base e+z*routingC M.base e =
      ell*routingA M.base e+P3R57.roleCoefficient M hp e 2 1*routingB M.base e) :
    (x=ell ∧ y=P3R57.roleCoefficient M hp e 2 1 ∧ z=0) ∨
    (P3R57.roleCoefficient M hp e 2 0 ≤ ell ∧
      x=ell-P3R57.roleCoefficient M hp e 2 0 ∧ y=0 ∧ z=criticalExponent M.base (e 2)) := by
  have hs := P3R58.p3_coefficient_sums M hp e
  have hsub := Nat.sub_add_cancel hell.le
  have he' : (x+(criticalExponent M.base (e 0)-ell))*routingA M.base e+
      y*routingB M.base e+z*routingC M.base e=omegaDegree M hp e := by
    dsimp [omegaDegree]
    nlinarith only [he, congrArg (fun t => t*routingA M.base e) hsub]
  rcases omega_factorization_table M hp e _ _ _ he' with h | h | h
  · exact Or.inl ⟨by omega,h.2⟩
  · omega
  · right
    rw [hs.1] at hsub
    exact ⟨by omega,by omega,h.2⟩

#print axioms short_strip_Z_factorization


/-- The exchanged short strip, at the level of the integral Herzog kernel. -/
theorem short_strip_V_lattice (P T U V W Z ell l k x y z : ℤ)
    (hP : 0<P) (hT : 0<T) (hU : 0<U) (hV : 0<V) (hW : 0<W) (hZ : 0<Z)
    (hell : ell<U+W) (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (hex : x=ell-(U+W)*l-W*k) (hey : y=P*l-Z*k)
    (hez : z=V+T*l+(T+V)*k) :
    (x=ell ∧ y=0 ∧ z=V) ∨ (U≤ell ∧ x=ell-U ∧ y=P+Z ∧ z=0) := by
  have ht := omega_lattice_points T P W Z U V (l+k) (-k)
    (x+(U+W)-ell) z y hT hP hW hZ hU hV (by linarith) hz hy
    (by nlinarith only [hex]) (by nlinarith only [hez]) (by nlinarith only [hey])
  rcases ht with h | h | h
  · left; obtain ⟨h1,h2,h3⟩ := h; exact ⟨by linarith,h3,h2⟩
  · linarith [h.1]
  · right; obtain ⟨h1,h2,h3⟩ := h; exact ⟨by linarith,by linarith,h3,h2⟩

/-- Complete factorization classification of the exchanged short critical strip (TW.07). -/
theorem short_strip_V_factorization (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (ell x y z : ℕ)
    (hell : ell < criticalExponent M.base (e 0))
    (he : x*routingA M.base e+y*routingB M.base e+z*routingC M.base e =
      ell*routingA M.base e+P3R57.roleCoefficient M hp e 1 2*routingC M.base e) :
    (x=ell ∧ y=0 ∧ z=P3R57.roleCoefficient M hp e 1 2) ∨
    (P3R57.roleCoefficient M hp e 1 0 ≤ ell ∧
      x=ell-P3R57.roleCoefficient M hp e 1 0 ∧ y=criticalExponent M.base (e 1) ∧ z=0) := by
  have heZ : ((x:ℤ)-ell)*routingA M.base e+(y:ℤ)*routingB M.base e+
      ((z:ℤ)-P3R57.roleCoefficient M hp e 1 2)*routingC M.base e=0 := by
    have hh : (x:ℤ)*routingA M.base e+(y:ℤ)*routingB M.base e+(z:ℤ)*routingC M.base e =
      (ell:ℤ)*routingA M.base e+(P3R57.roleCoefficient M hp e 1 2:ℤ)*routingC M.base e := by exact_mod_cast he
    nlinarith only [hh]
  obtain ⟨l,k,hl,hk,hz⟩ := P3R59.p3_integer_kernel_basis M hp e _ _ _ heZ
  have hs := P3R58.p3_coefficient_sums M hp e
  have hp0 := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have ht0 := P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hu0 := P3R58.p3_coefficients_positive M hp e 1 0 (by decide)
  have hv0 := P3R58.p3_coefficients_positive M hp e 1 2 (by decide)
  have hw0 := P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  have hz0 := P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  rw [hs.1] at hl
  rw [hs.2.2] at hz
  have ht := short_strip_V_lattice
    (P3R57.roleCoefficient M hp e 0 1) (P3R57.roleCoefficient M hp e 0 2)
    (P3R57.roleCoefficient M hp e 1 0) (P3R57.roleCoefficient M hp e 1 2)
    (P3R57.roleCoefficient M hp e 2 0) (P3R57.roleCoefficient M hp e 2 1)
    ell l k x y z (by exact_mod_cast hp0) (by exact_mod_cast ht0) (by exact_mod_cast hu0)
    (by exact_mod_cast hv0) (by exact_mod_cast hw0) (by exact_mod_cast hz0)
    (by rw [hs.1] at hell; exact_mod_cast hell) (by positivity) (by positivity) (by positivity)
    (by push_cast at hl ⊢; nlinarith only [hl]) (by linarith only [hk])
    (by push_cast at hz ⊢; nlinarith only [hz])
  rcases ht with h | h
  · left; exact_mod_cast h
  · right
    have hU : P3R57.roleCoefficient M hp e 1 0 ≤ ell := by exact_mod_cast h.1
    refine ⟨hU,?_,?_,?_⟩
    · have hh := h.2.1
      exact_mod_cast (show (x:ℤ)=(ell-P3R57.roleCoefficient M hp e 1 0:ℕ) by rw [Nat.cast_sub hU]; exact hh)
    · rw [hs.2.1]; exact_mod_cast h.2.2.1
    · exact_mod_cast h.2.2.2

#print axioms short_strip_V_lattice
#print axioms short_strip_V_factorization

end NS25Lean.P3R67

