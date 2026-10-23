import NS25Lean.P3CommonArmR59

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R63
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2B4AR1 L5A2C4A L5A2C4D L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

/-- The RB sign argument in the saturated integral lattice. -/
theorem rb_lattice_coordinates
    (P T U V W Z A B J K l k : ℤ)
    (hP : 0 < P) (hT : 0 < T) (hU : 0 < U) (hV : 0 < V)
    (hW : 0 < W) (hZ : 0 < Z)
    (hA0 : 0 < A) (hA : A ≤ (U+W)+U-2)
    (hB : B ≤ Z) (hJ : 2*P < J) (hK : 0 < K)
    (ha : A = (U+W)*l+W*k) (hj : J = B+P*l-Z*k)
    (hk : K = T*l+(T+V)*k)
    (hsector : K ≤ 2*T-2 ∨ B=Z) :
    l=1 ∧ k=0 := by
  have hk0 : 0 ≤ k := by
    by_contra hn
    have hkneg : k ≤ -1 := by omega
    have hlk : 1 ≤ l+k := by
      by_contra hn
      have hh : l+k ≤ 0 := by omega
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hT.le hh,
        mul_nonpos_of_nonneg_of_nonpos hV.le (show k ≤ 0 by omega)]
    have hl : 2 ≤ l := by omega
    nlinarith [mul_nonneg hU.le (show 0 ≤ l-2 by omega),
      mul_nonneg hW.le (show 0 ≤ l+k-1 by omega)]
  have hl : 1 ≤ l := by
    by_contra hn
    have hl0 : l ≤ 0 := by omega
    by_cases hk1 : 1 ≤ k
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hP.le hl0,
        mul_nonneg hZ.le (show 0 ≤ k-1 by omega)]
    · have hkz : k=0 := by omega
      rw [hkz] at ha
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ U+W by omega) hl0]
  have hkz : k=0 := by
    by_contra hn
    have hk1 : 1 ≤ k := by omega
    rcases hsector with hbound | hBZ
    · nlinarith [mul_nonneg hT.le (show 0 ≤ l-1 by omega),
        mul_nonneg (show 0 ≤ T+V by omega) (show 0 ≤ k-1 by omega)]
    · have hbound : J ≤ P*l := by
        nlinarith [mul_nonneg hZ.le (show 0 ≤ k-1 by omega)]
      have hl3 : 3 ≤ l := by
        by_contra hn
        have hl2 : l ≤ 2 := by omega
        nlinarith [mul_nonneg hP.le (show 0 ≤ 2-l by omega)]
      nlinarith [mul_nonneg (show 0 ≤ U+W by omega) (show 0 ≤ l-3 by omega),
        mul_nonneg hW.le hk0]
  refine ⟨?_, hkz⟩
  rw [hkz] at ha
  by_contra hn
  have hl2 : 2 ≤ l := by omega
  nlinarith [mul_nonneg (show 0 ≤ U+W by omega) (show 0 ≤ l-2 by omega)]

/-- Saturation and RB bounds identify the relation as exactly the first critical relation. -/
theorem rb_relation_of_bounds (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (A B J K : ℕ)
    (hA0 : 0<A)
    (hA : A+2 ≤ criticalExponent M.base (e 0)+P3R57.roleCoefficient M hp e 1 0)
    (hB : B≤P3R57.roleCoefficient M hp e 2 1)
    (hJ : 2*P3R57.roleCoefficient M hp e 0 1<J) (hK : 0<K)
    (he : (A : ℤ)*routingA M.base e+B*routingB M.base e =
      J*routingB M.base e+K*routingC M.base e)
    (hsector : K+2≤2*P3R57.roleCoefficient M hp e 0 2 ∨ B=P3R57.roleCoefficient M hp e 2 1) :
    A=criticalExponent M.base (e 0) ∧
      J=B+P3R57.roleCoefficient M hp e 0 1 ∧ K=P3R57.roleCoefficient M hp e 0 2 := by
  obtain ⟨l,k,hl,hj,hk⟩ := P3R59.p3_integer_kernel_basis M hp e
    (-(A : ℤ)) ((J : ℤ)-B) K (by linear_combination -he)
  have hs := P3R58.p3_coefficient_sums M hp e
  have hP : (0 : ℤ)<P3R57.roleCoefficient M hp e 0 1 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hT : (0 : ℤ)<P3R57.roleCoefficient M hp e 0 2 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  have hU : (0 : ℤ)<P3R57.roleCoefficient M hp e 1 0 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 0 (by decide)
  have hV : (0 : ℤ)<P3R57.roleCoefficient M hp e 1 2 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 2 (by decide)
  have hW : (0 : ℤ)<P3R57.roleCoefficient M hp e 2 0 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  have hZ : (0 : ℤ)<P3R57.roleCoefficient M hp e 2 1 := by
    exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  have hAc : (A : ℤ)+2 ≤ criticalExponent M.base (e 0)+P3R57.roleCoefficient M hp e 1 0 := by exact_mod_cast hA
  rw [hs.1] at hl hAc
  rw [hs.2.2] at hk
  push_cast at hl hAc hk
  have hsec : (K : ℤ) ≤ 2*(P3R57.roleCoefficient M hp e 0 2 : ℤ)-2 ∨
      (B : ℤ)=P3R57.roleCoefficient M hp e 2 1 := by
    rcases hsector with hh | hh
    · left
      have hh' : (K : ℤ)+2≤2*(P3R57.roleCoefficient M hp e 0 2 : ℤ) := by exact_mod_cast hh
      linarith
    · right; exact_mod_cast hh
  obtain ⟨rfl,rfl⟩ := rb_lattice_coordinates
    (P3R57.roleCoefficient M hp e 0 1) (P3R57.roleCoefficient M hp e 0 2)
    (P3R57.roleCoefficient M hp e 1 0) (P3R57.roleCoefficient M hp e 1 2)
    (P3R57.roleCoefficient M hp e 2 0) (P3R57.roleCoefficient M hp e 2 1)
    A B J K l k hP hT hU hV hW hZ (by exact_mod_cast hA0)
    (by linarith) (by exact_mod_cast hB) (by exact_mod_cast hJ)
    (by exact_mod_cast hK) (by linarith only [hl]) (by linarith only [hj]) hk hsec
  rw [hs.1]
  constructor
  · exact_mod_cast (by linarith only [hl] : (A : ℤ)=
      P3R57.roleCoefficient M hp e 1 0+P3R57.roleCoefficient M hp e 2 0)
  constructor
  · exact_mod_cast (by linarith only [hj] : (J : ℤ)=B+P3R57.roleCoefficient M hp e 0 1)
  · exact_mod_cast (by linarith only [hk] : (K : ℤ)=P3R57.roleCoefficient M hp e 0 2)

/-- Complementary RB returns for the mixed principal shape. -/
theorem rb_complement_mixed (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (n n' i j d i' j' d' L I : ℕ)
    (hsum : n+n'=principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hi : P3R57.roleCoefficient M hp e 0 1 < i)
    (hi' : P3R57.roleCoefficient M hp e 0 1 < i')
    (hj : 0<j) (hj' : 0<j')
    (hjT : j<P3R57.roleCoefficient M hp e 0 2)
    (hjT' : j'<P3R57.roleCoefficient M hp e 0 2)
    (hd : d<P3R57.roleCoefficient M hp e 1 0)
    (hd' : d'<P3R57.roleCoefficient M hp e 1 0)
    (hL : 0<L) (hLW : L≤P3R57.roleCoefficient M hp e 2 0)
    (hIZ : I≤P3R57.roleCoefficient M hp e 2 1)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      L*routingA M.base e+I*routingB M.base e)
    (he : (i : ℤ)*routingB M.base e+j*routingC M.base e=
      n*M.base.q.val+d*routingA M.base e)
    (he' : (i' : ℤ)*routingB M.base e+j'*routingC M.base e=
      n'*M.base.q.val+d'*routingA M.base e) :
    i+i'=P3R57.roleCoefficient M hp e 0 1+I ∧
    j+j'=P3R57.roleCoefficient M hp e 0 2 ∧
    d+d'+L=criticalExponent M.base (e 0) := by
  have ht' : (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive : ℤ)*M.base.q.val =
      L*routingA M.base e+I*routingB M.base e := by exact_mod_cast ht
  have hsum' : (n : ℤ)+n'=principalIndex (routingH M.base e) M.base.q.val M.base.q_positive := by exact_mod_cast hsum
  have hs := P3R58.p3_coefficient_sums M hp e
  obtain ⟨hA,hJ,hK⟩ := rb_relation_of_bounds M hp e (L+d+d') I (i+i') (j+j')
    (by omega) (by omega) hIZ (by omega) (by omega)
    (by simp only [Nat.cast_add]; linear_combination -he-he'-ht'-(M.base.q.val : ℤ)*hsum')
    (Or.inl (by omega))
  exact ⟨by omega,hK,by omega⟩

/-- Complementary RB returns for the pure principal shape. -/
theorem rb_complement_pure (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (n n' i j d i' j' d' k : ℕ)
    (hsum : n+n'=principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hi : P3R57.roleCoefficient M hp e 0 1 < i)
    (hi' : P3R57.roleCoefficient M hp e 0 1 < i')
    (hj : 0<j) (hj' : 0<j')
    (hd : d<P3R57.roleCoefficient M hp e 1 0)
    (hd' : d'<P3R57.roleCoefficient M hp e 1 0)
    (hk : k<criticalExponent M.base (e 2))
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      k*routingC M.base e)
    (he : (i : ℤ)*routingB M.base e+j*routingC M.base e=
      n*M.base.q.val+d*routingA M.base e)
    (he' : (i' : ℤ)*routingB M.base e+j'*routingC M.base e=
      n'*M.base.q.val+d'*routingA M.base e) :
    i+i'=criticalExponent M.base (e 1) ∧
    j+j'+P3R57.roleCoefficient M hp e 1 2=k ∧
    d+d'=P3R57.roleCoefficient M hp e 1 0 := by
  have ht' : (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive : ℤ)*M.base.q.val =
      k*routingC M.base e := by exact_mod_cast ht
  have hsum' : (n : ℤ)+n'=principalIndex (routingH M.base e) M.base.q.val M.base.q_positive := by exact_mod_cast hsum
  have hrel : (criticalExponent M.base (e 2) : ℤ)*routingC M.base e=
      P3R57.roleCoefficient M hp e 2 0*routingA M.base e+
      P3R57.roleCoefficient M hp e 2 1*routingB M.base e := by
    exact_mod_cast P3R59.h3_normalized_relation M hp e
  have hs := P3R58.p3_coefficient_sums M hp e
  have hW := P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  obtain ⟨hA,hJ,hK⟩ := rb_relation_of_bounds M hp e
    (P3R57.roleCoefficient M hp e 2 0+d+d') (P3R57.roleCoefficient M hp e 2 1)
    (i+i') (j+j'+(criticalExponent M.base (e 2)-k))
    (by omega) (by omega) le_rfl (by omega) (by omega)
    (by simp only [Nat.cast_add]; rw [Nat.cast_sub hk.le]
        linear_combination -he-he'-ht'-(M.base.q.val : ℤ)*hsum'-hrel)
    (Or.inr rfl)
  exact ⟨by omega,by omega,by omega⟩

end NS25Lean.P3R63
