import NS25Lean.P3HerzogLatticeR59
import NS25Lean.P3CanonicalReturnR59
import NS25Lean.P3ShadowArithmeticR59

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R59
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4OR6 L5A2B4AR1
variable {Gamma : NumericalSemigroup}

theorem same_degree_lattice (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (A B A' B' C' : ℕ)
    (he : A'*routingA M.base e+B'*routingB M.base e+C'*routingC M.base e =
      A*routingA M.base e+B*routingB M.base e) :
    ∃ l k : ℤ,
      (A' : ℤ)=A-(criticalExponent M.base (e 0) : ℤ)*l-
        (P3R57.roleCoefficient M hp e 2 0 : ℤ)*k ∧
      (B' : ℤ)=B+(P3R57.roleCoefficient M hp e 0 1 : ℤ)*l-
        (P3R57.roleCoefficient M hp e 2 1 : ℤ)*k ∧
      (C' : ℤ)=(P3R57.roleCoefficient M hp e 0 2 : ℤ)*l+
        (criticalExponent M.base (e 2) : ℤ)*k := by
  have heZ : (A' : ℤ)*routingA M.base e+B'*routingB M.base e+C'*routingC M.base e =
      A*routingA M.base e+B*routingB M.base e := by exact_mod_cast he
  obtain ⟨l,k,ha,hb,hc⟩ := p3_integer_kernel_basis M hp e ((A' : ℤ)-A) ((B' : ℤ)-B) C'
    (by nlinarith only [heZ])
  exact ⟨l,k,by linarith,by linarith,hc⟩

/-- Both mixed predecessors are covered by the actual W-by-Z rectangle. -/
theorem mixed_shadow_rb (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (A B q : ℕ)
    (hA : A ≤ P3R57.roleCoefficient M hp e 2 0)
    (hB : B ≤ P3R57.roleCoefficient M hp e 2 1) (hret : RBReturn M hp e q) :
    ((A*routingA M.base e+B*routingB M.base e : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (q*M.base.q.val) := by
  intro hx
  rcases hret with ⟨s,t,d,hs,_,ht,_,_,hd,hbeta⟩
  obtain ⟨n,hn,heq⟩ := hx.2
  obtain ⟨x,y,z,hfac⟩ := routingH_factorization M.base e hn
  have hnEq : A*routingA M.base e+B*routingB M.base e=q*M.base.q.val+n := by
    simp only [Nat.cast_add, Nat.cast_mul] at heq
    exact_mod_cast (show (A : ℤ)*routingA M.base e+B*routingB M.base e=
      q*M.base.q.val+n by omega)
  have hbN : (P3R57.roleCoefficient M hp e 0 1+s)*routingB M.base e+t*routingC M.base e=
      q*M.base.q.val+d*routingA M.base e := by exact_mod_cast hbeta
  have he : x*routingA M.base e+(P3R57.roleCoefficient M hp e 0 1+s+y)*routingB M.base e+
      (t+z)*routingC M.base e=(A+d)*routingA M.base e+B*routingB M.base e := by
    nlinarith only [hfac,hnEq,hbN]
  obtain ⟨l,k,ha,hb,hc⟩ := same_degree_lattice M hp e (A+d) B x
    (P3R57.roleCoefficient M hp e 0 1+s+y) (t+z) he
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hs1 : (criticalExponent M.base (e 0) : ℤ)=
      P3R57.roleCoefficient M hp e 1 0+P3R57.roleCoefficient M hp e 2 0 := by
    exact_mod_cast hsum.1
  have hs3 : (criticalExponent M.base (e 2) : ℤ)=
      P3R57.roleCoefficient M hp e 0 2+P3R57.roleCoefficient M hp e 1 2 := by
    exact_mod_cast hsum.2.2
  rw [hs1] at ha
  rw [hs3] at hc
  apply rb_shadow_arithmetic
    (P3R57.roleCoefficient M hp e 0 1) (P3R57.roleCoefficient M hp e 0 2)
    (P3R57.roleCoefficient M hp e 1 0) (P3R57.roleCoefficient M hp e 1 2)
    (P3R57.roleCoefficient M hp e 2 0) (P3R57.roleCoefficient M hp e 2 1)
    (A+d) B x (P3R57.roleCoefficient M hp e 0 1+s+y) (t+z) l k
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 0 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 2 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  · have hh : A+d < P3R57.roleCoefficient M hp e 1 0+
        P3R57.roleCoefficient M hp e 2 0 := by omega
    exact_mod_cast hh
  · exact_mod_cast hB
  · positivity
  · have hh : 0 < P3R57.roleCoefficient M hp e 0 1+s+y := by omega
    exact_mod_cast hh
  · have hh : 0 < t+z := by omega
    exact_mod_cast hh
  · exact ha
  · exact hb
  · exact hc

theorem mixed_shadow_lt (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (A B q : ℕ)
    (hA : A ≤ P3R57.roleCoefficient M hp e 2 0)
    (hB : B ≤ P3R57.roleCoefficient M hp e 2 1) (hret : LTReturn M hp e q) :
    ((A*routingA M.base e+B*routingB M.base e : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (q*M.base.q.val) := by
  intro hx
  rcases hret with ⟨s,t,d,hs,_,ht,_,_,hd,hbeta⟩
  obtain ⟨n,hn,heq⟩ := hx.2
  obtain ⟨x,y,z,hfac⟩ := routingH_factorization M.base e hn
  have hnEq : A*routingA M.base e+B*routingB M.base e=q*M.base.q.val+n := by
    simp only [Nat.cast_add, Nat.cast_mul] at heq
    exact_mod_cast (show (A : ℤ)*routingA M.base e+B*routingB M.base e=
      q*M.base.q.val+n by omega)
  have hbN : s*routingB M.base e+(P3R57.roleCoefficient M hp e 0 2+t)*routingC M.base e=
      q*M.base.q.val+d*routingA M.base e := by exact_mod_cast hbeta
  have he : x*routingA M.base e+(s+y)*routingB M.base e+
      (P3R57.roleCoefficient M hp e 0 2+t+z)*routingC M.base e=
      (A+d)*routingA M.base e+B*routingB M.base e := by
    nlinarith only [hfac,hnEq,hbN]
  obtain ⟨l,k,ha,hb,hc⟩ := same_degree_lattice M hp e (A+d) B x
    (s+y) (P3R57.roleCoefficient M hp e 0 2+t+z) he
  have hsum := P3R58.p3_coefficient_sums M hp e
  have hs1 : (criticalExponent M.base (e 0) : ℤ)=
      P3R57.roleCoefficient M hp e 1 0+P3R57.roleCoefficient M hp e 2 0 := by
    exact_mod_cast hsum.1
  have hs3 : (criticalExponent M.base (e 2) : ℤ)=
      P3R57.roleCoefficient M hp e 0 2+P3R57.roleCoefficient M hp e 1 2 := by
    exact_mod_cast hsum.2.2
  rw [hs1] at ha
  rw [hs3] at hc
  apply lt_shadow_arithmetic
    (P3R57.roleCoefficient M hp e 0 1) (P3R57.roleCoefficient M hp e 0 2)
    (P3R57.roleCoefficient M hp e 1 0) (P3R57.roleCoefficient M hp e 1 2)
    (P3R57.roleCoefficient M hp e 2 0) (P3R57.roleCoefficient M hp e 2 1)
    (A+d) B x (s+y) (P3R57.roleCoefficient M hp e 0 2+t+z) l k
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 2 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 0 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 2 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  · exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  · have hh : A+d < 2*P3R57.roleCoefficient M hp e 2 0 := by omega
    exact_mod_cast hh
  · exact_mod_cast hB
  · positivity
  · have hh : 0 < s+y := by omega
    exact_mod_cast hh
  · have hh : P3R57.roleCoefficient M hp e 0 2 <
        P3R57.roleCoefficient M hp e 0 2+t+z := by omega
    exact_mod_cast hh
  · exact ha
  · exact hb
  · exact hc

end NS25Lean.P3R59
