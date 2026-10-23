import NS25Lean.P3R1PrincipalWindowR65
import NS25Lean.P3CanonicalDivisorR61

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R65
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2B4AR1 L5A2C4H L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

/-- CU.01 in the signed basis of the first and second actual critical relations. -/
theorem signed_integer_kernel_basis (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (x y z : ℤ)
    (h : x*routingA M.base e+y*routingB M.base e+z*routingC M.base e=0) :
    ∃ l u : ℤ,
      x=(criticalExponent M.base (e 0):ℤ)*l-(P3R57.roleCoefficient M hp e 1 0:ℤ)*u ∧
      y= -(P3R57.roleCoefficient M hp e 0 1:ℤ)*l+(criticalExponent M.base (e 1):ℤ)*u ∧
      z= -(P3R57.roleCoefficient M hp e 0 2:ℤ)*l-(P3R57.roleCoefficient M hp e 1 2:ℤ)*u := by
  obtain ⟨l,k,hx,hy,hz⟩ := P3R59.p3_integer_kernel_basis M hp e x y z h
  have hs := P3R58.p3_coefficient_sums M hp e
  refine ⟨-l-k,-k,?_,?_,?_⟩
  · rw [hs.1] at hx ⊢
    push_cast at hx ⊢
    nlinarith only [hx]
  · rw [hs.2.1]
    push_cast
    nlinarith only [hy]
  · rw [hs.2.2] at hz
    push_cast at hz
    nlinarith only [hz]

/-- A complementary pair on the RB arm contradicts the principal window. -/
theorem rb_complement_impossible (P T U V W Z k D I J l u : ℤ)
    (hP : 0<P) (hT : 0<T) (hU : 0<U) (hV : 0<V) (hW : 0<W) (hZ : 0<Z)
    (hTk : T<k) (hkV : k≤V) (hD : 0<D) (hDu : D<2*U)
    (hJ : 0<J) (hJT : J<2*T)
    (heD : D=(U+W)*l-U*u) (heI : I=P*l-(P+Z)*u)
    (heJ : J=k+T*l+V*u) : False := by
  by_cases hu : 0≤u
  · have hl : 1≤l := by
      by_contra hn
      have hl0 : l≤0 := by omega
      nlinarith [mul_nonneg (show 0≤U+W by omega) (show 0≤-l by omega),
        mul_nonneg hU.le hu]
    nlinarith [mul_nonneg hT.le (show 0≤l-1 by omega),mul_nonneg hV.le hu]
  · have hu1 : 1≤-u := by omega
    have hl : 1≤l := by
      by_contra hn
      have hl0 : l≤0 := by omega
      nlinarith [mul_nonneg hT.le (show 0≤-l by omega),
        mul_nonneg hV.le (show 0≤-u-1 by omega)]
    nlinarith [mul_nonneg (show 0≤U+W by omega) (show 0≤l-1 by omega),
      mul_nonneg hU.le (show 0≤-u-1 by omega)]

/-- The LT bounds force exactly the first signed critical relation. -/
theorem lt_complement_coordinates (P T U V W Z k D I J l u : ℤ)
    (hP : 0<P) (hT : 0<T) (hU : 0<U) (hV : 0<V) (hW : 0<W) (hZ : 0<Z)
    (hkV : k≤V) (hD : 0<D) (hDW : D<2*W)
    (hI : 0<I) (hIP : I<2*P) (hJ : 0<J)
    (heD : D=(U+W)*l-U*u) (heI : I=P*l-(P+Z)*u)
    (heJ : J=k+T*l+V*u) : l=1 ∧ u=0 := by
  have hu0 : u=0 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hu | hu
    · have hu1 : 1≤-u := by omega
      have hl : 1≤l := by
        by_contra hn
        have hl0 : l≤0 := by omega
        nlinarith [mul_nonneg hT.le (show 0≤-l by omega),
          mul_nonneg hV.le (show 0≤-u-1 by omega)]
      nlinarith [mul_nonneg hP.le (show 0≤l-1 by omega),
        mul_nonneg (show 0≤P+Z by omega) (show 0≤-u-1 by omega)]
    · have hlu : u+1≤l := by
        by_contra hn
        have hle : l≤u := by omega
        nlinarith [mul_nonneg hP.le (show 0≤u-l by omega),mul_nonneg hZ.le hu.le]
      have hl2 : 2≤l := by omega
      nlinarith [mul_nonneg hW.le (show 0≤l-2 by omega),
        mul_nonneg hU.le (show 0≤l-u-1 by omega)]
  refine ⟨?_,hu0⟩
  rw [hu0] at heI
  simp only [mul_zero,sub_zero] at heI
  have hl0 : 0<l := by nlinarith
  have hl2 : l<2 := by nlinarith
  omega

#print axioms signed_integer_kernel_basis
#print axioms rb_complement_impossible
#print axioms lt_complement_coordinates

/-- The integral relation of complementary actual return values. -/
theorem complement_relation_coordinates (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (k q r i j d i' j' d' : ℕ)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=k*routingC M.base e)
    (hsum : q+r=principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (he : (i:ℤ)*routingB M.base e+j*routingC M.base e=q*M.base.q.val+d*routingA M.base e)
    (he' : (i':ℤ)*routingB M.base e+j'*routingC M.base e=r*M.base.q.val+d'*routingA M.base e) :
    ∃ l u : ℤ,
      (d:ℤ)+d'=((P3R57.roleCoefficient M hp e 1 0:ℤ)+P3R57.roleCoefficient M hp e 2 0)*l-
        P3R57.roleCoefficient M hp e 1 0*u ∧
      (i:ℤ)+i'=P3R57.roleCoefficient M hp e 0 1*l-
        ((P3R57.roleCoefficient M hp e 0 1:ℤ)+P3R57.roleCoefficient M hp e 2 1)*u ∧
      (j:ℤ)+j'=k+P3R57.roleCoefficient M hp e 0 2*l+P3R57.roleCoefficient M hp e 1 2*u := by
  have htotal : (q:ℤ)*M.base.q.val+r*M.base.q.val=k*routingC M.base e := by
    have hh := congrArg (fun n : ℕ => n*M.base.q.val) hsum
    rw [ht] at hh
    exact_mod_cast (show q*M.base.q.val+r*M.base.q.val=k*routingC M.base e by nlinarith only [hh])
  obtain ⟨l,u,hD,hI,hJ⟩ := signed_integer_kernel_basis M hp e
    ((d:ℤ)+d') (-((i:ℤ)+i')) ((k:ℤ)-j-j') (by nlinarith only [he,he',htotal])
  have hs := P3R58.p3_coefficient_sums M hp e
  rw [hs.1] at hD
  rw [hs.2.1] at hI
  push_cast at hD hI
  exact ⟨l,u,hD,by nlinarith only [hI],by nlinarith only [hJ]⟩

/-- CU.03: every actual nonprincipal return of the original pure-c role is LT. -/
theorem all_nonprincipal_lt (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (hb : killedCount M (criticalExponent M.base (e 1)*weights M.base (e 1))=1)
    (hc : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive : ∀ j : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base j ∈ M.base.apery)
    (k : ℕ) (hk : 0<k)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=k*routingC M.base e)
    (q : ℕ) (hq : 0<q)
    (hpre : q<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    P3R59.LTReturn M hp e q := by
  have hw := principal_window M hp e hb hlive k hk ht
  rcases P3R59.oneArmPrefix_of_legal_role M hp e hc hlive with hRB | hLT
  · let Q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
    have hr : 0<Q-q := by omega
    have hrQ : Q-q<Q := by omega
    obtain ⟨s,t,d,hs,hZ,ht0,htT,hd,hdU,he⟩ := hRB q hq hpre
    obtain ⟨s',t',d',hs',hZ',ht0',htT',hd',hdU',he'⟩ := hRB (Q-q) hr hrQ
    obtain ⟨l,u,hD,hI,hJ⟩ := complement_relation_coordinates M hp e k q (Q-q)
      (P3R57.roleCoefficient M hp e 0 1+s) t d
      (P3R57.roleCoefficient M hp e 0 1+s') t' d' ht (by dsimp [Q]; omega) he he'
    exfalso
    apply rb_complement_impossible
      (P3R57.roleCoefficient M hp e 0 1) (P3R57.roleCoefficient M hp e 0 2)
      (P3R57.roleCoefficient M hp e 1 0) (P3R57.roleCoefficient M hp e 1 2)
      (P3R57.roleCoefficient M hp e 2 0) (P3R57.roleCoefficient M hp e 2 1)
      k ((d:ℤ)+d') ((P3R57.roleCoefficient M hp e 0 1+s:ℕ)+
        (P3R57.roleCoefficient M hp e 0 1+s'):ℕ) ((t:ℤ)+t') l u
      (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 1 (by decide))
      (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 2 (by decide))
      (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 0 (by decide))
      (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 2 (by decide))
      (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 0 (by decide))
      (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 1 (by decide))
      (by exact_mod_cast hw.1) (by exact_mod_cast hw.2)
      (by omega) (by omega) (by omega) (by omega) hD (by simpa only [Nat.cast_add] using hI) hJ
  · exact hLT q hq hpre

#print axioms complement_relation_coordinates
#print axioms all_nonprincipal_lt


/-- CU.04: arbitrary complementary LT representatives have exact critical sums. -/
theorem complementary_lt_identities (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (hb : killedCount M (criticalExponent M.base (e 1)*weights M.base (e 1))=1)
    (hlive : ∀ j : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base j ∈ M.base.apery)
    (k : ℕ) (hk : 0<k)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=k*routingC M.base e)
    (q r i j d i' j' d' : ℕ)
    (hsum : q+r=principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hi : 0 < i) (hiP : i < P3R57.roleCoefficient M hp e 0 1)
    (hj : P3R57.roleCoefficient M hp e 0 2 < j) (hd : 0<d) (hdW : d < P3R57.roleCoefficient M hp e 2 0)
    (hi' : 0 < i') (hiP' : i' < P3R57.roleCoefficient M hp e 0 1)
    (hj' : P3R57.roleCoefficient M hp e 0 2 < j') (hd' : 0<d') (hdW' : d' < P3R57.roleCoefficient M hp e 2 0)
    (he : (i:ℤ)*routingB M.base e+j*routingC M.base e=q*M.base.q.val+d*routingA M.base e)
    (he' : (i':ℤ)*routingB M.base e+j'*routingC M.base e=r*M.base.q.val+d'*routingA M.base e) :
    d+d'=criticalExponent M.base (e 0) ∧ i+i'=P3R57.roleCoefficient M hp e 0 1 ∧
      j+j'=P3R57.roleCoefficient M hp e 0 2+k := by
  have hw := principal_window M hp e hb hlive k hk ht
  obtain ⟨l,u,hD,hI,hJ⟩ := complement_relation_coordinates M hp e k q r i j d i' j' d' ht hsum he he'
  obtain ⟨hl,hu⟩ := lt_complement_coordinates
    (P3R57.roleCoefficient M hp e 0 1) (P3R57.roleCoefficient M hp e 0 2)
    (P3R57.roleCoefficient M hp e 1 0) (P3R57.roleCoefficient M hp e 1 2)
    (P3R57.roleCoefficient M hp e 2 0) (P3R57.roleCoefficient M hp e 2 1)
    k ((d:ℤ)+d') ((i:ℤ)+i') ((j:ℤ)+j') l u
    (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 1 (by decide))
    (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 0 2 (by decide))
    (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 0 (by decide))
    (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 1 2 (by decide))
    (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 0 (by decide))
    (by exact_mod_cast P3R58.p3_coefficients_positive M hp e 2 1 (by decide))
    (by exact_mod_cast hw.2) (by omega) (by omega) (by omega) (by omega) (by omega) hD hI hJ
  rw [hl,hu] at hD hI hJ
  simp only [mul_one,mul_zero,sub_zero,add_zero] at hD hI hJ
  have hs := P3R58.p3_coefficient_sums M hp e
  refine ⟨?_,?_,?_⟩
  · rw [hs.1]
    exact_mod_cast hD
  · exact_mod_cast hI
  · exact_mod_cast (by linarith only [hJ] : (j:ℤ)+j'=P3R57.roleCoefficient M hp e 0 2+k)

/-- All-Q complementary returns, with both strict LT depths and exact sums. -/
theorem nonprincipal_complement (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (hb : killedCount M (criticalExponent M.base (e 1)*weights M.base (e 1))=1)
    (hc : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive : ∀ j : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base j ∈ M.base.apery)
    (k : ℕ) (hk : 0<k)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=k*routingC M.base e)
    (q : ℕ) (hq : 0<q)
    (hpre : q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive) :
    ∃ i j d i' j' d' : ℕ,
      0 < i ∧ i < P3R57.roleCoefficient M hp e 0 1 ∧
      P3R57.roleCoefficient M hp e 0 2 < j ∧ j < k ∧
      P3R57.roleCoefficient M hp e 1 0 < d ∧ d < P3R57.roleCoefficient M hp e 2 0 ∧
      0 < i' ∧ i' < P3R57.roleCoefficient M hp e 0 1 ∧
      P3R57.roleCoefficient M hp e 0 2 < j' ∧ j' < k ∧
      P3R57.roleCoefficient M hp e 1 0 < d' ∧ d' < P3R57.roleCoefficient M hp e 2 0 ∧
      d+d'=criticalExponent M.base (e 0) ∧ i+i'=P3R57.roleCoefficient M hp e 0 1 ∧
      j+j'=P3R57.roleCoefficient M hp e 0 2+k ∧
      (i:ℤ)*routingB M.base e+j*routingC M.base e=q*M.base.q.val+d*routingA M.base e ∧
      (i':ℤ)*routingB M.base e+j'*routingC M.base e=
        ((principalIndex (routingH M.base e) M.base.q.val M.base.q_positive-q:ℕ):ℤ)*M.base.q.val+d'*routingA M.base e := by
  let Q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  have hr : 0<Q-q := by omega
  have hrQ : Q-q<Q := by omega
  obtain ⟨i,t,d,hi,hiP,ht0,htV,hd,hdW,he⟩ := all_nonprincipal_lt M hp e hb hc hlive k hk ht q hq hpre
  obtain ⟨i',t',d',hi',hiP',ht0',htV',hd',hdW',he'⟩ := all_nonprincipal_lt M hp e hb hc hlive k hk ht (Q-q) hr hrQ
  have hj : P3R57.roleCoefficient M hp e 0 2 < P3R57.roleCoefficient M hp e 0 2+t := by omega
  have hj' : P3R57.roleCoefficient M hp e 0 2 < P3R57.roleCoefficient M hp e 0 2+t' := by omega
  obtain ⟨hds,his,hjs⟩ := complementary_lt_identities M hp e hb hlive k hk ht q (Q-q)
    i (P3R57.roleCoefficient M hp e 0 2+t) d i' (P3R57.roleCoefficient M hp e 0 2+t') d'
    (by dsimp [Q]; omega) hi hiP hj hd hdW hi' hiP' hj' hd' hdW' he he'
  have hs := P3R58.p3_coefficient_sums M hp e
  refine ⟨i,P3R57.roleCoefficient M hp e 0 2+t,d,i',P3R57.roleCoefficient M hp e 0 2+t',d',
    hi,hiP,hj,?_,?_,hdW,hi',hiP',hj',?_,?_,hdW',hds,his,hjs,he,he'⟩
  · omega
  · rw [hs.1] at hds
    omega
  · omega
  · rw [hs.1] at hds
    omega

#print axioms complementary_lt_identities
#print axioms nonprincipal_complement



/-- CU.04 depth bounds apply to every actual LTLevel, independently of choices. -/
theorem deep_lt_level (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base=3) (e : Fin 3 ≃ Fin 3)
    (hb : killedCount M (criticalExponent M.base (e 1)*weights M.base (e 1))=1)
    (hc : killedCount M (criticalExponent M.base (e 2)*weights M.base (e 2))=1)
    (hlive : ∀ j : Fin 3, criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base j ∈ M.base.apery)
    (k : ℕ) (hk : 0 < k)
    (ht : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val=k*routingC M.base e)
    (n i j d : ℕ) (hn : 0 < n)
    (hpre : n < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hl : P3R61.LTLevel M hp e n i j d) :
    P3R57.roleCoefficient M hp e 1 0 < d ∧ j < k := by
  let Q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  have hr : 0 < Q-n := by omega
  have hrQ : Q-n < Q := by omega
  obtain ⟨i',j',d',hl'⟩ := P3R61.lt_level_exists M hp e (Q-n)
    (all_nonprincipal_lt M hp e hb hc hlive k hk ht (Q-n) hr hrQ)
  rcases hl with ⟨hi0,hj0,hd0,hiP,hjT,hiB,hjC,hdW,he⟩
  rcases hl' with ⟨hi0',hj0',hd0',hiP',hjT',hiB',hjC',hdW',he'⟩
  obtain ⟨hds,his,hjs⟩ := complementary_lt_identities M hp e hb hlive k hk ht n (Q-n)
    i j d i' j' d' (by dsimp [Q]; omega) hi0 hiP hjT hd0 hdW hi0' hiP' hjT' hd0' hdW'
    (by simpa only [Nat.cast_mul] using he) (by simpa only [Nat.cast_mul] using he')
  have hs := P3R58.p3_coefficient_sums M hp e
  rw [hs.1] at hds
  constructor <;> omega

#print axioms deep_lt_level
end NS25Lean.P3R65
