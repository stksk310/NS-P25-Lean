import NS25Lean.P3R3PrincipalR67
import NS25Lean.P3R3ComplementR67
import NS25Lean.P3HerzogLatticeR59
import NS25Lean.P3CriticalDivisorAlignment
set_option linter.style.header false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4OR6 L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- A pure relation bounds the actual normalized critical exponent. -/
theorem normalized_pure_minimum (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j : Fin 3) (hij : j ≠ i) (x y : ℕ) (hx : 0 < x)
    (he : x*P3R59.normalizedRoleWeight B e i = y*P3R59.normalizedRoleWeight B e j) :
    criticalExponent B (e i) ≤ x := by
  apply P3R57.critical_pair_minimum B (e i) (e j) (e j)
    (e.injective.ne hij) (e.injective.ne hij) x y 0 hx
  have h := congrArg (fun t => routingD B e*t) he
  rw [← P3R59.normalizedRoleWeight_scale B e i,
      ← P3R59.normalizedRoleWeight_scale B e j]
  nlinarith only [h]

/-- Elementary pure-critical exclusion, including boundary and pure-axis cases. -/
theorem critical_not_pure_aux (a b c A P T C : ℕ)
    (hb : 0 < b) (hT : 0 < T) (hTC : T < C)
    (hrel : A*a=P*b+T*c) (hc : 0 < c)
    (hmin : ∀ x y : ℕ, 0 < x → x*c=y*b → C ≤ x) :
    ∀ k : ℕ, A*a ≠ k*b := by
  intro k he
  have hPk : P < k := by nlinarith
  have hsub := Nat.sub_add_cancel hPk.le
  have hpure : T*c=(k-P)*b := by nlinarith [congrArg (fun t => t*b) hsub]
  have := hmin T (k-P) hT hpure
  omega

/-- Uniqueness in one zero-coordinate plane at the syzygy degree. -/
theorem critical_plane_unique_aux (a b A B Z x y : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hZ : Z < B)
    (hminA : ∀ r s : ℕ, 0 < r → r*a=s*b → A ≤ r)
    (hminB : ∀ r s : ℕ, 0 < r → r*b=s*a → B ≤ r)
    (hpure : ∀ k : ℕ, A*a ≠ k*b)
    (he : x*a+y*b=A*a+Z*b) : x=A ∧ y=Z := by
  by_cases hx : x=A
  · exact ⟨hx, by rw [hx] at he; nlinarith⟩
  rcases lt_or_gt_of_ne hx with hx | hx
  · by_cases hx0 : x=0
    · subst x; simp only [zero_mul,zero_add] at he
      have hZy : Z ≤ y := by nlinarith
      have hs := Nat.sub_add_cancel hZy
      apply False.elim
      apply hpure (y-Z)
      nlinarith [congrArg (fun t => t*b) hs]
    have hZy : Z < y := by nlinarith
    have hs := Nat.sub_add_cancel hx.le
    have ht := Nat.sub_add_cancel hZy.le
    have hm := hminA (A-x) (y-Z) (by omega) (by nlinarith [congrArg (fun t => t*a) hs,congrArg (fun t => t*b) ht])
    omega
  · have hyZ : y < Z := by nlinarith
    have hs := Nat.sub_add_cancel hx.le
    have ht := Nat.sub_add_cancel hyZ.le
    have hm := hminB (Z-y) (x-A) (by omega) (by nlinarith [congrArg (fun t => t*a) hs,congrArg (fun t => t*b) ht])
    omega



/-- The integral Herzog lattice has exactly three nonnegative points over this degree. -/
theorem omega_lattice_points (P T U V W Z l k x y z : ℤ)
    (hP : 0<P) (hT : 0<T) (hU : 0<U) (hV : 0<V) (hW : 0<W) (hZ : 0<Z)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z)
    (hex : x=(U+W)*(1-l)-W*k)
    (hey : y=Z+P*l-Z*k) (hez : z=T*l+(T+V)*k) :
    (x=U+W ∧ y=Z ∧ z=0) ∨ (x=0 ∧ y=P+Z ∧ z=T) ∨ (x=U ∧ y=0 ∧ z=T+V) := by
  have hl : 0≤l := by
    by_contra h
    have hl : l≤-1 := by omega
    by_cases hk : k≤0
    · have ht := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤T+V) hk
      nlinarith
    · have hk : 1≤k := by omega
      have ht := mul_nonneg (by linarith : 0≤Z) (by omega : 0≤k-1)
      nlinarith
  have hk : 0≤k := by
    by_contra h
    have hk : k≤-1 := by omega
    have hlk : 1≤l+k := by
      by_contra h
      have hs : l+k≤0 := by omega
      have ht := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤T) hs
      nlinarith
    have ht := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤U+W) (by omega : 1-l-k≤0)
    nlinarith
  by_cases hl0 : l=0
  · have hk1 : k≤1 := by
      by_contra h
      have hk2 : 2≤k := by omega
      have ht := mul_nonneg (by linarith : 0≤Z) (by omega : 0≤k-2)
      nlinarith
    have hkcases : k=0 ∨ k=1 := by omega
    rcases hkcases with hk0 | hk1
    · left; simp_all
    · right; right; simp_all
  · have hl1 : 1≤l := by omega
    have ht := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤U+W) (by omega : 1-l≤0)
    have hk0 : k=0 := by nlinarith
    have hlone : l=1 := by
      by_contra h
      have hl2 : 2≤l := by omega
      have ht := mul_nonneg (by linarith : 0≤U+W) (by omega : 0≤l-2)
      nlinarith
    right; left; simp_all [add_comm]

/-- The actual common syzygy degree, expressed in normalized physical generators. -/
def omegaDegree (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) : ℕ :=
  criticalExponent M.base (e 0)*routingA M.base e +
    P3R57.roleCoefficient M hp e 2 1 * routingB M.base e

/-- NF.02: complete factorization table of the actual syzygy degree. -/
theorem omega_factorization_table (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (x y z : ℕ)
    (he : x*routingA M.base e+y*routingB M.base e+z*routingC M.base e = omegaDegree M hp e) :
    (x=criticalExponent M.base (e 0) ∧ y=P3R57.roleCoefficient M hp e 2 1 ∧ z=0) ∨
    (x=0 ∧ y=criticalExponent M.base (e 1) ∧ z=P3R57.roleCoefficient M hp e 0 2) ∨
    (x=P3R57.roleCoefficient M hp e 1 0 ∧ y=0 ∧ z=criticalExponent M.base (e 2)) := by
  have heZ : ((x:ℤ)-criticalExponent M.base (e 0))*routingA M.base e+
      ((y:ℤ)-P3R57.roleCoefficient M hp e 2 1)*routingB M.base e+(z:ℤ)*routingC M.base e=0 := by
    dsimp [omegaDegree] at he
    have hh : (x:ℤ)*(routingA M.base e)+(y:ℤ)*routingB M.base e+(z:ℤ)*routingC M.base e =
      (criticalExponent M.base (e 0):ℤ)*routingA M.base e+
        (P3R57.roleCoefficient M hp e 2 1:ℤ)*routingB M.base e := by exact_mod_cast he
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
  have htable := omega_lattice_points
    (P3R57.roleCoefficient M hp e 0 1) (P3R57.roleCoefficient M hp e 0 2)
    (P3R57.roleCoefficient M hp e 1 0) (P3R57.roleCoefficient M hp e 1 2)
    (P3R57.roleCoefficient M hp e 2 0) (P3R57.roleCoefficient M hp e 2 1)
    l k x y z (by exact_mod_cast hp0) (by exact_mod_cast ht0) (by exact_mod_cast hu0)
    (by exact_mod_cast hv0) (by exact_mod_cast hw0) (by exact_mod_cast hz0)
    (by positivity) (by positivity) (by positivity) (by push_cast at hl ⊢; nlinarith only [hl])
    (by linarith only [hk]) (by push_cast at hz ⊢; exact hz)
  rw [hs.1,hs.2.1,hs.2.2]
  exact_mod_cast htable

/-- Two factors complementary to the same live principal factor must coincide. -/
theorem complement_table_unique_aux (A B C U Z T fa fb fc x y z x' y' z' : ℕ)
    (hUA : U<A) (hZB : Z<B) (hTC : T<C)
    (hfa : fb=0 → fc=0 → A≤fa) (hfb : fa=0 → fc=0 → B≤fb)
    (hfc : fa=0 → fb=0 → C≤fc)
    (h : (fa+x=A ∧ fb+y=Z ∧ fc+z=0) ∨ (fa+x=0 ∧ fb+y=B ∧ fc+z=T) ∨
      (fa+x=U ∧ fb+y=0 ∧ fc+z=C))
    (h' : (fa+x'=A ∧ fb+y'=Z ∧ fc+z'=0) ∨ (fa+x'=0 ∧ fb+y'=B ∧ fc+z'=T) ∨
      (fa+x'=U ∧ fb+y'=0 ∧ fc+z'=C)) : x=x' ∧ y=y' ∧ z=z' := by
  rcases h with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;>
    rcases h' with ⟨h4,h5,h6⟩ | ⟨h4,h5,h6⟩ | ⟨h4,h5,h6⟩ <;>
    first | omega | (have := hfa (by omega) (by omega); omega) |
      (have := hfb (by omega) (by omega); omega) |
      (have := hfc (by omega) (by omega); omega)

/-- NF.04: the signed semigroup complement of the actual principal degree has
at most one factorization, including the zero complement. -/
theorem principal_complement_factorization_unique (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (x y z x' y' z' : ℕ)
    (h : ((omegaDegree M hp e : ℕ) : ℤ) -
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val : ℕ) =
      (x:ℤ)*routingA M.base e+y*routingB M.base e+z*routingC M.base e)
    (h' : ((omegaDegree M hp e : ℕ) : ℤ) -
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val : ℕ) =
      (x':ℤ)*routingA M.base e+y'*routingB M.base e+z'*routingC M.base e) :
    x=x' ∧ y=y' ∧ z=z' := by
  by_contra hne
  have hneq : (x,y,z) ≠ (x',y',z') := by
    intro he
    have hx := congrArg (fun p : ℕ × ℕ × ℕ => p.1) he
    have hy := congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) he
    have hz := congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) he
    exact hne ⟨hx,hy,hz⟩
  have hdegree : L5A2C4OR20.monomialDegree M.base e (x,y,z) =
      L5A2C4OR20.monomialDegree M.base e (x',y',z') := by
    change x*routingA M.base e+y*routingB M.base e+z*routingC M.base e =
      x'*routingA M.base e+y'*routingB M.base e+z'*routingC M.base e
    have heZ : ((x*routingA M.base e+y*routingB M.base e+z*routingC M.base e:ℕ):ℤ) =
        ((x'*routingA M.base e+y'*routingB M.base e+z'*routingC M.base e:ℕ):ℤ) := by
      simp only [Nat.cast_add,Nat.cast_mul]
      linarith only [h,h']
    exact_mod_cast heZ
  obtain ⟨k,r,hr,hdiv⟩ := P3CriticalDivisor.nonunique_critical_divisor M.base e
    (P3R58.p3_coherentHerzogData M hp e) (x,y,z) (x',y',z') hdegree hneq
  let Q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  have hQ := (principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive).1
  have hs := P3R58.p3_coefficient_sums M hp e
  have hrels := L5A2C4OR5.coherent_normalized_relations M.base e
    (P3R58.p3_coherentHerzogData M hp e)
  have hsum : L5A2C4OR20.monomialDegree M.base e (x,y,z)+Q*M.base.q.val=
      omegaDegree M hp e := by
    have hN : (x*routingA M.base e+y*routingB M.base e+z*routingC M.base e)+Q*M.base.q.val=
        omegaDegree M hp e := by
      have heZ : (((x*routingA M.base e+y*routingB M.base e+z*routingC M.base e)+Q*M.base.q.val:ℕ):ℤ)=
          (omegaDegree M hp e:ℤ) := by
        dsimp only [Q]
        simp only [Nat.cast_add,Nat.cast_mul]
        have hh := h
        simp only [Nat.cast_mul] at hh
        linarith only [hh]
      exact_mod_cast heZ
    exact hN
  have absent (axis : Fin 3) (t : ℕ) (ht : t<criticalExponent M.base (e axis))
      (he : t*P3R59.normalizedRoleWeight M.base e axis=Q*M.base.q.val+r) : False := by
    apply live_subcritical_pure_return_absent M hp hR3 e axis t Q ht hQ
    have hg : P3R59.normalizedRoleWeight M.base e axis ∈ routingH M.base e := by
      apply (P3R59.routing_scaled_mem_iff M.base e _).mp
      rw [P3R59.normalizedRoleWeight_scale]
      exact (M.base.tailDegrees (e axis)).property
    refine ⟨⟨_,(routingH M.base e).toAddSubmonoid.nsmul_mem hg t,rfl⟩,r,hr,?_⟩
    rw [he]
    push_cast
    ring
  fin_cases k
  · apply absent 1 (P3R57.roleCoefficient M hp e 2 1)
      (P3R57.roleCoefficient_lt_critical M hp e 2 1 (by decide))
    change _ = criticalExponent M.base (e 0)*routingA M.base e+r at hdiv
    change _*routingB M.base e=Q*M.base.q.val+r
    dsimp only [omegaDegree] at hsum
    omega
  · apply absent 2 (P3R57.roleCoefficient M hp e 0 2)
      (P3R57.roleCoefficient_lt_critical M hp e 0 2 (by decide))
    change _ = criticalExponent M.base (e 1)*routingB M.base e+r at hdiv
    change _*routingC M.base e=Q*M.base.q.val+r
    have ha := hrels.1
    change criticalExponent M.base (e 0)*routingA M.base e=
      P3R57.roleCoefficient M hp e 0 1*routingB M.base e+
      P3R57.roleCoefficient M hp e 0 2*routingC M.base e at ha
    dsimp only [omegaDegree] at hsum
    have heB := congrArg (fun n => n*routingB M.base e) hs.2.1
    nlinarith only [hdiv,hsum,ha,heB]
  · apply absent 0 (P3R57.roleCoefficient M hp e 1 0)
      (P3R57.roleCoefficient_lt_critical M hp e 1 0 (by decide))
    change _ = criticalExponent M.base (e 2)*routingC M.base e+r at hdiv
    change _*routingA M.base e=Q*M.base.q.val+r
    have hc := hrels.2.2
    change criticalExponent M.base (e 2)*routingC M.base e=
      P3R57.roleCoefficient M hp e 2 0*routingA M.base e+
      P3R57.roleCoefficient M hp e 2 1*routingB M.base e at hc
    dsimp only [omegaDegree] at hsum
    have heA := congrArg (fun n => n*routingA M.base e) hs.1
    nlinarith only [hdiv,hsum,hc,heA]


/-- NF.05: any actual principal factorization has a supported deficit surplus.
The explicit level-one identity and box inequalities are the genuine return data. -/
theorem supported_deficit_surplus (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (tx ty tz fa fb fc x y z : ℕ)
    (hQ : 1 < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (htx : 0<tx) (hty : 0<ty) (htz : 0<tz)
    (htA : tx<criticalExponent M.base (e 0))
    (htB : ty<criticalExponent M.base (e 1))
    (htC : tz<criticalExponent M.base (e 2))
    (hlevel : M.base.q.val+tx*routingA M.base e+ty*routingB M.base e+tz*routingC M.base e=omegaDegree M hp e)
    (hf : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      fa*routingA M.base e+fb*routingB M.base e+fc*routingC M.base e)
    (hcomp : ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) =
      (x:ℤ)*routingA M.base e+y*routingB M.base e+z*routingC M.base e) :
    (0<fa ∧ x<tx) ∨ (0<fb ∧ y<ty) ∨ (0<fc ∧ z<tz) := by
  by_contra hn
  have hfa : 0<fa → tx≤x := by omega
  have hfb : 0<fb → ty≤y := by omega
  have hfc : 0<fc → tz≤z := by omega
  have hpa : fb=0 → fc=0 → criticalExponent M.base (e 0) ≤ fa := by
    intro hb hc; apply principal_pure_ge_critical M hp hR3 e 0 fa
    simpa [hb,hc,P3R59.normalizedRoleWeight] using hf
  have hpb : fa=0 → fc=0 → criticalExponent M.base (e 1) ≤ fb := by
    intro ha hc; apply principal_pure_ge_critical M hp hR3 e 1 fb
    simpa [ha,hc,P3R59.normalizedRoleWeight] using hf
  have hpc : fa=0 → fb=0 → criticalExponent M.base (e 2) ≤ fc := by
    intro ha hb; apply principal_pure_ge_critical M hp hR3 e 2 fc
    simpa [ha,hb,P3R59.normalizedRoleWeight] using hf
  have hh : (fa+x)*routingA M.base e+(fb+y)*routingB M.base e+(fc+z)*routingC M.base e=omegaDegree M hp e := by
    have hfZ : (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive:ℤ)*M.base.q.val =
      (fa:ℤ)*routingA M.base e+fb*routingB M.base e+fc*routingC M.base e := by exact_mod_cast hf
    have hhZ : ((fa+x:ℕ):ℤ)*routingA M.base e+((fb+y:ℕ):ℤ)*routingB M.base e+
        ((fc+z:ℕ):ℤ)*routingC M.base e=(omegaDegree M hp e:ℤ) := by
      simp only [Nat.cast_add,Nat.cast_mul] at hcomp ⊢
      nlinarith only [hfZ,hcomp]
    exact_mod_cast hhZ
  have hdelta : (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive-1)*M.base.q.val+
      x*routingA M.base e+y*routingB M.base e+z*routingC M.base e =
      tx*routingA M.base e+ty*routingB M.base e+tz*routingC M.base e := by
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    have heZ : ((principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ):ℤ)+
      (x:ℤ)*routingA M.base e+y*routingB M.base e+z*routingC M.base e=(omegaDegree M hp e:ℤ) := by linarith
    have heN : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val+
      x*routingA M.base e+y*routingB M.base e+z*routingC M.base e=omegaDegree M hp e := by exact_mod_cast heZ
    nlinarith only [heN,hlevel,congrArg (fun t => t*M.base.q.val) hs]
  have hu := P3R57.roleCoefficient_lt_critical M hp e 1 0 (by decide)
  have hz := P3R57.roleCoefficient_lt_critical M hp e 2 1 (by decide)
  have ht := P3R57.roleCoefficient_lt_critical M hp e 0 2 (by decide)
  rcases omega_factorization_table M hp e _ _ _ hh with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
  · have hfc0 : fc=0 := by omega
    have hz0 : z=0 := by omega
    rw [hz0,zero_mul,add_zero] at hdelta
    have hfa0 : 0<fa := by by_contra h; have := hpb (by omega) hfc0; omega
    have hfb0 : 0<fb := by by_contra h; have := hpa (by omega) hfc0; have := hfa hfa0; omega
    have hx := hfa hfa0
    have hy := hfb hfb0
    apply live_subcritical_pure_return_absent M hp hR3 e 2 tz (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive-1) htC (by omega)
    apply two_generator_return M.base e 0 1 2 tz _ (x-tx) (y-ty)
    change tz*routingC M.base e = (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive-1)*M.base.q.val+(x-tx)*routingA M.base e+(y-ty)*routingB M.base e
    have hs := Nat.sub_add_cancel hx
    have ht := Nat.sub_add_cancel hy
    nlinarith only [hdelta,congrArg (fun t => t*routingA M.base e) hs,
      congrArg (fun t => t*routingB M.base e) ht,hz0]
  · have hfa0 : fa=0 := by omega
    have hx0 : x=0 := by omega
    rw [hx0,zero_mul,add_zero] at hdelta
    have hfb0 : 0<fb := by by_contra h; have := hpc hfa0 (by omega); omega
    have hfc0 : 0<fc := by by_contra h; have := hpb hfa0 (by omega); have := hfb hfb0; omega
    have hy := hfb hfb0
    have hz := hfc hfc0
    apply live_subcritical_pure_return_absent M hp hR3 e 0 tx (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive-1) htA (by omega)
    apply two_generator_return M.base e 1 2 0 tx _ (y-ty) (z-tz)
    change tx*routingA M.base e = (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive-1)*M.base.q.val+(y-ty)*routingB M.base e+(z-tz)*routingC M.base e
    have hs := Nat.sub_add_cancel hy
    have ht := Nat.sub_add_cancel hz
    nlinarith only [hdelta,congrArg (fun t => t*routingB M.base e) hs,
      congrArg (fun t => t*routingC M.base e) ht,hx0]
  · have hfb0 : fb=0 := by omega
    have hy0 : y=0 := by omega
    rw [hy0,zero_mul,add_zero] at hdelta
    have hfc0 : 0<fc := by by_contra h; have := hpa hfb0 (by omega); omega
    have hfa0 : 0<fa := by by_contra h; have := hpc (by omega) hfb0; have := hfc hfc0; omega
    have hx := hfa hfa0
    have hz := hfc hfc0
    apply live_subcritical_pure_return_absent M hp hR3 e 1 ty (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive-1) htB (by omega)
    apply two_generator_return M.base e 0 2 1 ty _ (x-tx) (z-tz)
    change ty*routingB M.base e = (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive-1)*M.base.q.val+(x-tx)*routingA M.base e+(z-tz)*routingC M.base e
    have hs := Nat.sub_add_cancel hx
    have ht := Nat.sub_add_cancel hz
    nlinarith only [hdelta,congrArg (fun t => t*routingA M.base e) hs,
      congrArg (fun t => t*routingC M.base e) ht,hy0]


/-- NF.06 arithmetic protection in any chosen physical axis, before cyclic role transport. -/
theorem complement_sub_supported_axis_absent (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (x y z D : ℕ) (k : Fin 3)
    (hD : ![x,y,z] k < D)
    (hcomp : ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) =
      (x:ℤ)*routingA M.base e+y*routingB M.base e+z*routingC M.base e) :
    ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ)-
      D*P3R59.normalizedRoleWeight M.base e k ∉ (routingH M.base e).asRelativeIdeal := by
  rintro ⟨n,hn,he⟩
  obtain ⟨u,v,w,hf⟩ := routingH_factorization M.base e hn
  have hfZ : (n:ℤ)=(u:ℤ)*routingA M.base e+v*routingB M.base e+w*routingC M.base e := by exact_mod_cast hf
  fin_cases k
  · have he' : ((omegaDegree M hp e:ℕ):ℤ)-
        (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) =
        ((u+D:ℕ):ℤ)*routingA M.base e+v*routingB M.base e+w*routingC M.base e := by
      change _-D*(routingA M.base e:ℤ)=(n:ℤ) at he
      simp only [Nat.cast_add]; nlinarith only [he,hfZ]
    have hu := (principal_complement_factorization_unique M hp hR3 e x y z (u+D) v w hcomp he').1
    change x<D at hD
    omega
  · have he' : ((omegaDegree M hp e:ℕ):ℤ)-
        (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) =
        (u:ℤ)*routingA M.base e+((v+D:ℕ):ℤ)*routingB M.base e+w*routingC M.base e := by
      change _-D*(routingB M.base e:ℤ)=(n:ℤ) at he
      simp only [Nat.cast_add]; nlinarith only [he,hfZ]
    have hu := (principal_complement_factorization_unique M hp hR3 e x y z u (v+D) w hcomp he').2.1
    norm_num at hD
    omega
  · have he' : ((omegaDegree M hp e:ℕ):ℤ)-
        (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) =
        (u:ℤ)*routingA M.base e+v*routingB M.base e+((w+D:ℕ):ℤ)*routingC M.base e := by
      change _-D*(routingC M.base e:ℤ)=(n:ℤ) at he
      simp only [Nat.cast_add]; nlinarith only [he,hfZ]
    have hu := (principal_complement_factorization_unique M hp hR3 e x y z u v (w+D) hcomp he').2.2
    norm_num at hD
    omega


/-- Actual level-one RB data populates the positive deficit box and Omega identity. -/
theorem rb_level_one_deficits (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hRB : P3R59.RBReturn M hp e 1) :
    ∃ tx ty tz : ℕ, 0<tx ∧ 0<ty ∧ 0<tz ∧
      tx<P3R57.roleCoefficient M hp e 1 0 ∧
      ty<P3R57.roleCoefficient M hp e 2 1 ∧
      tz<P3R57.roleCoefficient M hp e 0 2 ∧
      M.base.q.val+tx*routingA M.base e+ty*routingB M.base e+tz*routingC M.base e=omegaDegree M hp e := by
  obtain ⟨s,t,d,hs,hsZ,ht,htT,hd,hdU,he⟩ := hRB
  refine ⟨d,P3R57.roleCoefficient M hp e 2 1-s,P3R57.roleCoefficient M hp e 0 2-t,
    hd,by omega,by omega,hdU,by omega,by omega,?_⟩
  have heN : (P3R57.roleCoefficient M hp e 0 1+s)*routingB M.base e+t*routingC M.base e =
      M.base.q.val+d*routingA M.base e := by simpa only [one_mul] using (show
      (P3R57.roleCoefficient M hp e 0 1+s)*routingB M.base e+t*routingC M.base e =
      1*M.base.q.val+d*routingA M.base e from by exact_mod_cast he)
  have hr := (L5A2C4OR5.coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)).1
  change criticalExponent M.base (e 0)*routingA M.base e =
      P3R57.roleCoefficient M hp e 0 1*routingB M.base e+
      P3R57.roleCoefficient M hp e 0 2*routingC M.base e at hr
  have hs' := Nat.sub_add_cancel hsZ.le
  have ht' := Nat.sub_add_cancel htT.le
  dsimp [omegaDegree]
  nlinarith only [heN,hr,congrArg (fun v => v*routingB M.base e) hs',congrArg (fun v => v*routingC M.base e) ht']

/-- NF.05 on actual level-one RB returns, with no abstract box caller obligation. -/
theorem actual_rb_supported_surplus (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hRB : P3R59.RBReturn M hp e 1) (fa fb fc x y z : ℕ)
    (hf : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val =
      fa*routingA M.base e+fb*routingB M.base e+fc*routingC M.base e)
    (hcomp : ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) =
      (x:ℤ)*routingA M.base e+y*routingB M.base e+z*routingC M.base e) :
    ∃ tx ty tz : ℕ, 0<tx ∧ 0<ty ∧ 0<tz ∧
      tx<P3R57.roleCoefficient M hp e 1 0 ∧
      ty<P3R57.roleCoefficient M hp e 2 1 ∧
      tz<P3R57.roleCoefficient M hp e 0 2 ∧
      M.base.q.val+tx*routingA M.base e+ty*routingB M.base e+tz*routingC M.base e=omegaDegree M hp e ∧
      ((0<fa ∧ x<tx) ∨ (0<fb ∧ y<ty) ∨ (0<fc ∧ z<tz)) := by
  obtain ⟨tx,ty,tz,htx,hty,htz,htU,htZ,htT,hlevel⟩ := rb_level_one_deficits M hp e hRB
  refine ⟨tx,ty,tz,htx,hty,htz,htU,htZ,htT,hlevel,?_⟩
  apply supported_deficit_surplus M hp hR3 e tx ty tz fa fb fc x y z hQ htx hty htz
    (htU.trans (P3R57.roleCoefficient_lt_critical M hp e 1 0 (by decide)))
    (htZ.trans (P3R57.roleCoefficient_lt_critical M hp e 2 1 (by decide)))
    (htT.trans (P3R57.roleCoefficient_lt_critical M hp e 0 2 (by decide))) hlevel hf hcomp


/-- NF.06 coordinate selection when the signed complement lies in H.
The selected physical coordinate is ready for actual cyclic role transport. -/
theorem actual_rb_safe_axis_of_complement_mem (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hRB : P3R59.RBReturn M hp e 1)
    (hmem : ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) ∈
      (routingH M.base e).asRelativeIdeal) :
    ∃ tx ty tz : ℕ, 0<tx ∧ 0<ty ∧ 0<tz ∧
      tx<P3R57.roleCoefficient M hp e 1 0 ∧ ty<P3R57.roleCoefficient M hp e 2 1 ∧
      tz<P3R57.roleCoefficient M hp e 0 2 ∧
      M.base.q.val+tx*routingA M.base e+ty*routingB M.base e+tz*routingC M.base e=omegaDegree M hp e ∧
      ∃ k : Fin 3,
      ((principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ):ℤ)-
        P3R59.normalizedRoleWeight M.base e k ∈ (routingH M.base e).asRelativeIdeal ∧
      ∀ D : ℕ, ![tx,ty,tz] k ≤ D →
      ((omegaDegree M hp e:ℕ):ℤ)-
        (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ)-
        D*P3R59.normalizedRoleWeight M.base e k ∉ (routingH M.base e).asRelativeIdeal := by
  obtain ⟨fa,fb,fc,hf⟩ := routingH_factorization M.base e
    (principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive).2
  obtain ⟨n,hn,he⟩ := hmem
  obtain ⟨x,y,z,hfac⟩ := routingH_factorization M.base e hn
  have hcomp : ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) =
      (x:ℤ)*routingA M.base e+y*routingB M.base e+z*routingC M.base e := by
    rw [he,hfac]; simp only [Nat.cast_add,Nat.cast_mul]
  obtain ⟨tx,ty,tz,htx,hty,htz,htU,htZ,htT,hlevel,hsur⟩ := actual_rb_supported_surplus M hp hR3 e hQ hRB fa fb fc x y z hf hcomp
  refine ⟨tx,ty,tz,htx,hty,htz,htU,htZ,htT,hlevel,?_⟩
  rcases hsur with ⟨hfa,hx⟩ | ⟨hfb,hy⟩ | ⟨hfc,hz⟩
  · refine ⟨0,factorization_sub_supported_mem M.base e _ fa fb fc 0 hf (by exact hfa),?_⟩
    intro D hD
    apply complement_sub_supported_axis_absent M hp hR3 e x y z D 0 (by change tx≤D at hD; change x<D; omega) hcomp
  · refine ⟨1,factorization_sub_supported_mem M.base e _ fa fb fc 1 hf (by exact hfb),?_⟩
    intro D hD
    apply complement_sub_supported_axis_absent M hp hR3 e x y z D 1 (by change ty≤D at hD; change y<D; omega) hcomp
  · refine ⟨2,factorization_sub_supported_mem M.base e _ fa fb fc 2 hf (by exact hfc),?_⟩
    intro D hD
    apply complement_sub_supported_axis_absent M hp hR3 e x y z D 2 (by change tz≤D at hD; change z<D; omega) hcomp


/-- NF.06 physical axis choice in both signed complement branches.
Only the subsequent actual cyclic reindexing and maximum transport remain. -/
theorem actual_rb_safe_axis (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hRB : P3R59.RBReturn M hp e 1) :
    ∃ tx ty tz : ℕ, 0<tx ∧ 0<ty ∧ 0<tz ∧
      tx<P3R57.roleCoefficient M hp e 1 0 ∧ ty<P3R57.roleCoefficient M hp e 2 1 ∧
      tz<P3R57.roleCoefficient M hp e 0 2 ∧
      M.base.q.val+tx*routingA M.base e+ty*routingB M.base e+tz*routingC M.base e=omegaDegree M hp e ∧
      ∃ k : Fin 3,
      ((principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ):ℤ)-
        P3R59.normalizedRoleWeight M.base e k ∈ (routingH M.base e).asRelativeIdeal ∧
      ∀ D : ℕ, ![tx,ty,tz] k ≤ D →
      ((omegaDegree M hp e:ℕ):ℤ)-
        (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ)-
        D*P3R59.normalizedRoleWeight M.base e k ∉ (routingH M.base e).asRelativeIdeal := by
  by_cases hm : ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) ∈
      (routingH M.base e).asRelativeIdeal
  · exact actual_rb_safe_axis_of_complement_mem M hp hR3 e hQ hRB hm
  · obtain ⟨tx,ty,tz,htx,hty,htz,htU,htZ,htT,hlevel⟩ := rb_level_one_deficits M hp e hRB
    have hspec := principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive
    obtain ⟨k,n,hn,he⟩ := positive_tail_has_generator M.base e _ hspec.2
      (Nat.mul_pos hspec.1 M.base.q_positive)
    refine ⟨tx,ty,tz,htx,hty,htz,htU,htZ,htT,hlevel,k,?_,?_⟩
    · refine ⟨n,hn,?_⟩
      rw [he,Nat.cast_add]; ring
    · intro D _
      exact sub_axis_not_mem_of_not_mem M.base e _ k D hm


/-- All three listed rows genuinely represent the same actual Omega. -/
theorem omega_degree_forms (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) :
    omegaDegree M hp e = criticalExponent M.base (e 1)*routingB M.base e+
      P3R57.roleCoefficient M hp e 0 2*routingC M.base e ∧
    omegaDegree M hp e = P3R57.roleCoefficient M hp e 1 0*routingA M.base e+
      criticalExponent M.base (e 2)*routingC M.base e := by
  have hs := P3R58.p3_coefficient_sums M hp e
  have hr := L5A2C4OR5.coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)
  change criticalExponent M.base (e 0)*routingA M.base e =
      P3R57.roleCoefficient M hp e 0 1*routingB M.base e+
      P3R57.roleCoefficient M hp e 0 2*routingC M.base e ∧
    criticalExponent M.base (e 1)*routingB M.base e =
      P3R57.roleCoefficient M hp e 1 0*routingA M.base e+
      P3R57.roleCoefficient M hp e 1 2*routingC M.base e ∧
    criticalExponent M.base (e 2)*routingC M.base e =
      P3R57.roleCoefficient M hp e 2 0*routingA M.base e+
      P3R57.roleCoefficient M hp e 2 1*routingB M.base e at hr
  dsimp [omegaDegree]
  constructor
  · rw [hr.1,hs.2.1]; ring
  · rw [hs.1,hr.2.2]; ring

/-- The complete Omega table is an equivalence, rather than merely a bound. -/
theorem omega_factorization_iff (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (x y z : ℕ) :
    x*routingA M.base e+y*routingB M.base e+z*routingC M.base e=omegaDegree M hp e ↔
    (x=criticalExponent M.base (e 0) ∧ y=P3R57.roleCoefficient M hp e 2 1 ∧ z=0) ∨
    (x=0 ∧ y=criticalExponent M.base (e 1) ∧ z=P3R57.roleCoefficient M hp e 0 2) ∨
    (x=P3R57.roleCoefficient M hp e 1 0 ∧ y=0 ∧ z=criticalExponent M.base (e 2)) := by
  constructor
  · exact omega_factorization_table M hp e x y z
  · intro ht
    rcases ht with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩
    · simp [omegaDegree]
    · simpa only [zero_mul,zero_add] using (omega_degree_forms M hp e).1.symm
    · simpa only [zero_mul,add_zero] using (omega_degree_forms M hp e).2.symm

/-- NF.04 existence and uniqueness, under literal signed complement membership. -/
theorem principal_complement_unique_factorization (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3)
    (hmem : ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) ∈
      (routingH M.base e).asRelativeIdeal) :
    ∃! p : ℕ×ℕ×ℕ, ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) =
      (p.1:ℤ)*routingA M.base e+p.2.1*routingB M.base e+p.2.2*routingC M.base e := by
  obtain ⟨n,hn,he⟩ := hmem
  obtain ⟨x,y,z,hfac⟩ := routingH_factorization M.base e hn
  have hcomp : ((omegaDegree M hp e:ℕ):ℤ)-
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive*M.base.q.val:ℕ) =
      (x:ℤ)*routingA M.base e+y*routingB M.base e+z*routingC M.base e := by
    rw [he,hfac]; simp only [Nat.cast_add,Nat.cast_mul]
  refine ⟨(x,y,z),hcomp,?_⟩
  rintro ⟨u,v,w⟩ huv
  obtain ⟨hu,hv,hw⟩ := principal_complement_factorization_unique M hp hR3 e u v w x y z huv hcomp
  simp only [hu,hv,hw]


/-- Actual cyclic role permutation (a,b,c) to (b,c,a). -/
def cycleRole (e : Fin 3 ≃ Fin 3) : Fin 3 ≃ Fin 3 :=
  ((Equiv.swap 1 2).trans (Equiv.swap 0 1)).trans e
@[simp] theorem cycleRole_zero (e : Fin 3 ≃ Fin 3) : cycleRole e 0=e 1 := by simp [cycleRole,Equiv.swap_apply_def]
@[simp] theorem cycleRole_one (e : Fin 3 ≃ Fin 3) : cycleRole e 1=e 2 := by simp [cycleRole,Equiv.swap_apply_def]
@[simp] theorem cycleRole_two (e : Fin 3 ≃ Fin 3) : cycleRole e 2=e 0 := by simp [cycleRole,Equiv.swap_apply_def]
@[simp] theorem routingD_cycle (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingD B (cycleRole e)=routingD B e := by
  simp only [routingD,routingN1,routingN2,routingN3,tailValue,
    cycleRole_zero,cycleRole_one,cycleRole_two,tailGcd]
  simp only [Nat.gcd_comm,Nat.gcd_left_comm]
@[simp] theorem routingA_cycle (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingA B (cycleRole e)=routingB B e := by simp [routingA,routingB,routingN1,routingN2,tailValue]
@[simp] theorem routingB_cycle (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingB B (cycleRole e)=routingC B e := by simp [routingB,routingC,routingN2,routingN3,tailValue]
@[simp] theorem routingC_cycle (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingC B (cycleRole e)=routingA B e := by simp [routingC,routingA,routingN3,routingN1,tailValue]

theorem numericalSemigroup_of_submonoid_eq (H H' : NumericalSemigroup)
    (h : H.toAddSubmonoid=H'.toAddSubmonoid) : H=H' := by
  cases H
  cases H'
  cases h
  rfl

theorem routingH_cycle (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingH B (cycleRole e)=routingH B e := by
  have hsub : (routingH B (cycleRole e)).toAddSubmonoid=(routingH B e).toAddSubmonoid := by
    ext n
    change n ∈ generatedThree (routingA B (cycleRole e)) (routingB B (cycleRole e)) (routingC B (cycleRole e)) ↔
      n ∈ generatedThree (routingA B e) (routingB B e) (routingC B e)
    rw [routingA_cycle,routingB_cycle,routingC_cycle]
    rw [mem_generatedThree_iff,mem_generatedThree_iff]
    constructor
    · rintro ⟨x,y,z,rfl⟩; exact ⟨z,x,y,by ring⟩
    · rintro ⟨x,y,z,rfl⟩; exact ⟨y,z,x,by ring⟩
  exact numericalSemigroup_of_submonoid_eq _ _ hsub

/-- An actual RB return remains RB after the genuine cyclic permutation. -/
theorem rbReturn_cycle (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (q : ℕ)
    (hRB : P3R59.RBReturn M hp e q) : P3R59.RBReturn M hp (cycleRole e) q := by
  obtain ⟨s,t,d,hs,hsZ,ht,htT,hd,hdU,he⟩ := hRB
  have hcoeff (i j : Fin 3) : P3R57.roleCoefficient M hp (cycleRole e) i j =
      P3R57.roleCoefficient M hp e (((Equiv.swap 1 2).trans (Equiv.swap 0 1)) i)
        (((Equiv.swap 1 2).trans (Equiv.swap 0 1)) j) := rfl
  refine ⟨t,P3R57.roleCoefficient M hp e 1 0-d,P3R57.roleCoefficient M hp e 2 1-s,?_,?_,?_,?_,?_,?_,?_⟩
  · exact ht
  · change t<P3R57.roleCoefficient M hp e 0 2; exact htT
  · omega
  · change P3R57.roleCoefficient M hp e 1 0-d<P3R57.roleCoefficient M hp e 1 0; omega
  · omega
  · change P3R57.roleCoefficient M hp e 2 1-s<P3R57.roleCoefficient M hp e 2 1; omega
  · have hr := (L5A2C4OR5.coherent_normalized_relations M.base e (P3R58.p3_coherentHerzogData M hp e)).2.1
    change criticalExponent M.base (e 1)*routingB M.base e =
      P3R57.roleCoefficient M hp e 1 0*routingA M.base e+
      P3R57.roleCoefficient M hp e 1 2*routingC M.base e at hr
    have hsums := (P3R58.p3_coefficient_sums M hp e).2.1
    rw [hsums] at hr
    have hrZ : ((P3R57.roleCoefficient M hp e 0 1+P3R57.roleCoefficient M hp e 2 1:ℕ):ℤ)*routingB M.base e =
      (P3R57.roleCoefficient M hp e 1 0:ℤ)*routingA M.base e+
      (P3R57.roleCoefficient M hp e 1 2:ℤ)*routingC M.base e := by exact_mod_cast hr
    simp only [routingA_cycle,routingB_cycle,routingC_cycle]
    simp only [P3R57.roleCoefficient,cycleRole_zero,cycleRole_one,cycleRole_two]
    change ((P3R57.roleCoefficient M hp e 1 2+t:ℕ):ℤ)*routingC M.base e+
      (P3R57.roleCoefficient M hp e 1 0-d:ℕ)*routingA M.base e =
      q*M.base.q.val+(P3R57.roleCoefficient M hp e 2 1-s:ℕ)*routingB M.base e
    simp only [Nat.cast_add,Nat.cast_sub hdU.le,Nat.cast_sub hsZ.le] at he hrZ ⊢
    nlinarith only [he,hrZ]


@[simp] theorem omegaDegree_cycle (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) :
    omegaDegree M hp (cycleRole e)=omegaDegree M hp e := by
  unfold omegaDegree
  rw [routingA_cycle,routingB_cycle]
  change criticalExponent M.base (e 1)*routingB M.base e+
    P3R57.roleCoefficient M hp e 0 2*routingC M.base e = _
  exact (omega_degree_forms M hp e).1.symm

/-- The actual positive Omega deficit box gives an actual RB level, at its stated depth. -/
theorem rbLevel_of_deficits (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (q tx ty tz : ℕ)
    (htx : 0<tx) (hty : 0<ty) (htz : 0<tz)
    (htU : tx<P3R57.roleCoefficient M hp e 1 0)
    (htZ : ty<P3R57.roleCoefficient M hp e 2 1)
    (htT : tz<P3R57.roleCoefficient M hp e 0 2)
    (he : q*M.base.q.val+tx*routingA M.base e+ty*routingB M.base e+tz*routingC M.base e=omegaDegree M hp e) :
    ∃ i j, P3R61.RBLevel M hp e q i j tx := by
  let i := P3R57.roleCoefficient M hp e 0 1+(P3R57.roleCoefficient M hp e 2 1-ty)
  let j := P3R57.roleCoefficient M hp e 0 2-tz
  have hs := P3R58.p3_coefficient_sums M hp e
  have hP := P3R58.p3_coefficients_positive M hp e 0 1 (by decide)
  have hTc := P3R57.roleCoefficient_lt_critical M hp e 0 2 (by decide)
  refine ⟨i,j,?_⟩
  dsimp only [P3R61.RBLevel,i,j]
  refine ⟨by omega,by omega,htx,by omega,by omega,by omega,by omega,htU,?_⟩
  have ho := (omega_degree_forms M hp e).1
  have hsZ := Nat.sub_add_cancel htZ.le
  have hsT := Nat.sub_add_cancel htT.le
  have heN : (P3R57.roleCoefficient M hp e 0 1+(P3R57.roleCoefficient M hp e 2 1-ty))*routingB M.base e+
      (P3R57.roleCoefficient M hp e 0 2-tz)*routingC M.base e=q*M.base.q.val+tx*routingA M.base e := by
    rw [hs.2.1] at ho
    nlinarith only [he,ho,congrArg (fun n => n*routingB M.base e) hsZ,
      congrArg (fun n => n*routingC M.base e) hsT]
  exact_mod_cast heN


theorem routingH_swap (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingH B (P3R57.swapRole e)=routingH B e := by
  apply numericalSemigroup_of_submonoid_eq
  ext n
  change n ∈ generatedThree (routingA B (P3R57.swapRole e)) (routingB B (P3R57.swapRole e)) (routingC B (P3R57.swapRole e)) ↔
    n ∈ generatedThree (routingA B e) (routingB B e) (routingC B e)
  rw [P3R57.routingA_swap,P3R57.routingB_swap,P3R57.routingC_swap]
  rw [mem_generatedThree_iff,mem_generatedThree_iff]
  constructor
  · rintro ⟨x,y,z,rfl⟩; exact ⟨x,z,y,by ring⟩
  · rintro ⟨x,y,z,rfl⟩; exact ⟨x,z,y,by ring⟩

theorem ltReturn_swap_rb (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (q : ℕ)
    (hLT : P3R59.LTReturn M hp e q) : P3R59.RBReturn M hp (P3R57.swapRole e) q := by
  obtain ⟨s,t,d,hs,hsP,ht,htV,hd,hdW,he⟩ := hLT
  refine ⟨t,s,d,ht,?_,hs,?_,hd,?_,?_⟩
  · simpa [P3R57.roleCoefficient_swap] using htV
  · change s<P3R57.roleCoefficient M hp e 0 1; exact hsP
  · change d<P3R57.roleCoefficient M hp e 2 0; exact hdW
  · simp only [P3R57.routingA_swap,P3R57.routingB_swap,P3R57.routingC_swap]
    have hc : P3R57.roleCoefficient M hp (P3R57.swapRole e) 0 1=P3R57.roleCoefficient M hp e 0 2 := rfl
    rw [hc]
    linarith only [he]

/-- NF.01: the signed no-full-support residual admits an actual common-RB role. -/
theorem residual_common_rb_role (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3)
    (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hn : ¬ PrincipalFullSupport M e) :
    ∃ f : Fin 3 ≃ Fin 3, routingH M.base f=routingH M.base e ∧
      ∀ q : ℕ, 0<q → q<principalIndex (routingH M.base f) M.base.q.val M.base.q_positive →
        P3R59.RBReturn M hp f q := by
  rcases no_fullSupport_one_arm M hp hR3 e hQ hn with hRB | hLT
  · exact ⟨e,rfl,hRB⟩
  · refine ⟨P3R57.swapRole e,routingH_swap M.base e,?_⟩
    intro q hq hpre
    rw [routingH_swap] at hpre
    exact ltReturn_swap_rb M hp e q (hLT q hq hpre)


theorem all_rb_cycle (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3)
    (hlevels : ∀q : ℕ,0<q → q<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive → P3R59.RBReturn M hp e q) :
    ∀q : ℕ,0<q → q<principalIndex (routingH M.base (cycleRole e)) M.base.q.val M.base.q_positive →
      P3R59.RBReturn M hp (cycleRole e) q := by
  intro q hq hpre
  rw [routingH_cycle] at hpre
  exact rbReturn_cycle M hp e q (hlevels q hq hpre)

/-- Cyclic transport keeps the full positive box, not only its support. -/
theorem deficit_box_cycle (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (tx ty tz : ℕ)
    (htx : 0<tx) (hty : 0<ty) (htz : 0<tz)
    (htU : tx<P3R57.roleCoefficient M hp e 1 0)
    (htZ : ty<P3R57.roleCoefficient M hp e 2 1)
    (htT : tz<P3R57.roleCoefficient M hp e 0 2)
    (he : M.base.q.val+tx*routingA M.base e+ty*routingB M.base e+tz*routingC M.base e=omegaDegree M hp e) :
    ty<P3R57.roleCoefficient M hp (cycleRole e) 1 0 ∧
    tz<P3R57.roleCoefficient M hp (cycleRole e) 2 1 ∧
    tx<P3R57.roleCoefficient M hp (cycleRole e) 0 2 ∧
    M.base.q.val+ty*routingA M.base (cycleRole e)+tz*routingB M.base (cycleRole e)+tx*routingC M.base (cycleRole e)=
      omegaDegree M hp (cycleRole e) := by
  refine ⟨?_,?_,?_,?_⟩
  · change ty<P3R57.roleCoefficient M hp e 2 1; exact htZ
  · change tz<P3R57.roleCoefficient M hp e 0 2; exact htT
  · change tx<P3R57.roleCoefficient M hp e 1 0; exact htU
  · rw [routingA_cycle,routingB_cycle,routingC_cycle,omegaDegree_cycle]
    nlinarith only [he]

/-- NF.06 actual role selection, with protection for every depth above its
actual level-one depth. The attained maximum is chosen downstream. -/
theorem safe_rb_role (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hlevels : ∀q : ℕ,0<q → q<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive → P3R59.RBReturn M hp e q) :
    ∃ f : Fin 3 ≃ Fin 3, routingH M.base f=routingH M.base e ∧
    (∀q : ℕ,0<q → q<principalIndex (routingH M.base f) M.base.q.val M.base.q_positive → P3R59.RBReturn M hp f q) ∧
    ∃ d i j : ℕ, P3R61.RBLevel M hp f 1 i j d ∧
      ((principalIndex (routingH M.base f) M.base.q.val M.base.q_positive*M.base.q.val:ℕ):ℤ)-routingA M.base f ∈
        (routingH M.base f).asRelativeIdeal ∧
      ∀D : ℕ,d≤D → ((omegaDegree M hp f:ℕ):ℤ)-
        (principalIndex (routingH M.base f) M.base.q.val M.base.q_positive*M.base.q.val:ℕ)-D*routingA M.base f ∉
        (routingH M.base f).asRelativeIdeal := by
  obtain ⟨tx,ty,tz,htx,hty,htz,htU,htZ,htT,hlevel,k,htau,hprotect⟩ :=
    actual_rb_safe_axis M hp hR3 e hQ (hlevels 1 (by omega) hQ)
  fin_cases k
  · obtain ⟨i,j,hlev⟩ := rbLevel_of_deficits M hp e 1 tx ty tz htx hty htz htU htZ htT (by simpa only [one_mul] using hlevel)
    refine ⟨e,rfl,hlevels,tx,i,j,hlev,htau,?_⟩
    intro D hD
    exact hprotect D hD
  · have hbox := deficit_box_cycle M hp e tx ty tz htx hty htz htU htZ htT hlevel
    obtain ⟨i,j,hlev⟩ := rbLevel_of_deficits M hp (cycleRole e) 1 ty tz tx hty htz htx hbox.1 hbox.2.1 hbox.2.2.1
      (by simpa only [one_mul] using hbox.2.2.2)
    refine ⟨cycleRole e,routingH_cycle M.base e,all_rb_cycle M hp e hlevels,ty,i,j,hlev,?_,?_⟩
    · rw [routingH_cycle,routingA_cycle]; exact htau
    · intro D hD
      have ht := hprotect D hD
      rw [routingH_cycle,routingA_cycle,omegaDegree_cycle]; exact ht
  · have hbox := deficit_box_cycle M hp e tx ty tz htx hty htz htU htZ htT hlevel
    have hbox' := deficit_box_cycle M hp (cycleRole e) ty tz tx hty htz htx hbox.1 hbox.2.1 hbox.2.2.1 hbox.2.2.2
    obtain ⟨i,j,hlev⟩ := rbLevel_of_deficits M hp (cycleRole (cycleRole e)) 1 tz tx ty htz htx hty hbox'.1 hbox'.2.1 hbox'.2.2.1
      (by simpa only [one_mul] using hbox'.2.2.2)
    refine ⟨cycleRole (cycleRole e),(routingH_cycle M.base (cycleRole e)).trans (routingH_cycle M.base e),
      all_rb_cycle M hp (cycleRole e) (all_rb_cycle M hp e hlevels),tz,i,j,hlev,?_,?_⟩
    · rw [routingH_cycle,routingH_cycle,routingA_cycle,routingB_cycle]; exact htau
    · intro D hD
      have ht := hprotect D hD
      rw [routingH_cycle,routingH_cycle,routingA_cycle,routingB_cycle,omegaDegree_cycle,omegaDegree_cycle]; exact ht

theorem residual_safe_rb_role (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (hQ : 1<principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (hn : ¬ PrincipalFullSupport M e) :
    ∃ f : Fin 3 ≃ Fin 3, routingH M.base f=routingH M.base e ∧
    (∀q : ℕ,0<q → q<principalIndex (routingH M.base f) M.base.q.val M.base.q_positive → P3R59.RBReturn M hp f q) ∧
    ∃ d i j : ℕ, P3R61.RBLevel M hp f 1 i j d ∧
      ((principalIndex (routingH M.base f) M.base.q.val M.base.q_positive*M.base.q.val:ℕ):ℤ)-routingA M.base f ∈
        (routingH M.base f).asRelativeIdeal ∧
      ∀D : ℕ,d≤D → ((omegaDegree M hp f:ℕ):ℤ)-
        (principalIndex (routingH M.base f) M.base.q.val M.base.q_positive*M.base.q.val:ℕ)-D*routingA M.base f ∉
        (routingH M.base f).asRelativeIdeal  := by
  obtain ⟨g,hg,hRB⟩ := residual_common_rb_role M hp hR3 e hQ hn
  have hQg : 1<principalIndex (routingH M.base g) M.base.q.val M.base.q_positive := by rw [hg]; exact hQ
  obtain ⟨f,hf,hlevels,d,i,j,hlev,htau,hprotect⟩ := safe_rb_role M hp hR3 g hQg hRB
  exact ⟨f,hf.trans hg,hlevels,d,i,j,hlev,htau,hprotect⟩

end NS25Lean.P3R67













