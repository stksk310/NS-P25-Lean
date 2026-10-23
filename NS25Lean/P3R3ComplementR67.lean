import NS25Lean.P3R3SignatureR66
import NS25Lean.P3ReturnNormalizationR59
import NS25Lean.P3CanonicalCoordinatesR61

set_option linter.style.header false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.P3R67
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4OR6 L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- Physical R3 liveness excludes every positive return from every critical predecessor. -/
theorem live_critical_predecessor_return_absent (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (i k : Fin 3) (n : ℕ) (hn : 0 < n) :
    ((criticalExponent M.base (e i) * P3R59.normalizedRoleWeight M.base e i -
      P3R59.normalizedRoleWeight M.base e k : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (n * M.base.q.val) := by
  intro hret
  have hK := (P3R59.original_K_iff_normalized_positive_return M.base e _).mpr ⟨n, hn, hret⟩
  have hs : routingD M.base e *
      (criticalExponent M.base (e i) * P3R59.normalizedRoleWeight M.base e i -
        P3R59.normalizedRoleWeight M.base e k) =
      criticalExponent M.base (e i) * weights M.base (e i) - weights M.base (e k) := by
    rw [Nat.mul_sub_left_distrib, ← P3R59.normalizedRoleWeight_scale M.base e i,
      ← P3R59.normalizedRoleWeight_scale M.base e k]
    ring
  rw [hs] at hK
  have hl := P3R66.r3_all_axes_live M hp hR3 (e i) (e k)
  rw [M.base.apery_eq_compl] at hl
  exact hl.2 hK


/-- A positive actual tail value has an actual generator divisor. -/
theorem positive_tail_has_generator (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (n : ℕ) (hn : n ∈ routingH B e) (hpos : 0 < n) :
    ∃ k : Fin 3, ∃ y : ℕ, y ∈ routingH B e ∧
      n = y + P3R59.normalizedRoleWeight B e k := by
  obtain ⟨x, y, z, he⟩ := routingH_factorization B e hn
  by_cases hx : 0 < x
  · refine ⟨0, (x-1)*routingA B e+y*routingB B e+z*routingC B e, ?_, ?_⟩
    · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨x-1,y,z,rfl⟩
    · change n = _ + routingA B e
      have hs := Nat.sub_add_cancel (by omega : 1 ≤ x)
      nlinarith [congrArg (fun t => t*routingA B e) hs]
  by_cases hy : 0 < y
  · refine ⟨1, x*routingA B e+(y-1)*routingB B e+z*routingC B e, ?_, ?_⟩
    · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨x,y-1,z,rfl⟩
    · change n = _ + routingB B e
      have hs := Nat.sub_add_cancel (by omega : 1 ≤ y)
      nlinarith [congrArg (fun t => t*routingB B e) hs]
  have hx0 : x = 0 := by omega
  have hy0 : y = 0 := by omega
  have hz : 0 < z := by
    by_contra hz
    have hz0 : z = 0 := by omega
    simp [hx0, hy0, hz0] at he
    omega
  refine ⟨2, x*routingA B e+y*routingB B e+(z-1)*routingC B e, ?_, ?_⟩
  · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨x,y,z-1,rfl⟩
  · change n = _ + routingC B e
    have hs := Nat.sub_add_cancel (by omega : 1 ≤ z)
    nlinarith [congrArg (fun t => t*routingC B e) hs]

/-- NF.03: a principal divisor cannot be a proper divisor of any live critical degree.
The subtraction and its positivity are both in the integers. -/
theorem live_critical_divisor (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (i : Fin 3)
    (hmem : ((criticalExponent M.base (e i) * P3R59.normalizedRoleWeight M.base e i : ℕ) : ℤ) -
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive * M.base.q.val : ℕ) ∈
        (routingH M.base e).asRelativeIdeal) :
    ¬ (0 < ((criticalExponent M.base (e i) * P3R59.normalizedRoleWeight M.base e i : ℕ) : ℤ) -
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive * M.base.q.val : ℕ)) := by
  intro hpos
  obtain ⟨n, hn, he⟩ := hmem
  have hnpos : 0 < n := by omega
  obtain ⟨k,y,hy,hny⟩ := positive_tail_has_generator M.base e n hn hnpos
  let Q := principalIndex (routingH M.base e) M.base.q.val M.base.q_positive
  have hQ := principalIndex_spec (routingH M.base e) M.base.q.val M.base.q_positive
  have hEn : criticalExponent M.base (e i) * P3R59.normalizedRoleWeight M.base e i =
      Q*M.base.q.val+n := by dsimp [Q]; omega
  have hpred : criticalExponent M.base (e i) * P3R59.normalizedRoleWeight M.base e i -
      P3R59.normalizedRoleWeight M.base e k = Q*M.base.q.val+y := by omega
  apply live_critical_predecessor_return_absent M hp hR3 e i k Q hQ.1
  rw [hpred]
  refine ⟨?_, ⟨y,hy,?_⟩⟩
  · exact ⟨_, (routingH M.base e).add_mem hQ.2 hy, rfl⟩
  · push_cast; ring


/-- A pure principal factorization has at least the actual critical exponent. -/
theorem principal_pure_ge_critical (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (i : Fin 3) (n : ℕ)
    (he : principalIndex (routingH M.base e) M.base.q.val M.base.q_positive * M.base.q.val =
      n*P3R59.normalizedRoleWeight M.base e i) : criticalExponent M.base (e i) ≤ n := by
  by_contra h
  have hlt : n < criticalExponent M.base (e i) := by omega
  have hg : 0 < P3R59.normalizedRoleWeight M.base e i := by
    have hs := P3R59.normalizedRoleWeight_scale M.base e i
    have hw := weights_positive M.base (e i)
    nlinarith
  have hm : (criticalExponent M.base (e i)-n)*P3R59.normalizedRoleWeight M.base e i ∈
      routingH M.base e := by
    apply (P3R59.routing_scaled_mem_iff M.base e _).mp
    rw [Nat.mul_left_comm, P3R59.normalizedRoleWeight_scale]
    exact M.base.H.nsmul_mem (M.base.tailDegrees (e i)).property _
  have hs := Nat.sub_add_cancel hlt.le
  have heZ : ((criticalExponent M.base (e i) * P3R59.normalizedRoleWeight M.base e i : ℕ) : ℤ) -
      (principalIndex (routingH M.base e) M.base.q.val M.base.q_positive * M.base.q.val : ℕ) =
      ((criticalExponent M.base (e i)-n)*P3R59.normalizedRoleWeight M.base e i : ℕ) := by
    rw [he, Nat.sub_mul, Nat.cast_sub (Nat.mul_le_mul_right _ hlt.le)]
  apply live_critical_divisor M hp hR3 e i ⟨_,hm,heZ⟩
  rw [heZ]
  exact_mod_cast Nat.mul_pos (Nat.sub_pos_of_lt hlt) hg


/-- R3 forbids every positive-return multiple below the critical exponent. -/
theorem live_subcritical_pure_return_absent (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR3 : (P3R51.internalDegrees M).card = 3)
    (e : Fin 3 ≃ Fin 3) (i : Fin 3) (t n : ℕ)
    (ht : t < criticalExponent M.base (e i)) (hn : 0 < n) :
    ((t*P3R59.normalizedRoleWeight M.base e i:ℕ):ℤ) ∉
      returnIdeal (routingH M.base e) (n*M.base.q.val) := by
  intro hret
  have hg : P3R59.normalizedRoleWeight M.base e i ∈ routingH M.base e := by
    apply (P3R59.routing_scaled_mem_iff M.base e _).mp
    rw [P3R59.normalizedRoleWeight_scale]
    exact (M.base.tailDegrees (e i)).property
  have hm := (routingH M.base e).toAddSubmonoid.nsmul_mem hg (criticalExponent M.base (e i)-1-t)
  change (criticalExponent M.base (e i)-1-t)*P3R59.normalizedRoleWeight M.base e i ∈ routingH M.base e at hm
  have hadd := (returnIdeal (routingH M.base e) (n*M.base.q.val)).add_mem hret hm
  have hs : t+(criticalExponent M.base (e i)-1-t)=criticalExponent M.base (e i)-1 := by omega
  have he : ((t*P3R59.normalizedRoleWeight M.base e i:ℕ):ℤ) +
      ((criticalExponent M.base (e i)-1-t)*P3R59.normalizedRoleWeight M.base e i:ℕ) =
      ((criticalExponent M.base (e i)*P3R59.normalizedRoleWeight M.base e i-
        P3R59.normalizedRoleWeight M.base e i:ℕ):ℤ) := by
    rw [← Nat.cast_add, ← Nat.add_mul, hs, Nat.sub_mul, one_mul]
  rw [he] at hadd
  exact live_critical_predecessor_return_absent M hp hR3 e i i n hn hadd


/-- A nonnegative two-generator remainder realizes a genuine return. -/
theorem two_generator_return (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j k : Fin 3) (t n p q : ℕ)
    (he : t*P3R59.normalizedRoleWeight B e k = n*B.q.val+
      p*P3R59.normalizedRoleWeight B e i+q*P3R59.normalizedRoleWeight B e j) :
    ((t*P3R59.normalizedRoleWeight B e k:ℕ):ℤ) ∈ returnIdeal (routingH B e) (n*B.q.val) := by
  have hgen (r : Fin 3) : P3R59.normalizedRoleWeight B e r ∈ routingH B e := by
    apply (P3R59.routing_scaled_mem_iff B e _).mp
    rw [P3R59.normalizedRoleWeight_scale]
    exact (B.tailDegrees (e r)).property
  refine ⟨⟨_,(routingH B e).toAddSubmonoid.nsmul_mem (hgen k) t,rfl⟩, ?_⟩
  refine ⟨_, (routingH B e).add_mem
    ((routingH B e).toAddSubmonoid.nsmul_mem (hgen i) p)
    ((routingH B e).toAddSubmonoid.nsmul_mem (hgen j) q), ?_⟩
  rw [he]
  simp only [Nat.cast_add]
  ring


/-- Removing a supported generator from an explicit physical factorization stays in H. -/
theorem factorization_sub_supported_mem (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (n fa fb fc : ℕ) (k : Fin 3)
    (hf : n=fa*routingA B e+fb*routingB B e+fc*routingC B e)
    (hk : 0< ![fa,fb,fc] k) :
    (n:ℤ)-P3R59.normalizedRoleWeight B e k ∈ (routingH B e).asRelativeIdeal := by
  fin_cases k
  · change 0<fa at hk
    refine ⟨(fa-1)*routingA B e+fb*routingB B e+fc*routingC B e,
      (mem_generatedThree_iff _ _ _ _).mpr ⟨fa-1,fb,fc,rfl⟩,?_⟩
    change (n:ℤ)-(routingA B e:ℤ)=_
    rw [hf]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1≤fa)]
    ring
  · change 0<fb at hk
    refine ⟨fa*routingA B e+(fb-1)*routingB B e+fc*routingC B e,
      (mem_generatedThree_iff _ _ _ _).mpr ⟨fa,fb-1,fc,rfl⟩,?_⟩
    change (n:ℤ)-(routingB B e:ℤ)=_
    rw [hf]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1≤fb)]
    ring
  · change 0<fc at hk
    refine ⟨fa*routingA B e+fb*routingB B e+(fc-1)*routingC B e,
      (mem_generatedThree_iff _ _ _ _).mpr ⟨fa,fb,fc-1,rfl⟩,?_⟩
    change (n:ℤ)-(routingC B e:ℤ)=_
    rw [hf]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1≤fc)]
    ring


/-- Subtracting a nonnegative physical generator multiple preserves nonmembership. -/
theorem sub_axis_not_mem_of_not_mem (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (v : ℤ) (k : Fin 3) (n : ℕ) (hv : v ∉ (routingH B e).asRelativeIdeal) :
    v-n*P3R59.normalizedRoleWeight B e k ∉ (routingH B e).asRelativeIdeal := by
  intro hm
  have hg : P3R59.normalizedRoleWeight B e k ∈ routingH B e := by
    apply (P3R59.routing_scaled_mem_iff B e _).mp
    rw [P3R59.normalizedRoleWeight_scale]
    exact (B.tailDegrees (e k)).property
  have hn : n*P3R59.normalizedRoleWeight B e k ∈ routingH B e := by
    exact (routingH B e).toAddSubmonoid.nsmul_mem hg n
  have hadd := (routingH B e).asRelativeIdeal.add_mem hm hn
  have he : v-n*P3R59.normalizedRoleWeight B e k+(n*P3R59.normalizedRoleWeight B e k:ℕ) = v := by
    simp only [Nat.cast_mul]; ring
  rw [he] at hadd
  exact hv hadd

end NS25Lean.P3R67










