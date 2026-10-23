import NS25Lean.P3RecordIffR60
import NS25Lean.P3RecordPhysicalR60

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R60
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4H L5A2C4OR3 L5A2B4AR1
variable {Gamma : NumericalSemigroup}

/-- Conditional G3 reduction. Positive b,c support is an explicit premise,
not a classifier established by this theorem. -/
theorem source_with_positive_bc_is_returnPoint (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0)*weights M.base (e 0)-weights M.base k ∈ M.base.apery)
    (Q : ℕ) (_hQ : 0 < Q)
    (hQlt : Q < principalIndex (routingH M.base e) M.base.q.val M.base.q_positive)
    (w : ℤ)
    (hs : IsSource (routingH M.base e)
      (prefixCarrier (routingH M.base e) M.base.q.val (Q+1)) w)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j)
    (hw : w = (i : ℤ)*routingB M.base e+j*routingC M.base e) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ w = returnPoint M.base e q ∧ StrictRecord M e q := by
  let H := routingH M.base e
  let a := routingA M.base e
  let b := routingB M.base e
  let c := routingC M.base e
  let m := M.base.q.val
  letI : NeZero a := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  change w = (i : ℤ)*b+j*c at hw
  change Q < principalIndex H m M.base.q_positive at hQlt
  have hbpos : 0 < b := quotient_pos_of_dvd (chosenBase_minimalFour M.base e).n₂_pos
    (tailGcd_dvd _ _ _).2.1
  have hcpos : 0 < c := quotient_pos_of_dvd (chosenBase_minimalFour M.base e).n₃_pos
    (tailGcd_dvd _ _ _).2.2
  obtain ⟨q,hq,hqQ,hwH,y,hy,he⟩ := hs.1
  change w-(q*m : ℕ) = (y : ℤ) at he
  have hqBound : q ≤ Q := by omega
  have hqpre : q < principalIndex H m M.base.q_positive := by omega
  have hy3 : y ∈ generatedThree a b c := hy
  obtain ⟨A,B,C,hyEq⟩ := (mem_generatedThree_iff a b c y).mp hy3
  have hforbid (t : ℕ) (ht : t ∈ H) (ht0 : t ≠ 0)
      (hwt : w-t ∈ H.asRelativeIdeal) (hyt : (y : ℤ)-t ∈ H.asRelativeIdeal) : False := by
    apply hs.2 t ht ht0
    refine ⟨q,hq,hqQ,hwt,?_⟩
    change w-t-(q*m : ℕ) ∈ H.asRelativeIdeal
    have heSub : w-t-(q*m : ℕ) = (y : ℤ)-t := by omega
    rw [heSub]
    exact hyt
  have hwb : w-b ∈ H.asRelativeIdeal := by
    refine ⟨(i-1)*b+j*c, ?_, ?_⟩
    · exact (mem_generatedThree_iff a b c _).mpr ⟨0,i-1,j,by simp⟩
    · rw [hw]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ i)]
      push_cast
      ring
  have hwc : w-c ∈ H.asRelativeIdeal := by
    refine ⟨i*b+(j-1)*c, ?_, ?_⟩
    · exact (mem_generatedThree_iff a b c _).mpr ⟨0,i,j-1,by simp⟩
    · rw [hw]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ j)]
      push_cast
      ring
  have hB : B = 0 := by
    by_contra hB
    apply hforbid b (routingHB M.base e) (Nat.ne_of_gt hbpos) hwb
    refine ⟨A*a+(B-1)*b+C*c, ?_, ?_⟩
    · exact (mem_generatedThree_iff a b c _).mpr ⟨A,B-1,C,rfl⟩
    · rw [hyEq]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ B)]
      push_cast
      ring
  have hC : C = 0 := by
    by_contra hC
    apply hforbid c (routingHC M.base e) (Nat.ne_of_gt hcpos) hwc
    refine ⟨A*a+B*b+(C-1)*c, ?_, ?_⟩
    · exact (mem_generatedThree_iff a b c _).mpr ⟨A,B,C-1,rfl⟩
    · rw [hyEq]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ C)]
      push_cast
      ring
  have hyA : y = A*a := by simpa [hB,hC] using hyEq
  have hwEq : w = (q : ℤ)*m+(A : ℤ)*a := by
    rw [hyA] at he
    push_cast at he
    omega
  have hA : 0 < A := by
    by_contra hA
    have hA0 : A=0 := by omega
    have hwqm : w = (q*m : ℕ) := by simpa [hA0] using hwEq
    obtain ⟨n,hn,hnEq⟩ := hwH
    have hnq : n=q*m := by rw [hwqm] at hnEq; exact_mod_cast hnEq.symm
    have hmem : q*m ∈ H := hnq ▸ hn
    have hmin := principalIndex_min H m M.base.q_positive hq hmem
    omega
  have hwa : w-a ∉ H.asRelativeIdeal := by
    intro hwa
    apply hforbid a (routingA_mem M.base e) (NeZero.ne a) hwa
    refine ⟨(A-1)*a, ?_, ?_⟩
    · exact (mem_generatedThree_iff a b c _).mpr ⟨A-1,0,0,by simp⟩
    · rw [hyA]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ A)]
      push_cast
      ring
  have hcan : CanonicalValue M.base e w :=
    aperyRepresentative_eq_of_mem_not_mem_sub H.asRelativeIdeal a
      (routingA_mem M.base e) w hwH hwa
  obtain ⟨hbeta,_⟩ := return_point_eq_of_canonical M.base e q w A hcan hwEq
  have hheight : 0 < recordHeight M e q := by
    by_contra hheight
    have hk : recordHeight M e q=0 := by omega
    have hcanB (r : ℕ) (hr : 0 < r) (hrq : r ≤ q) :=
      (nonprincipal_canonical_stencil M hp e hlive r hr (by
        change r < principalIndex H m M.base.q_positive
        omega)).2.2.2.1
    have hbRep := prefix_stencil_representative M hp e hlive q hq hqpre b hcanB
      (gate_canonical_stencil M hp e).1
    let I := birthIdeal H m q hq
    have hbMem := I.aperyRepresentative_mem a
      ((returnPoint M.base e q-b : ℤ) : ZMod a)
    rw [hbRep,hk] at hbMem
    simp only [Nat.cast_zero,mul_zero,add_zero] at hbMem
    obtain ⟨r,hr,hrq,hrMem⟩ := hbMem
    apply hs.2 b (routingHB M.base e) (Nat.ne_of_gt hbpos)
    rw [← hbeta]
    exact ⟨r,hr,by omega,hrMem⟩
  refine ⟨q,hq,hqBound,hbeta.symm,?_⟩
  exact (record_height_pos_iff _ _ q hq).1 hheight

end NS25Lean.P3R60



