import NS25Lean.SharedTailPositiveCritical
import NS25Lean.AppendixBTwoGenerator

set_option autoImplicit false
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse L4A L3C

/-- The actual true critical pure-pair hypotheses. The last condition is the
literal minimal-three condition (no generator has outside exponent one). -/
structure PurePair (H : NumericalSemigroup) where
  triple : Triple H
  critical : Critical triple
  pair : critical.exponent 0*triple.g 0=critical.exponent 1*triple.g 1
  primitive : Nat.gcd (triple.g 0) (Nat.gcd (triple.g 1) (triple.g 2))=1
  minimal : ∀ i, 2≤critical.exponent i

abbrev PurePair.a {H : NumericalSemigroup} (D : PurePair H) := D.triple.g 0
abbrev PurePair.b {H : NumericalSemigroup} (D : PurePair H) := D.triple.g 1
abbrev PurePair.c {H : NumericalSemigroup} (D : PurePair H) := D.triple.g 2
def PurePair.d {H : NumericalSemigroup} (D : PurePair H) := Nat.gcd D.a D.b
def PurePair.alpha {H : NumericalSemigroup} (D : PurePair H) := D.a/D.d
def PurePair.beta {H : NumericalSemigroup} (D : PurePair H) := D.b/D.d

theorem PurePair.d_pos {H : NumericalSemigroup} (D : PurePair H) : 0<D.d :=
  Nat.gcd_pos_of_pos_left D.b (D.triple.positive 0)
theorem PurePair.scale_a {H : NumericalSemigroup} (D : PurePair H) : D.a=D.d*D.alpha :=
  (Nat.mul_div_cancel' (Nat.gcd_dvd_left D.a D.b)).symm
theorem PurePair.scale_b {H : NumericalSemigroup} (D : PurePair H) : D.b=D.d*D.beta :=
  (Nat.mul_div_cancel' (Nat.gcd_dvd_right D.a D.b)).symm
theorem PurePair.alpha_pos {H : NumericalSemigroup} (D : PurePair H) : 0<D.alpha := by
  have hp := D.triple.positive 0
  change 0<D.a at hp
  nlinarith [D.scale_a]
theorem PurePair.beta_pos {H : NumericalSemigroup} (D : PurePair H) : 0<D.beta := by
  have hp := D.triple.positive 1
  change 0<D.b at hp
  nlinarith [D.scale_b]
theorem PurePair.alpha_beta_coprime {H : NumericalSemigroup} (D : PurePair H) :
    Nat.Coprime D.alpha D.beta := Nat.coprime_div_gcd_div_gcd D.d_pos
theorem PurePair.d_c_coprime {H : NumericalSemigroup} (D : PurePair H) :
    Nat.Coprime D.d D.c := by
  change Nat.gcd (Nat.gcd D.a D.b) D.c=1
  rw [Nat.gcd_assoc]
  exact D.primitive

theorem PurePair.pure_exponents {H : NumericalSemigroup} (D : PurePair H) :
    D.critical.exponent 0=D.beta ∧ D.critical.exponent 1=D.alpha := by
  have hp : D.critical.exponent 0*D.alpha=D.critical.exponent 1*D.beta := by
    apply Nat.eq_of_mul_eq_mul_left D.d_pos
    nlinarith [D.pair,D.scale_a,D.scale_b]
  have hbdiv : D.beta∣D.critical.exponent 0 := by
    apply D.alpha_beta_coprime.symm.dvd_of_dvd_mul_right
    rw [hp]
    exact dvd_mul_left _ _
  have hadiv : D.alpha∣D.critical.exponent 1 := by
    apply D.alpha_beta_coprime.dvd_of_dvd_mul_right
    rw [←hp]
    exact dvd_mul_left _ _
  have hpure : D.beta*D.a=D.alpha*D.b := by rw [D.scale_a,D.scale_b]; ring
  have h0 := D.critical.least 0 D.beta (Finsupp.single 1 D.alpha) D.beta_pos
    (by simp) (by rw [D.triple.weight_single]; exact hpure)
  have h1 := D.critical.least 1 D.alpha (Finsupp.single 0 D.beta) D.alpha_pos
    (by simp) (by rw [D.triple.weight_single]; exact hpure.symm)
  have hb := Nat.le_of_dvd (D.critical.positive 0) hbdiv
  have ha := Nat.le_of_dvd (D.critical.positive 1) hadiv
  omega

/-- True critical pure rigidity excludes the Sylvester complement witness,
so the third primitive weight lies in the coprime two-generator monoid. -/
theorem PurePair.third_mem_twoGenerator {H : NumericalSemigroup} (D : PurePair H) :
    D.c∈twoGenerator D.alpha D.beta := by
  by_contra hn
  have hnint : ¬twoGeneratorInt D.alpha D.beta D.c := by
    intro h
    exact hn ((twoGeneratorInt_nat _ _ _).mp h)
  obtain ⟨u,v,he⟩ := (two_generator_symmetry D.alpha D.beta D.alpha_pos D.beta_pos
    D.alpha_beta_coprime D.c).mp hnint
  have hsum : D.alpha*D.beta=D.alpha*(u+1)+D.beta*(v+1)+D.c := by
    exact_mod_cast (show (D.alpha:ℤ)*D.beta=D.alpha*((u:ℤ)+1)+D.beta*((v:ℤ)+1)+D.c by
      nlinarith [he])
  have hw : D.triple.weight (vector (u+1) (v+1) D.d)=
      D.critical.exponent 0*D.a := by
    rw [D.pure_exponents.1,vector_weight,Triple.grid]
    change (u+1)*D.a+(v+1)*D.b+D.d*D.c=D.beta*D.a
    rw [D.scale_a,D.scale_b]
    nlinarith [hsum]
  have hu := critical_pure_unique D.triple D.critical 0 (vector (u+1) (v+1) D.d)
    hw (by simp)
  have hz := congrArg (fun e : Exponent => e 1) hu
  simp at hz

theorem PurePair.third_exponent {H : NumericalSemigroup} (D : PurePair H) :
    D.critical.exponent 2=D.d := by
  obtain ⟨u,v,he⟩ := (mem_twoGenerator _ _ _).mp D.third_mem_twoGenerator
  have hleast := D.critical.least 2 D.d (vector u v 0) D.d_pos (by simp) (by
    rw [vector_weight,Triple.grid]
    change D.d*D.c=u*D.a+v*D.b+0*D.c
    rw [D.scale_a,D.scale_b]
    nlinarith [he])
  obtain ⟨e,hei,hew⟩ := D.critical.outside 2
  have hthree := D.triple.weight_three e
  rw [hei] at hthree
  dsimp [Triple.grid] at hthree
  have hdprod : D.d∣D.critical.exponent 2*D.c := by
    refine ⟨e 0*D.alpha+e 1*D.beta,?_⟩
    nlinarith [hthree,hew,D.scale_a,D.scale_b]
  have hdiv : D.d∣D.critical.exponent 2 := D.d_c_coprime.dvd_of_dvd_mul_right hdprod
  have hge := Nat.le_of_dvd (D.critical.positive 2) hdiv
  omega

theorem PurePair.parameters_ge_two {H : NumericalSemigroup} (D : PurePair H) :
    2≤D.alpha ∧ 2≤D.beta ∧ 2≤D.d := by
  have h0 := D.minimal 0
  have h1 := D.minimal 1
  have h2 := D.minimal 2
  rw [D.pure_exponents.1] at h0
  rw [D.pure_exponents.2] at h1
  rw [D.third_exponent] at h2
  exact ⟨h1,h0,h2⟩

theorem PurePair.reduced_witness_exists {H : NumericalSemigroup} (D : PurePair H) :
    ∃ r s : ℕ, s<D.alpha ∧ D.c=r*D.alpha+s*D.beta := by
  obtain ⟨u,v,he⟩ := (mem_twoGenerator _ _ _).mp D.third_mem_twoGenerator
  refine ⟨u+D.beta*(v/D.alpha),v%D.alpha,Nat.mod_lt _ D.alpha_pos,?_⟩
  have hd := Nat.div_add_mod v D.alpha
  nlinarith [he]

/-- Preserve the actual positive witness when reducing its second coordinate.
At the s=0 endpoint the a coefficient is strictly above beta. -/
theorem PurePair.positive_witness_reduction {H : NumericalSemigroup} (D : PurePair H)
    (r0 s0 : ℕ) (hr : 0<r0) (hs : 0<s0) (he : D.c=r0*D.alpha+s0*D.beta) :
    let r := r0+D.beta*(s0/D.alpha)
    let s := s0%D.alpha
    s<D.alpha ∧ D.c=r*D.alpha+s*D.beta ∧ 0<r ∧ (s=0 → D.beta<r) := by
  dsimp only
  have hd := Nat.div_add_mod s0 D.alpha
  refine ⟨Nat.mod_lt _ D.alpha_pos,by nlinarith,by positivity,?_⟩
  intro hz
  have hq : 0<s0/D.alpha := by
    by_contra hn
    have hq0 : s0/D.alpha=0 := Nat.eq_zero_of_not_pos hn
    rw [hz,hq0] at hd
    simp only [mul_zero,add_zero] at hd
    omega
  nlinarith [D.beta_pos]

end NS25Lean.SharedTail
