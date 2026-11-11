import NS25Lean.SharedTailPositiveChart
import Mathlib.Tactic.LinearCombination
set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse CriticalCapGeometry CriticalPresentationModes L3C
/-- Explicit integral saturation of a primitive cross product. -/
theorem integer_kernel_of_primitive_minors
    (r0 r1 r2 s0 s1 s2 a b c u v w x y z : ℤ)
    (ha : a = r1*s2-r2*s1) (hb : b = r2*s0-r0*s2)
    (hc : c = r0*s1-r1*s0) (hbez : u*a+v*b+w*c=1)
    (hker : x*a+y*b+z*c=0) :
    ∃ l k : ℤ, x=r0*l+s0*k ∧ y=r1*l+s1*k ∧ z=r2*l+s2*k := by
  refine ⟨u*(y*s2-z*s1)+v*(z*s0-x*s2)+w*(x*s1-y*s0),
    u*(r1*z-r2*y)+v*(r2*x-r0*z)+w*(r0*y-r1*x), ?_, ?_, ?_⟩ <;>
    rw [ha, hb, hc] at hbez hker
  · linear_combination -x*hbez+u*hker
  · linear_combination -y*hbez+v*hker
  · linear_combination -z*hbez+w*hker

/-- Three-variable integer Bezout, with the actual primitive natural gcd. -/
theorem bezout_three (a b c : ℕ) (hg : Nat.gcd a (Nat.gcd b c)=1) :
    ∃ u v w : ℤ, u*a+v*b+w*c=1 := by
  have h1 := Nat.gcd_eq_gcd_ab a (Nat.gcd b c)
  have h2 := Nat.gcd_eq_gcd_ab b c
  rw [hg] at h1
  refine ⟨Nat.gcdA a (Nat.gcd b c),
    Nat.gcdB a (Nat.gcd b c)*Nat.gcdA b c,
    Nat.gcdB a (Nat.gcd b c)*Nat.gcdB b c, ?_⟩
  rw [h2] at h1
  linear_combination -h1


/-- Primitivity of the positive minors follows from the proved finite residue
bijection. It is not postulated as a determinantal normalization. -/
theorem Positive.primitive_minors {H : NumericalSemigroup} (D : Positive H) :
    D.a=D.p*D.v+D.q*D.B ∧ D.b=D.A*D.v+D.u*D.q ∧ D.c=D.A*D.B-D.p*D.u := by
  letI : NeZero D.a := ⟨(D.triple.positive 0).ne'⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective _ D.residue_bijective)
  simp only [GenericLShape.Index,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,ZMod.card] at hcard
  have ha : D.a=D.p*D.v+D.q*D.B := by rw [D.coefficient_sums.2.1]; nlinarith only [hcard]
  have hbp : D.a*D.b=D.a*(D.A*D.v+D.u*D.q) := by
    have h0 := congrArg (fun n => n*D.v) D.center
    have h1 := congrArg (fun n => n*D.q) D.middle
    have hab := congrArg (fun n => n*D.b) ha
    change D.A*D.a*D.v=(D.p*D.b+D.q*D.c)*D.v at h0
    change D.B*D.b*D.q=(D.u*D.a+D.v*D.c)*D.q at h1
    nlinarith only [h0,h1,hab]
  have hb : D.b=D.A*D.v+D.u*D.q :=
    Nat.eq_of_mul_eq_mul_left (D.triple.positive 0) hbp
  have hcadd : D.c+D.p*D.u=D.A*D.B := by
    have h0 := congrArg (fun n => n*D.B) D.center
    have h1 := congrArg (fun n => n*D.p) D.middle
    change D.A*D.a*D.B=(D.p*D.b+D.q*D.c)*D.B at h0
    change D.B*D.b*D.p=(D.u*D.a+D.v*D.c)*D.p at h1
    have hac := congrArg (fun n => n*D.c) ha
    have he : D.a*(D.c+D.p*D.u)=D.a*(D.A*D.B) := by
      nlinarith only [h0,h1,hac]
    exact Nat.eq_of_mul_eq_mul_left (D.triple.positive 0) he
  exact ⟨ha,hb,by omega⟩

/-- The two actual integer Herzog rows span the full saturated kernel. -/
theorem Positive.integer_kernel_basis {H : NumericalSemigroup} (D : Positive H)
    (x y z : ℤ) (hker : x*D.a+y*D.b+z*D.c=0) :
    ∃ l k : ℤ, x=-(D.A:ℤ)*l-(D.w:ℤ)*k ∧
      y=(D.p:ℤ)*l-(D.z:ℤ)*k ∧ z=(D.q:ℤ)*l+(D.C:ℤ)*k := by
  obtain ⟨u,v,w,hbez⟩ := bezout_three D.a D.b D.c D.primitive
  obtain ⟨ha,hb,hc⟩ := D.primitive_minors
  have hs := D.coefficient_sums
  have hcadd : D.c+D.p*D.u=D.A*D.B := by
    have h0 := congrArg (fun n => n*D.B) D.center
    have h1 := congrArg (fun n => n*D.p) D.middle
    change D.A*D.a*D.B=(D.p*D.b+D.q*D.c)*D.B at h0
    change D.B*D.b*D.p=(D.u*D.a+D.v*D.c)*D.p at h1
    have hac := congrArg (fun n => n*D.c) ha
    have he : D.a*(D.c+D.p*D.u)=D.a*(D.A*D.B) := by
      nlinarith only [h0,h1,hac]
    exact Nat.eq_of_mul_eq_mul_left (D.triple.positive 0) he
  obtain ⟨l,k,hx,hy,hz⟩ := integer_kernel_of_primitive_minors
    (-(D.A:ℤ)) D.p D.q (-(D.w:ℤ)) (-(D.z:ℤ)) D.C D.a D.b D.c
    u v w x y z
    (by rw [ha,hs.2.1,hs.2.2]; push_cast; ring)
    (by rw [hb,hs.1,hs.2.2]; push_cast; ring)
    (by
      simp only [neg_mul,mul_neg,neg_neg,sub_neg_eq_add]
      exact_mod_cast (show D.c=D.A*D.z+D.p*D.w by
        rw [hs.1,hs.2.1] at hcadd
        rw [hs.1]
        nlinarith only [hcadd])) hbez hker
  exact ⟨l,k,by simpa [sub_eq_add_neg] using hx,
    by simpa [sub_eq_add_neg] using hy,hz⟩

theorem Positive.integer_kernel_coordinates_unique {H : NumericalSemigroup} (D : Positive H)
    (l k l' k' : ℤ)
    (hx : -(D.A:ℤ)*l-(D.w:ℤ)*k= -(D.A:ℤ)*l'-(D.w:ℤ)*k')
    (hy : (D.p:ℤ)*l-(D.z:ℤ)*k=(D.p:ℤ)*l'-(D.z:ℤ)*k')
    (hz : (D.q:ℤ)*l+(D.C:ℤ)*k=(D.q:ℤ)*l'+(D.C:ℤ)*k') : l=l' ∧ k=k' := by
  have ha := D.primitive_minors.1
  have hs := D.coefficient_sums.2.2
  have hap := D.triple.positive 0
  have hap' : (0:ℤ)<D.a := by exact_mod_cast hap
  have hat : (D.a:ℤ)=D.p*D.C+D.q*D.z := by
    exact_mod_cast (show D.a=D.p*D.C+D.q*D.z by
      rw [ha,hs,D.coefficient_sums.2.1]; ring)
  constructor <;> nlinarith [congrArg (fun n : ℤ => n*D.C) hy,
    congrArg (fun n : ℤ => n*D.z) hz,congrArg (fun n : ℤ => n*D.q) hy,
    congrArg (fun n : ℤ => n*D.p) hz]

end NS25Lean.SharedTail
