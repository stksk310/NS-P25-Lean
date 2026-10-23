import NS25Lean.P3StrictReturnFormsR58

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R59
open ChosenBase L2B L5A1 FourGeneratedBridge
open L5A2C4A L5A2C4D L5A2C4H L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

/-- The primitive minor normalization comes from the finite residue bijection. -/
theorem primitiveHerzog_minor_formula (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) :
    let P := P3R57.roleCoefficient M hp e 0 1
    let Q := P3R57.roleCoefficient M hp e 0 2
    let U := P3R57.roleCoefficient M hp e 1 0
    let V := P3R57.roleCoefficient M hp e 1 2
    let W := P3R57.roleCoefficient M hp e 2 0
    let Z := P3R57.roleCoefficient M hp e 2 1
    routingA M.base e = P*Q+P*V+Q*Z ∧
      routingB M.base e = U*Q+U*V+W*V ∧
      routingC M.base e = U*Z+W*Z+W*P := by
  dsimp only
  let D := P3R58.p3_coherentHerzogData M hp e
  have hbij := coherent_lShape_residue_bijective M.base e D
  have ha := Fintype.card_congr (Equiv.ofBijective _ hbij)
  simp only [GenericLShape.Index, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, ZMod.card] at ha
  change P3R57.roleCoefficient M hp e 0 1 *
      (P3R57.roleCoefficient M hp e 0 2 + P3R57.roleCoefficient M hp e 1 2) +
      P3R57.roleCoefficient M hp e 2 1 * P3R57.roleCoefficient M hp e 0 2 =
      routingA M.base e at ha
  have hs := P3R58.p3_coefficient_sums M hp e
  have hr := coherent_normalized_relations M.base e D
  change criticalExponent M.base (e 0) * routingA M.base e =
    P3R57.roleCoefficient M hp e 0 1 * routingB M.base e +
    P3R57.roleCoefficient M hp e 0 2 * routingC M.base e ∧
    criticalExponent M.base (e 1) * routingB M.base e =
    P3R57.roleCoefficient M hp e 1 0 * routingA M.base e +
    P3R57.roleCoefficient M hp e 1 2 * routingC M.base e ∧
    criticalExponent M.base (e 2) * routingC M.base e =
    P3R57.roleCoefficient M hp e 2 0 * routingA M.base e +
    P3R57.roleCoefficient M hp e 2 1 * routingB M.base e at hr
  rw [hs.1, hs.2.1, hs.2.2] at hr
  have ha' : routingA M.base e =
      P3R57.roleCoefficient M hp e 0 1 * P3R57.roleCoefficient M hp e 0 2 +
      P3R57.roleCoefficient M hp e 0 1 * P3R57.roleCoefficient M hp e 1 2 +
      P3R57.roleCoefficient M hp e 0 2 * P3R57.roleCoefficient M hp e 2 1 := by
    nlinarith only [ha]
  rw [ha'] at hr
  refine ⟨ha', ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left (routingA_pos M.base e)
    rw [ha']
    nlinarith only [congrArg (fun n => n * (P3R57.roleCoefficient M hp e 0 2 +
      P3R57.roleCoefficient M hp e 1 2)) hr.1,
      congrArg (fun n => n * P3R57.roleCoefficient M hp e 0 2) hr.2.2, ha]
  · apply Nat.eq_of_mul_eq_mul_left (routingA_pos M.base e)
    rw [ha']
    nlinarith only [congrArg (fun n => n * P3R57.roleCoefficient M hp e 2 1) hr.1,
      congrArg (fun n => n * P3R57.roleCoefficient M hp e 0 1) hr.2.2, ha]

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

/-- Every normalized actual integer relation has integer Herzog coordinates. -/
theorem p3_integer_kernel_basis (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (x y z : ℤ)
    (hker : x*routingA M.base e+y*routingB M.base e+z*routingC M.base e=0) :
    ∃ l k : ℤ,
      x= -(criticalExponent M.base (e 0) : ℤ)*l -
        (P3R57.roleCoefficient M hp e 2 0 : ℤ)*k ∧
      y= (P3R57.roleCoefficient M hp e 0 1 : ℤ)*l -
        (P3R57.roleCoefficient M hp e 2 1 : ℤ)*k ∧
      z= (P3R57.roleCoefficient M hp e 0 2 : ℤ)*l +
        (criticalExponent M.base (e 2) : ℤ)*k := by
  have hg : Nat.gcd (routingA M.base e)
      (Nat.gcd (routingB M.base e) (routingC M.base e))=1 := by
    simpa [routingA, routingB, routingC, routingD, routingN1, routingN2, routingN3]
      using normalized_gcd_eq_one (chosenBase_minimalFour M.base e).n₁_pos
  obtain ⟨u,v,w,hbez⟩ := bezout_three _ _ _ hg
  obtain ⟨ha,hb,hc⟩ := primitiveHerzog_minor_formula M hp e
  have hs := P3R58.p3_coefficient_sums M hp e
  obtain ⟨l,k,hx,hy,hz⟩ := integer_kernel_of_primitive_minors
    (-(criticalExponent M.base (e 0) : ℤ))
    (P3R57.roleCoefficient M hp e 0 1) (P3R57.roleCoefficient M hp e 0 2)
    (-(P3R57.roleCoefficient M hp e 2 0 : ℤ))
    (-(P3R57.roleCoefficient M hp e 2 1 : ℤ))
    (criticalExponent M.base (e 2))
    (routingA M.base e) (routingB M.base e) (routingC M.base e)
    u v w x y z (by rw [ha,hs.2.2]; push_cast; ring)
    (by rw [hb,hs.1,hs.2.2]; push_cast; ring)
    (by rw [hc,hs.1]; push_cast; ring) hbez hker
  exact ⟨l,k,by simpa [sub_eq_add_neg] using hx,
    by simpa [sub_eq_add_neg] using hy,hz⟩

end NS25Lean.P3R59



