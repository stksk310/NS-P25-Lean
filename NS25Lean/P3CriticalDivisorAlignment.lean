import NS25Lean.P2SectorCDirectPFSourceModelR29
import NS25Lean.P3CoherentHerzogR58
import NS25Lean.P3ReturnNormalizationR59

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3CriticalDivisor
open ChosenBase L2B FourGeneratedBridge L5A2C4A L5A2C4C L5A2C4D L5A2C4H
  L5A2C4OR1 L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR29
variable {Gamma : NumericalSemigroup}

/-- A first actual Herzog move witnesses a critical-degree H-divisor. -/
theorem rewrite_critical_divisor (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {z z' : Monomial}
    (h : HerzogRewrite B e HD z z') :
    ∃ i : Fin 3, ∃ r : ℕ, r ∈ routingH B e ∧
      monomialDegree B e z =
        criticalExponent B (e i) * P3R59.normalizedRoleWeight B e i + r := by
  have hr := coherent_normalized_relations B e HD
  cases h with
  | central r i j hi hj =>
    refine ⟨0, normalizedGrid B e r (i-cr12 HD) (j-cr13 HD), ?_, ?_⟩
    · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨r,i-cr12 HD,j-cr13 HD,rfl⟩
    · change r*routingA B e+i*routingB B e+j*routingC B e =
        c1 B e*routingA B e + _
      simp only [normalizedGrid]
      have hb := congrArg (fun n => n*routingB B e) (Nat.sub_add_cancel hi)
      have hc := congrArg (fun n => n*routingC B e) (Nat.sub_add_cancel hj)
      simp only [Nat.add_mul] at hb hc
      nlinarith only [hr.1,hb,hc]
  | bWrap r i j _ hi =>
    refine ⟨1, normalizedGrid B e r (i-c2 B e) j, ?_, ?_⟩
    · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨r,i-c2 B e,j,rfl⟩
    · change r*routingA B e+i*routingB B e+j*routingC B e =
        c2 B e*routingB B e + _
      simp only [normalizedGrid]
      have hb := congrArg (fun n => n*routingB B e) (Nat.sub_add_cancel hi)
      simp only [Nat.add_mul] at hb
      omega
  | cWrap r i j _ _ hj =>
    refine ⟨2, normalizedGrid B e r i (j-c3 B e), ?_, ?_⟩
    · exact (mem_generatedThree_iff _ _ _ _).mpr ⟨r,i,j-c3 B e,rfl⟩
    · change r*routingA B e+i*routingB B e+j*routingC B e =
        c3 B e*routingC B e + _
      simp only [normalizedGrid]
      have hc := congrArg (fun n => n*routingC B e) (Nat.sub_add_cancel hj)
      simp only [Nat.add_mul] at hc
      omega

private theorem path_eq_of_no_first {X : Type*} {R : X → X → Prop}
    {x y : X} (hn : ∀ z, ¬R x z) (hp : Relation.ReflTransGen R x y) : x=y := by
  induction hp with
  | refl => rfl
  | @tail y z hp hyz ih =>
    subst y
    exact (hn z hyz).elim

/-- D6 for every degree: whole-fiber connectivity supplies a first move on
one of two distinct factorizations, hence one actual critical H-divisor. -/
theorem nonunique_critical_divisor (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z z' : Monomial)
    (he : monomialDegree B e z = monomialDegree B e z') (hne : z≠z') :
    ∃ i : Fin 3, ∃ r : ℕ, r ∈ routingH B e ∧
      monomialDegree B e z =
        criticalExponent B (e i) * P3R59.normalizedRoleWeight B e i + r := by
  classical
  obtain ⟨w,hp,hp'⟩ := equal_degree_has_common_herzog_reduct B e HD he
  by_cases h : ∃ v, HerzogRewrite B e HD z v
  · obtain ⟨v,hv⟩ := h
    exact rewrite_critical_divisor B e HD hv
  have hzw : z=w := path_eq_of_no_first (by simpa using h) hp
  have h' : ∃ v, HerzogRewrite B e HD z' v := by
    by_contra hn
    have hzw' : z'=w := path_eq_of_no_first (by simpa using hn) hp'
    exact hne (hzw.trans hzw'.symm)
  obtain ⟨v,hv⟩ := h'
  obtain ⟨i,r,hr,hd⟩ := rewrite_critical_divisor B e HD hv
  exact ⟨i,r,hr,he.trans hd⟩
end NS25Lean.P3CriticalDivisor
