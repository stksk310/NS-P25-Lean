import NS25Lean.P2SectorCSourceQuotientR31

set_option linter.style.header false
set_option linter.style.whitespace false
noncomputable section
namespace NS25Lean.L5A2C4OR32
open L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR5
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 L5A2C4OR29 FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

/-- Exact promotion of the R31 verification-only generator set. -/
def M4Generators {P : P2Data Gamma} (R : ActualRolePacket P) : Set Monomial :=
  Set.range (sourceNormal R) ∪ {boundaryAliveMonomial R} ∪
    {w | ∃ s : ModelSources P.M.base R.e,
      0 < (sourceNormal R s).2.1 ∧ w=sourceWrap R (sourceNormal R s)}

theorem subcritical_pure_a_fiber {P : P2Data Gamma} (R : ActualRolePacket P)
    {A r i j : ℕ} (hA : A<c1 P.M.base R.e)
    (he : monomialDegree P.M.base R.e (r,i,j)=A*routingA P.M.base R.e) :
    r=A ∧ i=0 ∧ j=0 := by
  have ha := routingA_pos P.M.base R.e
  have hb := routingB_positive P.M.base R.e
  have hc := routingC_positive P.M.base R.e
  simp only [monomialDegree,normalizedGrid] at he
  have hr : r≤A := by nlinarith
  have hra : r=A := by
    by_contra hn
    have hd : 0<A-r := by omega
    have hrec := Nat.sub_add_cancel hr
    have hmul := congrArg (fun n => n*routingA P.M.base R.e) hrec
    simp only [Nat.add_mul] at hmul
    have hmin := (actual_normalized_critical_minima R).1 (A-r) i j hd
      (by nlinarith only [he,hmul])
    omega
  exact ⟨hra,by nlinarith [he],by nlinarith [he]⟩

/-- Constructed from the actual inactive predecessor and least axis cut,
not supplied as a generator-existence hypothesis. -/
theorem actual_pure_a_source {P : P2Data Gamma} (R : ActualRolePacket P) :
    ∃ s : ModelSources P.M.base R.e, ∃ A : ℕ,
      0<A ∧ A<c1 P.M.base R.e ∧ sourceNormal R s=(A,0,0) := by
  classical
  let a := routingA P.M.base R.e
  let K := cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
  have hc1 : 0<c1 P.M.base R.e := herzogC_positive P.M.base R.e 0
  have hex : ∃ A : ℕ, A*a ∈ K := by
    refine ⟨c1 P.M.base R.e-1,?_⟩
    simpa only [Nat.sub_mul,one_mul] using (actual_normalized_inactive_killed R).1
  let A := Nat.find hex
  have hK : A*a ∈ K := Nat.find_spec hex
  have hle : A≤c1 P.M.base R.e-1 := Nat.find_min' hex
    (by simpa only [Nat.sub_mul,one_mul] using (actual_normalized_inactive_killed R).1)
  have hlt : A<c1 P.M.base R.e := by omega
  have hpos : 0<A := by
    obtain ⟨_,n,hn,y,_,heq⟩ := hK
    have hm := routingM_pos P.M.base R.e
    have ha := routingA_pos P.M.base R.e
    change A*a=n*routingM P.M.base R.e+y at heq
    nlinarith
  have hs : IsMinimalTailGenerator (routingH P.M.base R.e).toAddSubmonoid K (A*a) := by
    apply (minimalTail_iff_literal _ _ _).mpr
    refine ⟨hK,?_⟩
    intro y h hy hh heq
    obtain ⟨r,i,j,hyfac⟩ := L5A2C4OR6.routingH_factorization P.M.base R.e hy.1
    obtain ⟨r',i',j',hhfac⟩ := L5A2C4OR6.routingH_factorization P.M.base R.e hh
    have hf : monomialDegree P.M.base R.e (r+r',i+i',j+j')=A*a := by
      change monomialDegree P.M.base R.e ((r,i,j)+(r',i',j'))=A*a
      rw [monomialDegree_add]
      change normalizedGrid P.M.base R.e r i j+normalizedGrid P.M.base R.e r' i' j'=A*a
      simpa only [normalizedGrid,←hyfac,←hhfac] using heq.symm
    obtain ⟨hr,hi,hj⟩ := subcritical_pure_a_fiber R hlt hf
    have hi0 : i=0 ∧ i'=0 := by omega
    have hj0 : j=0 ∧ j'=0 := by omega
    have hyA : y=r*a := by simpa [normalizedGrid,hi0.1,hj0.1] using hyfac
    have hrmin : A≤r := Nat.find_min' hex (by rwa [←hyA])
    have hr' : r'=0 := by omega
    simpa [normalizedGrid,hr',hi0.2,hj0.2] using hhfac
  let s : ModelSources P.M.base R.e := ⟨A*a,hs⟩
  have hn := (sourceNormal_spec R s).2.2 (A,0,0)
    (by simp [s,a,monomialDegree,normalizedGrid])
  refine ⟨s,A,hpos,hlt,?_⟩
  simpa [f2Normal] using hn.symm

theorem mixed_boundary_wrap_redundant {P : P2Data Gamma} (R : ActualRolePacket P) :
    (cr31 R.HD+cr21 R.HD,0,cr23 R.HD) ∈ monomialClosure (M4Generators R) := by
  obtain ⟨s,A,_,hA,hs⟩ := actual_pure_a_source R
  have hc := (coherent_coefficients P.M.base R.e R.HD).1
  refine ⟨(A,0,0),Or.inl (Or.inl ⟨s,hs⟩),?_,by simp,by simp⟩
  simp only [Prod.fst]
  omega

/-- The normal form of every multiple of a source is covered by the
original source or its first wrap, including all repeated wrap periods. -/
theorem normal_source_multiple {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (t : Monomial) :
    f2Normal P.M.base R.e R.HD (sourceNormal R s+t) ∈ monomialClosure (M4Generators R) := by
  generalize he : sourceNormal R s=g
  have hg : g ∈ M4Generators R := Or.inl (Or.inl ⟨s,he⟩)
  have hC : 0<c2 P.M.base R.e := herzogC_positive _ _ 1
  by_cases h : g.2.1+t.2.1<c2 P.M.base R.e
  · refine ⟨g,hg,?_,?_,?_⟩ <;>
      simp only [f2Normal,Prod.fst_add,Prod.snd_add,Nat.div_eq_of_lt h,
        Nat.mod_eq_of_lt h,mul_zero,add_zero,Prod.fst,Prod.snd] <;> omega
  · have hdiv : 1≤(g.2.1+t.2.1)/c2 P.M.base R.e :=
      (Nat.le_div_iff_mul_le hC).mpr (by omega)
    by_cases hy : 0<g.2.1
    · refine ⟨sourceWrap R g,Or.inr ⟨s,by rwa [he],by rw [he]⟩,?_,by simp [sourceWrap],?_⟩
      all_goals
        simp only [f2Normal,sourceWrap,Prod.fst_add,Prod.snd_add,Prod.fst,Prod.snd]
        nlinarith
    · have hy0 : g.2.1=0 := by omega
      refine ⟨g,hg,?_,?_,?_⟩ <;>
        simp only [f2Normal,Prod.fst_add,Prod.snd_add,Prod.fst,Prod.snd] <;> omega

theorem normal_boundary_multiple {P : P2Data Gamma} (R : ActualRolePacket P)
    (t : Monomial) :
    f2Normal P.M.base R.e R.HD (boundaryAliveMonomial R+t) ∈
      monomialClosure (M4Generators R) := by
  classical
  have hg : boundaryAliveMonomial R ∈ M4Generators R := Or.inl (Or.inr rfl)
  have hC : 0<c2 P.M.base R.e := herzogC_positive _ _ 1
  by_cases hc : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
  · simp only [boundaryAliveMonomial,if_pos hc] at hg ⊢
    refine ⟨(0,0,c3 P.M.base R.e),hg,by simp [f2Normal],by simp [f2Normal],?_⟩
    simp only [f2Normal,Prod.fst_add,Prod.snd_add,Prod.fst,Prod.snd,zero_add]
    omega
  · simp only [boundaryAliveMonomial,if_neg hc] at hg ⊢
    by_cases h : cr32 R.HD+t.2.1<c2 P.M.base R.e
    · refine ⟨(cr31 R.HD,cr32 R.HD,0),hg,?_,?_,?_⟩ <;>
        simp only [f2Normal,Prod.fst_add,Prod.snd_add,Prod.fst,Prod.snd,
          Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h,mul_zero,add_zero] <;> omega
    · have hd : 1≤(cr32 R.HD+t.2.1)/c2 P.M.base R.e :=
        (Nat.le_div_iff_mul_le hC).mpr (by omega)
      apply monomialClosure_upward (mixed_boundary_wrap_redundant R)
      · simp only [f2Normal,Prod.fst_add,Prod.snd_add,Prod.fst,Prod.snd]
        nlinarith
      · simp [f2Normal]
      · simp only [f2Normal,Prod.fst_add,Prod.snd_add,Prod.fst,Prod.snd,zero_add]
        nlinarith

/-- Literal coordinates in the original variable indexing. -/
def roleCoordinates (e : Fin 3 ≃ Fin 3) (d : Fin 3 →₀ ℕ) : Monomial :=
  (d (e 0),d (e 1),d (e 2))

@[simp] theorem roleCoordinates_exponent (e : Fin 3 ≃ Fin 3) (z : Monomial) :
    roleCoordinates e (roleExponent e z)=z := by
  obtain ⟨r,i,j⟩ := z
  simp [roleCoordinates,roleExponent]

def f2LinearNormalForm (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) : ToricPresentation.Poly k 3 →ₗ[k] ToricPresentation.Poly k 3 :=
  AddMonoidAlgebra.mapDomainLinearMap k k (fun d => roleExponent R.e
    (f2Normal P.M.base R.e R.HD (roleCoordinates R.e d)))

@[simp] theorem linearNormalForm_monomial (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (d : Fin 3 →₀ ℕ) (c : k) :
    f2LinearNormalForm k R (MvPolynomial.monomial d c)=
      MvPolynomial.monomial (roleExponent R.e
        (f2Normal P.M.base R.e R.HD (roleCoordinates R.e d))) c := by
  exact AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

@[simp] theorem linearNormalForm_role (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z : Monomial) :
    f2LinearNormalForm k R (roleMonomial k R.e z)=
      roleMonomial k R.e (f2Normal P.M.base R.e R.HD z) := by
  simp [roleMonomial]

def stripSupported (k : Type*) [Field k] {P : P2Data Gamma} (R : ActualRolePacket P) :
    Submodule k (ToricPresentation.Poly k 3) :=
  AddMonoidAlgebra.supported k k {d | roleCoordinates R.e d ∈ monomialClosure (M4Generators R)}

theorem supported_role_iff (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z : Monomial) :
    roleMonomial k R.e z ∈ stripSupported k R ↔ z ∈ monomialClosure (M4Generators R) := by
  classical
  change Finsupp.single (roleExponent R.e z) (1:k) ∈ Finsupp.supported k k
    {d | roleCoordinates R.e d ∈ monomialClosure (M4Generators R)} ↔ _
  simp [Finsupp.mem_supported,roleCoordinates_exponent]

theorem scalar_role_monomial (k : Type*) [Field k] (e : Fin 3 ≃ Fin 3)
    (d : Fin 3 →₀ ℕ) (c : k) :
    MvPolynomial.monomial d c=c • roleMonomial k e (roleCoordinates e d) := by
  have hd : roleExponent e (roleCoordinates e d)=d := roleExponent_coordinates e d
  simp [roleMonomial,hd,MvPolynomial.smul_monomial]

/-- Testing all literal monomial translates makes this a genuine ideal;
its construction does not presuppose any desired generator or bound. -/
def normalFormTestIdeal (k : Type*) [Field k] {P : P2Data Gamma} (R : ActualRolePacket P)
    (W : Submodule k (ToricPresentation.Poly k 3)) :
    Ideal (ToricPresentation.Poly k 3) where
  carrier := {f | ∀ t : Monomial,
    f2LinearNormalForm k R (roleMonomial k R.e t*f) ∈ W}
  zero_mem' := by intro t; simp
  add_mem' := by
    intro f g hf hg t
    rw [mul_add,map_add]
    exact W.add_mem (hf t) (hg t)
  smul_mem' := by
    intro a f hf
    change ∀ t, f2LinearNormalForm k R (roleMonomial k R.e t*(a*f)) ∈ W
    induction a using MvPolynomial.induction_on' with
    | monomial d c =>
      intro t
      rw [scalar_role_monomial k R.e d c,smul_mul_assoc,mul_smul_comm,map_smul]
      apply W.smul_mem
      simpa only [roleMonomial_add,mul_assoc] using hf (t+roleCoordinates R.e d)
    | add a b ha hb =>
      intro t
      rw [add_mul,mul_add,map_add]
      exact W.add_mem (ha t) (hb t)

def stripTestIdeal (k : Type*) [Field k] {P : P2Data Gamma} (R : ActualRolePacket P) :
    Ideal (ToricPresentation.Poly k 3) := normalFormTestIdeal k R (stripSupported k R)

theorem F2_mem_normalFormTestIdeal (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (W : Submodule k (ToricPresentation.Poly k 3)) :
    roleMonomial k R.e (0,c2 P.M.base R.e,0)-roleMonomial k R.e (cr21 R.HD,0,cr23 R.HD) ∈
      normalFormTestIdeal k R W := by
  intro t
  rw [mul_sub,←roleMonomial_add,←roleMonomial_add,map_sub,linearNormalForm_role,linearNormalForm_role]
  have hn : f2Normal P.M.base R.e R.HD (t+(0,c2 P.M.base R.e,0))=
      f2Normal P.M.base R.e R.HD (t+(cr21 R.HD,0,cr23 R.HD)) := by
    obtain ⟨r,i,j⟩ := t
    change f2Normal P.M.base R.e R.HD (r,i+c2 P.M.base R.e,j)=
      f2Normal P.M.base R.e R.HD (r+cr21 R.HD,i,j+cr23 R.HD)
    simpa only [Nat.add_sub_cancel] using
      f2Normal_bWrap P.M.base R.e R.HD r (i+c2 P.M.base R.e) j (by omega)
  rw [hn,sub_self]
  exact W.zero_mem

theorem F2_mem_stripTestIdeal (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) :
    roleMonomial k R.e (0,c2 P.M.base R.e,0)-roleMonomial k R.e (cr21 R.HD,0,cr23 R.HD) ∈
      stripTestIdeal k R := F2_mem_normalFormTestIdeal k R _

theorem source_mem_stripTestIdeal (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (s : ModelSources P.M.base R.e) :
    roleMonomial k R.e (sourceNormal R s) ∈ stripTestIdeal k R := by
  intro t
  rw [←roleMonomial_add,linearNormalForm_role,supported_role_iff]
  have he : t+sourceNormal R s=sourceNormal R s+t := add_comm _ _
  rw [he]
  exact normal_source_multiple R s t

theorem boundary_mem_stripTestIdeal (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) :
    roleMonomial k R.e (boundaryAliveMonomial R) ∈ stripTestIdeal k R := by
  intro t
  rw [←roleMonomial_add,linearNormalForm_role,supported_role_iff,add_comm t]
  exact normal_boundary_multiple R t

theorem sourceQuotient_le_stripTestIdeal (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) : sourceQuotientIdeal k R ≤ stripTestIdeal k R := by
  apply Ideal.span_le.mpr
  intro f hf
  rcases hf with (hf | hf) | hf
  · rw [Set.mem_singleton_iff] at hf
    subst f
    exact F2_mem_stripTestIdeal k R
  · obtain ⟨s,rfl⟩ := hf
    exact source_mem_stripTestIdeal k R s
  · rw [Set.mem_singleton_iff] at hf
    subst f
    exact boundary_mem_stripTestIdeal k R

theorem normal_strip_fixed {P : P2Data Gamma} (R : ActualRolePacket P)
    (z : Monomial) (hz : z.2.1<c2 P.M.base R.e) :
    f2Normal P.M.base R.e R.HD z=z := by
  obtain ⟨r,i,j⟩ := z
  simp only [f2Normal,Nat.div_eq_of_lt hz,Nat.mod_eq_of_lt hz,mul_zero,add_zero]

theorem source_initial_normal_strip_forward (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z : Monomial) (hz : z.2.1<c2 P.M.base R.e)
    (hJ : roleMonomial k R.e z ∈ P.M.base.J k) : z ∈ monomialClosure (M4Generators R) := by
  have hQ : roleMonomial k R.e z ∈ sourceQuotientIdeal k R := by
    rwa [actual_source_quotient_eq k R]
  have htest := sourceQuotient_le_stripTestIdeal k R hQ (0,0,0)
  have hzero : (0,0,0)+z=z := zero_add z
  rw [←roleMonomial_add,hzero,linearNormalForm_role,normal_strip_fixed R z hz,
    supported_role_iff] at htest
  exact htest

theorem generators_quotient_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) {z : Monomial} (hz : z ∈ M4Generators R) :
    sourceQuotientMonomial k R z=0 := by
  rcases hz with (hz | hz) | hz
  · obtain ⟨s,rfl⟩ := hz
    exact source_normal_quotient_zero k R s
  · rw [Set.mem_singleton_iff] at hz
    subst z
    exact boundary_alive_quotient_zero k R
  · obtain ⟨s,hy,rfl⟩ := hz
    exact source_wrap_quotient_zero k R s hy

theorem monomialClosure_mem_actual (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) {z : Monomial} (hz : z ∈ monomialClosure (M4Generators R)) :
    roleMonomial k R.e z ∈ P.M.base.J k := by
  obtain ⟨g,hg,hr,hi,hj⟩ := hz
  have he : z=g+(z.1-g.1,z.2.1-g.2.1,z.2.2-g.2.2) := by
    ext <;> simp <;> omega
  rw [←actual_source_quotient_eq k R]
  apply (sourceQuotientMonomial_eq_zero_iff k R z).mp
  rw [he,sourceQuotientMonomial_add,generators_quotient_zero k R hg,zero_mul]

/-- M4: exact original arbitrary-role and arbitrary-field binder. -/
theorem source_initial_normal_strip :
    ∀ {Gamma : NumericalSemigroup} {P : P2Data Gamma}
      (R : ActualRolePacket P) (k : Type*) [Field k] (z : Monomial),
      z.2.1<c2 P.M.base R.e →
      (roleMonomial k R.e z ∈ P.M.base.J k ↔ z ∈ monomialClosure (M4Generators R)) := by
  intro Gamma P R k inst z hz
  exact ⟨source_initial_normal_strip_forward k R z hz,monomialClosure_mem_actual k R⟩

theorem linearNormalForm_fixed_of_strip_support (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (f : ToricPresentation.Poly k 3)
    (hf : ∀ d ∈ f.support, (roleCoordinates R.e d).2.1<c2 P.M.base R.e) :
    f2LinearNormalForm k R f=f := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.as_sum f]
  apply Finset.sum_congr rfl
  intro d hd
  rw [linearNormalForm_monomial,normal_strip_fixed R _ (hf d hd)]
  have he : roleExponent R.e (roleCoordinates R.e d)=d := roleExponent_coordinates R.e d
  rw [he]

theorem monic_F2_normalForm_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) {f : ToricPresentation.Poly k 3}
    (hf : f ∈ Ideal.span
      {roleMonomial k R.e (0,c2 P.M.base R.e,0)-roleMonomial k R.e (cr21 R.HD,0,cr23 R.HD)}) :
    f2LinearNormalForm k R f=0 := by
  have hle : Ideal.span
      {roleMonomial k R.e (0,c2 P.M.base R.e,0)-roleMonomial k R.e (cr21 R.HD,0,cr23 R.HD)} ≤
      normalFormTestIdeal k R ⊥ := by
    apply Ideal.span_le.mpr
    rintro g rfl
    exact F2_mem_normalFormTestIdeal k R ⊥
  have h := hle hf (0,0,0)
  simpa [roleMonomial,roleExponent] using h

/-- Uniqueness for arbitrary normal-strip polynomials, not just monomials.
This explicitly rules out cancellation creating an extra normal relation. -/
theorem monic_F2_strip_unique (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (f g : ToricPresentation.Poly k 3)
    (hf : ∀ d ∈ f.support, (roleCoordinates R.e d).2.1<c2 P.M.base R.e)
    (hg : ∀ d ∈ g.support, (roleCoordinates R.e d).2.1<c2 P.M.base R.e)
    (he : f-g ∈ Ideal.span
      {roleMonomial k R.e (0,c2 P.M.base R.e,0)-roleMonomial k R.e (cr21 R.HD,0,cr23 R.HD)}) :
    f=g := by
  have hz := monic_F2_normalForm_zero k R he
  rw [map_sub,linearNormalForm_fixed_of_strip_support k R f hf,
    linearNormalForm_fixed_of_strip_support k R g hg,sub_eq_zero] at hz
  exact hz

theorem actual_normalForm_supported (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) {f : ToricPresentation.Poly k 3} (hf : f ∈ P.M.base.J k) :
    f2LinearNormalForm k R f ∈ stripSupported k R := by
  have hQ : f ∈ sourceQuotientIdeal k R := by rwa [actual_source_quotient_eq k R]
  have h := sourceQuotient_le_stripTestIdeal k R hQ (0,0,0)
  simpa [roleMonomial,roleExponent] using h

/-- Role lex order: y first, then x, then z. Original coordinates are
reindexed explicitly, and equal y-level terms are not discarded. -/
def IsRoleLeading (k : Type*) [Field k] {P : P2Data Gamma} (R : ActualRolePacket P)
    (f : ToricPresentation.Poly k 3) (z : Monomial) : Prop :=
  MvPolynomial.coeff (roleExponent R.e z) f ≠ 0 ∧
    ∀ d ∈ f.support, let w := roleCoordinates R.e d
      w.2.1<z.2.1 ∨ (w.2.1=z.2.1 ∧
        (w.1<z.1 ∨ (w.1=z.1 ∧ w.2.2≤z.2.2)))

def initialGenerators {P : P2Data Gamma} (R : ActualRolePacket P) : Set Monomial :=
  {(0,c2 P.M.base R.e,0)} ∪ M4Generators R

theorem leading_monomial (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z : Monomial) : IsRoleLeading k R (roleMonomial k R.e z) z := by
  classical
  constructor
  · simp [roleMonomial]
  · intro d hd
    have he' : roleExponent R.e z=d := by simpa [roleMonomial] using hd
    have he : d=roleExponent R.e z := he'.symm
    subst d
    simp [roleCoordinates_exponent]

theorem leading_F2_multiple (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z w : Monomial) (hy : w.2.1<z.2.1) :
    IsRoleLeading k R (roleMonomial k R.e z-roleMonomial k R.e w) z := by
  classical
  have he : roleExponent R.e w ≠ roleExponent R.e z := by
    intro h
    have hc := congrArg (roleCoordinates R.e) h
    simp only [roleCoordinates_exponent] at hc
    subst w
    omega
  constructor
  · simp [roleMonomial,MvPolynomial.coeff_sub,he]
  · intro d hd
    have hcoef := MvPolynomial.mem_support_iff.mp hd
    by_cases hz : roleExponent R.e z=d
    · subst d
      simp [roleCoordinates_exponent]
    · have hw : roleExponent R.e w=d := by
        by_contra hn
        simp [roleMonomial,MvPolynomial.coeff_sub,hz,hn] at hcoef
      subst d
      exact Or.inl (by simpa only [roleCoordinates_exponent] using hy)

theorem role_initial_forward (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) {f : ToricPresentation.Poly k 3} (hf : f ∈ P.M.base.J k)
    {z : Monomial} (hz : IsRoleLeading k R f z) :
    z ∈ monomialClosure (initialGenerators R) := by
  classical
  by_cases hy : z.2.1<c2 P.M.base R.e
  · have hs : ∀ d ∈ f.support, (roleCoordinates R.e d).2.1<c2 P.M.base R.e := by
      intro d hd
      rcases hz.2 d hd with h | ⟨h,_⟩ <;> omega
    have hgood := actual_normalForm_supported k R hf
    rw [linearNormalForm_fixed_of_strip_support k R f hs] at hgood
    have hm : roleExponent R.e z ∈ f.support := MvPolynomial.mem_support_iff.mpr hz.1
    have hmem := hgood hm
    change roleCoordinates R.e (roleExponent R.e z) ∈ monomialClosure (M4Generators R) at hmem
    rw [roleCoordinates_exponent] at hmem
    obtain ⟨g,hg,hr,hi,hj⟩ := hmem
    exact ⟨g,Or.inr hg,hr,hi,hj⟩
  · exact ⟨(0,c2 P.M.base R.e,0),Or.inl rfl,Nat.zero_le _,
      by simpa only [Prod.fst,Prod.snd] using (show c2 P.M.base R.e≤z.2.1 by omega),Nat.zero_le _⟩

theorem role_initial_reverse (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) {z : Monomial}
    (hz : z ∈ monomialClosure (initialGenerators R)) :
    ∃ f ∈ P.M.base.J k, IsRoleLeading k R f z := by
  obtain ⟨g,hg,hr,hi,hj⟩ := hz
  rcases hg with hg | hg
  · rw [Set.mem_singleton_iff] at hg
    subst g
    change c2 P.M.base R.e≤z.2.1 at hi
    let t : Monomial := (z.1,z.2.1-c2 P.M.base R.e,z.2.2)
    let w := t+(cr21 R.HD,0,cr23 R.HD)
    have he : t+(0,c2 P.M.base R.e,0)=z := by ext <;> simp [t] <;> omega
    have hF : roleMonomial k R.e (0,c2 P.M.base R.e,0)-
        roleMonomial k R.e (cr21 R.HD,0,cr23 R.HD) ∈ P.M.base.J k := by
      rw [←actual_source_quotient_eq k R]
      exact Ideal.subset_span (Or.inl (Or.inl rfl))
    refine ⟨roleMonomial k R.e z-roleMonomial k R.e w,?_,?_⟩
    · have hm := (P.M.base.J k).mul_mem_left (roleMonomial k R.e t) hF
      rwa [mul_sub,←roleMonomial_add,←roleMonomial_add,he] at hm
    · apply leading_F2_multiple k R
      have hC : 0<c2 P.M.base R.e := herzogC_positive _ _ 1
      change z.2.1-c2 P.M.base R.e+0<z.2.1
      omega
  · exact ⟨roleMonomial k R.e z,
      monomialClosure_mem_actual k R ⟨g,hg,hr,hi,hj⟩,leading_monomial k R z⟩

/-- Whole role-lex initial monomial ideal, represented exactly by its
exponents. This is NOT an assertion that y^C itself lies in actual J. -/
theorem role_initial_exponents_eq (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) :
    {z | ∃ f ∈ P.M.base.J k, IsRoleLeading k R f z} = monomialClosure (initialGenerators R) := by
  ext z
  exact ⟨fun ⟨f,hf,hz⟩ => role_initial_forward k R hf hz,role_initial_reverse k R⟩

def monicF2Ideal (k : Type*) [Field k] {P : P2Data Gamma} (R : ActualRolePacket P) :
    Ideal (ToricPresentation.Poly k 3) := Ideal.span
      {roleMonomial k R.e (0,c2 P.M.base R.e,0)-roleMonomial k R.e (cr21 R.HD,0,cr23 R.HD)}

theorem monomial_normalForm_congr (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z : Monomial) :
    roleMonomial k R.e z-roleMonomial k R.e (f2Normal P.M.base R.e R.HD z) ∈ monicF2Ideal k R := by
  obtain ⟨r,i,j⟩ := z
  induction i using Nat.strong_induction_on generalizing r j with
  | h i ih =>
    by_cases hi : i<c2 P.M.base R.e
    · rw [normal_strip_fixed R _ hi,sub_self]
      exact (monicF2Ideal k R).zero_mem
    have hle : c2 P.M.base R.e ≤ i := by omega
    have hC : 0<c2 P.M.base R.e := herzogC_positive _ _ 1
    have hprev := ih (i-c2 P.M.base R.e) (by omega) (r+cr21 R.HD) (j+cr23 R.HD)
    have he : (r,i-c2 P.M.base R.e,j)+(0,c2 P.M.base R.e,0)=(r,i,j) := by
      ext <;> simp <;> omega
    have he' : (r,i-c2 P.M.base R.e,j)+(cr21 R.HD,0,cr23 R.HD)=
        (r+cr21 R.HD,i-c2 P.M.base R.e,j+cr23 R.HD) := rfl
    have hgen : roleMonomial k R.e (0,c2 P.M.base R.e,0)-
        roleMonomial k R.e (cr21 R.HD,0,cr23 R.HD) ∈ monicF2Ideal k R :=
      Ideal.subset_span rfl
    have hs := (monicF2Ideal k R).mul_mem_left (roleMonomial k R.e (r,i-c2 P.M.base R.e,j)) hgen
    rw [mul_sub,←roleMonomial_add,←roleMonomial_add,he,he'] at hs
    have hsum := (monicF2Ideal k R).add_mem hs hprev
    rw [f2Normal_bWrap P.M.base R.e R.HD r i j hle]
    convert hsum using 1 <;> ring

theorem polynomial_normalForm_congr (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (f : ToricPresentation.Poly k 3) :
    f-f2LinearNormalForm k R f ∈ monicF2Ideal k R := by
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [scalar_role_monomial k R.e d c,map_smul,linearNormalForm_role,←smul_sub]
    exact ((monicF2Ideal k R).restrictScalars k).smul_mem c (monomial_normalForm_congr k R _)
  | add f g hf hg =>
    rw [map_add]
    convert (monicF2Ideal k R).add_mem hf hg using 1 <;> ring

theorem monicF2_mem_iff_normalForm_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (f : ToricPresentation.Poly k 3) :
    f ∈ monicF2Ideal k R ↔ f2LinearNormalForm k R f=0 := by
  constructor
  · exact monic_F2_normalForm_zero k R
  · intro h
    simpa only [h,sub_zero] using polynomial_normalForm_congr k R f

end NS25Lean.L5A2C4OR32
