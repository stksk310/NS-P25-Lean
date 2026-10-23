import NS25Lean.P2SectorCPureInternalSourceQuotientR41
import NS25Lean.P2SectorCNormalStripR32

set_option linter.style.header false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.L5A2C4OR42
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR19 L5A2C4OR20 L5A2C4OR22 L5A2C4OR29
  L5A2C4OR39 L5A2C4OR40 L5A2C4OR41 L5A2C4OR1 FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

theorem pure_alpha_pos (A : SectorBCriticalRoleBranchA P) : 0 < alpha A := by
  have hp := (branchA_symmetricTailData A).n0_pos
  rw [(branchA_symmetricTailData A).n0_eq] at hp
  exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hp)

/-- Reduction uses only the internal monic relation, not the boundary relation. -/
def pureNormal (A : SectorBCriticalRoleBranchA P) (z : Monomial) : Monomial :=
  (z.1+beta A*(z.2.1/alpha A),z.2.1%alpha A,z.2.2)

theorem pureNormal_y_lt (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    (pureNormal A z).2.1 < alpha A := Nat.mod_lt _ (pure_alpha_pos A)

theorem pureNormal_fixed (A : SectorBCriticalRoleBranchA P) (z : Monomial)
    (hz : z.2.1 < alpha A) : pureNormal A z=z := by
  obtain ⟨x,y,z⟩ := z
  simp [pureNormal,Nat.div_eq_of_lt hz,Nat.mod_eq_of_lt hz]

theorem pureNormal_step (A : SectorBCriticalRoleBranchA P) (x y z : ℕ)
    (hy : alpha A ≤ y) :
    pureNormal A (x,y,z)=pureNormal A (x+beta A,y-alpha A,z) := by
  have hdiv : y/alpha A=(y-alpha A)/alpha A+1 := by
    have he : y=(y-alpha A)+alpha A := (Nat.sub_add_cancel hy).symm
    conv_lhs => rw [he]
    rw [Nat.add_div_right _ (pure_alpha_pos A)]
  have hmod : y%alpha A=(y-alpha A)%alpha A := by
    have he : y=(y-alpha A)+alpha A := (Nat.sub_add_cancel hy).symm
    conv_lhs => rw [he]
    simp
  ext <;> simp [pureNormal,hdiv,hmod] <;> ring

theorem pureNormal_degree (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    monomialDegree P.M.base A.reindex (pureNormal A z)=
      monomialDegree P.M.base A.reindex z := by
  obtain ⟨x,y,z⟩ := z
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases hy : y<alpha A
    · rw [pureNormal_fixed A _ hy]
    · rw [pureNormal_step A x y z (by omega),ih (y-alpha A)
        (by have := pure_alpha_pos A; omega)]
      exact (pure_tail_pure_step_degree A x y z (by omega)).symm

def pureMonicIdeal (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    Ideal (ToricPresentation.Poly k 3) := Ideal.span
      {roleMonomial k A.reindex (0,alpha A,0)-roleMonomial k A.reindex (beta A,0,0)}

theorem pureNormal_congr (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) : roleMonomial k A.reindex z-
      roleMonomial k A.reindex (pureNormal A z) ∈ pureMonicIdeal A k := by
  obtain ⟨x,y,z⟩ := z
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases hy : y<alpha A
    · rw [pureNormal_fixed A _ hy,sub_self]; exact (pureMonicIdeal A k).zero_mem
    have hle : alpha A ≤ y := by omega
    have hp := ih (y-alpha A) (by have := pure_alpha_pos A; omega) (x+beta A)
    have he : (x,y-alpha A,z)+(0,alpha A,0)=(x,y,z) := by
      ext <;> simp <;> omega
    have he' : (x,y-alpha A,z)+(beta A,0,0)=(x+beta A,y-alpha A,z) := rfl
    have hg : roleMonomial k A.reindex (0,alpha A,0)-
        roleMonomial k A.reindex (beta A,0,0) ∈ pureMonicIdeal A k :=
      Ideal.subset_span rfl
    have hs := (pureMonicIdeal A k).mul_mem_left (roleMonomial k A.reindex (x,y-alpha A,z)) hg
    rw [mul_sub,←roleMonomial_add,←roleMonomial_add,he,he'] at hs
    rw [pureNormal_step A x y z hle]
    convert (pureMonicIdeal A k).add_mem hs hp using 1 <;> ring

/-- Component-status choice is exactly R41's live endpoint. Canonical s may be zero. -/
def pureAliveRaw (A : SectorBCriticalRoleBranchA P) : Monomial := by
  classical
  exact if BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent
    then (r A,s A,0) else (0,0,d A)

def pureAlive (A : SectorBCriticalRoleBranchA P) : Monomial := pureNormal A (pureAliveRaw A)

def pureOriginals (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  Set.range (pureSourceNormal A) ∪ {pureAlive A}

def pureWrap (A : SectorBCriticalRoleBranchA P) (g : Monomial) : Monomial :=
  (g.1+beta A,0,g.2.2)

/-- Include wraps of *all* original monomials, including the live boundary.
No redundancy or B=0 claim is hidden in this definition. -/
def pureStripGenerators (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  pureOriginals A ∪ {w | ∃ g ∈ pureOriginals A, 0<g.2.1 ∧ w=pureWrap A g}

def pureInitialGenerators (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  {(0,alpha A,0)} ∪ pureStripGenerators A

theorem pureOriginals_y_lt (A : SectorBCriticalRoleBranchA P) {g : Monomial}
    (hg : g ∈ pureOriginals A) : g.2.1 < alpha A := by
  rcases hg with ⟨v,rfl⟩ | rfl
  · exact (pureSourceNormal_spec A v).2.1
  · exact pureNormal_y_lt A _

theorem pureWrap_y_zero (A : SectorBCriticalRoleBranchA P) (g : Monomial) :
    (pureWrap A g).2.1=0 := rfl

theorem pureNormal_multiple (A : SectorBCriticalRoleBranchA P) {g : Monomial}
    (hg : g ∈ pureOriginals A) (t : Monomial) :
    pureNormal A (g+t) ∈ monomialClosure (pureStripGenerators A) := by
  have hgy := pureOriginals_y_lt A hg
  by_cases hy : g.2.1+t.2.1 < alpha A
  · refine ⟨g,Or.inl hg,?_,?_,?_⟩
    all_goals simp [pureNormal,Nat.div_eq_of_lt hy,Nat.mod_eq_of_lt hy] <;> omega
  · have hdiv : 1 ≤ (g.2.1+t.2.1)/alpha A := by
      apply (Nat.le_div_iff_mul_le (pure_alpha_pos A)).mpr
      simpa using (show alpha A≤g.2.1+t.2.1 by omega)
    by_cases hz : g.2.1=0
    · refine ⟨g,Or.inl hg,?_,?_,?_⟩
      all_goals simp [pureNormal,hz] <;> omega
    · refine ⟨pureWrap A g,Or.inr ⟨g,hg,by omega,rfl⟩,?_,?_,?_⟩
      · change g.1+beta A≤g.1+t.1+beta A*((g.2.1+t.2.1)/alpha A)
        have := Nat.mul_le_mul_left (beta A) hdiv
        simp only [mul_one] at this
        omega
      · exact Nat.zero_le _
      · change g.2.2≤g.2.2+t.2.2; omega

open L5A2C4OR32

def pureLinearNormalForm (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    ToricPresentation.Poly k 3 →ₗ[k] ToricPresentation.Poly k 3 :=
  AddMonoidAlgebra.mapDomainLinearMap k k
    (fun u => roleExponent A.reindex (pureNormal A (roleCoordinates A.reindex u)))

@[simp] theorem pureLinearNormalForm_monomial (A : SectorBCriticalRoleBranchA P)
    (k : Type*) [Field k] (u : Fin 3 →₀ ℕ) (c : k) :
    pureLinearNormalForm A k (MvPolynomial.monomial u c)=
      MvPolynomial.monomial (roleExponent A.reindex
        (pureNormal A (roleCoordinates A.reindex u))) c :=
  AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

@[simp] theorem pureLinearNormalForm_role (A : SectorBCriticalRoleBranchA P)
    (k : Type*) [Field k] (z : Monomial) :
    pureLinearNormalForm A k (roleMonomial k A.reindex z)=
      roleMonomial k A.reindex (pureNormal A z) := by simp [roleMonomial]

def pureStripSupported (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    Submodule k (ToricPresentation.Poly k 3) :=
  AddMonoidAlgebra.supported k k
    {u | roleCoordinates A.reindex u ∈ monomialClosure (pureStripGenerators A)}

theorem pureSupported_role_iff (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) : roleMonomial k A.reindex z ∈ pureStripSupported A k ↔
      z ∈ monomialClosure (pureStripGenerators A) := by
  classical
  change Finsupp.single (roleExponent A.reindex z) (1:k) ∈ Finsupp.supported k k
    {u | roleCoordinates A.reindex u ∈ monomialClosure (pureStripGenerators A)} ↔ _
  simp [Finsupp.mem_supported,roleCoordinates_exponent]

def pureNormalTestIdeal (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (W : Submodule k (ToricPresentation.Poly k 3)) : Ideal (ToricPresentation.Poly k 3) where
  carrier := {f | ∀ t : Monomial, pureLinearNormalForm A k (roleMonomial k A.reindex t*f) ∈ W}
  zero_mem' := by intro t; simp
  add_mem' := by
    intro f g hf hg t
    rw [mul_add,map_add]
    exact W.add_mem (hf t) (hg t)
  smul_mem' := by
    intro a f hf
    change ∀ t, pureLinearNormalForm A k (roleMonomial k A.reindex t*(a*f)) ∈ W
    induction a using MvPolynomial.induction_on' with
    | monomial u c =>
      intro t
      rw [scalar_role_monomial k A.reindex u c,smul_mul_assoc,mul_smul_comm,map_smul]
      apply W.smul_mem
      simpa only [roleMonomial_add,mul_assoc] using hf (t+roleCoordinates A.reindex u)
    | add a b ha hb =>
      intro t
      rw [add_mul,mul_add,map_add]
      exact W.add_mem (ha t) (hb t)

theorem pureMonic_le_test (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (W : Submodule k (ToricPresentation.Poly k 3)) :
    pureMonicIdeal A k ≤ pureNormalTestIdeal A k W := by
  apply Ideal.span_le.mpr
  rintro f rfl t
  rw [mul_sub,←roleMonomial_add,←roleMonomial_add,map_sub,
    pureLinearNormalForm_role,pureLinearNormalForm_role]
  have hn : pureNormal A (t+(0,alpha A,0))=pureNormal A (t+(beta A,0,0)) := by
    obtain ⟨x,y,z⟩ := t
    change pureNormal A (x,y+alpha A,z)=pureNormal A (x+beta A,y,z)
    simpa only [Nat.add_sub_cancel] using pureNormal_step A x (y+alpha A) z (by omega)
  rw [hn,sub_self]
  exact W.zero_mem

theorem pureLinearNormalForm_congr (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (f : ToricPresentation.Poly k 3) :
    f-pureLinearNormalForm A k f ∈ pureMonicIdeal A k := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [scalar_role_monomial k A.reindex u c,map_smul,pureLinearNormalForm_role,←smul_sub]
    exact ((pureMonicIdeal A k).restrictScalars k).smul_mem c (pureNormal_congr A k _)
  | add f g hf hg =>
    rw [map_add]
    convert (pureMonicIdeal A k).add_mem hf hg using 1 <;> ring

theorem pureMonic_mem_iff_normal_zero (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (f : ToricPresentation.Poly k 3) :
    f ∈ pureMonicIdeal A k ↔ pureLinearNormalForm A k f=0 := by
  constructor
  · intro hf
    have ht := pureMonic_le_test A k ⊥ hf (0,0,0)
    simpa [roleMonomial,roleExponent] using ht
  · intro hf
    simpa only [hf,sub_zero] using pureLinearNormalForm_congr A k f

theorem pureLinearNormalForm_fixed (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (f : ToricPresentation.Poly k 3)
    (hf : ∀ u ∈ f.support, (roleCoordinates A.reindex u).2.1<alpha A) :
    pureLinearNormalForm A k f=f := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.as_sum f]
  apply Finset.sum_congr rfl
  intro u hu
  rw [pureLinearNormalForm_monomial,pureNormal_fixed A _ (hf u hu)]
  have he : roleExponent A.reindex (roleCoordinates A.reindex u)=u :=
    roleExponent_coordinates A.reindex u
  rw [he]

theorem pureMonic_strip_unique (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (f g : ToricPresentation.Poly k 3)
    (hf : ∀ u ∈ f.support, (roleCoordinates A.reindex u).2.1<alpha A)
    (hg : ∀ u ∈ g.support, (roleCoordinates A.reindex u).2.1<alpha A)
    (he : f-g ∈ pureMonicIdeal A k) : f=g := by
  have hz := (pureMonic_mem_iff_normal_zero A k (f-g)).mp he
  rw [map_sub,pureLinearNormalForm_fixed A k f hf,
    pureLinearNormalForm_fixed A k g hg,sub_eq_zero] at hz
  exact hz

/-- Replace the raw live mixed endpoint by its internal monic normal form.
This does not identify raw mixed support with canonical mixed support. -/
theorem internal_candidate_le_test (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    pureInternalSourceIdeal A k ≤ pureNormalTestIdeal A k (pureStripSupported A k) := by
  classical
  let T := pureNormalTestIdeal A k (pureStripSupported A k)
  have hmono : pureMonicIdeal A k ≤ T := pureMonic_le_test A k _
  have horiginal (g : Monomial) (hg : g∈pureOriginals A) : roleMonomial k A.reindex g∈T := by
    intro t
    rw [←roleMonomial_add,pureLinearNormalForm_role,pureSupported_role_iff,add_comm t]
    exact pureNormal_multiple A hg t
  apply Ideal.span_le.mpr
  intro f hf
  rcases hf with (hf | ⟨v,rfl⟩) | hf
  · rcases hf with rfl
    exact hmono (Ideal.subset_span rfl)
  · exact horiginal _ (Or.inl ⟨v,rfl⟩)
  · rcases hf with rfl
    have he : (if BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent
        then roleMonomial k A.reindex (r A,s A,0)
        else roleMonomial k A.reindex (0,0,d A))=
        roleMonomial k A.reindex (pureAliveRaw A) := by
      unfold pureAliveRaw
      split_ifs <;> rfl
    rw [he]
    change roleMonomial k A.reindex (pureAliveRaw A) ∈ T
    have hdiff := hmono (pureNormal_congr A k (pureAliveRaw A))
    have hnorm := horiginal (pureAlive A) (Or.inr rfl)
    simpa only [pureAlive,sub_add_cancel] using T.add_mem hdiff hnorm

theorem actual_pureNormal_supported (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (k : Type*) [Field k]
    {f : ToricPresentation.Poly k 3} (hf : f∈P.M.base.J k) :
    pureLinearNormalForm A k f ∈ pureStripSupported A k := by
  rw [internal_source_quotient_exact A hk k] at hf
  have ht := internal_candidate_le_test A k hf (0,0,0)
  simpa [roleMonomial,roleExponent] using ht

theorem pure_strip_forward (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (k : Type*) [Field k]
    (z : Monomial) (hy : z.2.1<alpha A)
    (hz : roleMonomial k A.reindex z∈P.M.base.J k) :
    z∈monomialClosure (pureStripGenerators A) := by
  have ht := actual_pureNormal_supported A hk k hz
  rw [pureLinearNormalForm_role,pureNormal_fixed A z hy,pureSupported_role_iff] at ht
  exact ht

theorem pureMonic_le_J (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    pureMonicIdeal A k ≤ P.M.base.J k := by
  have hIH : P.M.base.IH k ≤ P.M.base.J k := by
    rw [Data.J_eq_IH_sup_MK]; exact le_sup_left
  apply Ideal.span_le.mpr
  rintro f rfl
  apply hIH
  rw [pure_tail_toric_exact A k]
  exact Ideal.subset_span (Or.inl rfl)

theorem pureOriginals_mem_J (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (k : Type*) [Field k]
    {g : Monomial} (hg : g∈pureOriginals A) : roleMonomial k A.reindex g∈P.M.base.J k := by
  classical
  rcases hg with ⟨v,rfl⟩ | rfl
  · rw [internal_source_quotient_exact A hk k]
    exact Ideal.subset_span (Or.inl (Or.inr ⟨v,rfl⟩))
  · have hraw : roleMonomial k A.reindex (pureAliveRaw A)∈P.M.base.J k := by
      rw [internal_source_quotient_exact A hk k]
      unfold pureAliveRaw
      split_ifs with hp
      · exact Ideal.subset_span (Or.inr (by simp [hp]))
      · exact Ideal.subset_span (Or.inr (by simp [hp]))
    have hd := pureMonic_le_J A k (pureNormal_congr A k (pureAliveRaw A))
    simpa only [sub_sub_cancel,pureAlive] using (P.M.base.J k).sub_mem hraw hd

theorem pureWrap_mem_J (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (k : Type*) [Field k]
    {g : Monomial} (hg : g∈pureOriginals A) (hy : 0<g.2.1) :
    roleMonomial k A.reindex (pureWrap A g)∈P.M.base.J k := by
  have hgy := pureOriginals_y_lt A hg
  let t : Monomial := (0,alpha A-g.2.1,0)
  have he : pureNormal A (g+t)=pureWrap A g := by
    have hy' : g.2.1+(alpha A-g.2.1)=alpha A := Nat.add_sub_of_le (by omega)
    ext <;> simp [pureNormal,pureWrap,t,hy',Nat.div_self (pure_alpha_pos A)]
  have hm : roleMonomial k A.reindex (g+t)∈P.M.base.J k := by
    rw [roleMonomial_add]
    exact (P.M.base.J k).mul_mem_right _ (pureOriginals_mem_J A hk k hg)
  have hd := pureMonic_le_J A k (pureNormal_congr A k (g+t))
  rw [he] at hd
  simpa only [sub_sub_cancel] using (P.M.base.J k).sub_mem hm hd

theorem pureStrip_mem_J (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (k : Type*) [Field k]
    {z : Monomial} (hz : z∈monomialClosure (pureStripGenerators A)) :
    roleMonomial k A.reindex z∈P.M.base.J k := by
  obtain ⟨g,hg,hx,hy,hz⟩ := hz
  have hmem : roleMonomial k A.reindex g∈P.M.base.J k := by
    rcases hg with hg | ⟨w,hw,hpositive,rfl⟩
    · exact pureOriginals_mem_J A hk k hg
    · exact pureWrap_mem_J A hk k hw hpositive
  have he : z=g+(z.1-g.1,z.2.1-g.2.1,z.2.2-g.2.2) := by ext <;> simp <;> omega
  rw [he,roleMonomial_add]
  exact (P.M.base.J k).mul_mem_right _ hmem

/-- Exact actual quotient membership on the full internal monic strip,
including both killed boundary orientations and arbitrary fields. -/
theorem pure_normal_strip_exact (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (k : Type*) [Field k]
    (z : Monomial) (hy : z.2.1<alpha A) :
    roleMonomial k A.reindex z∈P.M.base.J k ↔
      z∈monomialClosure (pureStripGenerators A) :=
  ⟨pure_strip_forward A hk k z hy,pureStrip_mem_J A hk k⟩

/-- Actual role-lex leading exponent (y, then x, then z). -/
def PureRoleLeading (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (f : ToricPresentation.Poly k 3) (z : Monomial) : Prop :=
  MvPolynomial.coeff (roleExponent A.reindex z) f≠0 ∧
    ∀ u∈f.support, let w := roleCoordinates A.reindex u
      w.2.1<z.2.1 ∨ (w.2.1=z.2.1 ∧ (w.1<z.1 ∨ (w.1=z.1 ∧ w.2.2≤z.2.2)))

theorem pure_leading_monomial (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) : PureRoleLeading A k (roleMonomial k A.reindex z) z := by
  classical
  constructor
  · simp [roleMonomial]
  · intro u hu
    have he : roleExponent A.reindex z=u := by simpa [roleMonomial] using hu
    subst u
    simp [roleCoordinates_exponent]

theorem pure_leading_difference (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z w : Monomial) (hy : w.2.1<z.2.1) :
    PureRoleLeading A k (roleMonomial k A.reindex z-roleMonomial k A.reindex w) z := by
  classical
  have he : roleExponent A.reindex w≠roleExponent A.reindex z := by
    intro h
    have hc := congrArg (roleCoordinates A.reindex) h
    simp only [roleCoordinates_exponent] at hc
    subst w
    omega
  constructor
  · simp [roleMonomial,MvPolynomial.coeff_sub,he]
  · intro u hu
    have hcoef := MvPolynomial.mem_support_iff.mp hu
    by_cases hz : roleExponent A.reindex z=u
    · subst u; simp [roleCoordinates_exponent]
    · have hw : roleExponent A.reindex w=u := by
        by_contra hn
        simp [roleMonomial,MvPolynomial.coeff_sub,hz,hn] at hcoef
      subst u
      exact Or.inl (by simpa only [roleCoordinates_exponent] using hy)

theorem pure_initial_forward (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (k : Type*) [Field k]
    {f : ToricPresentation.Poly k 3} (hf : f∈P.M.base.J k)
    {z : Monomial} (hz : PureRoleLeading A k f z) :
    z∈monomialClosure (pureInitialGenerators A) := by
  classical
  by_cases hy : z.2.1<alpha A
  · have hs : ∀ u∈f.support, (roleCoordinates A.reindex u).2.1<alpha A := by
      intro u hu
      rcases hz.2 u hu with h | ⟨h,_⟩ <;> omega
    have hgood := actual_pureNormal_supported A hk k hf
    rw [pureLinearNormalForm_fixed A k f hs] at hgood
    have hm := MvPolynomial.mem_support_iff.mpr hz.1
    have hmem := hgood hm
    change roleCoordinates A.reindex (roleExponent A.reindex z) ∈
      monomialClosure (pureStripGenerators A) at hmem
    rw [roleCoordinates_exponent] at hmem
    obtain ⟨g,hg,hx,hy,hz⟩ := hmem
    exact ⟨g,Or.inr hg,hx,hy,hz⟩
  · exact ⟨(0,alpha A,0),Or.inl rfl,Nat.zero_le _,by
      change alpha A≤z.2.1; omega,Nat.zero_le _⟩

theorem pure_initial_reverse (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (k : Type*) [Field k]
    {z : Monomial} (hz : z∈monomialClosure (pureInitialGenerators A)) :
    ∃ f∈P.M.base.J k, PureRoleLeading A k f z := by
  obtain ⟨g,hg,hx,hy,hz⟩ := hz
  rcases hg with rfl | hg
  · change alpha A≤z.2.1 at hy
    let t : Monomial := (z.1,z.2.1-alpha A,z.2.2)
    let w : Monomial := t+(beta A,0,0)
    have he : t+(0,alpha A,0)=z := by ext <;> simp [t] <;> omega
    have hF : roleMonomial k A.reindex (0,alpha A,0)-
        roleMonomial k A.reindex (beta A,0,0)∈P.M.base.J k :=
      pureMonic_le_J A k (Ideal.subset_span rfl)
    refine ⟨roleMonomial k A.reindex z-roleMonomial k A.reindex w,?_,?_⟩
    · have hm := (P.M.base.J k).mul_mem_left (roleMonomial k A.reindex t) hF
      rwa [mul_sub,←roleMonomial_add,←roleMonomial_add,he] at hm
    · apply pure_leading_difference A k
      change z.2.1-alpha A+0<z.2.1
      have := pure_alpha_pos A
      omega
  · exact ⟨roleMonomial k A.reindex z,pureStrip_mem_J A hk k ⟨g,hg,hx,hy,hz⟩,
      pure_leading_monomial A k z⟩

/-- Whole actual initial monomial ideal, over every field, with boundary
wraps retained. This is not a claim that y^alpha belongs to actual J. -/
theorem pure_initial_exponents_eq (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (k : Type*) [Field k] :
    {z | ∃ f∈P.M.base.J k, PureRoleLeading A k f z}=
      monomialClosure (pureInitialGenerators A) := by
  ext z
  exact ⟨fun ⟨f,hf,hz⟩ => pure_initial_forward A hk k hf hz,pure_initial_reverse A hk k⟩

/-- The original unrestricted actual P/G binder: killed count comes from
the actual boundary signature, never from an extra caller assumption. -/
theorem internal_all_pure_initial_exact (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp≠bm) (hp : IsPureBoundaryComponent G bp)
    (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,(componentSupport P.M.base G.internalDegree C).card=1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.internalDegree ∧ A.mixedDegree=G.boundaryDegree ∧
      ∀ (k : Type*) [Field k],
        {z | ∃ f∈P.M.base.J k, PureRoleLeading A k f z}=
          monomialClosure (pureInitialGenerators A) := by
  obtain ⟨A,ha,hb,_⟩ := internal_all_pure_geometry P G bp bm hne hp hm hi
  refine ⟨A,ha,hb,fun k _ => pure_initial_exponents_eq A ?_ k⟩
  rw [hb]
  exact G.boundarySignature.2

theorem pure_role_mem_iff_cut (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) : roleMonomial k A.reindex z∈P.M.base.J k ↔
    monomialDegree P.M.base A.reindex z∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
  rw [roleMonomial,ChosenBase.Data.J_eq_comap_tail]
  change ToricPresentation.toricMap k P.M.base.H P.M.base.tailDegrees
      (MvPolynomial.monomial (roleExponent A.reindex z) 1) ∈
      ToricPresentation.tailMonomialIdeal k Gamma.toAddSubmonoid P.M.base.H P.M.base.q.val ↔ _
  rw [ChosenBase.Data.tailMap_monomial,
    ToricPresentation.single_mem_tailMonomialIdeal_iff k _ _ _ P.M.base.H_le,
    ←L2B.weight_eq_degree,roleExponent_weight]
  exact (actual_scaled_cut_iff P.M.base A.reindex _).symm

theorem pure_normal_mem_iff_cut (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (z : Monomial) :
    pureNormal A z∈monomialClosure (pureStripGenerators A) ↔
      monomialDegree P.M.base A.reindex z∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
  rw [←pure_normal_strip_exact A hk ℚ _ (pureNormal_y_lt A z),
    pure_role_mem_iff_cut,pureNormal_degree]

theorem pure_initial_mem_iff (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    z∈monomialClosure (pureInitialGenerators A) ↔
      alpha A≤z.2.1 ∨ z∈monomialClosure (pureStripGenerators A) := by
  constructor
  · rintro ⟨g,hg,hx,hy,hz⟩
    rcases hg with rfl | hg
    · exact Or.inl hy
    · exact Or.inr ⟨g,hg,hx,hy,hz⟩
  · rintro (hy | hz)
    · exact ⟨(0,alpha A,0),Or.inl rfl,Nat.zero_le _,hy,Nat.zero_le _⟩
    · obtain ⟨g,hg,hx,hy,hz⟩ := hz
      exact ⟨g,Or.inr hg,hx,hy,hz⟩

theorem pure_strip_initial_mem_iff (A : SectorBCriticalRoleBranchA P) (z : Monomial)
    (hy : z.2.1<alpha A) : z∈monomialClosure (pureInitialGenerators A) ↔
      z∈monomialClosure (pureStripGenerators A) := by
  rw [pure_initial_mem_iff]
  simp only [Nat.not_le.mpr hy,false_or]

def PureStandard (A : SectorBCriticalRoleBranchA P) (z : Monomial) : Prop :=
  z.2.1<alpha A ∧ z∉monomialClosure (pureStripGenerators A)

theorem pure_standard_iff (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    PureStandard A z ↔ z∉monomialClosure (pureInitialGenerators A) := by
  rw [pure_initial_mem_iff]
  exact ⟨fun h => not_or.mpr ⟨Nat.not_le_of_lt h.1,h.2⟩,
    fun h => ⟨by have := (not_or.mp h).1; omega,(not_or.mp h).2⟩⟩

theorem pure_initial_axes (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) :
    ∃ a b c : ℕ, 0<a ∧ 0<b ∧ 0<c ∧
      (a,0,0)∈monomialClosure (pureInitialGenerators A) ∧
      (0,b,0)∈monomialClosure (pureInitialGenerators A) ∧
      (0,0,c)∈monomialClosure (pureInitialGenerators A) := by
  let m := routingM P.M.base A.reindex
  have ha := pure_alpha_pos A
  have hm := routingM_pos P.M.base A.reindex
  have axis (z : Monomial) (hy : z.2.1<alpha A)
      (hc : monomialDegree P.M.base A.reindex z∈
        cyclicCut (routingH P.M.base A.reindex) m) :
      z∈monomialClosure (pureInitialGenerators A) := by
    apply (pure_strip_initial_mem_iff A z hy).mpr
    simpa only [pureNormal_fixed A z hy] using (pure_normal_mem_iff_cut A hk z).mpr hc
  refine ⟨m,alpha A,m,hm,ha,hm,?_,?_,?_⟩
  · apply axis _ ha
    refine ⟨L5A2C4OR33.grid_mem_H _ _ _,routingA P.M.base A.reindex,
      routingA_pos _ _,0,(routingH _ _).zero_mem,?_⟩
    simp [monomialDegree,normalizedGrid,m,Nat.mul_comm]
  · exact ⟨(0,alpha A,0),Or.inl rfl,le_rfl,le_rfl,le_rfl⟩
  · apply axis _ ha
    refine ⟨L5A2C4OR33.grid_mem_H _ _ _,routingC P.M.base A.reindex,
      routingC_positive _ _,0,(routingH _ _).zero_mem,?_⟩
    simp [monomialDegree,normalizedGrid,m,Nat.mul_comm]

end NS25Lean.L5A2C4OR42
