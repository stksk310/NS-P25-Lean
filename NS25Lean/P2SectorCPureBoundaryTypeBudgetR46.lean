import NS25Lean.P2SectorCPureInternalBorderCompensationR45
set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR46
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR33 L5A2C4OR35
  L5A2C4OR39 L5A2C4OR40 L5A2C4OR42 L5A2C4OR43 L5A2C4OR44
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

theorem boundary_d_pos (A : SectorBCriticalRoleBranchA P) : 0<d A := by
  have h := (branchA_symmetricTailData A).n0_pos
  rw [(branchA_symmetricTailData A).n0_eq] at h
  exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)

/-- Literal (a,b,c) coordinates: the internal relation is z-monic. -/
def boundaryNormal (A : SectorBCriticalRoleBranchA P) (z : Monomial) : Monomial :=
  (z.1+r A*(z.2.2/d A),z.2.1+s A*(z.2.2/d A),z.2.2%d A)

theorem boundaryNormal_z_lt (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    (boundaryNormal A z).2.2<d A := Nat.mod_lt _ (boundary_d_pos A)

theorem boundaryNormal_fixed (A : SectorBCriticalRoleBranchA P) (z : Monomial)
    (hz : z.2.2<d A) : boundaryNormal A z=z := by
  obtain ⟨x,y,z⟩ := z
  simp [boundaryNormal,Nat.div_eq_of_lt hz,Nat.mod_eq_of_lt hz]

theorem boundaryNormal_step (A : SectorBCriticalRoleBranchA P) (x y z : ℕ)
    (hz : d A≤z) : boundaryNormal A (x,y,z)=boundaryNormal A (x+r A,y+s A,z-d A) := by
  have hd : z/d A=(z-d A)/d A+1 := by
    have he : z=(z-d A)+d A := (Nat.sub_add_cancel hz).symm
    conv_lhs => rw [he]
    rw [Nat.add_div_right _ (boundary_d_pos A)]
  have hm : z%d A=(z-d A)%d A := by
    have he : z=(z-d A)+d A := (Nat.sub_add_cancel hz).symm
    conv_lhs => rw [he]
    simp
  ext <;> simp [boundaryNormal,hd,hm] <;> ring

theorem boundaryNormal_degree (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    monomialDegree P.M.base A.reindex (boundaryNormal A z)=
      monomialDegree P.M.base A.reindex z := by
  obtain ⟨x,y,z⟩ := z
  induction z using Nat.strong_induction_on generalizing x y with
  | h z ih =>
    by_cases hz : z<d A
    · rw [boundaryNormal_fixed A _ hz]
    · rw [boundaryNormal_step A x y z (by omega),ih (z-d A)
        (by have := boundary_d_pos A; omega)]
      exact (pure_tail_mixed_step_degree A x y z (by omega)).symm

def boundaryMonicIdeal (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    Ideal (ToricPresentation.Poly k 3) := Ideal.span
      {roleMonomial k A.reindex (0,0,d A)-roleMonomial k A.reindex (r A,s A,0)}

theorem boundaryNormal_congr (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) : roleMonomial k A.reindex z-
      roleMonomial k A.reindex (boundaryNormal A z) ∈ boundaryMonicIdeal A k := by
  obtain ⟨x,y,z⟩ := z
  induction z using Nat.strong_induction_on generalizing x y with
  | h z ih =>
    by_cases hz : z<d A
    · rw [boundaryNormal_fixed A _ hz,sub_self]; exact (boundaryMonicIdeal A k).zero_mem
    have hle : d A≤z := by omega
    have hp := ih (z-d A) (by have := boundary_d_pos A; omega) (x+r A) (y+s A)
    have he : (x,y,z-d A)+(0,0,d A)=(x,y,z) := by ext <;> simp <;> omega
    have he' : (x,y,z-d A)+(r A,s A,0)=(x+r A,y+s A,z-d A) := rfl
    have hg : roleMonomial k A.reindex (0,0,d A)-roleMonomial k A.reindex (r A,s A,0)
        ∈ boundaryMonicIdeal A k := Ideal.subset_span rfl
    have hs := (boundaryMonicIdeal A k).mul_mem_left (roleMonomial k A.reindex (x,y,z-d A)) hg
    rw [mul_sub,←roleMonomial_add,←roleMonomial_add,he,he'] at hs
    rw [boundaryNormal_step A x y z hle]
    convert (boundaryMonicIdeal A k).add_mem hs hp using 1 <;> ring

def boundaryOriginals (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  Set.range (pureSourceNormal A) ∪ {(0,alpha A,0)}

def boundaryWrap (A : SectorBCriticalRoleBranchA P) (g : Monomial) : Monomial :=
  (g.1+r A,g.2.1+s A,0)

def boundaryStripGenerators (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  boundaryOriginals A ∪ {w | ∃ g∈boundaryOriginals A, 0<g.2.2 ∧ w=boundaryWrap A g}

def boundaryInitialGenerators (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  {(0,0,d A)} ∪ boundaryStripGenerators A

theorem boundaryOriginals_z_lt (A : SectorBCriticalRoleBranchA P) {g : Monomial}
    (hg : g∈boundaryOriginals A) : g.2.2<d A := by
  rcases hg with ⟨v,rfl⟩ | rfl
  · exact (pureSourceNormal_spec A v).2.2
  · exact boundary_d_pos A

theorem boundaryNormal_multiple (A : SectorBCriticalRoleBranchA P) {g : Monomial}
    (hg : g∈boundaryOriginals A) (t : Monomial) :
    boundaryNormal A (g+t)∈monomialClosure (boundaryStripGenerators A) := by
  by_cases hz : g.2.2+t.2.2<d A
  · refine ⟨g,Or.inl hg,?_,?_,?_⟩
    all_goals simp [boundaryNormal,Nat.div_eq_of_lt hz,Nat.mod_eq_of_lt hz] <;> omega
  · have hd : 1≤(g.2.2+t.2.2)/d A := by
      apply (Nat.le_div_iff_mul_le (boundary_d_pos A)).mpr
      simpa using (show d A≤g.2.2+t.2.2 by omega)
    by_cases hgz : g.2.2=0
    · refine ⟨g,Or.inl hg,?_,?_,?_⟩
      all_goals simp [boundaryNormal,hgz] <;> omega
    · refine ⟨boundaryWrap A g,Or.inr ⟨g,hg,by omega,rfl⟩,?_,?_,Nat.zero_le _⟩
      · change g.1+r A≤g.1+t.1+r A*((g.2.2+t.2.2)/d A)
        have := Nat.mul_le_mul_left (r A) hd
        simp only [mul_one] at this
        omega
      · change g.2.1+s A≤g.2.1+t.2.1+s A*((g.2.2+t.2.2)/d A)
        have := Nat.mul_le_mul_left (s A) hd
        simp only [mul_one] at this
        omega

def boundaryLinearNormalForm (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    ToricPresentation.Poly k 3 →ₗ[k] ToricPresentation.Poly k 3 :=
  AddMonoidAlgebra.mapDomainLinearMap k k
    (fun u => roleExponent A.reindex (boundaryNormal A (roleCoordinates A.reindex u)))

@[simp] theorem boundaryLinearNormalForm_monomial (A : SectorBCriticalRoleBranchA P)
    (k : Type*) [Field k] (u : Fin 3 →₀ ℕ) (c : k) :
    boundaryLinearNormalForm A k (MvPolynomial.monomial u c)=
      MvPolynomial.monomial (roleExponent A.reindex
        (boundaryNormal A (roleCoordinates A.reindex u))) c :=
  AddMonoidAlgebra.mapDomainLinearMap_single _ _ _

@[simp] theorem boundaryLinearNormalForm_role (A : SectorBCriticalRoleBranchA P)
    (k : Type*) [Field k] (z : Monomial) :
    boundaryLinearNormalForm A k (roleMonomial k A.reindex z)=
      roleMonomial k A.reindex (boundaryNormal A z) := by simp [roleMonomial]

def boundaryStripSupported (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    Submodule k (ToricPresentation.Poly k 3) :=
  AddMonoidAlgebra.supported k k
    {u | roleCoordinates A.reindex u∈monomialClosure (boundaryStripGenerators A)}

theorem boundarySupported_role_iff (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) : roleMonomial k A.reindex z∈boundaryStripSupported A k ↔
      z∈monomialClosure (boundaryStripGenerators A) := by
  classical
  change Finsupp.single (roleExponent A.reindex z) (1:k) ∈ Finsupp.supported k k
    {u | roleCoordinates A.reindex u∈monomialClosure (boundaryStripGenerators A)} ↔ _
  simp [Finsupp.mem_supported,roleCoordinates_exponent]

def boundaryNormalTestIdeal (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (W : Submodule k (ToricPresentation.Poly k 3)) : Ideal (ToricPresentation.Poly k 3) where
  carrier := {f | ∀ t : Monomial, boundaryLinearNormalForm A k (roleMonomial k A.reindex t*f)∈W}
  zero_mem' := by intro t; simp
  add_mem' := by
    intro f g hf hg t
    rw [mul_add,map_add]
    exact W.add_mem (hf t) (hg t)
  smul_mem' := by
    intro a f hf
    change ∀ t, boundaryLinearNormalForm A k (roleMonomial k A.reindex t*(a*f))∈W
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

theorem boundaryMonic_le_test (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (W : Submodule k (ToricPresentation.Poly k 3)) :
    boundaryMonicIdeal A k≤boundaryNormalTestIdeal A k W := by
  apply Ideal.span_le.mpr
  rintro f rfl t
  rw [mul_sub,←roleMonomial_add,←roleMonomial_add,map_sub,
    boundaryLinearNormalForm_role,boundaryLinearNormalForm_role]
  have hn : boundaryNormal A (t+(0,0,d A))=boundaryNormal A (t+(r A,s A,0)) := by
    obtain ⟨x,y,z⟩ := t
    change boundaryNormal A (x,y,z+d A)=boundaryNormal A (x+r A,y+s A,z)
    simpa only [Nat.add_sub_cancel] using boundaryNormal_step A x y (z+d A) (by omega)
  rw [hn,sub_self]
  exact W.zero_mem

theorem boundaryLinearNormalForm_congr (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (f : ToricPresentation.Poly k 3) : f-boundaryLinearNormalForm A k f∈boundaryMonicIdeal A k := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [scalar_role_monomial k A.reindex u c,map_smul,boundaryLinearNormalForm_role,←smul_sub]
    exact ((boundaryMonicIdeal A k).restrictScalars k).smul_mem c (boundaryNormal_congr A k _)
  | add f g hf hg =>
    rw [map_add]
    convert (boundaryMonicIdeal A k).add_mem hf hg using 1 <;> ring

theorem boundaryLinearNormalForm_fixed (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (f : ToricPresentation.Poly k 3)
    (hf : ∀ u∈f.support, (roleCoordinates A.reindex u).2.2<d A) :
    boundaryLinearNormalForm A k f=f := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum]
  conv_rhs => rw [MvPolynomial.as_sum f]
  apply Finset.sum_congr rfl
  intro u hu
  rw [boundaryLinearNormalForm_monomial,boundaryNormal_fixed A _ (hf u hu)]
  have he : roleExponent A.reindex (roleCoordinates A.reindex u)=u :=
    roleExponent_coordinates A.reindex u
  rw [he]

theorem boundary_candidate_le_test (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    pureBoundarySourceIdeal A k≤boundaryNormalTestIdeal A k (boundaryStripSupported A k) := by
  let T := boundaryNormalTestIdeal A k (boundaryStripSupported A k)
  have hmono : boundaryMonicIdeal A k≤T := boundaryMonic_le_test A k _
  have ho (g : Monomial) (hg : g∈boundaryOriginals A) : roleMonomial k A.reindex g∈T := by
    intro t
    rw [←roleMonomial_add,boundaryLinearNormalForm_role,boundarySupported_role_iff,add_comm t]
    exact boundaryNormal_multiple A hg t
  apply Ideal.span_le.mpr
  intro f hf
  rcases hf with (hf | ⟨v,rfl⟩) | hf
  · rcases hf with rfl
    exact hmono (Ideal.subset_span rfl)
  · exact ho _ (Or.inl ⟨v,rfl⟩)
  · rcases hf with rfl
    exact ho _ (Or.inr rfl)

theorem actual_boundaryNormal_supported (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k]
    {f : ToricPresentation.Poly k 3} (hf : f∈P.M.base.J k) :
    boundaryLinearNormalForm A k f∈boundaryStripSupported A k := by
  rw [boundary_source_quotient_exact A hk k] at hf
  have ht := boundary_candidate_le_test A k hf (0,0,0)
  simpa [roleMonomial,roleExponent] using ht

theorem boundary_strip_forward (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k]
    (z : Monomial) (hz : z.2.2<d A) (hJ : roleMonomial k A.reindex z∈P.M.base.J k) :
    z∈monomialClosure (boundaryStripGenerators A) := by
  have ht := actual_boundaryNormal_supported A hk k hJ
  rw [boundaryLinearNormalForm_role,boundaryNormal_fixed A z hz,boundarySupported_role_iff] at ht
  exact ht

theorem boundaryMonic_le_J (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    boundaryMonicIdeal A k≤P.M.base.J k := by
  have hIH : P.M.base.IH k≤P.M.base.J k := by rw [Data.J_eq_IH_sup_MK]; exact le_sup_left
  apply Ideal.span_le.mpr
  rintro f rfl
  apply hIH
  rw [pure_tail_toric_exact A k]
  exact Ideal.subset_span (Or.inr rfl)

theorem boundaryOriginals_mem_J (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k]
    {g : Monomial} (hg : g∈boundaryOriginals A) : roleMonomial k A.reindex g∈P.M.base.J k := by
  rw [boundary_source_quotient_exact A hk k]
  rcases hg with ⟨v,rfl⟩ | rfl
  · exact Ideal.subset_span (Or.inl (Or.inr ⟨v,rfl⟩))
  · exact Ideal.subset_span (Or.inr rfl)

theorem boundaryWrap_mem_J (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k]
    {g : Monomial} (hg : g∈boundaryOriginals A) (hz : 0<g.2.2) :
    roleMonomial k A.reindex (boundaryWrap A g)∈P.M.base.J k := by
  have hgz := boundaryOriginals_z_lt A hg
  let t : Monomial := (0,0,d A-g.2.2)
  have he : boundaryNormal A (g+t)=boundaryWrap A g := by
    have he' : g.2.2+(d A-g.2.2)=d A := Nat.add_sub_of_le (by omega)
    ext <;> simp [boundaryNormal,boundaryWrap,t,he',Nat.div_self (boundary_d_pos A)]
  have hm : roleMonomial k A.reindex (g+t)∈P.M.base.J k := by
    rw [roleMonomial_add]
    exact (P.M.base.J k).mul_mem_right _ (boundaryOriginals_mem_J A hk k hg)
  have hd := boundaryMonic_le_J A k (boundaryNormal_congr A k (g+t))
  rw [he] at hd
  simpa only [sub_sub_cancel] using (P.M.base.J k).sub_mem hm hd

theorem boundaryStrip_mem_J (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k]
    {z : Monomial} (hz : z∈monomialClosure (boundaryStripGenerators A)) :
    roleMonomial k A.reindex z∈P.M.base.J k := by
  obtain ⟨g,hg,hx,hy,hz⟩ := hz
  have hm : roleMonomial k A.reindex g∈P.M.base.J k := by
    rcases hg with hg | ⟨w,hw,hp,rfl⟩
    · exact boundaryOriginals_mem_J A hk k hg
    · exact boundaryWrap_mem_J A hk k hw hp
  have he : z=g+(z.1-g.1,z.2.1-g.2.1,z.2.2-g.2.2) := by ext <;> simp <;> omega
  rw [he,roleMonomial_add]
  exact (P.M.base.J k).mul_mem_right _ hm

theorem boundary_normal_strip_exact (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k]
    (z : Monomial) (hz : z.2.2<d A) : roleMonomial k A.reindex z∈P.M.base.J k ↔
      z∈monomialClosure (boundaryStripGenerators A) :=
  ⟨boundary_strip_forward A hk k z hz,boundaryStrip_mem_J A hk k⟩

theorem boundary_normal_mem_iff_cut (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (z : Monomial) :
    boundaryNormal A z∈monomialClosure (boundaryStripGenerators A) ↔
      monomialDegree P.M.base A.reindex z∈cyclicCut (routingH P.M.base A.reindex)
        (routingM P.M.base A.reindex) := by
  rw [←boundary_normal_strip_exact A hk ℚ _ (boundaryNormal_z_lt A z),
    pure_role_mem_iff_cut,boundaryNormal_degree]

def BoundaryRoleLeading (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (f : ToricPresentation.Poly k 3) (z : Monomial) : Prop :=
  MvPolynomial.coeff (roleExponent A.reindex z) f≠0 ∧
    ∀ u∈f.support, let w := roleCoordinates A.reindex u
      w.2.2<z.2.2 ∨ (w.2.2=z.2.2 ∧ (w.1<z.1 ∨ (w.1=z.1 ∧ w.2.1≤z.2.1)))

theorem boundary_leading_monomial (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) : BoundaryRoleLeading A k (roleMonomial k A.reindex z) z := by
  classical
  constructor
  · simp [roleMonomial]
  · intro u hu
    have he : roleExponent A.reindex z=u := by simpa [roleMonomial] using hu
    subst u
    simp [roleCoordinates_exponent]

theorem boundary_leading_difference (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z w : Monomial) (hz : w.2.2<z.2.2) :
    BoundaryRoleLeading A k (roleMonomial k A.reindex z-roleMonomial k A.reindex w) z := by
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
    by_cases hzu : roleExponent A.reindex z=u
    · subst u; simp [roleCoordinates_exponent]
    · have hw : roleExponent A.reindex w=u := by
        by_contra hn
        simp [roleMonomial,MvPolynomial.coeff_sub,hzu,hn] at hcoef
      subst u
      exact Or.inl (by simpa only [roleCoordinates_exponent] using hz)

theorem boundary_initial_forward (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k]
    {f : ToricPresentation.Poly k 3} (hf : f∈P.M.base.J k)
    {z : Monomial} (hz : BoundaryRoleLeading A k f z) :
    z∈monomialClosure (boundaryInitialGenerators A) := by
  classical
  by_cases hzd : z.2.2<d A
  · have hs : ∀ u∈f.support, (roleCoordinates A.reindex u).2.2<d A := by
      intro u hu
      rcases hz.2 u hu with h | ⟨h,_⟩ <;> omega
    have ht := actual_boundaryNormal_supported A hk k hf
    rw [boundaryLinearNormalForm_fixed A k f hs] at ht
    have hmem := ht (MvPolynomial.mem_support_iff.mpr hz.1)
    change roleCoordinates A.reindex (roleExponent A.reindex z)∈
      monomialClosure (boundaryStripGenerators A) at hmem
    rw [roleCoordinates_exponent] at hmem
    obtain ⟨g,hg,hx,hy,hz⟩ := hmem
    exact ⟨g,Or.inr hg,hx,hy,hz⟩
  · exact ⟨(0,0,d A),Or.inl rfl,Nat.zero_le _,Nat.zero_le _,by
      change d A≤z.2.2; omega⟩

theorem boundary_initial_reverse (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k]
    {z : Monomial} (hz : z∈monomialClosure (boundaryInitialGenerators A)) :
    ∃ f∈P.M.base.J k, BoundaryRoleLeading A k f z := by
  obtain ⟨g,hg,hx,hy,hz⟩ := hz
  rcases hg with rfl | hg
  · change d A≤z.2.2 at hz
    let t : Monomial := (z.1,z.2.1,z.2.2-d A)
    let w : Monomial := t+(r A,s A,0)
    have he : t+(0,0,d A)=z := by ext <;> simp [t] <;> omega
    have hF : roleMonomial k A.reindex (0,0,d A)-roleMonomial k A.reindex (r A,s A,0)
        ∈P.M.base.J k := boundaryMonic_le_J A k (Ideal.subset_span rfl)
    refine ⟨roleMonomial k A.reindex z-roleMonomial k A.reindex w,?_,?_⟩
    · have hm := (P.M.base.J k).mul_mem_left (roleMonomial k A.reindex t) hF
      rwa [mul_sub,←roleMonomial_add,←roleMonomial_add,he] at hm
    · apply boundary_leading_difference A k
      change z.2.2-d A+0<z.2.2
      have := boundary_d_pos A
      omega
  · exact ⟨roleMonomial k A.reindex z,boundaryStrip_mem_J A hk k ⟨g,hg,hx,hy,hz⟩,
      boundary_leading_monomial A k z⟩

theorem boundary_initial_exponents_eq (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k] :
    {z | ∃ f∈P.M.base.J k, BoundaryRoleLeading A k f z}=
      monomialClosure (boundaryInitialGenerators A) := by
  ext z
  exact ⟨fun ⟨f,hf,hz⟩ => boundary_initial_forward A hk k hf hz,boundary_initial_reverse A hk k⟩

theorem boundary_all_pure_initial_exact (P : P2Data Gamma) (G : SectorCActualFibers P)
    (h : ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.boundaryDegree ∧ A.mixedDegree=G.internalDegree ∧
      BoundaryKilled P.M A.pairDegree A.pair.leftComponent ∧
      ∀ (k : Type*) [Field k], {z | ∃ f∈P.M.base.J k, BoundaryRoleLeading A k f z}=
        monomialClosure (boundaryInitialGenerators A) := by
  obtain ⟨A,hp,hm,hk,_,_⟩ := boundary_all_pure_geometry P G h
  exact ⟨A,hp,hm,hk,fun k _ => boundary_initial_exponents_eq A hk k⟩

theorem boundary_initial_mem_iff (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    z∈monomialClosure (boundaryInitialGenerators A) ↔
      d A≤z.2.2 ∨ z∈monomialClosure (boundaryStripGenerators A) := by
  constructor
  · rintro ⟨g,hg,hx,hy,hz⟩
    rcases hg with rfl | hg
    · exact Or.inl hz
    · exact Or.inr ⟨g,hg,hx,hy,hz⟩
  · rintro (hz | hg)
    · exact ⟨(0,0,d A),Or.inl rfl,Nat.zero_le _,Nat.zero_le _,hz⟩
    · obtain ⟨g,hg,hx,hy,hz⟩ := hg
      exact ⟨g,Or.inr hg,hx,hy,hz⟩

theorem boundary_strip_initial_mem_iff (A : SectorBCriticalRoleBranchA P) (z : Monomial)
    (hz : z.2.2<d A) : z∈monomialClosure (boundaryInitialGenerators A) ↔
      z∈monomialClosure (boundaryStripGenerators A) := by
  rw [boundary_initial_mem_iff]
  simp only [Nat.not_le.mpr hz,false_or]

def BoundaryStandard (A : SectorBCriticalRoleBranchA P) (z : Monomial) : Prop :=
  z.2.2<d A ∧ z∉monomialClosure (boundaryStripGenerators A)

theorem boundary_standard_iff (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    BoundaryStandard A z ↔ z∉monomialClosure (boundaryInitialGenerators A) := by
  rw [boundary_initial_mem_iff]
  exact ⟨fun h => not_or.mpr ⟨Nat.not_le_of_lt h.1,h.2⟩,
    fun h => ⟨by have := (not_or.mp h).1; omega,(not_or.mp h).2⟩⟩

theorem boundary_standard_y_lt (A : SectorBCriticalRoleBranchA P) {z : Monomial}
    (hz : BoundaryStandard A z) : z.2.1<alpha A := by
  by_contra hn
  exact hz.2 ⟨(0,alpha A,0),Or.inl (Or.inr rfl),Nat.zero_le _,by
    change alpha A≤z.2.1; omega,Nat.zero_le _⟩

theorem boundary_standard_degree_injective (A : SectorBCriticalRoleBranchA P)
    {z w : Monomial} (hz : BoundaryStandard A z) (hw : BoundaryStandard A w)
    (he : monomialDegree P.M.base A.reindex z=monomialDegree P.M.base A.reindex w) : z=w :=
  pure_tail_normal_unique A ⟨boundary_standard_y_lt A hz,hz.1⟩
    ⟨boundary_standard_y_lt A hw,hw.1⟩ he

theorem boundary_standard_degree_surjective (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) {x : ℕ}
    (hx : x∈routingH P.M.base A.reindex)
    (hn : x∉cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    ∃ z, BoundaryStandard A z ∧ monomialDegree P.M.base A.reindex z=x := by
  obtain ⟨r,i,j,he⟩ := L5A2C4OR6.routingH_factorization P.M.base A.reindex hx
  refine ⟨boundaryNormal A (r,i,j),⟨boundaryNormal_z_lt A _,?_⟩,?_⟩
  · intro hm
    apply hn
    simpa only [monomialDegree,normalizedGrid,←he] using
      (boundary_normal_mem_iff_cut A hk (r,i,j)).mp hm
  · rw [boundaryNormal_degree]
    exact he.symm

def boundaryBorderExceptional (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  {z | MonomialSocle (boundaryInitialGenerators A) z ∧ z.2.2+1=d A ∧
    boundaryWrap A z∉monomialClosure (boundaryStripGenerators A)}

def BoundaryTrueSocle (A : SectorBCriticalRoleBranchA P) (z : Monomial) : Prop :=
  BoundaryStandard A z ∧
    boundaryNormal A (z.1+1,z.2.1,z.2.2)∈monomialClosure (boundaryStripGenerators A) ∧
    boundaryNormal A (z.1,z.2.1+1,z.2.2)∈monomialClosure (boundaryStripGenerators A) ∧
    boundaryNormal A (z.1,z.2.1,z.2.2+1)∈monomialClosure (boundaryStripGenerators A)

theorem boundary_top_z_normal (A : SectorBCriticalRoleBranchA P) (z : Monomial)
    (hz : z.2.2+1=d A) :
    boundaryNormal A (z.1,z.2.1,z.2.2+1)=boundaryWrap A z := by
  simp [boundaryNormal,boundaryWrap,hz,Nat.div_self (boundary_d_pos A)]

theorem boundary_trueSocle_iff_complement (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    BoundaryTrueSocle A z ↔ MonomialSocle (boundaryInitialGenerators A) z ∧
      z∉boundaryBorderExceptional A := by
  constructor
  · rintro ⟨hs,hx,hy,hz⟩
    rw [boundaryNormal_fixed A (z.1+1,z.2.1,z.2.2) hs.1] at hx
    rw [boundaryNormal_fixed A (z.1,z.2.1+1,z.2.2) hs.1] at hy
    have hx' := (boundary_strip_initial_mem_iff A (z.1+1,z.2.1,z.2.2) hs.1).mpr hx
    have hy' := (boundary_strip_initial_mem_iff A (z.1,z.2.1+1,z.2.2) hs.1).mpr hy
    have hz' : (z.1,z.2.1,z.2.2+1)∈monomialClosure (boundaryInitialGenerators A) := by
      by_cases ht : z.2.2+1<d A
      · rw [boundaryNormal_fixed A _ ht] at hz
        exact (boundary_strip_initial_mem_iff A _ ht).mpr hz
      · exact (boundary_initial_mem_iff A _).mpr (Or.inl (by
          change d A≤z.2.2+1; omega))
    refine ⟨⟨(boundary_standard_iff A z).mp hs,hx',hy',hz'⟩,?_⟩
    rintro ⟨_,ht,hn⟩
    rw [boundary_top_z_normal A z ht] at hz
    exact hn hz
  · rintro ⟨⟨hn,hx,hy,hz⟩,he⟩
    have hs := (boundary_standard_iff A z).mpr hn
    refine ⟨hs,?_,?_,?_⟩
    · rw [boundaryNormal_fixed A (z.1+1,z.2.1,z.2.2) hs.1]
      exact (boundary_strip_initial_mem_iff A (z.1+1,z.2.1,z.2.2) hs.1).mp hx
    · rw [boundaryNormal_fixed A (z.1,z.2.1+1,z.2.2) hs.1]
      exact (boundary_strip_initial_mem_iff A (z.1,z.2.1+1,z.2.2) hs.1).mp hy
    · by_cases ht : z.2.2+1<d A
      · rw [boundaryNormal_fixed A _ ht]
        exact (boundary_strip_initial_mem_iff A _ ht).mp hz
      · have htop : z.2.2+1=d A := by have := hs.1; omega
        rw [boundary_top_z_normal A z htop]
        by_contra hw
        exact he ⟨⟨hn,hx,hy,hz⟩,htop,hw⟩

theorem boundary_trueSocle_iff_modelTop (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (z : Monomial)
    (hs : BoundaryStandard A z) : BoundaryTrueSocle A z ↔
      ModelTop P.M.base A.reindex (monomialDegree P.M.base A.reindex z) := by
  have hn : monomialDegree P.M.base A.reindex z∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    intro hc
    have ht := (boundary_normal_mem_iff_cut A hk z).mpr hc
    rw [boundaryNormal_fixed A z hs.1] at ht
    exact hs.2 ht
  rw [BoundaryTrueSocle,pure_modelTop_iff_steps,boundary_normal_mem_iff_cut A hk,
    boundary_normal_mem_iff_cut A hk,boundary_normal_mem_iff_cut A hk]
  have hx : monomialDegree P.M.base A.reindex (z.1+1,z.2.1,z.2.2)=
      monomialDegree P.M.base A.reindex z+routingA P.M.base A.reindex := by
    simp [monomialDegree,normalizedGrid]; ring
  have hy : monomialDegree P.M.base A.reindex (z.1,z.2.1+1,z.2.2)=
      monomialDegree P.M.base A.reindex z+routingB P.M.base A.reindex := by
    simp [monomialDegree,normalizedGrid]; ring
  have hz : monomialDegree P.M.base A.reindex (z.1,z.2.1,z.2.2+1)=
      monomialDegree P.M.base A.reindex z+routingC P.M.base A.reindex := by
    simp [monomialDegree,normalizedGrid]; ring
  rw [hx,hy,hz]
  simp only [hs,hn,grid_mem_H,true_and,not_false_eq_true]

def boundaryTrueSocleEquivTops (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    {z // BoundaryTrueSocle A z} ≃ ModelTops P.M.base A.reindex := by
  let f : {z // BoundaryTrueSocle A z} → ModelTops P.M.base A.reindex := fun z =>
    ⟨monomialDegree P.M.base A.reindex z.val,
      (boundary_trueSocle_iff_modelTop A hk z.val z.property.1).mp z.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro z w he
    apply Subtype.ext
    exact boundary_standard_degree_injective A z.property.1 w.property.1 (congrArg Subtype.val he)
  · intro x
    obtain ⟨z,hs,he⟩ := boundary_standard_degree_surjective A hk x.property.1 x.property.2.1
    refine ⟨⟨z,(boundary_trueSocle_iff_modelTop A hk z hs).mpr (he.symm ▸ x.property)⟩,?_⟩
    exact Subtype.ext he

theorem boundary_initial_axes (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    ∃ a b c : ℕ, 0<a ∧ 0<b ∧ 0<c ∧
      (a,0,0)∈monomialClosure (boundaryInitialGenerators A) ∧
      (0,b,0)∈monomialClosure (boundaryInitialGenerators A) ∧
      (0,0,c)∈monomialClosure (boundaryInitialGenerators A) := by
  let m := routingM P.M.base A.reindex
  have hd := boundary_d_pos A
  have hm := routingM_pos P.M.base A.reindex
  refine ⟨m,alpha A,d A,hm,pure_alpha_pos A,hd,?_,?_,?_⟩
  · apply (boundary_strip_initial_mem_iff A (m,0,0) hd).mpr
    have hc : monomialDegree P.M.base A.reindex (m,0,0)∈
        cyclicCut (routingH P.M.base A.reindex) m := by
      refine ⟨grid_mem_H _ _ _,routingA P.M.base A.reindex,
        routingA_pos _ _,0,(routingH _ _).zero_mem,?_⟩
      simp [monomialDegree,normalizedGrid,m,Nat.mul_comm]
    simpa only [boundaryNormal_fixed A (m,0,0) hd] using
      (boundary_normal_mem_iff_cut A hk (m,0,0)).mpr hc
  · exact ⟨(0,alpha A,0),Or.inr (Or.inl (Or.inr rfl)),le_rfl,le_rfl,le_rfl⟩
  · exact ⟨(0,0,d A),Or.inl rfl,le_rfl,le_rfl,le_rfl⟩

/-- Exact correction uses top z, not the frozen internal branch's top y. -/
theorem boundary_one_binomial_type_correction (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    Gamma.asRelativeIdeal.idealType+Nat.card {z // z∈boundaryBorderExceptional A}=
      Nat.card {z // MonomialSocle (boundaryInitialGenerators A) z} := by
  have hsub : boundaryBorderExceptional A⊆{z | MonomialSocle (boundaryInitialGenerators A) z} :=
    fun _ h => h.1
  obtain ⟨a,b,c,_,_,_,ha,hb,hc⟩ := boundary_initial_axes A hk
  have hf := monomialSocle_finite (boundaryInitialGenerators A) a b c ha hb hc
  have he : {z // BoundaryTrueSocle A z} ≃
      {z // z∈{z | MonomialSocle (boundaryInitialGenerators A) z}\boundaryBorderExceptional A} :=
    L5A2C4OR34.predicateSubtypeEquiv (boundary_trueSocle_iff_complement A)
  have hcount := Nat.card_congr (boundaryTrueSocleEquivTops A hk)
  rw [pure_model_top_count P A.reindex] at hcount
  rw [←hcount,Nat.card_congr he]
  exact Set.ncard_sdiff_add_ncard_of_subset hsub hf

theorem boundary_internal_predecessors_not_cut (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree) :
    (d A*routingC P.M.base A.reindex-routingA P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) ∧
    (d A*routingC P.M.base A.reindex-routingB P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) ∧
    (d A*routingC P.M.base A.reindex-routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) := by
  have halive := none_killed_of_count_zero P.M A.mixedDegree
    (by rw [hm]; exact G.internalSignature.2)
  refine ⟨?_,?_,?_⟩
  · intro hc
    exact halive A.mixed.mixedComponent
      ((normalized_component_killed_iff _ P.M rfl _
        (L5A2C4OR41.mixed_boundary_degree_scale A) _).mpr
        ⟨0,(mixed_support_first_two A).1,by simpa [roleWeight] using hc⟩)
  · intro hc
    exact halive A.mixed.mixedComponent
      ((normalized_component_killed_iff _ P.M rfl _
        (L5A2C4OR41.mixed_boundary_degree_scale A) _).mpr
        ⟨1,(mixed_support_first_two A).2,by simpa [roleWeight] using hc⟩)
  · intro hc
    apply halive A.mixed.pureComponent
    apply (normalized_component_killed_iff _ P.M rfl _
      (L5A2C4OR41.mixed_boundary_degree_scale A) _).mpr
    refine ⟨2,?_,by simpa [roleWeight] using hc⟩
    rw [A.mixed.pureSupport,←A.reindex_two]; simp

theorem boundary_pure_x_source (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    ∃ v : ModelSources P.M.base A.reindex, ∃ p : ℕ,
      0<p ∧ p<beta A ∧ pureSourceNormal A v=(p,0,0) := by
  obtain ⟨i,hi,hcut⟩ := (normalized_component_killed_iff _ P.M rfl _
    (pair_degree_scale A) A.pair.leftComponent).mp hk
  rw [A.pair.leftSupport,←A.reindex_zero,Finset.mem_singleton] at hi
  have hi0 : i=0 := A.reindex.injective hi
  subst i
  have hc : (beta A-1)*routingA P.M.base A.reindex∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    simpa [roleWeight,Nat.sub_mul] using hcut
  obtain ⟨v,t,ht,he⟩ := cut_source_cover _ _ _ hc
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  let g := pureSourceNormal A v
  let w : Monomial := (x,y,z)
  have hg : monomialDegree P.M.base A.reindex g=v.val := (pureSourceNormal_spec A v).1
  have hd : monomialDegree P.M.base A.reindex (g+w)=
      (beta A-1)*routingA P.M.base A.reindex := by
    rw [monomialDegree_add,hg,show monomialDegree P.M.base A.reindex w=t from hfac.symm,←he]
  have hb := pure_beta_pos A
  have hs := (branchA_symmetricTailData A).c0_eq_beta
  change criticalExponent P.M.base (A.reindex 0)=beta A at hs
  have hu : weight P.M.base (roleExponent A.reindex (g+w))=
      (beta A-1)*weights P.M.base (A.reindex 0) := by
    have ha : routingD P.M.base A.reindex*routingA P.M.base A.reindex=
        weights P.M.base (A.reindex 0) := by simpa [roleWeight] using roleWeight_scale P.M.base A.reindex 0
    rw [roleExponent_weight,hd,←ha]; ring
  have hp := factorization_below_critical_is_pure _ _
    (by rw [hs]; omega : beta A-1<criticalExponent P.M.base (A.reindex 0)) _ hu
  have hx := congrArg (fun u : Fin 3 →₀ ℕ => u (A.reindex 0)) hp
  have hy := congrArg (fun u : Fin 3 →₀ ℕ => u (A.reindex 1)) hp
  have hz := congrArg (fun u : Fin 3 →₀ ℕ => u (A.reindex 2)) hp
  simp [roleExponent] at hx hy hz
  have gy : g.2.1=0 := hy.1
  have gz : g.2.2=0 := hz.1
  have gp : 0<g.1 := by
    have hv := source_val_pos _ _ v
    simp only [monomialDegree,normalizedGrid,gy,gz,zero_mul,add_zero] at hg
    by_contra hn
    have h0 : g.1=0 := by omega
    simp [h0] at hg
    omega
  exact ⟨v,g.1,gp,by simp [w] at hx; omega,Prod.ext rfl (Prod.ext gy gz)⟩

/-- Coefficient bounds derived from the same actual internal alive fiber. -/
theorem boundary_actual_coefficient_bounds (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    ∃ v : ModelSources P.M.base A.reindex, ∃ p : ℕ,
      pureSourceNormal A v=(p,0,0) ∧ 0<r A ∧ r A<p ∧ p<beta A ∧ 0<s A ∧ s A<alpha A := by
  obtain ⟨v,p,hp,hpb,hg⟩ := boundary_pure_x_source A hk
  have hn := boundary_internal_predecessors_not_cut G A hm
  have hr := (branchA_symmetricTailData A).r_pos
  have hs := (branchA_symmetricTailData A).s_pos
  have hrel := (branchA_symmetricTailData A).mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hrel
  have hpc : p*routingA P.M.base A.reindex∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    have hh := v.property.1
    rw [←(pureSourceNormal_spec A v).1,hg] at hh
    simpa [monomialDegree,normalizedGrid] using hh
  have hrp : r A<p := by
    by_contra hbad
    have hle : p≤r A := by omega
    have hc := cut_add_tail hpc (grid_mem_H P.M.base A.reindex (r A-p,s A-1,0))
    apply hn.2.1
    have hx := congrArg (fun t => t*routingA P.M.base A.reindex) (Nat.sub_add_cancel hle)
    have hy := congrArg (fun t => t*routingB P.M.base A.reindex)
      (Nat.sub_add_cancel (by omega : 1≤s A))
    simp only [Nat.add_mul,one_mul] at hx hy
    convert hc using 1
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
    omega
  have hsa : s A<alpha A := by
    by_contra hbad
    have hle : alpha A≤s A := by omega
    have hpure := (branchA_symmetricTailData A).pure_relation
    rw [←routingA_eq_n0,←routingB_eq_n1] at hpure
    have hc := cut_add_tail hpc (grid_mem_H P.M.base A.reindex
      (r A+beta A-1-p,s A-alpha A,0))
    apply hn.1
    have hx := congrArg (fun t => t*routingA P.M.base A.reindex)
      (Nat.sub_add_cancel (show p≤r A+beta A-1 by omega))
    have hy := congrArg (fun t => t*routingB P.M.base A.reindex) (Nat.sub_add_cancel hle)
    have hz := congrArg (fun t => t*routingA P.M.base A.reindex)
      (Nat.sub_add_cancel (show 1≤r A+beta A by omega))
    simp only [Nat.add_mul,one_mul] at hx hy hz
    convert hc using 1
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
    omega
  exact ⟨v,p,hg,hr,hrp,hpb,hs,hsa⟩

theorem boundary_alive_y_predecessor_not_cut (A : SectorBCriticalRoleBranchA P)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    (alpha A-1)*routingB P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
  intro hc
  apply hl
  have hrel := (branchA_symmetricTailData A).pure_relation
  rw [←routingA_eq_n0,←routingB_eq_n1] at hrel
  have hscale : routingD P.M.base A.reindex*(alpha A*routingB P.M.base A.reindex)=A.pairDegree := by
    rw [←hrel]; exact pair_degree_scale A
  apply (normalized_component_killed_iff _ P.M rfl _ hscale _).mpr
  refine ⟨1,?_,?_⟩
  · rw [A.pair.rightSupport,←A.reindex_one]; simp
  · simpa [roleWeight,Nat.sub_mul] using hc

theorem boundary_axis_cut_bounds (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    (∀ y : ℕ, y*routingB P.M.base A.reindex∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) → alpha A≤y) ∧
    (∀ z : ℕ, z*routingC P.M.base A.reindex∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) → d A≤z) := by
  have hy := boundary_alive_y_predecessor_not_cut A hl
  have hz : (d A-1)*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    simpa [Nat.sub_mul] using (boundary_internal_predecessors_not_cut G A hm).2.2
  constructor
  · intro y hc
    by_contra hn
    have hle : y≤alpha A-1 := by have := pure_alpha_pos A; omega
    have ht := cut_add_tail hc (grid_mem_H P.M.base A.reindex (0,alpha A-1-y,0))
    apply hy
    have he := congrArg (fun n => n*routingB P.M.base A.reindex) (Nat.sub_add_cancel hle)
    simp only [Nat.add_mul] at he
    convert ht using 1
    simp only [monomialDegree,normalizedGrid,zero_mul,zero_add,add_zero]
    omega
  · intro z hc
    by_contra hn
    have hle : z≤d A-1 := by have := boundary_d_pos A; omega
    have ht := cut_add_tail hc (grid_mem_H P.M.base A.reindex (0,0,d A-1-z))
    apply hz
    have he := congrArg (fun n => n*routingC P.M.base A.reindex) (Nat.sub_add_cancel hle)
    simp only [Nat.add_mul] at he
    convert ht using 1
    simp only [monomialDegree,normalizedGrid,zero_mul,zero_add,add_zero]
    omega

def boundaryRaw (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  {(0,0,d A)} ∪ boundaryOriginals A

def BoundarySurvivingWraps (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  {w | PolynomialMinimal (boundaryInitialGenerators A) w ∧ w∉boundaryRaw A}

def boundarySurvivingWrapCount (A : SectorBCriticalRoleBranchA P) : ℕ :=
  Nat.card (BoundarySurvivingWraps A)

theorem boundaryStrip_z_lt (A : SectorBCriticalRoleBranchA P) {g : Monomial}
    (hg : g∈boundaryStripGenerators A) : g.2.2<d A := by
  rcases hg with hg | ⟨w,hw,hz,rfl⟩
  · exact boundaryOriginals_z_lt A hg
  · exact boundary_d_pos A

theorem boundaryStrip_cut (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) {w : Monomial}
    (hw : w∈boundaryStripGenerators A) : monomialDegree P.M.base A.reindex w∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
  apply (pure_role_mem_iff_cut A ℚ w).mp
  exact boundaryStrip_mem_J A hk ℚ ⟨w,hw,le_rfl,le_rfl,le_rfl⟩

theorem boundary_initial_divisor_of_raw_eq (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    {w g : Monomial} (hg : g∈boundaryRaw A) (hw : w∈boundaryInitialGenerators A)
    (h : Divides w g) : w=g := by
  rcases hg with rfl | (⟨v,rfl⟩ | rfl)
  · rcases hw with rfl | hw
    · rfl
    · have hwz := boundaryStrip_z_lt A hw
      have hx : w.1=0 := by have := h.1; simpa using this
      have hy : w.2.1=0 := by have := h.2.1; simpa using this
      have hc := boundaryStrip_cut A hk hw
      have hcz : w.2.2*routingC P.M.base A.reindex∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
        simpa [monomialDegree,normalizedGrid,hx,hy] using hc
      have := (boundary_axis_cut_bounds G A hm hl).2 w.2.2 hcz
      omega
  · rcases hw with rfl | hw
    · have hlt := (pureSourceNormal_spec A v).2.2
      have hle := h.2.2
      change d A≤(pureSourceNormal A v).2.2 at hle
      omega
    · exact pureSource_divisor_eq A v h (boundaryStrip_cut A hk hw)
  · rcases hw with rfl | hw
    · have hle := h.2.2
      have := boundary_d_pos A
      change d A≤0 at hle
      omega
    · have hx : w.1=0 := by have := h.1; simpa using this
      have hz : w.2.2=0 := by have := h.2.2; simpa using this
      have hc := boundaryStrip_cut A hk hw
      have hcy : w.2.1*routingB P.M.base A.reindex∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
        simpa [monomialDegree,normalizedGrid,hx,hz] using hc
      have hlow := (boundary_axis_cut_bounds G A hm hl).1 w.2.1 hcy
      have hu := h.2.1
      exact Prod.ext hx (Prod.ext (by
        change w.2.1≤alpha A at hu
        change w.2.1=alpha A
        omega) hz)

theorem boundary_raw_minimal (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    {g : Monomial} (hg : g∈boundaryRaw A) : PolynomialMinimal (boundaryInitialGenerators A) g := by
  have hi : g∈boundaryInitialGenerators A := by
    rcases hg with hg | hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl hg)
  refine ⟨⟨g,hi,le_rfl,le_rfl,le_rfl⟩,?_⟩
  rintro z ⟨w,hw,hx,hy,hz⟩ hz1 hz2 hz3
  have he := boundary_initial_divisor_of_raw_eq G A hm hk hl hg hw
    ⟨hx.trans hz1,hy.trans hz2,hz.trans hz3⟩
  subst w
  exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))

theorem boundary_initial_finite (A : SectorBCriticalRoleBranchA P) :
    (boundaryInitialGenerators A).Finite := by
  let := pure_model_sources_finite A
  have ho : (boundaryOriginals A).Finite := (Set.finite_range _).union (Set.finite_singleton _)
  have hw : {w | ∃ g∈boundaryOriginals A, 0<g.2.2 ∧ w=boundaryWrap A g} ⊆
      boundaryWrap A '' boundaryOriginals A := by
    rintro w ⟨g,hg,_,rfl⟩
    exact ⟨g,hg,rfl⟩
  exact (Set.finite_singleton _).union (ho.union ((ho.image _).subset hw))

theorem boundary_raw_card (A : SectorBCriticalRoleBranchA P) :
    Nat.card (boundaryRaw A)=P.sourceCount+2 := by
  let := pure_model_sources_finite A
  have hf : (Set.range (pureSourceNormal A)).Finite := Set.finite_range _
  have hy : (0,alpha A,0)∉Set.range (pureSourceNormal A) := by
    rintro ⟨v,hv⟩
    have h := (pureSourceNormal_spec A v).2.1
    rw [hv] at h
    exact (Nat.lt_irrefl _ h)
  have hz : (0,0,d A)∉Set.range (pureSourceNormal A) := by
    rintro ⟨v,hv⟩
    have h := (pureSourceNormal_spec A v).2.2
    rw [hv] at h
    exact (Nat.lt_irrefl _ h)
  have hzy : (0,0,d A)≠(0,alpha A,0) := by
    intro he
    have hh := congrArg (fun t : Monomial => t.2.2) he
    have := boundary_d_pos A
    dsimp at hh
    omega
  have he : boundaryRaw A=insert (0,0,d A) (insert (0,alpha A,0) (Set.range (pureSourceNormal A))) := by
    ext g
    simp only [boundaryRaw,boundaryOriginals,Set.mem_union,Set.mem_singleton_iff,Set.mem_insert_iff]
    tauto
  have hnot : (0,0,d A)∉insert (0,alpha A,0) (Set.range (pureSourceNormal A)) := by
    exact fun h => (Set.mem_insert_iff.mp h).elim hzy hz
  change (boundaryRaw A).ncard=P.sourceCount+2
  rw [he,Set.ncard_insert_of_notMem hnot (hf.insert _),Set.ncard_insert_of_notMem hy hf,
    Set.ncard_range_of_injective (pureSourceNormal_injective A),pure_model_source_count]

theorem boundary_polynomialMinimal_card_exact (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    Nat.card {g // PolynomialMinimal (boundaryInitialGenerators A) g}=
      P.sourceCount+2+boundarySurvivingWrapCount A := by
  have hp : {g | PolynomialMinimal (boundaryInitialGenerators A) g}=
      boundaryRaw A ∪ BoundarySurvivingWraps A := by
    ext g
    constructor
    · intro hg
      by_cases hr : g∈boundaryRaw A
      · exact Or.inl hr
      · exact Or.inr ⟨hg,hr⟩
    · rintro (hg | hg)
      · exact boundary_raw_minimal G A hm hk hl hg
      · exact hg.1
  have hd : Disjoint (boundaryRaw A) (BoundarySurvivingWraps A) :=
    Set.disjoint_left.mpr (fun _ hr hs => hs.2 hr)
  have hf : (BoundarySurvivingWraps A).Finite := (boundary_initial_finite A).subset
    (fun _ hg => polynomialMinimal_mem_generator _ _ hg.1)
  have hr : (boundaryRaw A).Finite := (boundary_initial_finite A).subset (by
    intro g hg; rcases hg with hg | hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl hg))
  change {g | PolynomialMinimal (boundaryInitialGenerators A) g}.ncard=
    P.sourceCount+2+(BoundarySurvivingWraps A).ncard
  rw [hp,Set.ncard_union_eq hd hr hf]
  rw [show (boundaryRaw A).ncard=P.sourceCount+2 from boundary_raw_card A]

def boundaryFullSourceCount (A : SectorBCriticalRoleBranchA P) : ℕ :=
  Nat.card {v : ModelSources P.M.base A.reindex // FullySupported (pureSourceNormal A v)}

theorem boundary_full_minima_card (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    Nat.card {g // PolynomialMinimal (boundaryInitialGenerators A) g ∧ FullySupported g}=
      boundaryFullSourceCount A := by
  let f : {v : ModelSources P.M.base A.reindex // FullySupported (pureSourceNormal A v)} →
      {g // PolynomialMinimal (boundaryInitialGenerators A) g ∧ FullySupported g} := fun v =>
    ⟨pureSourceNormal A v.val,boundary_raw_minimal G A hm hk hl (Or.inr (Or.inl ⟨v.val,rfl⟩)),v.property⟩
  have he : Function.Bijective f := by
    constructor
    · intro v w h
      apply Subtype.ext
      apply pureSourceNormal_injective A
      exact congrArg (fun z : {g // PolynomialMinimal (boundaryInitialGenerators A) g ∧ FullySupported g} => z.val) h
    · rintro ⟨g,hmin,hfull⟩
      have hg := polynomialMinimal_mem_generator _ _ hmin
      rcases hg with rfl | (⟨v,rfl⟩ | rfl) | ⟨w,hw,hz,rfl⟩
      · simp [FullySupported] at hfull
      · exact ⟨⟨v,hfull⟩,rfl⟩
      · simp [FullySupported] at hfull
      · simp [FullySupported,boundaryWrap] at hfull
  exact (Nat.card_congr (Equiv.ofBijective f he)).symm

theorem boundary_full_source_count_le_one (A : SectorBCriticalRoleBranchA P) :
    boundaryFullSourceCount A≤1 := by
  let := pure_model_sources_finite A
  let f : {v : ModelSources P.M.base A.reindex // FullySupported (pureSourceNormal A v)} →
      {v : ModelSources P.M.base A.reindex // ModelFullSupport P.M.base A.reindex v.val} := fun v =>
    ⟨v.val,by
      have h := pure_positive_coordinates_full_support A (pureSourceNormal A v.val)
        v.property.1 v.property.2.1 v.property.2.2
      rwa [(pureSourceNormal_spec A v.val).1] at h⟩
  have hf : Function.Injective f := by
    intro v w h
    exact Subtype.ext (congrArg
      (fun z : {v : ModelSources P.M.base A.reindex // ModelFullSupport P.M.base A.reindex v.val} => z.val) h)
  exact (Nat.card_le_card_of_injective f hf).trans (pure_full_support_source_count_le_one _ _)

theorem boundary_initial_proper (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    (0,0,0)∉monomialClosure (boundaryInitialGenerators A) := by
  intro hc
  have ht := (boundary_strip_initial_mem_iff A (0,0,0) (boundary_d_pos A)).mp hc
  have hcut := (boundary_normal_mem_iff_cut A hk (0,0,0)).mp
    (by simpa [boundaryNormal] using ht)
  obtain ⟨_,n,hn,y,_,he⟩ := hcut
  have hp := routingM_pos P.M.base A.reindex
  simp only [monomialDegree,normalizedGrid,zero_mul,zero_add] at he
  nlinarith

/-- Generic R24 surcharge is retained: no plane-only or B=0 assumption. -/
theorem boundary_socle_source_budget (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    Nat.card {z // MonomialSocle (boundaryInitialGenerators A) z}+2≤
      P.sourceCount+2+boundarySurvivingWrapCount A+boundaryFullSourceCount A := by
  let F : Finset Monomial := (boundary_initial_finite A).toFinset
  have hF : (F : Set Monomial)=boundaryInitialGenerators A := (boundary_initial_finite A).coe_toFinset
  have hp : (0,0,0)∉monomialClosure (F : Set Monomial) := by
    rw [hF]; exact boundary_initial_proper A hk
  have ha := boundary_initial_axes A hk
  rw [←hF] at ha
  have ht := L5A2C4OR24.abstract_monomial_socle_bound_general F hp ha
  rw [hF,boundary_polynomialMinimal_card_exact G A hm hk hl,boundary_full_minima_card G A hm hk hl] at ht
  exact ht

theorem boundary_corrected_type_budget (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    Gamma.asRelativeIdeal.idealType+Nat.card {z // z∈boundaryBorderExceptional A}≤
      P.sourceCount+boundarySurvivingWrapCount A+boundaryFullSourceCount A := by
  have hb := boundary_socle_source_budget G A hm hk hl
  have he := boundary_one_binomial_type_correction A hk
  omega

/-- All constructions share the original Gamma/P/G and the same extracted A. -/
theorem boundary_all_pure_corrected_budget (P : P2Data Gamma) (G : SectorCActualFibers P)
    (h : ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.boundaryDegree ∧ A.mixedDegree=G.internalDegree ∧
      BoundaryKilled P.M A.pairDegree A.pair.leftComponent ∧
      ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent ∧
      (∃ v : ModelSources P.M.base A.reindex, ∃ p : ℕ,
        pureSourceNormal A v=(p,0,0) ∧ 0<r A ∧ r A<p ∧ p<beta A ∧ 0<s A ∧ s A<alpha A) ∧
      Nat.card {g // PolynomialMinimal (boundaryInitialGenerators A) g}=
        P.sourceCount+2+boundarySurvivingWrapCount A ∧
      boundaryFullSourceCount A≤1 ∧
      Gamma.asRelativeIdeal.idealType+Nat.card {z // z∈boundaryBorderExceptional A}≤
        P.sourceCount+boundarySurvivingWrapCount A+boundaryFullSourceCount A := by
  obtain ⟨A,hp,hm,hk,hl,_⟩ := boundary_all_pure_geometry P G h
  exact ⟨A,hp,hm,hk,hl,boundary_actual_coefficient_bounds G A hm hk,
    boundary_polynomialMinimal_card_exact G A hm hk hl,boundary_full_source_count_le_one A,
    boundary_corrected_type_budget G A hm hk hl⟩

/-- A nonfirst z-positive source has a nonzero return in the complementary
axis. Conjugating that return gives a strict cut divisor of its wrap. -/
theorem boundary_nonfirst_wrap_redundant (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v : ModelSources P.M.base A.reindex) (hz : 0<(pureSourceNormal A v).2.2)
    (hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex) :
    ¬PolynomialMinimal (boundaryInitialGenerators A) (boundaryWrap A (pureSourceNormal A v)) := by
  let g := pureSourceNormal A v
  have hg : monomialDegree P.M.base A.reindex g=v.val := (pureSourceNormal_spec A v).1
  have hgz := (pureSourceNormal_spec A v).2.2
  change g.2.2<d A at hgz
  change 0<g.2.2 at hz
  obtain ⟨n,t,hn,_,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ v hnf
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base A.reindex (x,y,z)=t := hfac.symm
  have sep := source_return_coordinate_separation _ _ v g (x,y,z) hg hn
    (he.trans (by rw [hd]))
  have z0 : z=0 := sep.2.2 hz
  have hrel := (branchA_symmetricTailData A).mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hrel
  have hr := (branchA_symmetricTailData A).r_pos
  have hs := (branchA_symmetricTailData A).s_pos
  have strict_cut_divisor (w : Monomial)
      (hw : monomialDegree P.M.base A.reindex w∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
      (hwz : w.2.2<d A) (hwdiv : Divides w (boundaryWrap A g))
      (hwne : w≠boundaryWrap A g) :
      ¬PolynomialMinimal (boundaryInitialGenerators A) (boundaryWrap A g) := by
    have hwi : w∈monomialClosure (boundaryInitialGenerators A) := by
      apply (boundary_strip_initial_mem_iff A w hwz).mpr
      simpa only [boundaryNormal_fixed A w hwz] using (boundary_normal_mem_iff_cut A hk w).mpr hw
    intro hmin
    exact hwne (hmin.2 w hwi hwdiv.1 hwdiv.2.1 hwdiv.2.2)
  rcases pure_nonfirst_source_plane A v hnf with gx0 | gy0 | gz0
  · change g.1=0 at gx0
    by_cases gy : 0<g.2.1
    · have y0 : y=0 := sep.2.1 gy
      have xp : 0<x := by
        by_contra hx
        have x0 : x=0 := by omega
        simp [monomialDegree,normalizedGrid,x0,y0,z0] at hd
        omega
      let w : Monomial := (r A-1,g.2.1+s A,0)
      have heq : monomialDegree P.M.base A.reindex w=
          n*routingM P.M.base A.reindex+monomialDegree P.M.base A.reindex (x-1,0,d A-g.2.2) := by
        have hx := congrArg (fun t => t*routingA P.M.base A.reindex)
          (Nat.sub_add_cancel (by omega : 1≤x))
        have hrr := congrArg (fun t => t*routingA P.M.base A.reindex)
          (Nat.sub_add_cancel (by omega : 1≤r A))
        have hzz := congrArg (fun t => t*routingC P.M.base A.reindex)
          (Nat.sub_add_cancel (Nat.le_of_lt hgz))
        simp only [Nat.add_mul,one_mul] at hx hrr hzz
        simp only [monomialDegree,normalizedGrid,y0,z0,zero_mul,add_zero] at hd
        simp only [monomialDegree,normalizedGrid,w,Nat.add_mul,zero_mul,zero_add,add_zero]
        simp only [monomialDegree,normalizedGrid,gx0,zero_mul,zero_add] at hg
        omega
      have hw : monomialDegree P.M.base A.reindex w∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) :=
        ⟨grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ _,heq⟩
      apply strict_cut_divisor w hw (boundary_d_pos A)
      · simp only [Divides,w,boundaryWrap,gx0,zero_add]; omega
      · intro hh
        have hx := congrArg (fun z : Monomial => z.1) hh
        simp only [w,boundaryWrap,gx0,zero_add] at hx
        omega
    · have gy0 : g.2.1=0 := by omega
      have hc : g.2.2*routingC P.M.base A.reindex∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
        have hh := v.property.1
        rw [←hg] at hh
        simpa [monomialDegree,normalizedGrid,gx0,gy0] using hh
      have hle := (boundary_axis_cut_bounds G A hm hl).2 g.2.2 hc
      omega
  · change g.2.1=0 at gy0
    have x0 : x=0 := sep.1 (show 0<g.1 by
      by_contra hx
      have gx0 : g.1=0 := by omega
      have hc : g.2.2*routingC P.M.base A.reindex∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
        have hh := v.property.1
        rw [←hg] at hh
        simpa [monomialDegree,normalizedGrid,gx0,gy0] using hh
      have hle := (boundary_axis_cut_bounds G A hm hl).2 g.2.2 hc
      omega)
    have yp : 0<y := by
      by_contra hy
      have y0 : y=0 := by omega
      simp [monomialDegree,normalizedGrid,x0,y0,z0] at hd
      omega
    let w : Monomial := (g.1+r A,s A-1,0)
    have heq : monomialDegree P.M.base A.reindex w=
        n*routingM P.M.base A.reindex+monomialDegree P.M.base A.reindex (0,y-1,d A-g.2.2) := by
      have hy := congrArg (fun t => t*routingB P.M.base A.reindex)
        (Nat.sub_add_cancel (by omega : 1≤y))
      have hss := congrArg (fun t => t*routingB P.M.base A.reindex)
        (Nat.sub_add_cancel (by omega : 1≤s A))
      have hzz := congrArg (fun t => t*routingC P.M.base A.reindex)
        (Nat.sub_add_cancel (Nat.le_of_lt hgz))
      simp only [Nat.add_mul,one_mul] at hy hss hzz
      simp only [monomialDegree,normalizedGrid,x0,z0,zero_mul,zero_add,add_zero] at hd
      simp only [monomialDegree,normalizedGrid,w,Nat.add_mul,zero_mul,zero_add,add_zero]
      simp only [monomialDegree,normalizedGrid,gy0,zero_mul,add_zero] at hg
      omega
    have hw : monomialDegree P.M.base A.reindex w∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) :=
      ⟨grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ _,heq⟩
    apply strict_cut_divisor w hw (boundary_d_pos A)
    · simp only [Divides,w,boundaryWrap,gy0,zero_add]; omega
    · intro hh
      have hy := congrArg (fun z : Monomial => z.2.1) hh
      simp only [w,boundaryWrap,gy0,zero_add] at hy
      omega
  · change g.2.2=0 at gz0
    omega

theorem boundary_surviving_wrap_is_first (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    {w : Monomial} (hw : w∈BoundarySurvivingWraps A) :
    ∃ v : ModelSources P.M.base A.reindex,
      v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex ∧
      0<(pureSourceNormal A v).2.2 ∧ w=boundaryWrap A (pureSourceNormal A v) := by
  have hg := polynomialMinimal_mem_generator _ _ hw.1
  rcases hg with hg | hg | ⟨g,hg,hgz,rfl⟩
  · exact (hw.2 (Or.inl hg)).elim
  · exact (hw.2 (Or.inr hg)).elim
  · rcases hg with ⟨v,rfl⟩ | rfl
    · refine ⟨v,?_,hgz,rfl⟩
      by_contra hnf
      exact boundary_nonfirst_wrap_redundant G A hm hk hl v hgz hnf hw.1
    · change 0<0 at hgz
      omega

theorem boundary_surviving_wrap_count_le_one (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    boundarySurvivingWrapCount A≤1 := by
  have : Subsingleton (BoundarySurvivingWraps A) := ⟨by
    rintro ⟨w,hw⟩ ⟨z,hz⟩
    obtain ⟨v,hv,_,he⟩ := boundary_surviving_wrap_is_first G A hm hk hl hw
    obtain ⟨u,hu,_,hf⟩ := boundary_surviving_wrap_is_first G A hm hk hl hz
    have huv : u=v := Subtype.ext (hu.trans hv.symm)
    subst u
    exact Subtype.ext (he.trans hf.symm)⟩
  let := this
  simpa [boundarySurvivingWrapCount] using Nat.card_le_card_of_injective
    (fun _ : BoundarySurvivingWraps A => ()) (fun _ _ _ => Subsingleton.elim _ _)

theorem boundary_first_z_zero_no_surviving_wrap (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v : ModelSources P.M.base A.reindex)
    (hv : v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hz : (pureSourceNormal A v).2.2=0) : boundarySurvivingWrapCount A=0 := by
  let : IsEmpty (BoundarySurvivingWraps A) := ⟨by
    rintro ⟨w,hw⟩
    obtain ⟨u,hu,huz,_⟩ := boundary_surviving_wrap_is_first G A hm hk hl hw
    have he : u=v := Subtype.ext (hu.trans hv.symm)
    subst u
    omega⟩
  exact Nat.card_of_isEmpty

theorem boundary_all_pure_checkpoint (P : P2Data Gamma) (G : SectorCActualFibers P)
    (h : ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.boundaryDegree ∧ A.mixedDegree=G.internalDegree ∧
      BoundaryKilled P.M A.pairDegree A.pair.leftComponent ∧
      ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent ∧
      Nat.card {g // PolynomialMinimal (boundaryInitialGenerators A) g}=
        P.sourceCount+2+boundarySurvivingWrapCount A ∧
      boundarySurvivingWrapCount A≤1 ∧ boundaryFullSourceCount A≤1 ∧
      Gamma.asRelativeIdeal.idealType+Nat.card {z // z∈boundaryBorderExceptional A}≤
        P.sourceCount+boundarySurvivingWrapCount A+boundaryFullSourceCount A := by
  obtain ⟨A,hp,hm,hk,hl,_⟩ := boundary_all_pure_geometry P G h
  exact ⟨A,hp,hm,hk,hl,boundary_polynomialMinimal_card_exact G A hm hk hl,
    boundary_surviving_wrap_count_le_one G A hm hk hl,boundary_full_source_count_le_one A,
    boundary_corrected_type_budget G A hm hk hl⟩

end NS25Lean.L5A2C4OR46
