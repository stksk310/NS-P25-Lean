import NS25Lean.P2CriticalPermutation
import NS25Lean.P2ErasureActualAdapters
import NS25Lean.P2GenericCriticalDuality
import NS25Lean.P2SectorCPureBoundaryExceptionalCapR47

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.PurePairGenericDualityAdapter
open Classical FourGeneratedBridge ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR33 L5A2C4OR35
  L5A2C4OR39 L5A2C4OR40 L5A2C4OR42 L5A2C4OR43 L5A2C4OR44 L5A2C4OR46 L5A2C4OR47
  ErasedSourceScreen ErasureActualAdapters PureInternalTransverse CriticalCapGeometry
  CriticalPresentationModes CriticalFullSignature GenericCriticalCompensation CriticalNormalForm
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

def perm (g : Monomial) : SharedCap.Monomial := (g.1,g.2.2,g.2.1)
@[simp] theorem perm_involutive (g : Monomial) : perm (perm g)=g := rfl
 theorem perm_injective : Function.Injective perm := fun _ _ h => congrArg perm h

def actualBase (A : SectorBCriticalRoleBranchA P) : Base (routingH P.M.base A.reindex) where
  triple := CriticalPermutation.triple (actualTriple P.M.base A.reindex)
  critical := CriticalPermutation.critical (actualCritical P.M.base A.reindex)
  m := routingM P.M.base A.reindex
  m_pos := routingM_pos _ _
  u := r A
  v := s A
  u_pos := (branchA_symmetricTailData A).r_pos
  v_pos := (branchA_symmetricTailData A).s_pos
  tie := by
    have hc := (branchA_symmetricTailData A).c2_eq_d
    change criticalExponent P.M.base (A.reindex 2)=d A at hc
    have hr := (branchA_symmetricTailData A).mixed_relation
    rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hr
    simpa [CriticalPermutation.critical,actualCritical,
      actual_g_zero,actual_g_one,actual_g_two,hc] using hr

@[simp] theorem base_u (A : SectorBCriticalRoleBranchA P) : (actualBase A).u=r A := rfl
@[simp] theorem base_v (A : SectorBCriticalRoleBranchA P) : (actualBase A).v=s A := rfl
@[simp] theorem base_K (A : SectorBCriticalRoleBranchA P) : (actualBase A).K=
    cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := rfl

@[simp] theorem base_C (A : SectorBCriticalRoleBranchA P) : (actualBase A).C=d A := by
  change criticalExponent P.M.base (A.reindex 2)=d A
  exact (branchA_symmetricTailData A).c2_eq_d
@[simp] theorem base_R (A : SectorBCriticalRoleBranchA P) : (actualBase A).R=beta A := by
  change criticalExponent P.M.base (A.reindex 0)=beta A
  exact (branchA_symmetricTailData A).c0_eq_beta
@[simp] theorem base_L (A : SectorBCriticalRoleBranchA P) : (actualBase A).L=alpha A := by
  change criticalExponent P.M.base (A.reindex 1)=alpha A
  exact (branchA_symmetricTailData A).c1_eq_alpha
@[simp] theorem base_g_zero (A : SectorBCriticalRoleBranchA P) :
    (actualBase A).triple.g 0=routingA P.M.base A.reindex := by simp [actualBase]
@[simp] theorem base_g_one (A : SectorBCriticalRoleBranchA P) :
    (actualBase A).triple.g 1=routingC P.M.base A.reindex := by simp [actualBase]
@[simp] theorem base_g_two (A : SectorBCriticalRoleBranchA P) :
    (actualBase A).triple.g 2=routingB P.M.base A.reindex := by simp [actualBase]

def actualMode (A : SectorBCriticalRoleBranchA P) : Mode (actualBase A) := .purePair (by
  have hr := (branchA_symmetricTailData A).pure_relation
  rw [←routingA_eq_n0,←routingB_eq_n1] at hr
  simpa only [base_R,base_L,base_g_zero,base_g_two] using hr)

theorem killed_axis (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    (beta A-1)*routingA P.M.base A.reindex∈cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
  have hp := (killed_iff_singleton_predecessor P.M A.pairDegree A.pair.leftComponent
    A.pair.leftRole A.pair.leftSupport).mp hk
  have hs := (branchA_symmetricTailData A).c0_eq_beta
  have he := A.pair.left_degree_eq_critical
  rw [←A.reindex_zero] at he hp
  change criticalExponent P.M.base (A.reindex 0)=beta A at hs
  rw [hs] at he
  have ha : routingD P.M.base A.reindex*routingA P.M.base A.reindex =
      weights P.M.base (A.reindex 0) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base A.reindex 1 0 0
  apply (actual_scaled_cut_iff _ _ _).mpr
  rw [he] at hp
  rw [Nat.sub_mul,Nat.one_mul,Nat.mul_sub_left_distrib]
  have hm : routingD P.M.base A.reindex*(beta A*routingA P.M.base A.reindex)=
      beta A*weights P.M.base (A.reindex 0) := by rw [←ha]; ring
  rwa [hm,ha]

def actualFront (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) : Front (actualBase A) (actualMode A) where
  mixed := false
  axis_killed := by simpa only [base_R,base_g_zero,base_K] using killed_axis A hk
  pure_b_live := by
    simpa only [base_C,base_g_one,base_K,Nat.sub_mul,one_mul] using (boundary_internal_predecessors_not_cut G A hm).2.2
  mixed_x_live := by
    have hr := (branchA_symmetricTailData A).mixed_relation
    rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hr
    have hu := congrArg (fun n => n*routingA P.M.base A.reindex) (show r A-1+1=r A by have := (branchA_symmetricTailData A).r_pos; omega)
    simp only [Nat.add_mul,one_mul] at hu
    have he : (r A-1)*routingA P.M.base A.reindex+s A*routingB P.M.base A.reindex=
        d A*routingC P.M.base A.reindex-routingA P.M.base A.reindex := by omega
    simpa only [base_g_zero,base_g_two,base_u,base_v,base_K,he] using (boundary_internal_predecessors_not_cut G A hm).1
  mixed_z_live := by
    have hr := (branchA_symmetricTailData A).mixed_relation
    rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hr
    have hv := congrArg (fun n => n*routingB P.M.base A.reindex) (show s A-1+1=s A by have := (branchA_symmetricTailData A).s_pos; omega)
    simp only [Nat.add_mul,one_mul] at hv
    have he : r A*routingA P.M.base A.reindex+(s A-1)*routingB P.M.base A.reindex=
        d A*routingC P.M.base A.reindex-routingB P.M.base A.reindex := by omega
    simpa only [base_g_zero,base_g_two,base_u,base_v,base_K,he] using (boundary_internal_predecessors_not_cut G A hm).2.1
  inactive_killed := True.intro
  boundary := by
    refine ⟨rfl,?_⟩
    simpa only [base_L,base_g_two,base_K] using boundary_alive_y_predecessor_not_cut A hl

theorem actual_normal_tuple (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v : ModelSources P.M.base A.reindex) :
    tuple ((actualBase A).norm v)=perm (pureSourceNormal A v) := by
  let e := vector (pureSourceNormal A v).1 (pureSourceNormal A v).2.2 (pureSourceNormal A v).2.1
  have hd : (actualBase A).triple.weight e=v.val := by
    simpa [actualBase,CriticalPermutation.weight,CriticalPermutation.swap,vector,actualTriple,
      monomialDegree,normalizedGrid,e] using (pureSourceNormal_spec A v).1
  have hy : e 1<(actualBase A).C := by simpa [e] using (pureSourceNormal_spec A v).2.2
  have hn := (actualFront G A hm hk hl).normal_unique v e hd
  rw [normal_fixed _ _ _ hy] at hn
  simpa [e,tuple,perm] using congrArg tuple hn.symm

theorem actual_family (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    GenericCriticalDuality.family (actualFront G A hm hk hl)=perm '' boundaryOriginals A := by
  ext g
  constructor
  · rintro ⟨e,(⟨v,rfl⟩ | rfl),rfl⟩
    · exact ⟨pureSourceNormal A v,Or.inl ⟨v,rfl⟩,(actual_normal_tuple G A hm hk hl v).symm⟩
    · refine ⟨(0,alpha A,0),Or.inr rfl,?_⟩
      simp [actualFront,actualMode,endpoint,tuple,perm,base_L]
  · rintro ⟨q,(⟨v,rfl⟩ | rfl),rfl⟩
    · exact ⟨(actualBase A).norm v,Or.inl ⟨v,rfl⟩,actual_normal_tuple G A hm hk hl v⟩
    · refine ⟨endpoint (actualMode A) false,Or.inr rfl,?_⟩
      simp [actualMode,endpoint,tuple,perm,base_L]

end NS25Lean.PurePairGenericDualityAdapter
