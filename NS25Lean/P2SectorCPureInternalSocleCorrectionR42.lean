import NS25Lean.P2SectorCPureInternalNormalStripR42
import NS25Lean.P2SectorCM7OneBinomialBorderR35

set_option linter.style.header false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.L5A2C4OR42
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR39 L5A2C4OR40 L5A2C4OR41
  FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

def pureBorderExceptional (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  {z | MonomialSocle (pureInitialGenerators A) z ∧ z.2.1+1=alpha A ∧
    pureWrap A z∉monomialClosure (pureStripGenerators A)}

def PureTrueSocle (A : SectorBCriticalRoleBranchA P) (z : Monomial) : Prop :=
  PureStandard A z ∧
    pureNormal A (z.1+1,z.2.1,z.2.2)∈monomialClosure (pureStripGenerators A) ∧
    pureNormal A (z.1,z.2.1+1,z.2.2)∈monomialClosure (pureStripGenerators A) ∧
    pureNormal A (z.1,z.2.1,z.2.2+1)∈monomialClosure (pureStripGenerators A)

theorem pure_top_y_normal (A : SectorBCriticalRoleBranchA P) (z : Monomial)
    (hy : z.2.1+1=alpha A) :
    pureNormal A (z.1,z.2.1+1,z.2.2)=pureWrap A z := by
  simp [pureNormal,pureWrap,hy,Nat.div_self (pure_alpha_pos A)]

theorem pure_trueSocle_iff_complement (A : SectorBCriticalRoleBranchA P) (z : Monomial) :
    PureTrueSocle A z ↔ MonomialSocle (pureInitialGenerators A) z ∧
      z∉pureBorderExceptional A := by
  constructor
  · rintro ⟨hs,hx,hy,hz⟩
    rw [pureNormal_fixed A (z.1+1,z.2.1,z.2.2) hs.1] at hx
    rw [pureNormal_fixed A (z.1,z.2.1,z.2.2+1) hs.1] at hz
    have hx' := (pure_strip_initial_mem_iff A (z.1+1,z.2.1,z.2.2) hs.1).mpr hx
    have hz' := (pure_strip_initial_mem_iff A (z.1,z.2.1,z.2.2+1) hs.1).mpr hz
    have hy' : (z.1,z.2.1+1,z.2.2)∈monomialClosure (pureInitialGenerators A) := by
      by_cases ht : z.2.1+1<alpha A
      · rw [pureNormal_fixed A _ ht] at hy
        exact (pure_strip_initial_mem_iff A _ ht).mpr hy
      · exact (pure_initial_mem_iff A _).mpr (Or.inl (by
          change alpha A≤z.2.1+1; omega))
    refine ⟨⟨(pure_standard_iff A z).mp hs,hx',hy',hz'⟩,?_⟩
    rintro ⟨_,ht,hn⟩
    rw [pure_top_y_normal A z ht] at hy
    exact hn hy
  · rintro ⟨⟨hn,hx,hy,hz⟩,he⟩
    have hs := (pure_standard_iff A z).mpr hn
    refine ⟨hs,?_,?_,?_⟩
    · rw [pureNormal_fixed A (z.1+1,z.2.1,z.2.2) hs.1]
      exact (pure_strip_initial_mem_iff A (z.1+1,z.2.1,z.2.2) hs.1).mp hx
    · by_cases ht : z.2.1+1<alpha A
      · rw [pureNormal_fixed A _ ht]
        exact (pure_strip_initial_mem_iff A _ ht).mp hy
      · have htop : z.2.1+1=alpha A := by have := hs.1; omega
        rw [pure_top_y_normal A z htop]
        by_contra hw
        exact he ⟨⟨hn,hx,hy,hz⟩,htop,hw⟩
    · rw [pureNormal_fixed A (z.1,z.2.1,z.2.2+1) hs.1]
      exact (pure_strip_initial_mem_iff A (z.1,z.2.1,z.2.2+1) hs.1).mp hz

/-- Standard degrees lie in the actual rectangle: the other boundary
endpoint is a cut by R41, regardless of which endpoint is live. -/
theorem pure_standard_z_lt (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) {z : Monomial} (hz : PureStandard A z) :
    z.2.2<d A := by
  have hJ := internal_candidate_le_J A hk ℚ (boundary_endpoints_mem A hk ℚ).1
  have hgen := pure_strip_forward A hk ℚ (0,0,d A) (pure_alpha_pos A) hJ
  by_contra hn
  have hu : z∈monomialClosure (pureStripGenerators A) :=
    monomialClosure_upward hgen (Nat.zero_le _) (Nat.zero_le _) (by
      change d A≤z.2.2; omega)
  exact hz.2 hu

theorem pure_standard_degree_injective (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) {z w : Monomial}
    (hz : PureStandard A z) (hw : PureStandard A w)
    (he : monomialDegree P.M.base A.reindex z=monomialDegree P.M.base A.reindex w) : z=w :=
  pure_tail_normal_unique A ⟨hz.1,pure_standard_z_lt A hk hz⟩
    ⟨hw.1,pure_standard_z_lt A hk hw⟩ he

theorem pure_standard_degree_surjective (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) {x : ℕ} (hx : x∈routingH P.M.base A.reindex)
    (hn : x∉cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    ∃ z, PureStandard A z ∧ monomialDegree P.M.base A.reindex z=x := by
  obtain ⟨r,i,j,he⟩ := L5A2C4OR6.routingH_factorization P.M.base A.reindex hx
  refine ⟨pureNormal A (r,i,j),⟨pureNormal_y_lt A _,?_⟩,?_⟩
  · intro hm
    apply hn
    simpa only [monomialDegree,normalizedGrid,←he] using (pure_normal_mem_iff_cut A hk (r,i,j)).mp hm
  · rw [pureNormal_degree]
    exact he.symm

/-- Generic actual H-order tops are detected by the three actual generators. -/
theorem pure_modelTop_iff_steps (A : SectorBCriticalRoleBranchA P) (x : ℕ) :
    ModelTop P.M.base A.reindex x ↔
      x∈routingH P.M.base A.reindex ∧
      x∉cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) ∧
      x+routingA P.M.base A.reindex∈cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) ∧
      x+routingB P.M.base A.reindex∈cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) ∧
      x+routingC P.M.base A.reindex∈cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
  have ha : routingA P.M.base A.reindex∈routingH P.M.base A.reindex := by
    simpa [monomialDegree,normalizedGrid] using L5A2C4OR33.grid_mem_H P.M.base A.reindex (1,0,0)
  constructor
  · rintro ⟨hx,hn,hh⟩
    exact ⟨hx,hn,hh _ ha (routingA_pos _ _).ne',hh _ (routingHB _ _) (routingB_positive _ _).ne',
      hh _ (routingHC _ _) (routingC_positive _ _).ne'⟩
  · rintro ⟨hx,hn,hA,hB,hC⟩
    refine ⟨hx,hn,?_⟩
    intro h hh h0
    obtain ⟨r,i,j,he⟩ := L5A2C4OR6.routingH_factorization P.M.base A.reindex hh
    cases r with
    | succ r =>
      have ht := L5A2C4OR35.cut_add_tail hA (L5A2C4OR33.grid_mem_H P.M.base A.reindex (r,i,j))
      convert ht using 1 <;> simp [monomialDegree,normalizedGrid,he,Nat.succ_mul] <;> ring
    | zero =>
      cases i with
      | succ i =>
        have ht := L5A2C4OR35.cut_add_tail hB (L5A2C4OR33.grid_mem_H P.M.base A.reindex (0,i,j))
        convert ht using 1 <;> simp [monomialDegree,normalizedGrid,he,Nat.succ_mul] <;> ring
      | zero =>
        cases j with
        | zero => exact (h0 (by simpa using he)).elim
        | succ j =>
          have ht := L5A2C4OR35.cut_add_tail hC (L5A2C4OR33.grid_mem_H P.M.base A.reindex (0,0,j))
          convert ht using 1 <;> simp [monomialDegree,normalizedGrid,he,Nat.succ_mul] <;> ring

theorem pure_trueSocle_iff_modelTop (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (z : Monomial) (hs : PureStandard A z) :
    PureTrueSocle A z ↔ ModelTop P.M.base A.reindex (monomialDegree P.M.base A.reindex z) := by
  have hn : monomialDegree P.M.base A.reindex z∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    intro hc
    have ht := (pure_normal_mem_iff_cut A hk z).mpr hc
    rw [pureNormal_fixed A z hs.1] at ht
    exact hs.2 ht
  rw [PureTrueSocle,pure_modelTop_iff_steps,pure_normal_mem_iff_cut A hk,
    pure_normal_mem_iff_cut A hk,pure_normal_mem_iff_cut A hk]
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
  simp only [hs,hn,L5A2C4OR33.grid_mem_H,true_and,not_false_eq_true]

def pureTrueSocleEquivTops (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) :
    {z // PureTrueSocle A z} ≃ ModelTops P.M.base A.reindex := by
  let f : {z // PureTrueSocle A z} → ModelTops P.M.base A.reindex := fun z =>
    ⟨monomialDegree P.M.base A.reindex z.val,
      (pure_trueSocle_iff_modelTop A hk z.val z.property.1).mp z.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro z w he
    apply Subtype.ext
    exact pure_standard_degree_injective A hk z.property.1 w.property.1 (congrArg Subtype.val he)
  · intro x
    obtain ⟨z,hs,he⟩ := pure_standard_degree_surjective A hk x.property.1 x.property.2.1
    refine ⟨⟨z,(pure_trueSocle_iff_modelTop A hk z hs).mpr (he.symm ▸ x.property)⟩,?_⟩
    exact Subtype.ext he

/-- Exact correction to the ORIGINAL physical Gamma type. Zero-centers,
owner resources and a supposed plane-only bound are not used. -/
theorem pure_one_binomial_type_correction (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) :
    Gamma.asRelativeIdeal.idealType+Nat.card {z // z∈pureBorderExceptional A}=
      Nat.card {z // MonomialSocle (pureInitialGenerators A) z} := by
  have hsub : pureBorderExceptional A⊆{z | MonomialSocle (pureInitialGenerators A) z} :=
    fun _ h => h.1
  obtain ⟨a,b,c,_,_,_,ha,hb,hc⟩ := pure_initial_axes A hk
  have hfinite := monomialSocle_finite (pureInitialGenerators A) a b c ha hb hc
  have he : {z // PureTrueSocle A z} ≃
      {z // z∈{z | MonomialSocle (pureInitialGenerators A) z} \ pureBorderExceptional A} :=
    L5A2C4OR34.predicateSubtypeEquiv (pure_trueSocle_iff_complement A)
  have hcount := Nat.card_congr (pureTrueSocleEquivTops A hk)
  rw [pure_model_top_count P A.reindex] at hcount
  rw [←hcount,Nat.card_congr he]
  exact Set.ncard_sdiff_add_ncard_of_subset hsub hfinite

theorem internal_all_pure_type_correction (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp≠bm) (hp : IsPureBoundaryComponent G bp)
    (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,(componentSupport P.M.base G.internalDegree C).card=1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.internalDegree ∧ A.mixedDegree=G.boundaryDegree ∧
      Gamma.asRelativeIdeal.idealType+Nat.card {z // z∈pureBorderExceptional A}=
        Nat.card {z // MonomialSocle (pureInitialGenerators A) z} := by
  obtain ⟨A,ha,hb,_⟩ := internal_all_pure_geometry P G bp bm hne hp hm hi
  refine ⟨A,ha,hb,pure_one_binomial_type_correction A ?_⟩
  rw [hb]
  exact G.boundarySignature.2

/-- Literal positive coordinates give actual union support, without a
surrogate role packet or an assumption equating source/owner labels. -/
theorem pure_positive_coordinates_full_support (A : SectorBCriticalRoleBranchA P)
    (z : Monomial) (hx : 0<z.1) (hy : 0<z.2.1) (hz : 0<z.2.2) :
    ModelFullSupport P.M.base A.reindex (monomialDegree P.M.base A.reindex z) := by
  have h1 := congrArg (fun t => t*routingA P.M.base A.reindex)
    (Nat.sub_add_cancel (show 1≤z.1 by omega))
  have h2 := congrArg (fun t => t*routingB P.M.base A.reindex)
    (Nat.sub_add_cancel (show 1≤z.2.1 by omega))
  have h3 := congrArg (fun t => t*routingC P.M.base A.reindex)
    (Nat.sub_add_cancel (show 1≤z.2.2 by omega))
  simp only [Nat.add_mul,one_mul] at h1 h2 h3
  refine ⟨⟨monomialDegree P.M.base A.reindex (z.1-1,z.2.1,z.2.2),
    L5A2C4OR33.grid_mem_H _ _ _,?_⟩,
    ⟨monomialDegree P.M.base A.reindex (z.1,z.2.1-1,z.2.2),
      L5A2C4OR33.grid_mem_H _ _ _,?_⟩,
    ⟨monomialDegree P.M.base A.reindex (z.1,z.2.1,z.2.2-1),
      L5A2C4OR33.grid_mem_H _ _ _,?_⟩⟩
  all_goals
    simp only [monomialDegree,normalizedGrid]
    omega

theorem pure_nonfirst_source_plane (A : SectorBCriticalRoleBranchA P)
    (v : ModelSources P.M.base A.reindex)
    (hn : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex) :
    (pureSourceNormal A v).1=0 ∨ (pureSourceNormal A v).2.1=0 ∨
      (pureSourceNormal A v).2.2=0 := by
  by_contra h
  have hpos : 0<(pureSourceNormal A v).1 ∧ 0<(pureSourceNormal A v).2.1 ∧
      0<(pureSourceNormal A v).2.2 := by omega
  have hf := pure_positive_coordinates_full_support A (pureSourceNormal A v) hpos.1 hpos.2.1 hpos.2.2
  rw [(pureSourceNormal_spec A v).1] at hf
  exact hn (model_full_support_source_is_first _ _ v hf)

end NS25Lean.L5A2C4OR42
