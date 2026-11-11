import NS25Lean.P2SectorCPureBoundaryExceptionalCapR47
import NS25Lean.AttainedCapCompensation
import NS25Lean.P2PurePairGenericDualityCounts

set_option autoImplicit false
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.PurePairCapAdapter
open FourGeneratedBridge ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR33 L5A2C4OR35
  L5A2C4OR39 L5A2C4OR40 L5A2C4OR42 L5A2C4OR43 L5A2C4OR44 L5A2C4OR46 L5A2C4OR47
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- New coordinates (X,Y,Z) are the literal old coordinates (X,Z,Y). -/
def perm (g : Monomial) : SharedCap.Monomial := (g.1,g.2.2,g.2.1)
@[simp] theorem perm_involutive (g : Monomial) : perm (perm g)=g := rfl
theorem perm_injective : Function.Injective perm := by
  intro p q h
  exact (congrArg perm h)

theorem below_perm (p q : Monomial) : SharedCap.Below (perm p) (perm q) ↔ Divides p q := by
  change (p.1≤q.1 ∧ p.2.2≤q.2.2 ∧ p.2.1≤q.2.1) ↔
    (p.1≤q.1 ∧ p.2.1≤q.2.1 ∧ p.2.2≤q.2.2)
  tauto

theorem closure_perm (O : Set Monomial) (g : Monomial) :
    perm g ∈ SharedCap.Closure (perm '' O) ↔ g ∈ monomialClosure O := by
  constructor
  · rintro ⟨p,⟨q,hq,rfl⟩,hd⟩
    exact ⟨q,hq,(below_perm q g).mp hd⟩
  · rintro ⟨q,hq,hd⟩
    exact ⟨perm q,⟨q,hq,rfl⟩,(below_perm q g).mpr hd⟩

theorem minimal_perm (O : Set Monomial) (g : Monomial) :
    SharedCap.MinimalGenerator (perm '' O) (perm g) ↔ PolynomialMinimal O g := by
  constructor
  · rintro ⟨hg,hmin⟩
    refine ⟨(closure_perm O g).mp hg,?_⟩
    intro q hq hx hy hz
    apply perm_injective
    exact hmin (perm q) ((closure_perm O q).mpr hq) ((below_perm q g).mpr ⟨hx,hy,hz⟩)
  · rintro ⟨hg,hmin⟩
    refine ⟨(closure_perm O g).mpr hg,?_⟩
    intro q hq hqg
    have hq' : perm q ∈ monomialClosure O := (closure_perm O (perm q)).mp (by simpa using hq)
    have hd : Divides (perm q) g := (below_perm (perm q) g).mp (by simpa using hqg)
    have he := hmin (perm q) hq' hd.1 hd.2.1 hd.2.2
    simpa using congrArg perm he

theorem socle_perm (O : Set Monomial) (g : Monomial) :
    SharedCap.Socle (perm '' O) (perm g) ↔ MonomialSocle O g := by
  change (perm g ∉ SharedCap.Closure (perm '' O) ∧
    perm (g.1+1,g.2.1,g.2.2) ∈ SharedCap.Closure (perm '' O) ∧
    perm (g.1,g.2.1,g.2.2+1) ∈ SharedCap.Closure (perm '' O) ∧
    perm (g.1,g.2.1+1,g.2.2) ∈ SharedCap.Closure (perm '' O)) ↔ _
  simp only [closure_perm,MonomialSocle]
  tauto

def originals (A : SectorBCriticalRoleBranchA P) : Set SharedCap.Monomial :=
  perm '' boundaryOriginals A

theorem zero_generators (A : SectorBCriticalRoleBranchA P) :
    SharedCap.ZeroGenerators (originals A)=perm '' boundaryPlaneOriginals A := by
  ext g
  constructor
  · rintro ⟨⟨q,hq,rfl⟩,hy⟩
    exact ⟨q,⟨hq,hy⟩,rfl⟩
  · rintro ⟨q,⟨hq,hz⟩,rfl⟩
    exact ⟨⟨q,hq,rfl⟩,hz⟩

theorem wrap_perm (A : SectorBCriticalRoleBranchA P) (g : Monomial) :
    SharedCap.Wrap (r A) (s A) (perm g)=perm (boundaryWrap A g) := rfl

theorem source_transverse_pos (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v : ModelSources P.M.base A.reindex) :
    0<(pureSourceNormal A v).1+(pureSourceNormal A v).2.1 := by
  by_contra h
  have hx : (pureSourceNormal A v).1=0 := by omega
  have hy : (pureSourceNormal A v).2.1=0 := by omega
  have hc := v.property.1
  rw [←(pureSourceNormal_spec A v).1] at hc
  have hc' : (pureSourceNormal A v).2.2*routingC P.M.base A.reindex∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    simpa only [monomialDegree,normalizedGrid,hx,hy,zero_mul,zero_add] using hc
  have hb := (boundary_axis_cut_bounds G A hm hl).2 _ hc'
  have hn := (pureSourceNormal_spec A v).2.2
  omega

/-- The only remaining pure-pair cap branch is constructed entirely from
actual sources and critical returns. In particular D*=alpha is retained. -/
def capData (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvz : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) : SharedCap.Data where
  C := d A
  u := r A
  v := s A
  U := boundaryRightCap A hk-r A
  V := boundaryLeftCap A-s A
  C_pos := boundary_d_pos A
  u_pos := (branchA_symmetricTailData A).r_pos
  v_pos := (branchA_symmetricTailData A).s_pos
  U_pos := by have := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck; omega
  V_pos := by have := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck; omega
  originals := originals A
  originals_finite := by
    letI := pure_model_sources_finite A
    exact ((Set.finite_range _).union (Set.finite_singleton _)).image perm
  first := perm (pureSourceNormal A v0)
  first_mem := ⟨_,Or.inl ⟨v0,rfl⟩,rfl⟩
  first_y_pos := hvz
  first_transverse_pos := source_transverse_pos G A hm hl v0
  normal := by
    rintro g ⟨q,hq,rfl⟩
    exact boundaryOriginals_z_lt A hq
  shape := by
    rintro g ⟨q,hq,rfl⟩ hne hy
    rcases hq with ⟨v,rfl⟩ | rfl
    · have hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
          (routingM_pos _ _)*routingM P.M.base A.reindex := by
        intro he
        have he' : v=v0 := Subtype.ext (he.trans hv0.symm)
        exact hne (congrArg (fun w => perm (pureSourceNormal A w)) he')
      have htrans := source_transverse_pos G A hm hl v
      rcases pure_nonfirst_source_plane A v hnf with hx | hyo | hz
      · exact Or.inr ⟨boundary_nonfirst_yz_projection_lower A hk v hnf hx (by omega) hy,hx⟩
      · exact Or.inl ⟨boundary_nonfirst_xz_projection_lower A hk v hnf (by omega) hyo hy,hyo⟩
      · exact (Nat.ne_of_gt hy hz).elim
    · change 0<0 at hy
      omega
  other_wraps := by
    rintro g ⟨q,hq,rfl⟩ hne hy
    rw [zero_generators,wrap_perm,closure_perm]
    rcases hq with ⟨v,rfl⟩ | rfl
    · apply boundary_nonfirst_wrap_in_plane G A hm hk hl v _ hy
      intro he
      have he' : v=v0 := Subtype.ext (he.trans hv0.symm)
      exact hne (congrArg (fun w => perm (pureSourceNormal A w)) he')
    · change 0<0 at hy
      omega
  rectangle := by
    intro i j hi hj
    rw [zero_generators]
    change perm (i,j,0) ∉ SharedCap.Closure (perm '' boundaryPlaneOriginals A)
    rw [closure_perm]
    have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck
    exact boundary_central_rectangle_exclusion G A hm hk v0 hv0 hvz hneck i j (by omega) (by omega)
  central := by
    intro i j hi hj
    rw [zero_generators]
    change (perm (i,j,0) ∉ SharedCap.Closure (perm '' boundaryPlaneOriginals A)) ↔ _
    rw [closure_perm,boundary_central_plane_envelope G A hm hk v0 hv0 hvz hneck i j hi hj]
    have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck
    omega
  attained_x := by
    intro hy
    change 0<(pureSourceNormal A v0).2.1 at hy
    obtain ⟨v,j,hnf,hj,hjd,he⟩ := boundary_right_small_return_cap G A hm hk hl v0 hv0 hy hvz hneck
    refine ⟨perm (pureSourceNormal A v),⟨_,Or.inl ⟨v,rfl⟩,rfl⟩,?_,?_,?_,?_⟩
    · intro hh
      have hc := congrArg (fun p : Monomial => p.2.2) hh
      rw [he] at hc
      change 0=(pureSourceNormal A v0).2.1 at hc
      omega
    · rw [he]; rfl
    · rw [he]; exact hj
    · rw [he]; rfl
  attained_z := by
    intro hx
    change 0<(pureSourceNormal A v0).1 at hx
    obtain ⟨v,j,hnf,hj,hjd,he⟩ := boundary_left_small_return_cap G A hm hk hl v0 hv0 hx hvz hneck
    refine ⟨perm (pureSourceNormal A v),⟨_,Or.inl ⟨v,rfl⟩,rfl⟩,?_,?_,?_,?_⟩
    · intro hh
      have hc := congrArg (fun p : Monomial => p.1) hh
      rw [he] at hc
      change 0=(pureSourceNormal A v0).1 at hc
      omega
    · rw [he]; rfl
    · rw [he]; exact hj
    · rw [he]; rfl

theorem MGenerators_eq (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl v0 hv0 hvz hneck) :
    SharedCap.MGenerators (capData G A hm hk hl v0 hv0 hvz hneck).originals
      (capData G A hm hk hl v0 hv0 hvz hneck).u (capData G A hm hk hl v0 hv0 hvz hneck).v =
      perm '' boundaryStripGenerators A := by
  ext g
  constructor
  · rintro (⟨q,hq,rfl⟩ | ⟨w,⟨q,hq,rfl⟩,hy,rfl⟩)
    · exact ⟨q,Or.inl hq,rfl⟩
    · exact ⟨boundaryWrap A q,Or.inr ⟨q,hq,hy,rfl⟩,rfl⟩
  · rintro ⟨q,(hq | ⟨w,hw,hy,rfl⟩),rfl⟩
    · exact Or.inl ⟨q,hq,rfl⟩
    · exact Or.inr ⟨perm w,⟨w,hw,rfl⟩,hy,rfl⟩

theorem LGenerators_eq (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl v0 hv0 hvz hneck) :
    SharedCap.LGenerators (capData G A hm hk hl v0 hv0 hvz hneck).originals
      (capData G A hm hk hl v0 hv0 hvz hneck).C (capData G A hm hk hl v0 hv0 hvz hneck).u
      (capData G A hm hk hl v0 hv0 hvz hneck).v=perm '' boundaryInitialGenerators A := by
  unfold SharedCap.LGenerators
  rw [MGenerators_eq]
  ext g
  simp only [Set.mem_insert_iff,Set.mem_image,Set.mem_union,Set.mem_singleton_iff,
    boundaryInitialGenerators]
  constructor
  · rintro (rfl | ⟨q,hq,rfl⟩)
    · exact ⟨(0,0,d A),Or.inl rfl,rfl⟩
    · exact ⟨q,Or.inr hq,rfl⟩
  · rintro ⟨q,(rfl | hq),rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨q,hq,rfl⟩

theorem exceptional_perm_iff (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl v0 hv0 hvz hneck) (p : Monomial) :
    perm p ∈ (capData G A hm hk hl v0 hv0 hvz hneck).exceptional ↔
      p ∈ boundaryBorderExceptional A := by
  unfold SharedCap.Data.exceptional
  rw [LGenerators_eq,MGenerators_eq]
  change (SharedCap.Socle (perm '' boundaryInitialGenerators A) (perm p) ∧
    p.2.2+1=d A ∧ SharedCap.Wrap (r A) (s A) (perm p) ∉
      SharedCap.Closure (perm '' boundaryStripGenerators A)) ↔ _
  rw [socle_perm,wrap_perm,closure_perm]
  rfl

theorem additional_perm_iff (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl v0 hv0 hvz hneck) (p : Monomial) :
    perm p ∈ (capData G A hm hk hl v0 hv0 hvz hneck).additionalWraps ↔
      p ∈ BoundarySurvivingWraps A := by
  unfold SharedCap.Data.additionalWraps
  rw [LGenerators_eq]
  change (SharedCap.MinimalGenerator (perm '' boundaryInitialGenerators A) (perm p) ∧
    perm p∉originals A ∧ ∃ g∈originals A, 0<g.2.1 ∧ perm p=SharedCap.Wrap (r A) (s A) g) ↔ _
  rw [minimal_perm]
  constructor
  · rintro ⟨hmin,hno,g,⟨q,hq,rfl⟩,hy,he⟩
    have hep : p=boundaryWrap A q := perm_injective he
    refine ⟨hmin,?_⟩
    rintro (hpure | ho)
    · have hz := congrArg (fun q : Monomial => q.2.2) hpure
      rw [hep] at hz
      have hd := boundary_d_pos A
      change 0=d A at hz
      omega
    · exact hno ⟨p,ho,rfl⟩
  · intro hp
    obtain ⟨v,hv,hy,he⟩ := boundary_surviving_wrap_is_first G A hm hk hl hp
    refine ⟨hp.1,?_,perm (pureSourceNormal A v),⟨_,Or.inl ⟨v,rfl⟩,rfl⟩,hy,?_⟩
    · rintro ⟨q,hq,hqp⟩
      have heq : q=p := perm_injective hqp
      exact hp.2 (Or.inr (heq ▸ hq))
    · rw [he]; rfl

def transportEquiv (S T : Set Monomial) (h : ∀ p, perm p∈T ↔ p∈S) :
    {p // p∈S} ≃ {p // p∈T} where
  toFun p := ⟨perm p.val,(h p.val).mpr p.property⟩
  invFun q := ⟨perm q.val,(h (perm q.val)).mp (by simpa using q.property)⟩
  left_inv p := Subtype.ext rfl
  right_inv q := Subtype.ext rfl

theorem additional_count (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl v0 hv0 hvz hneck) :
    (capData G A hm hk hl v0 hv0 hvz hneck).additionalWraps.ncard=boundarySurvivingWrapCount A := by
  exact (Nat.card_congr (transportEquiv _ _ (additional_perm_iff G A hm hk hl v0 hv0 hvz hneck))).symm

theorem exceptional_count (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl v0 hv0 hvz hneck) :
    (capData G A hm hk hl v0 hv0 hvz hneck).exceptional.ncard=
      Nat.card {p // p∈boundaryBorderExceptional A} := by
  exact (Nat.card_congr (transportEquiv _ _ (exceptional_perm_iff G A hm hk hl v0 hv0 hvz hneck))).symm

theorem full_support_count (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl v0 hv0 hvz hneck) :
    (capData G A hm hk hl v0 hv0 hvz hneck).fullSupport=boundaryFullSourceCount A := by
  classical
  letI := pure_model_sources_finite A
  by_cases hf : 0<(pureSourceNormal A v0).1 ∧ 0<(pureSourceNormal A v0).2.1
  · have hpos : 0<boundaryFullSourceCount A := Nat.card_pos_iff.mpr
      ⟨⟨⟨v0,hf.1,hf.2,hvz⟩⟩,inferInstance⟩
    have hle := boundary_full_source_count_le_one A
    change (if 0<(pureSourceNormal A v0).1 ∧ 0<(pureSourceNormal A v0).2.1 then 1 else 0)=_
    rw [if_pos hf]
    omega
  · have hz := boundary_first_not_full_no_full_source A v0 hv0
      (by intro h; exact hf ⟨h.1,h.2.1⟩)
    change (if 0<(pureSourceNormal A v0).1 ∧ 0<(pureSourceNormal A v0).2.1 then 1 else 0)=_
    rw [if_neg hf,hz]

/-- Exact actual pure-pair compensation by the shared attained-cap theorem.
The only other branches reduce to first-z-zero before any cap construction. -/
theorem boundary_compensation (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    boundarySurvivingWrapCount A+boundaryFullSourceCount A≤
      Nat.card {p // p∈boundaryBorderExceptional A} := by
  exact PurePairGenericDualityAdapter.boundary_compensation G A hm hk hl

end NS25Lean.PurePairCapAdapter

#check NS25Lean.PurePairCapAdapter.boundary_compensation
#print axioms NS25Lean.PurePairCapAdapter.capData
#print axioms NS25Lean.PurePairCapAdapter.additional_count
#print axioms NS25Lean.PurePairCapAdapter.exceptional_count
#print axioms NS25Lean.PurePairCapAdapter.full_support_count
#print axioms NS25Lean.PurePairCapAdapter.boundary_compensation
