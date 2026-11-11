import NS25Lean.P2PurePairGenericDualityAdapter

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.PurePairGenericDualityAdapter
open Classical FourGeneratedBridge ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR33 L5A2C4OR35
  L5A2C4OR39 L5A2C4OR40 L5A2C4OR42 L5A2C4OR43 L5A2C4OR44 L5A2C4OR46 L5A2C4OR47
  ErasedSourceScreen PureInternalTransverse CriticalCapGeometry
  CriticalPresentationModes CriticalFullSignature GenericCriticalCompensation
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

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

theorem wrap_perm (A : SectorBCriticalRoleBranchA P) (g : Monomial) :
    SharedCap.Wrap (r A) (s A) (perm g)=perm (boundaryWrap A g) := rfl

theorem MGenerators_eq (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl) :
    SharedCap.MGenerators (GenericCriticalDuality.family (actualFront G A hm hk hl))
      (actualBase A).u (actualBase A).v=perm '' boundaryStripGenerators A := by
  rw [actual_family]
  ext g
  constructor
  · rintro (⟨q,hq,rfl⟩ | ⟨w,⟨q,hq,rfl⟩,hy,rfl⟩)
    · exact ⟨q,Or.inl hq,rfl⟩
    · exact ⟨boundaryWrap A q,Or.inr ⟨q,hq,hy,rfl⟩,rfl⟩
  · rintro ⟨q,(hq | ⟨w,hw,hy,rfl⟩),rfl⟩
    · exact Or.inl ⟨q,hq,rfl⟩
    · exact Or.inr ⟨perm w,⟨w,hw,rfl⟩,hy,rfl⟩

theorem LGenerators_eq (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl) :
    SharedCap.LGenerators (GenericCriticalDuality.family (actualFront G A hm hk hl))
      (actualBase A).C (actualBase A).u (actualBase A).v=perm '' boundaryInitialGenerators A := by
  unfold SharedCap.LGenerators
  rw [MGenerators_eq,base_C]
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
    (hm hk hl) (p : Monomial) :
    perm p∈GenericCriticalDuality.exceptional (actualFront G A hm hk hl) ↔ p∈boundaryBorderExceptional A := by
  unfold GenericCriticalDuality.exceptional
  rw [LGenerators_eq,MGenerators_eq,base_C]
  change (SharedCap.Socle (perm '' boundaryInitialGenerators A) (perm p) ∧
    p.2.2+1=d A ∧ SharedCap.Wrap (r A) (s A) (perm p) ∉
      SharedCap.Closure (perm '' boundaryStripGenerators A)) ↔ _
  rw [socle_perm,wrap_perm,closure_perm]
  rfl

theorem additional_perm_iff (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl) (p : Monomial) :
    perm p∈GenericCriticalDuality.additional (actualFront G A hm hk hl) ↔ p∈BoundarySurvivingWraps A := by
  unfold GenericCriticalDuality.additional
  rw [LGenerators_eq,actual_family]
  change (SharedCap.MinimalGenerator (perm '' boundaryInitialGenerators A) (perm p) ∧
    perm p∉perm '' boundaryOriginals A ∧ ∃ g∈perm '' boundaryOriginals A,
      0<g.2.1 ∧ perm p=SharedCap.Wrap (r A) (s A) g) ↔ _
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
    obtain ⟨g,hg,hxp,hyp,hzp⟩ := hp.1.1
    have heq : g=p := hp.1.2 g ⟨g,hg,le_rfl,le_rfl,le_rfl⟩ hxp hyp hzp
    rw [heq] at hg
    rcases hg with hlead | (ho | ⟨g,hg,hy,he⟩)
    · exact (hp.2 (Or.inl hlead)).elim
    · exact (hp.2 (Or.inr ho)).elim
    · refine ⟨hp.1,?_,perm g,⟨g,hg,rfl⟩,hy,?_⟩
      · rintro ⟨q,hq,hqp⟩
        have heqp : q=p := perm_injective hqp
        exact hp.2 (Or.inr (heqp ▸ hq))
      · rw [he]; rfl

def transportEquiv (S T : Set Monomial) (h : ∀ p, perm p∈T ↔ p∈S) :
    {p // p∈S} ≃ {p // p∈T} where
  toFun p := ⟨perm p.val,(h p.val).mpr p.property⟩
  invFun q := ⟨perm q.val,(h (perm q.val)).mp (by simpa using q.property)⟩
  left_inv p := Subtype.ext rfl
  right_inv q := Subtype.ext rfl

theorem additional_count (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl) : (GenericCriticalDuality.additional (actualFront G A hm hk hl)).ncard=boundarySurvivingWrapCount A :=
  (Nat.card_congr (transportEquiv _ _ (additional_perm_iff G A hm hk hl))).symm

theorem exceptional_count (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl) : (GenericCriticalDuality.exceptional (actualFront G A hm hk hl)).ncard=
      Nat.card {z // z∈boundaryBorderExceptional A} :=
  (Nat.card_congr (transportEquiv _ _ (exceptional_perm_iff G A hm hk hl))).symm

theorem full_source_count (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm hk hl) : GenericCriticalDuality.fullSupport (actualFront G A hm hk hl)=boundaryFullSourceCount A := by
  rw [GenericCriticalDuality.fullSupport_source_count]
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight (fun v => ?_)
  change (0<((actualBase A).norm v) 0 ∧ 0<((actualBase A).norm v) 1 ∧ 0<((actualBase A).norm v) 2) ↔
    (0<(pureSourceNormal A v).1 ∧ 0<(pureSourceNormal A v).2.1 ∧ 0<(pureSourceNormal A v).2.2)
  have he := actual_normal_tuple G A hm hk hl v
  change tuple ((actualBase A).norm v)=perm (pureSourceNormal A v) at he
  have h0 := congrArg (fun p : Monomial => p.1) he
  have h1 := congrArg (fun p : Monomial => p.2.1) he
  have h2 := congrArg (fun p : Monomial => p.2.2) he
  change ((actualBase A).norm v) 0=(pureSourceNormal A v).1 at h0
  change ((actualBase A).norm v) 1=(pureSourceNormal A v).2.2 at h1
  change ((actualBase A).norm v) 2=(pureSourceNormal A v).2.1 at h2
  rw [h0,h1,h2]
  tauto

/-- The original pure-pair branch is a direct instance of the whole common
critical-return theorem under the literal X,Z,Y transport. -/
theorem boundary_compensation (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    boundarySurvivingWrapCount A+boundaryFullSourceCount A≤Nat.card {z // z∈boundaryBorderExceptional A} := by
  have h := GenericCriticalDuality.compensation (actualFront G A hm hk hl)
  rw [additional_count,full_source_count,exceptional_count] at h
  exact h

end NS25Lean.PurePairGenericDualityAdapter
