import NS25Lean.P2SectorCPureBoundarySourceQuotientR40

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR41
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR29 L5A2C4OR39 L5A2C4OR40 FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The internal pure relation, actual source normals, and the actual live
boundary endpoint. The conditional is component status, not a numeric gate. -/
def pureInternalSourceIdeal (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k] :
    Ideal (ToricPresentation.Poly k 3) := by
  classical
  exact Ideal.span (
    {roleMonomial k A.reindex (0,alpha A,0)-roleMonomial k A.reindex (beta A,0,0)} ∪
    Set.range (fun v : ModelSources P.M.base A.reindex =>
      roleMonomial k A.reindex (pureSourceNormal A v)) ∪
    {if BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent
      then roleMonomial k A.reindex (r A,s A,0)
      else roleMonomial k A.reindex (0,0,d A)})

/-- Below the boundary degree source generation uses only the internal
pure relation; neither the boundary binomial nor IH is used. -/
theorem cut_below_boundary_mem (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) (hz : monomialDegree P.M.base A.reindex z ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    (hlt : monomialDegree P.M.base A.reindex z < d A * routingC P.M.base A.reindex) :
    roleMonomial k A.reindex z ∈ pureInternalSourceIdeal A k := by
  obtain ⟨v,t,ht,he⟩ := cut_source_cover _ _ _ hz
  obtain ⟨x,y,z',hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  let g := pureSourceNormal A v
  let w : Monomial := (x,y,z')
  have hdeg : monomialDegree P.M.base A.reindex z=
      monomialDegree P.M.base A.reindex (g+w) := by
    rw [monomialDegree_add,(pureSourceNormal_spec A v).1]
    exact he.trans (congrArg (v.val+ ·) hfac)
  have hc : 0 < routingC P.M.base A.reindex := by
    simpa only [routingC_eq_n2] using (branchA_symmetricTailData A).n2_pos
  have bounds (u : Monomial) (hu : monomialDegree P.M.base A.reindex u=
      monomialDegree P.M.base A.reindex z) : u.2.2<d A := by
    have hh := hlt
    rw [←hu] at hh
    simp only [monomialDegree,normalizedGrid] at hh
    nlinarith [Nat.zero_le (u.1*routingA P.M.base A.reindex),
      Nat.zero_le (u.2.1*routingB P.M.base A.reindex)]
  have hd := bounded_z_fiber_internal A k (bounds z rfl) (bounds (g+w) hdeg.symm) hdeg
  have hd' : roleMonomial k A.reindex z-roleMonomial k A.reindex (g+w) ∈
      pureInternalSourceIdeal A k := by
    apply (show Ideal.span {roleMonomial k A.reindex (0,alpha A,0)-
      roleMonomial k A.reindex (beta A,0,0)} ≤ pureInternalSourceIdeal A k from ?_) hd
    apply Ideal.span_le.mpr
    rintro f rfl
    exact Ideal.subset_span (Or.inl (Or.inl rfl))
  have hm : roleMonomial k A.reindex (g+w) ∈ pureInternalSourceIdeal A k := by
    rw [roleMonomial_add]
    exact (pureInternalSourceIdeal A k).mul_mem_right _
      (Ideal.subset_span (Or.inl (Or.inr ⟨v,rfl⟩)))
  simpa only [sub_add_cancel] using (pureInternalSourceIdeal A k).add_mem hd' hm

theorem mixed_boundary_degree_scale (A : SectorBCriticalRoleBranchA P) :
    routingD P.M.base A.reindex*(d A * routingC P.M.base A.reindex)=A.mixedDegree := by
  have hs := (branchA_symmetricTailData A).c2_eq_d
  have he := A.mixed.degree_eq_critical
  rw [←A.reindex_two] at he
  have hc : routingD P.M.base A.reindex*routingC P.M.base A.reindex =
      weights P.M.base (A.reindex 2) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base A.reindex 0 0 1
  change criticalExponent P.M.base (A.reindex 2)=d A at hs
  rw [hs] at he
  rw [he,←hc]
  ring

/-- A genuine killed endpoint is generated through its strict predecessor.
The returned cut membership also establishes soundness independently. -/
theorem endpoint_from_predecessor (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (z : Monomial) (hz : monomialDegree P.M.base A.reindex z = d A * routingC P.M.base A.reindex)
    (i : Fin 3) (hi : 0 < roleExponent A.reindex z (A.reindex i))
    (hk : A.mixedDegree - weights P.M.base (A.reindex i) ∈ P.M.base.K) :
    monomialDegree P.M.base A.reindex z ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) ∧
    roleMonomial k A.reindex z ∈ pureInternalSourceIdeal A k := by
  let u : Monomial := ![(1,0,0),(0,1,0),(0,0,1)] i
  let p : Monomial := (z.1-u.1,z.2.1-u.2.1,z.2.2-u.2.2)
  have hsum : p+u=z := by
    fin_cases i <;> simp [roleExponent] at hi <;> ext <;> simp [p,u] <;> omega
  have hscale : routingD P.M.base A.reindex*monomialDegree P.M.base A.reindex u =
      weights P.M.base (A.reindex i) := by
    fin_cases i
    · simpa [u,monomialDegree,normalizedGrid,gridDegree] using
        normalizedGrid_scale P.M.base A.reindex 1 0 0
    · simpa [u,monomialDegree,normalizedGrid,gridDegree] using
        normalizedGrid_scale P.M.base A.reindex 0 1 0
    · simpa [u,monomialDegree,normalizedGrid,gridDegree] using
        normalizedGrid_scale P.M.base A.reindex 0 0 1
  have hup : 0 < monomialDegree P.M.base A.reindex u := by
    have hh := weights_positive P.M.base (A.reindex i)
    rw [←hscale] at hh
    nlinarith
  have hdeg := monomialDegree_add P.M.base A.reindex p u
  rw [hsum,hz] at hdeg
  have hpScale : routingD P.M.base A.reindex*monomialDegree P.M.base A.reindex p=
      A.mixedDegree - weights P.M.base (A.reindex i) := by
    have hh := mixed_boundary_degree_scale A
    rw [hdeg,Nat.mul_add,hscale] at hh
    omega
  have hpCut : monomialDegree P.M.base A.reindex p ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    apply (actual_scaled_cut_iff _ _ _).mpr
    rwa [hpScale]
  have hm := cut_below_boundary_mem A k p hpCut (by omega)
  have hpK := (actual_scaled_cut_iff _ _ _).mp hpCut
  have hactualH : weights P.M.base (A.reindex i) ∈ P.M.base.H := by
    have ht := (Presentation.factorizationMap P.M.base.tailDegrees
      (Finsupp.single (A.reindex i) 1)).property
    rw [←weight_eq_degree,weight_single,one_mul] at ht
    exact ht
  have hsumK := aperyTail_add_mem P.M.base.H_le hpK hactualH
  have htotal : routingD P.M.base A.reindex*monomialDegree P.M.base A.reindex p+
      weights P.M.base (A.reindex i)=routingD P.M.base A.reindex*
      monomialDegree P.M.base A.reindex z := by
    rw [←hscale,←Nat.mul_add,←monomialDegree_add,hsum]
  refine ⟨(actual_scaled_cut_iff _ _ _).mpr (htotal ▸ hsumK),?_⟩
  rw [←hsum,roleMonomial_add]
  exact (pureInternalSourceIdeal A k).mul_mem_right _ hm

theorem boundary_has_killed_endpoint (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree = 1) :
    BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent ∨
      BoundaryKilled P.M A.mixedDegree A.mixed.mixedComponent := by
  obtain ⟨K,_⟩ := Nat.card_eq_one_iff_exists.mp hk
  obtain ⟨C,D,hne,hset⟩ := Nat.card_eq_two_iff.mp A.mixed.componentCount_eq_two
  have hall (F : FiberComponent P.M.base A.mixedDegree) : F=C ∨ F=D := by
    have hh : F ∈ ({C,D} : Set (FiberComponent P.M.base A.mixedDegree)) :=
      hset.symm ▸ Set.mem_univ F
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hh
  have hor : K.val=A.mixed.pureComponent ∨ K.val=A.mixed.mixedComponent := by
    have := A.mixed.components_ne
    rcases hall K.val with he | he <;> rcases hall A.mixed.pureComponent with hp | hp <;>
      rcases hall A.mixed.mixedComponent with hm | hm <;> grind
  rcases hor with he | he
  · exact Or.inl (he ▸ K.property)
  · exact Or.inr (he ▸ K.property)

theorem pure_endpoint_of_killed (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (hk : BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent) :
    d A * routingC P.M.base A.reindex ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) ∧
    roleMonomial k A.reindex (0,0,d A) ∈ pureInternalSourceIdeal A k := by
  have hp := (killed_iff_singleton_predecessor P.M A.mixedDegree A.mixed.pureComponent
    A.mixed.pureRole A.mixed.pureSupport).mp hk
  rw [←A.reindex_two] at hp
  have hd : 0 < d A := by
    have hh := (branchA_symmetricTailData A).n0_pos
    rw [(branchA_symmetricTailData A).n0_eq] at hh
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hh)
  simpa [monomialDegree,normalizedGrid] using endpoint_from_predecessor A k (0,0,d A)
    (by simp [monomialDegree,normalizedGrid]) 2 (by simpa [roleExponent] using hd) hp

theorem mixed_endpoint_of_killed (A : SectorBCriticalRoleBranchA P) (k : Type*) [Field k]
    (hk : BoundaryKilled P.M A.mixedDegree A.mixed.mixedComponent) :
    d A * routingC P.M.base A.reindex ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) ∧
    roleMonomial k A.reindex (r A,s A,0) ∈ pureInternalSourceIdeal A k := by
  obtain ⟨j,hj,hpred⟩ := (killed_iff_support_predecessor P.M A.mixedDegree
    A.mixed.mixedComponent).mp hk
  have hz : A.mixed.witness.val (A.reindex 2)=0 := by
    rw [A.reindex_two]; exact A.mixed.witness_pure_zero
  have he : roleExponent A.reindex (r A,s A,0)=A.mixed.witness.val := by
    simpa only [r,s,hz] using roleExponent_coordinates A.reindex A.mixed.witness.val
  have hp := A.mixed.witness_pos_of_mem_mixedSupport j hj
  obtain ⟨i,rfl⟩ := A.reindex.surjective j
  have hdeg : monomialDegree P.M.base A.reindex (r A,s A,0)=
      d A * routingC P.M.base A.reindex := by
    simpa [monomialDegree,normalizedGrid,routingA_eq_n0,routingB_eq_n1,routingC_eq_n2]
      using (branchA_symmetricTailData A).mixed_relation.symm
  simpa only [hdeg] using endpoint_from_predecessor A k (r A,s A,0) hdeg i (he ▸ hp) hpred

/-- Both endpoints belong after independently recovering the killed one;
the other is the explicit live generator. -/
theorem boundary_endpoints_mem (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree = 1) (k : Type*) [Field k] :
    roleMonomial k A.reindex (0,0,d A) ∈ pureInternalSourceIdeal A k ∧
      roleMonomial k A.reindex (r A,s A,0) ∈ pureInternalSourceIdeal A k := by
  classical
  by_cases hp : BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent
  · refine ⟨(pure_endpoint_of_killed A k hp).2,?_⟩
    exact Ideal.subset_span (Or.inr (by simp [hp]))
  · refine ⟨?_,(mixed_endpoint_of_killed A k
      ((boundary_has_killed_endpoint A hk).resolve_left hp)).2⟩
    exact Ideal.subset_span (Or.inr (by simp [hp]))

theorem toric_le_internal_candidate (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree = 1) (k : Type*) [Field k] :
    P.M.base.IH k ≤ pureInternalSourceIdeal A k := by
  rw [pure_tail_toric_exact A k]
  apply Ideal.span_le.mpr
  intro f hf
  rcases hf with rfl | hf
  · exact Ideal.subset_span (Or.inl (Or.inl rfl))
  · rcases hf with rfl
    exact (pureInternalSourceIdeal A k).sub_mem (boundary_endpoints_mem A hk k).1
      (boundary_endpoints_mem A hk k).2

theorem cut_monomial_mem_internal_candidate (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree = 1) (k : Type*) [Field k]
    (z : Monomial) (hz : monomialDegree P.M.base A.reindex z ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    roleMonomial k A.reindex z ∈ pureInternalSourceIdeal A k := by
  obtain ⟨v,t,ht,he⟩ := cut_source_cover _ _ _ hz
  obtain ⟨x,y,z',hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  let g := pureSourceNormal A v
  let w : Monomial := (x,y,z')
  have hdeg : monomialDegree P.M.base A.reindex z=
      monomialDegree P.M.base A.reindex (g+w) := by
    rw [monomialDegree_add,(pureSourceNormal_spec A v).1]
    exact he.trans (congrArg (v.val+ ·) hfac)
  have hdiff := pure_tail_equal_degree_binomial A k hdeg
  have hm : roleMonomial k A.reindex (g+w) ∈ pureInternalSourceIdeal A k := by
    rw [roleMonomial_add]
    exact (pureInternalSourceIdeal A k).mul_mem_right _
      (Ideal.subset_span (Or.inl (Or.inr ⟨v,rfl⟩)))
  have hd : roleMonomial k A.reindex z-roleMonomial k A.reindex (g+w) ∈
      pureInternalSourceIdeal A k := by
    apply toric_le_internal_candidate A hk k
    rw [pure_tail_toric_exact A k]
    exact hdiff
  simpa only [sub_add_cancel] using (pureInternalSourceIdeal A k).add_mem hd hm

theorem internal_candidate_le_J (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree = 1) (k : Type*) [Field k] :
    pureInternalSourceIdeal A k ≤ P.M.base.J k := by
  classical
  have hIH : P.M.base.IH k ≤ P.M.base.J k := by
    rw [Data.J_eq_IH_sup_MK]; exact le_sup_left
  have hcut : d A * routingC P.M.base A.reindex ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    rcases boundary_has_killed_endpoint A hk with hp | hm
    · exact (pure_endpoint_of_killed A k hp).1
    · exact (mixed_endpoint_of_killed A k hm).1
  have hpure : roleMonomial k A.reindex (0,0,d A) ∈ P.M.base.J k := by
    apply L2B2A2.boundary_monomial_mem_J
    rw [roleExponent_weight]
    apply (actual_scaled_cut_iff _ _ _).mp
    simpa [monomialDegree,normalizedGrid] using hcut
  have hmixed : roleMonomial k A.reindex (r A,s A,0) ∈ P.M.base.J k := by
    apply L2B2A2.boundary_monomial_mem_J
    rw [roleExponent_weight]
    apply (actual_scaled_cut_iff _ _ _).mp
    have he := (branchA_symmetricTailData A).mixed_relation
    simpa [monomialDegree,normalizedGrid,routingA_eq_n0,routingB_eq_n1,routingC_eq_n2,he] using hcut
  apply Ideal.span_le.mpr
  intro f hf
  rcases hf with (hf | ⟨v,rfl⟩) | hf
  · rcases hf with rfl
    apply hIH
    rw [pure_tail_toric_exact A k]
    exact Ideal.subset_span (Or.inl rfl)
  · apply L2B2A2.boundary_monomial_mem_J
    rw [roleExponent_weight,(pureSourceNormal_spec A v).1]
    exact (actual_scaled_cut_iff _ _ _).mp v.property.1
  · rcases hf with rfl
    split_ifs <;> assumption

/-- Actual J equality in either boundary orientation. -/
theorem internal_source_quotient_exact (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree = 1) (k : Type*) [Field k] :
    P.M.base.J k=pureInternalSourceIdeal A k := by
  apply le_antisymm
  · rw [Data.J_eq_IH_sup_MK]
    apply sup_le (toric_le_internal_candidate A hk k)
    have hl : (P.M.base.MK k).restrictScalars k ≤
        (pureInternalSourceIdeal A k).restrictScalars k := by
      rw [L2B2A2.MK_eq_span_boundaryMonomials]
      apply Submodule.span_le.mpr
      rintro f ⟨u,hu,rfl⟩
      let z : Monomial := (u (A.reindex 0),u (A.reindex 1),u (A.reindex 2))
      have he : roleExponent A.reindex z=u := roleExponent_coordinates A.reindex u
      have hc : monomialDegree P.M.base A.reindex z ∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
        apply (actual_scaled_cut_iff _ _ _).mpr
        rwa [←roleExponent_weight,he]
      change MvPolynomial.monomial u (1 : k) ∈ pureInternalSourceIdeal A k
      simpa only [roleMonomial,he] using cut_monomial_mem_internal_candidate A hk k z hc
    exact hl
  · exact internal_candidate_le_J A hk k

/-- The original unrestricted P/G binder; the boundary killed count is
derived from the actual fiber signature, not supplied to this theorem. -/
theorem internal_all_pure_source_quotient (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp ≠ bm) (hp : IsPureBoundaryComponent G bp)
    (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G, (componentSupport P.M.base G.internalDegree C).card=1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.internalDegree ∧ A.mixedDegree=G.boundaryDegree ∧
      ∀ (k : Type*) [Field k], P.M.base.J k=pureInternalSourceIdeal A k := by
  obtain ⟨A,ha,hb,_⟩ := internal_all_pure_geometry P G bp bm hne hp hm hi
  refine ⟨A,ha,hb,fun k _ => internal_source_quotient_exact A ?_ k⟩
  rw [hb]
  exact G.boundarySignature.2

end NS25Lean.L5A2C4OR41
