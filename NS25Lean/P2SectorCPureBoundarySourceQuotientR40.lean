import NS25Lean.P2SectorCPureSourceFiberR39

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR40
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR29 L5A2C4OR39 FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

/-- Every actual cut degree descends to an actual minimal source. -/
theorem cut_source_cover (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (n : ℕ)
    (hn : n ∈ cyclicCut (routingH B e) (routingM B e)) :
    ∃ v : ModelSources B e, ∃ t : ℕ, t ∈ routingH B e ∧ n=v.val+t := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : IsMinimalTailGenerator (routingH B e).toAddSubmonoid
        (cyclicCut (routingH B e) (routingM B e)) n
    · exact ⟨⟨n,hs⟩,0,(routingH B e).zero_mem,by simp⟩
    have hnot : ¬∀ y t : ℕ, y ∈ cyclicCut (routingH B e) (routingM B e) →
        t ∈ routingH B e → n=y+t → t=0 := by
      intro hm
      exact hs ((minimalTail_iff_literal _ _ _).mpr ⟨hn,hm⟩)
    push Not at hnot
    obtain ⟨y,t,hy,ht,he,hne⟩ := hnot
    obtain ⟨v,u,hu,hvu⟩ := ih y (by omega) hy
    exact ⟨v,u+t,(routingH B e).add_mem hu ht,by omega⟩

/-- Critical minimality gives pure rigidity strictly below the critical exponent.
This lemma uses no toric-ideal membership or pure-pair relation. -/
theorem factorization_below_critical_is_pure (B : Data Gamma) (j : Fin 3)
    {n : ℕ} (hn : n < criticalExponent B j) (u : Fin 3 →₀ ℕ)
    (hu : weight B u=n*weights B j) : u=Finsupp.single j n := by
  let c := criticalExponent B j
  have hw : weight B (u+Finsupp.single j (c-n))=c*weights B j := by
    rw [map_add,weight_single,hu,←Nat.add_mul,Nat.add_sub_of_le (Nat.le_of_lt hn)]
  have hp : 0 < (u+Finsupp.single j (c-n)) j := by
    simp only [Finsupp.add_apply,Finsupp.single_eq_same]
    omega
  have he := congrArg Subtype.val
    (L5A2C4B.factorization_eq_criticalPure_of_coord_pos B j ⟨_,hw⟩ hp)
  change u+Finsupp.single j (c-n)=Finsupp.single j c at he
  ext i
  have hi := congrArg (fun w : Fin 3 →₀ ℕ => w i) he
  by_cases hij : i=j
  · subst i
    simp only [Finsupp.add_apply,Finsupp.single_eq_same] at hi ⊢
    omega
  · simpa [Finsupp.add_apply,Finsupp.single_apply,Ne.symm hij,hij] using hi

private theorem killed_x_predecessor {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    (beta A-1)*routingA P.M.base A.reindex ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
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

/-- The killed x endpoint is recovered using a source divisor below criticality,
independently of IH and of the omitted pure-pair binomial. -/
theorem killed_x_monomial_mem {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k] :
    roleMonomial k A.reindex (beta A,0,0) ∈ pureBoundarySourceIdeal A k := by
  obtain ⟨v,t,ht,he⟩ := cut_source_cover _ _ _ (killed_x_predecessor A hk)
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  let g := pureSourceNormal A v
  let w : Monomial := (x,y,z)
  have hg : monomialDegree P.M.base A.reindex g=v.val := (pureSourceNormal_spec A v).1
  have hw : monomialDegree P.M.base A.reindex w=t := hfac.symm
  have hdeg : monomialDegree P.M.base A.reindex (g+w)=
      (beta A-1)*routingA P.M.base A.reindex := by
    rw [monomialDegree_add,hg,hw,←he]
  have hs := (branchA_symmetricTailData A).c0_eq_beta
  change criticalExponent P.M.base (A.reindex 0)=beta A at hs
  have hb : 0 < beta A := by
    have h := (branchA_symmetricTailData A).n1_pos
    rw [(branchA_symmetricTailData A).n1_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have ha : routingD P.M.base A.reindex*routingA P.M.base A.reindex =
      weights P.M.base (A.reindex 0) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base A.reindex 1 0 0
  have hu : weight P.M.base (roleExponent A.reindex (g+w))=
      (beta A-1)*weights P.M.base (A.reindex 0) := by
    rw [roleExponent_weight,hdeg,←ha]; ring
  have hp := factorization_below_critical_is_pure _ _
    (by rw [hs]; omega : beta A-1 < criticalExponent P.M.base (A.reindex 0)) _ hu
  have hx := congrArg (fun u : Fin 3 →₀ ℕ => u (A.reindex 0)) hp
  have hy := congrArg (fun u : Fin 3 →₀ ℕ => u (A.reindex 1)) hp
  have hz := congrArg (fun u : Fin 3 →₀ ℕ => u (A.reindex 2)) hp
  simp [roleExponent] at hx hy hz
  have hgy : g.2.1=0 := hy.1
  have hgz : g.2.2=0 := hz.1
  have hgle : g.1 ≤ beta A := by simp [w] at hx; omega
  have hsum : g+(beta A-g.1,0,0)=(beta A,0,0) := by
    ext <;> simp [hgy,hgz,Nat.add_sub_of_le hgle]
  have hm : roleMonomial k A.reindex g ∈ pureBoundarySourceIdeal A k :=
    Ideal.subset_span (Or.inl (Or.inr ⟨v,rfl⟩))
  rw [←hsum,roleMonomial_add]
  exact (pureBoundarySourceIdeal A k).mul_mem_right _ hm

private theorem internal_mem {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (k : Type*) [Field k] :
    roleMonomial k A.reindex (0,0,d A)-roleMonomial k A.reindex (r A,s A,0) ∈
      pureBoundarySourceIdeal A k :=
  Ideal.subset_span (Or.inl (Or.inl rfl))

/-- Recover the full original toric ideal only after the independent killed endpoint. -/
theorem toric_le_boundary_candidate {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k] :
    P.M.base.IH k ≤ pureBoundarySourceIdeal A k := by
  rw [pure_tail_toric_exact A k]
  apply Ideal.span_le.mpr
  intro f hf
  rcases hf with rfl | hf
  · exact (pureBoundarySourceIdeal A k).sub_mem
      (Ideal.subset_span (Or.inr rfl)) (killed_x_monomial_mem A hk k)
  · rcases hf with rfl
    exact internal_mem A k

/-- All cut monomials are generated by sources modulo the already recovered IH. -/
theorem cut_monomial_mem_boundary_candidate {P : P2Data Gamma}
    (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k]
    (z : Monomial) (hz : monomialDegree P.M.base A.reindex z ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    roleMonomial k A.reindex z ∈ pureBoundarySourceIdeal A k := by
  obtain ⟨v,t,ht,he⟩ := cut_source_cover _ _ _ hz
  obtain ⟨x,y,z',hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  let g := pureSourceNormal A v
  let w : Monomial := (x,y,z')
  have hdeg : monomialDegree P.M.base A.reindex z=
      monomialDegree P.M.base A.reindex (g+w) := by
    rw [monomialDegree_add,(pureSourceNormal_spec A v).1]
    exact he.trans (congrArg (v.val+ ·) hfac)
  have hdiff := pure_tail_equal_degree_binomial A k hdeg
  have hm : roleMonomial k A.reindex (g+w) ∈ pureBoundarySourceIdeal A k := by
    rw [roleMonomial_add]
    exact (pureBoundarySourceIdeal A k).mul_mem_right _
      (Ideal.subset_span (Or.inl (Or.inr ⟨v,rfl⟩)))
  have hd : roleMonomial k A.reindex z-roleMonomial k A.reindex (g+w) ∈
      pureBoundarySourceIdeal A k := by
    apply toric_le_boundary_candidate A hk k
    rw [pure_tail_toric_exact A k]
    exact hdiff
  simpa only [sub_add_cancel] using (pureBoundarySourceIdeal A k).add_mem hd hm

/-- The actual J, not IH, contains all three candidate generator classes. -/
theorem boundary_candidate_le_J {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k] :
    pureBoundarySourceIdeal A k ≤ P.M.base.J k := by
  have hIH : P.M.base.IH k ≤ P.M.base.J k := by
    rw [Data.J_eq_IH_sup_MK]; exact le_sup_left
  have hcut : beta A*routingA P.M.base A.reindex ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    have hp := (actual_scaled_cut_iff _ _ _).mp (killed_x_predecessor A hk)
    have ha : routingD P.M.base A.reindex*routingA P.M.base A.reindex =
        weights P.M.base (A.reindex 0) := by
      simpa [normalizedGrid,gridDegree] using normalizedGrid_scale P.M.base A.reindex 1 0 0
    have hb : 0 < beta A := by
      have h := (branchA_symmetricTailData A).n1_pos
      rw [(branchA_symmetricTailData A).n1_eq] at h
      exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
    have hwH : weights P.M.base (A.reindex 0) ∈ P.M.base.H := by
      have ht := (Presentation.factorizationMap P.M.base.tailDegrees
        (Finsupp.single (A.reindex 0) 1)).property
      rw [←weight_eq_degree,weight_single,one_mul] at ht
      exact ht
    have hp' := aperyTail_add_mem P.M.base.H_le hp hwH
    apply (actual_scaled_cut_iff _ _ _).mpr
    have he : routingD P.M.base A.reindex*((beta A-1)*routingA P.M.base A.reindex)+
        weights P.M.base (A.reindex 0)=
        routingD P.M.base A.reindex*(beta A*routingA P.M.base A.reindex) := by
      rw [←ha,←Nat.mul_add]; congr 1
      calc
        _ = (beta A-1+1)*routingA P.M.base A.reindex := by ring
        _ = _ := by congr 1; omega
    rwa [he] at hp'
  apply Ideal.span_le.mpr
  intro f hf
  rcases hf with (hf | ⟨v,rfl⟩) | hf
  · rcases hf with rfl
    apply hIH
    rw [pure_tail_toric_exact A k]
    exact Ideal.subset_span (Or.inr rfl)
  · apply L2B2A2.boundary_monomial_mem_J
    rw [roleExponent_weight,(pureSourceNormal_spec A v).1]
    exact (actual_scaled_cut_iff _ _ _).mp v.property.1
  · rcases hf with rfl
    apply L2B2A2.boundary_monomial_mem_J
    rw [roleExponent_weight]
    apply (actual_scaled_cut_iff _ _ _).mp
    have he := (branchA_symmetricTailData A).pure_relation
    simpa [monomialDegree,normalizedGrid,routingA_eq_n0,routingB_eq_n1,he] using hcut

/-- Actual polynomial ideal equality at the killed-x/alive-y pure boundary. -/
theorem boundary_source_quotient_exact {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) (k : Type*) [Field k] :
    P.M.base.J k=pureBoundarySourceIdeal A k := by
  apply le_antisymm
  · rw [Data.J_eq_IH_sup_MK]
    apply sup_le (toric_le_boundary_candidate A hk k)
    have hl : (P.M.base.MK k).restrictScalars k ≤
        (pureBoundarySourceIdeal A k).restrictScalars k := by
      rw [L2B2A2.MK_eq_span_boundaryMonomials]
      apply Submodule.span_le.mpr
      rintro f ⟨u,hu,rfl⟩
      let z : Monomial := (u (A.reindex 0),u (A.reindex 1),u (A.reindex 2))
      have he : roleExponent A.reindex z=u := roleExponent_coordinates A.reindex u
      have hc : monomialDegree P.M.base A.reindex z ∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
        apply (actual_scaled_cut_iff _ _ _).mpr
        rwa [←roleExponent_weight,he]
      change MvPolynomial.monomial u (1 : k) ∈ pureBoundarySourceIdeal A k
      simpa only [roleMonomial,he] using cut_monomial_mem_boundary_candidate A hk k z hc
    exact hl
  · exact boundary_candidate_le_J A hk k

/-- Original unrestricted P/G/all-pure target, over every field. -/
theorem boundary_all_pure_source_quotient (P : P2Data Gamma) (G : SectorCActualFibers P)
    (h : ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.boundaryDegree ∧ A.mixedDegree=G.internalDegree ∧
      BoundaryKilled P.M A.pairDegree A.pair.leftComponent ∧
      ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent ∧
      ∀ (k : Type*) [Field k], P.M.base.J k=pureBoundarySourceIdeal A k := by
  obtain ⟨A,hp,hm,hk,ha,_⟩ := boundary_all_pure_geometry P G h
  exact ⟨A,hp,hm,hk,ha,fun k _ => boundary_source_quotient_exact A hk k⟩

/-- Optional internal-all-pure continuation: below the boundary z exponent,
all equal-degree moves use only the internal pure relation. No source or
Sector-B counting premise is used. -/
theorem bounded_z_fiber_internal {P : P2Data Gamma} (A : SectorBCriticalRoleBranchA P)
    (k : Type*) [Field k] {z w : Monomial} (hz : z.2.2 < d A) (hw : w.2.2 < d A)
    (he : monomialDegree P.M.base A.reindex z=monomialDegree P.M.base A.reindex w) :
    roleMonomial k A.reindex z-roleMonomial k A.reindex w ∈ Ideal.span
      {roleMonomial k A.reindex (0,alpha A,0)-roleMonomial k A.reindex (beta A,0,0)} := by
  let I : Ideal (ToricPresentation.Poly k 3) := Ideal.span
    {roleMonomial k A.reindex (0,alpha A,0)-roleMonomial k A.reindex (beta A,0,0)}
  let q (t : Monomial) := Ideal.Quotient.mk I (roleMonomial k A.reindex t)
  have qadd (t u : Monomial) : q (t+u)=q t*q u := by
    simp only [q,roleMonomial_add,map_mul]
  have qrel : q (0,alpha A,0)=q (beta A,0,0) :=
    Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))
  have ha : 0 < alpha A := by
    have h := (branchA_symmetricTailData A).n0_pos
    rw [(branchA_symmetricTailData A).n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have normal (t : Monomial) (ht : t.2.2<d A) :
      ∃ u : Monomial, u.2.1<alpha A ∧ u.2.2<d A ∧
        monomialDegree P.M.base A.reindex u=monomialDegree P.M.base A.reindex t ∧ q t=q u := by
    obtain ⟨x,y,z⟩ := t
    induction y using Nat.strong_induction_on generalizing x with
    | h y ih =>
      by_cases hya : alpha A ≤ y
      · obtain ⟨u,huy,huz,hdeg,hq⟩ := ih (y-alpha A) (by omega) (x+beta A) ht
        refine ⟨u,huy,huz,hdeg.trans (pure_tail_pure_step_degree A x y z hya).symm,?_⟩
        have h1 : (x,y,z)=(x,y-alpha A,z)+(0,alpha A,0) := by ext <;> simp <;> omega
        have h2 : (x+beta A,y-alpha A,z)=(x,y-alpha A,z)+(beta A,0,0) := by ext <;> simp
        have hctx : q (x,y,z)=q (x+beta A,y-alpha A,z) := by
          rw [h1,h2,qadd,qadd,qrel]
        exact hctx.trans hq
      · exact ⟨(x,y,z),Nat.lt_of_not_ge hya,ht,rfl,rfl⟩
  obtain ⟨z',hzy,hzz,hzd,hzq⟩ := normal z hz
  obtain ⟨w',hwy,hwz,hwd,hwq⟩ := normal w hw
  have heq := pure_tail_normal_unique A ⟨hzy,hzz⟩ ⟨hwy,hwz⟩ (hzd.trans (he.trans hwd.symm))
  apply Ideal.Quotient.eq.mp
  exact hzq.trans (by rw [heq]; exact hwq.symm)

end NS25Lean.L5A2C4OR40

