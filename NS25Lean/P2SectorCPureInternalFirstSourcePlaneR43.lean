import NS25Lean.P2SectorCPureInternalSocleCorrectionR42

set_option linter.style.header false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.L5A2C4OR43
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR33 L5A2C4OR35 L5A2C4OR39 L5A2C4OR40
  L5A2C4OR41 L5A2C4OR42 FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

def roleWeight (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) : ℕ :=
  ![routingA B e,routingB B e,routingC B e] i

theorem roleWeight_scale (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    routingD B e * roleWeight B e i = weights B (e i) := by
  fin_cases i
  · simpa [roleWeight,normalizedGrid,gridDegree] using normalizedGrid_scale B e 1 0 0
  · simpa [roleWeight,normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 1 0
  · simpa [roleWeight,normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 0 1

theorem roleWeight_pos (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    0 < roleWeight B e i := by
  have h := weights_positive B (e i)
  rw [←roleWeight_scale B e i] at h
  nlinarith

/-- Actual component status transported through D, including Nat subtraction. -/
theorem normalized_component_killed_iff (B : Data Gamma) (M : MultiplicityBase Gamma)
    (hB : M.base = B) (e : Fin 3 ≃ Fin 3) {h n : ℕ}
    (hs : routingD B e*n=h) (C : FiberComponent M.base h) :
    BoundaryKilled M h C ↔ ∃ i : Fin 3,
      e i ∈ componentSupport M.base h C ∧
      n-roleWeight B e i ∈ cyclicCut (routingH B e) (routingM B e) := by
  subst B
  rw [killed_iff_support_predecessor]
  constructor
  · rintro ⟨j,hj,hk⟩
    obtain ⟨i,rfl⟩ := e.surjective j
    refine ⟨i,hj,(actual_scaled_cut_iff _ _ _).mpr ?_⟩
    rwa [Nat.mul_sub_left_distrib,hs,roleWeight_scale]
  · rintro ⟨i,hi,hk⟩
    refine ⟨e i,hi,?_⟩
    have hh := (actual_scaled_cut_iff _ _ _).mp hk
    rwa [Nat.mul_sub_left_distrib,hs,roleWeight_scale] at hh

theorem monomial_positive_predecessors (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (z : Monomial) :
    (0<z.1 → ∃ y ∈ routingH B e, monomialDegree B e z=y+routingA B e) ∧
    (0<z.2.1 → ∃ y ∈ routingH B e, monomialDegree B e z=y+routingB B e) ∧
    (0<z.2.2 → ∃ y ∈ routingH B e, monomialDegree B e z=y+routingC B e) := by
  refine ⟨?_,?_,?_⟩
  · intro hp
    refine ⟨monomialDegree B e (z.1-1,z.2.1,z.2.2),grid_mem_H _ _ _,?_⟩
    have hh := congrArg (fun n => n*routingA B e) (Nat.sub_add_cancel (by omega : 1≤z.1))
    simp only [Nat.add_mul,one_mul] at hh
    simp only [monomialDegree,normalizedGrid]
    omega
  · intro hp
    refine ⟨monomialDegree B e (z.1,z.2.1-1,z.2.2),grid_mem_H _ _ _,?_⟩
    have hh := congrArg (fun n => n*routingB B e) (Nat.sub_add_cancel (by omega : 1≤z.2.1))
    simp only [Nat.add_mul,one_mul] at hh
    simp only [monomialDegree,normalizedGrid]
    omega
  · intro hp
    refine ⟨monomialDegree B e (z.1,z.2.1,z.2.2-1),grid_mem_H _ _ _,?_⟩
    have hh := congrArg (fun n => n*routingC B e) (Nat.sub_add_cancel (by omega : 1≤z.2.2))
    simp only [Nat.add_mul,one_mul] at hh
    simp only [monomialDegree,normalizedGrid]
    omega

/-- Separation holds for every return and every actual source factorization. -/
theorem source_return_coordinate_separation (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (v : ModelSources B e) (g t : Monomial) (hg : monomialDegree B e g=v.val)
    {n : ℕ} (hn : 0<n) (ht : v.val=n*routingM B e+monomialDegree B e t) :
    (0<g.1 → t.1=0) ∧ (0<g.2.1 → t.2.1=0) ∧ (0<g.2.2 → t.2.2=0) := by
  have gp := monomial_positive_predecessors B e g
  have tp := monomial_positive_predecessors B e t
  have common {a : ℕ} (ha : 0<a) (haH : a ∈ routingH B e)
      (hgp : ∃ y ∈ routingH B e, monomialDegree B e g=y+a)
      (htp : ∃ y ∈ routingH B e, monomialDegree B e t=y+a) : False := by
    obtain ⟨y,hy,hgy⟩ := hgp
    obtain ⟨z,hz,htz⟩ := htp
    have hh := model_source_return_no_common_summand B e v hn hz hy haH
      (hg.symm.trans hgy) (ht.trans (by rw [htz]))
    omega
  refine ⟨?_,?_,?_⟩
  · intro hgp
    by_contra htp
    exact common (routingA_pos _ _) (by simpa [monomialDegree,normalizedGrid] using grid_mem_H B e (1,0,0)) (gp.1 hgp) (tp.1 (by omega))
  · intro hgp
    by_contra htp
    exact common (routingB_positive _ _) (routingHB B e) (gp.2.1 hgp) (tp.2.1 (by omega))
  · intro hgp
    by_contra htp
    exact common (routingC_positive _ _) (routingHC B e) (gp.2.2 hgp) (tp.2.2 (by omega))

/-- All zero remainders, not one zero remainder, imply firstness. -/
theorem source_first_of_all_returns_zero (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (v : ModelSources B e)
    (hall : ∀ n y : ℕ, 0<n → y∈routingH B e → v.val=n*routingM B e+y → y=0) :
    v.val=firstPrincipal (routingH B e) (routingM B e) (routingM_pos _ _)*routingM B e := by
  by_contra hfirst
  obtain ⟨n,y,hn,_,hy,hyp,he⟩ := model_nonfirst_source_small_return B e v hfirst
  have := hall n y hn hy he
  omega

theorem source_val_pos (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (v : ModelSources B e) :
    0<v.val := by
  obtain ⟨_,n,hn,y,_,he⟩ := v.property.1
  have := routingM_pos B e
  nlinarith

theorem pair_degree_scale (A : SectorBCriticalRoleBranchA P) :
    routingD P.M.base A.reindex*(beta A*routingA P.M.base A.reindex)=A.pairDegree := by
  have hs := (branchA_symmetricTailData A).c0_eq_beta
  have he := A.pair.left_degree_eq_critical
  rw [←A.reindex_zero] at he
  change criticalExponent P.M.base (A.reindex 0)=beta A at hs
  rw [hs] at he
  rw [he,←roleWeight_scale P.M.base A.reindex 0]
  simp only [roleWeight,Matrix.cons_val_zero]
  ring

theorem boundary_not_both_killed (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) :
    ¬(BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent ∧
      BoundaryKilled P.M A.mixedDegree A.mixed.mixedComponent) := by
  rintro ⟨hp,hm⟩
  obtain ⟨K,huniq⟩ := Nat.card_eq_one_iff_exists.mp hk
  have he : (⟨A.mixed.pureComponent,hp⟩ : {C // BoundaryKilled P.M A.mixedDegree C})=
      ⟨A.mixed.mixedComponent,hm⟩ := (huniq _).trans (huniq _).symm
  exact A.mixed.components_ne (congrArg Subtype.val he)

theorem bounded_z_equal_z (A : SectorBCriticalRoleBranchA P) {z w : Monomial}
    (hz : z.2.2<d A) (hw : w.2.2<d A)
    (he : monomialDegree P.M.base A.reindex z=monomialDegree P.M.base A.reindex w) :
    z.2.2=w.2.2 := by
  have hh := pure_tail_normal_unique A ⟨pureNormal_y_lt A z,hz⟩
    ⟨pureNormal_y_lt A w,hw⟩
    ((pureNormal_degree A z).trans (he.trans (pureNormal_degree A w).symm))
  simpa only [pureNormal] using congrArg (fun t : Monomial => t.2.2) hh

theorem pure_boundary_predecessor (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent) :
    (d A-1)*routingC P.M.base A.reindex ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
  obtain ⟨i,hi,hcut⟩ := (normalized_component_killed_iff P.M.base P.M rfl A.reindex
    (mixed_boundary_degree_scale A) A.mixed.pureComponent).mp hk
  rw [A.mixed.pureSupport,←A.reindex_two,Finset.mem_singleton] at hi
  have hi2 : i=2 := A.reindex.injective hi
  subst i
  simpa [roleWeight,Nat.sub_mul] using hcut

theorem mixed_predecessors_mem_H (A : SectorBCriticalRoleBranchA P) :
    d A*routingC P.M.base A.reindex-routingA P.M.base A.reindex ∈ routingH P.M.base A.reindex ∧
    d A*routingC P.M.base A.reindex-routingB P.M.base A.reindex ∈ routingH P.M.base A.reindex := by
  have ht := branchA_symmetricTailData A
  have hr := ht.mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hr
  have hx := congrArg (fun t => t*routingA P.M.base A.reindex)
    (Nat.sub_add_cancel (show 1≤r A by have := ht.r_pos; omega))
  have hy := congrArg (fun t => t*routingB P.M.base A.reindex)
    (Nat.sub_add_cancel (show 1≤s A by have := ht.s_pos; omega))
  simp only [Nat.add_mul,one_mul] at hx hy
  constructor
  · convert grid_mem_H P.M.base A.reindex (r A-1,s A,0) using 1
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
    omega
  · convert grid_mem_H P.M.base A.reindex (r A,s A-1,0) using 1
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
    omega

theorem mixed_support_first_two (A : SectorBCriticalRoleBranchA P) :
    A.reindex 0 ∈ componentSupport P.M.base A.mixedDegree A.mixed.mixedComponent ∧
    A.reindex 1 ∈ componentSupport P.M.base A.mixedDegree A.mixed.mixedComponent := by
  have ht := branchA_symmetricTailData A
  exact ⟨(mem_componentSupport _ _ _ _).mpr ⟨A.mixed.witness,A.mixed.witness_component,ht.r_pos⟩,
    (mem_componentSupport _ _ _ _).mpr ⟨A.mixed.witness,A.mixed.witness_component,ht.s_pos⟩⟩

theorem pure_killed_source (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent) :
    ∃ v : ModelSources P.M.base A.reindex, ∃ C : ℕ,
      0<C ∧ C<d A ∧ pureSourceNormal A v=(0,0,C) := by
  obtain ⟨v,t,ht,he⟩ := cut_source_cover _ _ _ (pure_boundary_predecessor A hk)
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  let g := pureSourceNormal A v
  let w : Monomial := (x,y,z)
  have hg : monomialDegree P.M.base A.reindex g=v.val := (pureSourceNormal_spec A v).1
  have hw : monomialDegree P.M.base A.reindex w=t := hfac.symm
  have hd : monomialDegree P.M.base A.reindex (g+w)=
      (d A-1)*routingC P.M.base A.reindex := by
    rw [monomialDegree_add,hg,hw,←he]
  have hc := (branchA_symmetricTailData A).c2_eq_d
  change criticalExponent P.M.base (A.reindex 2)=d A at hc
  have hdp : 0<d A := by
    have hh := (branchA_symmetricTailData A).n0_pos
    rw [(branchA_symmetricTailData A).n0_eq] at hh
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hh)
  have hu : weight P.M.base (roleExponent A.reindex (g+w))=
      (d A-1)*weights P.M.base (A.reindex 2) := by
    have hscale : routingD P.M.base A.reindex*routingC P.M.base A.reindex=
        weights P.M.base (A.reindex 2) := by simpa [roleWeight] using roleWeight_scale P.M.base A.reindex 2
    rw [roleExponent_weight,hd,←hscale]
    ring
  have hp := factorization_below_critical_is_pure _ _
    (by rw [hc]; omega : d A-1<criticalExponent P.M.base (A.reindex 2)) _ hu
  have hx := congrArg (fun u : Fin 3 →₀ ℕ => u (A.reindex 0)) hp
  have hy := congrArg (fun u : Fin 3 →₀ ℕ => u (A.reindex 1)) hp
  have hz := congrArg (fun u : Fin 3 →₀ ℕ => u (A.reindex 2)) hp
  simp [roleExponent] at hx hy hz
  have hgx : g.1=0 := hx.1
  have hgy : g.2.1=0 := hy.1
  have hgz : 0<g.2.2 := by
    have hpos := source_val_pos _ _ v
    simp only [monomialDegree,normalizedGrid,hgx,hgy,zero_mul,zero_add] at hg
    by_contra hn
    have hh : g.2.2=0 := by omega
    simp [hh] at hg
    omega
  refine ⟨v,g.2.2,hgz,by omega,?_⟩
  exact Prod.ext hgx (Prod.ext hgy rfl)

/-- Pure killed / raw mixed live: every return of the pure source is zero. -/
theorem pure_killed_first_source (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent)
    (hl : ¬BoundaryKilled P.M A.mixedDegree A.mixed.mixedComponent) :
    ∃ v : ModelSources P.M.base A.reindex,
      v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex ∧
      (pureSourceNormal A v).1=0 ∧ (pureSourceNormal A v).2.1=0 := by
  obtain ⟨v,C,hC,hCd,hg⟩ := pure_killed_source A hk
  have hs := (pureSourceNormal_spec A v).1
  rw [hg] at hs
  have hsC : v.val=C*routingC P.M.base A.reindex := by
    simpa [monomialDegree,normalizedGrid] using hs.symm
  have hfirst := source_first_of_all_returns_zero P.M.base A.reindex v (by
    intro n t hn ht he
    obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
    have hdeg : monomialDegree P.M.base A.reindex (x,y,z)=t := hfac.symm
    have sep := source_return_coordinate_separation _ _ v (0,0,C) (x,y,z) hs hn
      (he.trans (by rw [hdeg]))
    have hz : z=0 := sep.2.2 hC
    have hsmall := congrArg (fun k => k*routingC P.M.base A.reindex)
      (Nat.sub_add_cancel (Nat.le_of_lt hCd))
    simp only [Nat.add_mul] at hsmall
    have hparent : d A*routingC P.M.base A.reindex=
        n*routingM P.M.base A.reindex+monomialDegree P.M.base A.reindex (x,y,d A-C) := by
      simp only [monomialDegree,normalizedGrid,hz,zero_mul,add_zero] at hdeg
      simp only [monomialDegree,normalizedGrid]
      omega
    have kill (i : Fin 3) (hi : A.reindex i ∈
        componentSupport P.M.base A.mixedDegree A.mixed.mixedComponent)
        (hpred : d A*routingC P.M.base A.reindex-roleWeight P.M.base A.reindex i ∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) : False :=
      hl ((normalized_component_killed_iff _ P.M rfl _ (mixed_boundary_degree_scale A) _).mpr
        ⟨i,hi,hpred⟩)
    by_cases hx : 0<x
    · obtain ⟨p,hp,hpeq⟩ := (monomial_positive_predecessors P.M.base A.reindex (x,y,d A-C)).1 hx
      have hsub : d A*routingC P.M.base A.reindex-routingA P.M.base A.reindex=
          n*routingM P.M.base A.reindex+p := by omega
      exact (kill 0 (mixed_support_first_two A).1
        (by simpa [roleWeight] using
          (show d A*routingC P.M.base A.reindex-routingA P.M.base A.reindex ∈
            cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) from
            ⟨(mixed_predecessors_mem_H A).1,n,hn,p,hp,hsub⟩))).elim
    · by_cases hy : 0<y
      · obtain ⟨p,hp,hpeq⟩ := (monomial_positive_predecessors P.M.base A.reindex (x,y,d A-C)).2.1 hy
        have hsub : d A*routingC P.M.base A.reindex-routingB P.M.base A.reindex=
            n*routingM P.M.base A.reindex+p := by omega
        exact (kill 1 (mixed_support_first_two A).2
          (by simpa [roleWeight] using
            (show d A*routingC P.M.base A.reindex-routingB P.M.base A.reindex ∈
              cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) from
              ⟨(mixed_predecessors_mem_H A).2,n,hn,p,hp,hsub⟩))).elim
      · have hx0 : x=0 := by omega
        have hy0 : y=0 := by omega
        simpa [monomialDegree,normalizedGrid,hx0,hy0,hz] using hdeg.symm)
  exact ⟨v,hfirst,by simp [hg],by simp [hg]⟩

/-- Internal alive forbids all subcritical pure cut degrees, not just sources. -/
theorem internal_axis_cut_bounds (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree) :
    (∀ x : ℕ, x*routingA P.M.base A.reindex ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) → beta A≤x) ∧
    (∀ y : ℕ, y*routingB P.M.base A.reindex ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) → alpha A≤y) := by
  have halive := none_killed_of_count_zero P.M A.pairDegree
    (by rw [ha]; exact G.internalSignature.2)
  have hxpred : (beta A-1)*routingA P.M.base A.reindex ∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    intro hk
    apply halive A.pair.leftComponent
    apply (normalized_component_killed_iff _ P.M rfl _ (pair_degree_scale A) _).mpr
    refine ⟨0,?_,?_⟩
    · rw [A.pair.leftSupport,←A.reindex_zero]; simp
    · simpa [roleWeight,Nat.sub_mul] using hk
  have hyScale : routingD P.M.base A.reindex*(alpha A*routingB P.M.base A.reindex)=
      A.pairDegree := by
    have hrel := (branchA_symmetricTailData A).pure_relation
    rw [←routingA_eq_n0,←routingB_eq_n1] at hrel
    rw [←hrel]; exact pair_degree_scale A
  have hypred : (alpha A-1)*routingB P.M.base A.reindex ∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    intro hk
    apply halive A.pair.rightComponent
    apply (normalized_component_killed_iff _ P.M rfl _ hyScale _).mpr
    refine ⟨1,?_,?_⟩
    · rw [A.pair.rightSupport,←A.reindex_one]; simp
    · simpa [roleWeight,Nat.sub_mul] using hk
  constructor
  · intro x hx
    by_contra hlt
    have hb : 0<beta A := by
      have h := (branchA_symmetricTailData A).n1_pos
      rw [(branchA_symmetricTailData A).n1_eq] at h
      exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
    have hle : x≤beta A-1 := by omega
    have hk := cut_add_tail hx (grid_mem_H P.M.base A.reindex (beta A-1-x,0,0))
    apply hxpred
    have he := congrArg (fun t => t*routingA P.M.base A.reindex) (Nat.sub_add_cancel hle)
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero] at hk
    simp only [Nat.add_mul] at he
    convert hk using 1; omega
  · intro y hy
    by_contra hlt
    have hle : y≤alpha A-1 := by have := pure_alpha_pos A; omega
    have hk := cut_add_tail hy (grid_mem_H P.M.base A.reindex (0,alpha A-1-y,0))
    apply hypred
    have he := congrArg (fun t => t*routingB P.M.base A.reindex) (Nat.sub_add_cancel hle)
    simp only [monomialDegree,normalizedGrid,zero_mul,zero_add,add_zero] at hk
    simp only [Nat.add_mul] at he
    convert hk using 1; omega

/-- A genuine strict raw xy predecessor, retaining raw positive r and s. -/
theorem mixed_killed_raw_predecessor (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.mixedDegree A.mixed.mixedComponent) :
    ∃ p : Monomial, p.2.2=0 ∧
      monomialDegree P.M.base A.reindex p ∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) ∧
      ∃ t : ℕ, t∈routingH P.M.base A.reindex ∧ 0<t ∧
        d A*routingC P.M.base A.reindex=monomialDegree P.M.base A.reindex p+t := by
  obtain ⟨i,hi,hcut⟩ := (normalized_component_killed_iff _ P.M rfl _
    (mixed_boundary_degree_scale A) A.mixed.mixedComponent).mp hk
  have hp := A.mixed.witness_pos_of_mem_mixedSupport (A.reindex i) hi
  have hrel := (branchA_symmetricTailData A).mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hrel
  fin_cases i
  · have hr : 1≤r A := by exact hp
    have he := congrArg (fun t => t*routingA P.M.base A.reindex) (Nat.sub_add_cancel hr)
    simp only [Nat.add_mul,one_mul] at he
    have hd : monomialDegree P.M.base A.reindex (r A-1,s A,0)+
        routingA P.M.base A.reindex=d A*routingC P.M.base A.reindex := by
      simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
      omega
    refine ⟨(r A-1,s A,0),rfl,?_,routingA P.M.base A.reindex,?_,routingA_pos _ _,hd.symm⟩
    · simpa [roleWeight,←hd] using hcut
    · simpa [monomialDegree,normalizedGrid] using grid_mem_H P.M.base A.reindex (1,0,0)
  · have hr : 1≤s A := by exact hp
    have he := congrArg (fun t => t*routingB P.M.base A.reindex) (Nat.sub_add_cancel hr)
    simp only [Nat.add_mul,one_mul] at he
    have hd : monomialDegree P.M.base A.reindex (r A,s A-1,0)+
        routingB P.M.base A.reindex=d A*routingC P.M.base A.reindex := by
      simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
      omega
    refine ⟨(r A,s A-1,0),rfl,?_,routingB P.M.base A.reindex,routingHB _ _,routingB_positive _ _,hd.symm⟩
    simpa [roleWeight,←hd] using hcut
  · change 0 < A.mixed.witness.val (A.reindex 2) at hp
    rw [A.reindex_two] at hp
    rw [A.mixed.witness_pure_zero] at hp
    omega

theorem mixed_killed_plane_source (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.mixedDegree A.mixed.mixedComponent) :
    ∃ v : ModelSources P.M.base A.reindex, ∃ t : ℕ,
      t∈routingH P.M.base A.reindex ∧
      d A*routingC P.M.base A.reindex=v.val+t ∧ (pureSourceNormal A v).2.2=0 := by
  obtain ⟨p,hpz,hp,q,hq,hqp,hpq⟩ := mixed_killed_raw_predecessor A hk
  obtain ⟨v,t,ht,he⟩ := cut_source_cover _ _ _ hp
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  let g := pureSourceNormal A v
  let w : Monomial := (x,y,z)
  have hdeg : monomialDegree P.M.base A.reindex (g+w)=monomialDegree P.M.base A.reindex p := by
    rw [monomialDegree_add,(pureSourceNormal_spec A v).1]
    rw [show monomialDegree P.M.base A.reindex w=t from hfac.symm]
    exact he.symm
  have hcz : 0<routingC P.M.base A.reindex := routingC_positive _ _
  have hlt : (g+w).2.2<d A := by
    have hh : monomialDegree P.M.base A.reindex (g+w)<d A*routingC P.M.base A.reindex := by omega
    simp only [monomialDegree,normalizedGrid] at hh
    nlinarith [Nat.zero_le ((g+w).1*routingA P.M.base A.reindex),
      Nat.zero_le ((g+w).2.1*routingB P.M.base A.reindex)]
  have hdp : 0<d A := by
    have h := (branchA_symmetricTailData A).n0_pos
    rw [(branchA_symmetricTailData A).n0_eq] at h
    exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)
  have hzz := bounded_z_equal_z A hlt (by omega : p.2.2<d A) hdeg
  refine ⟨v,t+q,(routingH _ _).add_mem ht hq,by omega,?_⟩
  change g.2.2=0
  change g.2.2+w.2.2=p.2.2 at hzz
  omega

/-- An xy source has both actual H-predecessors: internal alive excludes
subcritical singleton support; F supplies the second support otherwise. -/
theorem xy_source_both_predecessors (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (v : ModelSources P.M.base A.reindex) (hz : (pureSourceNormal A v).2.2=0) :
    (∃ y∈routingH P.M.base A.reindex,v.val=y+routingA P.M.base A.reindex) ∧
    (∃ y∈routingH P.M.base A.reindex,v.val=y+routingB P.M.base A.reindex) := by
  let g := pureSourceNormal A v
  have hg := (pureSourceNormal_spec A v).1
  have hgy := (pureSourceNormal_spec A v).2.1
  change g.2.1<alpha A at hgy
  have hx : 0<g.1 := by
    by_contra hn
    have hx0 : g.1=0 := by omega
    have hyK : g.2.1*routingB P.M.base A.reindex ∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
      have hh := v.property.1
      rw [←hg] at hh
      simpa [monomialDegree,normalizedGrid,hx0,hz,g] using hh
    have hh := (internal_axis_cut_bounds G A ha).2 g.2.1 hyK
    omega
  have hp := monomial_positive_predecessors P.M.base A.reindex g
  refine ⟨by rw [←hg]; exact hp.1 hx,?_⟩
  by_cases hy : 0<g.2.1
  · rw [←hg]; exact hp.2.1 hy
  · have hy0 : g.2.1=0 := by omega
    have hxK : g.1*routingA P.M.base A.reindex ∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
      have hh := v.property.1
      rw [←hg] at hh
      simpa [monomialDegree,normalizedGrid,hy0,hz,g] using hh
    have hxb := (internal_axis_cut_bounds G A ha).1 g.1 hxK
    have hrel := (branchA_symmetricTailData A).pure_relation
    rw [←routingA_eq_n0,←routingB_eq_n1] at hrel
    have hm := congrArg (fun t => t*routingA P.M.base A.reindex) (Nat.sub_add_cancel hxb)
    simp only [Nat.add_mul] at hm
    have he : monomialDegree P.M.base A.reindex (g.1-beta A,alpha A,0)=v.val := by
      simp only [monomialDegree,normalizedGrid,hy0,hz,zero_mul,add_zero,g] at hg ⊢
      nlinarith only [hm,hrel,hg]
    rw [←he]
    exact (monomial_positive_predecessors P.M.base A.reindex (g.1-beta A,alpha A,0)).2.1
      (pure_alpha_pos A)

/-- Mixed killed / pure live: both actual xy predecessors exclude every
nonzero return remainder, including the reduced-y-zero case. -/
theorem mixed_killed_first_source (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.mixedDegree A.mixed.mixedComponent)
    (hl : ¬BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent) :
    ∃ v : ModelSources P.M.base A.reindex,
      v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex ∧
      (pureSourceNormal A v).2.2=0 := by
  obtain ⟨v,t,ht,he,hvz⟩ := mixed_killed_plane_source A hk
  obtain ⟨hva,hvb⟩ := xy_source_both_predecessors G A ha v hvz
  have hfirst := source_first_of_all_returns_zero P.M.base A.reindex v (by
    intro n y hn hy hret
    obtain ⟨x1,y1,z1,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ hy
    have hd : monomialDegree P.M.base A.reindex (x1,y1,z1)=y := hfac.symm
    have hx0 : x1=0 := by
      by_contra hx
      obtain ⟨z,hz,hze⟩ :=
        (monomial_positive_predecessors P.M.base A.reindex (x1,y1,z1)).1 (by omega)
      obtain ⟨w,hw,hwe⟩ := hva
      have hh := model_source_return_no_common_summand _ _ v hn hz hw
        (show routingA P.M.base A.reindex∈routingH P.M.base A.reindex from
          by simpa [monomialDegree,normalizedGrid] using grid_mem_H P.M.base A.reindex (1,0,0))
        hwe (hret.trans (by rw [←hd,hze]))
      have := routingA_pos P.M.base A.reindex
      omega
    have hy0 : y1=0 := by
      by_contra hx
      obtain ⟨z,hz,hze⟩ :=
        (monomial_positive_predecessors P.M.base A.reindex (x1,y1,z1)).2.1 (Nat.pos_of_ne_zero hx)
      obtain ⟨w,hw,hwe⟩ := hvb
      have hh := model_source_return_no_common_summand _ _ v hn hz hw
        (routingHB _ _) hwe (hret.trans (by rw [←hd,hze]))
      have := routingB_positive P.M.base A.reindex
      omega
    by_cases hzpos : 0<z1
    · have hp := grid_mem_H P.M.base A.reindex (0,0,z1-1)
      have hzsum := congrArg (fun z => z*routingC P.M.base A.reindex)
        (Nat.sub_add_cancel (by omega : 1≤z1))
      simp only [Nat.add_mul,one_mul] at hzsum
      have hsub : d A*routingC P.M.base A.reindex-routingC P.M.base A.reindex=
          n*routingM P.M.base A.reindex+
            (monomialDegree P.M.base A.reindex (0,0,z1-1)+t) := by
        simp only [monomialDegree,normalizedGrid,hx0,hy0,zero_mul,zero_add] at hd ⊢
        omega
      have hH : d A*routingC P.M.base A.reindex-routingC P.M.base A.reindex∈
          routingH P.M.base A.reindex := by
        have hdpos : 0<d A := by
          have hh := (branchA_symmetricTailData A).n0_pos
          rw [(branchA_symmetricTailData A).n0_eq] at hh
          exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at hh)
        simpa [monomialDegree,normalizedGrid,Nat.sub_mul] using
          grid_mem_H P.M.base A.reindex (0,0,d A-1)
      have hcut : d A*routingC P.M.base A.reindex-routingC P.M.base A.reindex∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) :=
        ⟨hH,n,hn,_,(routingH _ _).add_mem hp ht,hsub⟩
      apply (hl ?_).elim
      apply (normalized_component_killed_iff _ P.M rfl _ (mixed_boundary_degree_scale A) _).mpr
      refine ⟨2,?_,?_⟩
      · rw [A.mixed.pureSupport,←A.reindex_two]; simp
      · simpa [roleWeight] using hcut
    · have hz0 : z1=0 := by omega
      simpa [monomialDegree,normalizedGrid,hx0,hy0,hz0] using hd.symm)
  exact ⟨v,hfirst,hvz⟩

theorem internal_first_source_shape (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp≠bm)
    (hp : IsPureBoundaryComponent G bp) (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,(componentSupport P.M.base G.internalDegree C).card=1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.internalDegree ∧ A.mixedDegree=G.boundaryDegree ∧
      ∀ v : ModelSources P.M.base A.reindex,
        v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
          (routingM_pos _ _)*routingM P.M.base A.reindex →
        ((pureSourceNormal A v).1=0 ∧ (pureSourceNormal A v).2.1=0) ∨
          (pureSourceNormal A v).2.2=0 := by
  obtain ⟨A,ha,hb,_⟩ := internal_all_pure_geometry P G bp bm hne hp hm hi
  have hk1 : killedCount P.M A.mixedDegree=1 := by rw [hb]; exact G.boundarySignature.2
  refine ⟨A,ha,hb,?_⟩
  obtain hpk | hmk := boundary_has_killed_endpoint A hk1
  · have hl := fun hh => boundary_not_both_killed A hk1 ⟨hpk,hh⟩
    obtain ⟨v,hv,hx,hy⟩ := pure_killed_first_source A hpk hl
    intro w hw
    have he : w=v := Subtype.ext (hw.trans hv.symm)
    subst w
    exact Or.inl ⟨hx,hy⟩
  · have hl := fun hh => boundary_not_both_killed A hk1 ⟨hh,hmk⟩
    obtain ⟨v,hv,hz⟩ := mixed_killed_first_source G A ha hmk hl
    intro w hw
    have he : w=v := Subtype.ext (hw.trans hv.symm)
    subst w
    exact Or.inr hz

/-- The exact original R43 target, without additional caller hypotheses. -/
theorem internal_first_source_plane (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp≠bm)
    (hp : IsPureBoundaryComponent G bp) (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,(componentSupport P.M.base G.internalDegree C).card=1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.internalDegree ∧ A.mixedDegree=G.boundaryDegree ∧
      ∀ v : ModelSources P.M.base A.reindex,
        v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
          (routingM_pos _ _)*routingM P.M.base A.reindex →
        (pureSourceNormal A v).1=0 ∨ (pureSourceNormal A v).2.1=0 ∨
          (pureSourceNormal A v).2.2=0 := by
  obtain ⟨A,ha,hb,hs⟩ := internal_first_source_shape P G bp bm hne hp hm hi
  refine ⟨A,ha,hb,?_⟩
  intro v hv
  rcases hs v hv with h | h
  · exact Or.inl h.1
  · exact Or.inr (Or.inr h)

theorem internal_all_source_plane (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp≠bm)
    (hp : IsPureBoundaryComponent G bp) (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,(componentSupport P.M.base G.internalDegree C).card=1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.internalDegree ∧ A.mixedDegree=G.boundaryDegree ∧
      (∀ v : ModelSources P.M.base A.reindex,
        (pureSourceNormal A v).1=0 ∨ (pureSourceNormal A v).2.1=0 ∨
          (pureSourceNormal A v).2.2=0) ∧
      Nat.card {v : ModelSources P.M.base A.reindex // FullySupported (pureSourceNormal A v)}=0 := by
  obtain ⟨A,ha,hb,hs⟩ := internal_first_source_plane P G bp bm hne hp hm hi
  have hall : ∀ v : ModelSources P.M.base A.reindex,
      (pureSourceNormal A v).1=0 ∨ (pureSourceNormal A v).2.1=0 ∨
        (pureSourceNormal A v).2.2=0 := by
    intro v
    by_cases hv : v.val=firstPrincipal (routingH P.M.base A.reindex)
        (routingM P.M.base A.reindex) (routingM_pos _ _)*routingM P.M.base A.reindex
    · exact hs v hv
    · exact pure_nonfirst_source_plane A v hv
  refine ⟨A,ha,hb,hall,?_⟩
  have hempty : IsEmpty {v : ModelSources P.M.base A.reindex // FullySupported (pureSourceNormal A v)} :=
    ⟨by rintro ⟨v,hv⟩; rcases hall v with h | h | h <;> simp [FullySupported,h] at hv⟩
  let := hempty
  exact Nat.card_of_isEmpty

/-- A positive-yz nonfirst source produces a strict cut divisor of its wrap.
The nonfirst guard is essential and is never inferred from one zero return. -/
theorem nonfirst_positive_yz_wrap_redundant (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (v : ModelSources P.M.base A.reindex)
    (hx : (pureSourceNormal A v).1=0) (hy : 0<(pureSourceNormal A v).2.1)
    (hz : 0<(pureSourceNormal A v).2.2)
    (hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex) :
    ¬PolynomialMinimal (pureInitialGenerators A) (pureWrap A (pureSourceNormal A v)) := by
  let g := pureSourceNormal A v
  have hg := (pureSourceNormal_spec A v).1
  have hgy := (pureSourceNormal_spec A v).2.1
  change g.2.1<alpha A at hgy
  obtain ⟨n,t,hn,_,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ v hnf
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base A.reindex (x,y,z)=t := hfac.symm
  have hret : v.val=n*routingM P.M.base A.reindex+monomialDegree P.M.base A.reindex (x,y,z) :=
    he.trans (by rw [hd])
  have sep := source_return_coordinate_separation _ _ v g (x,y,z) hg hn hret
  have hy0 : y=0 := sep.2.1 hy
  have hz0 : z=0 := sep.2.2 hz
  have hta : t=x*routingA P.M.base A.reindex := by
    simpa [monomialDegree,normalizedGrid,hy0,hz0] using hd.symm
  have hxp : 0<x := Nat.pos_of_ne_zero (fun hh => by simp [hh] at hta; omega)
  have hrel := (branchA_symmetricTailData A).pure_relation
  rw [←routingA_eq_n0,←routingB_eq_n1] at hrel
  have hxb : x<beta A := by
    by_contra hbad
    have hle : beta A≤x := by omega
    have hh := congrArg (fun t => t*routingA P.M.base A.reindex) (Nat.sub_add_cancel hle)
    simp only [Nat.add_mul] at hh
    have hnew : monomialDegree P.M.base A.reindex (x-beta A,alpha A,0)=t := by
      simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
      nlinarith only [hh,hrel,hta]
    have hs := source_return_coordinate_separation _ _ v g (x-beta A,alpha A,0) hg hn
      (he.trans (by rw [hnew]))
    have hzero : alpha A=0 := hs.2.1 hy
    have := pure_alpha_pos A
    omega
  let w : Monomial := (beta A-x,0,g.2.2)
  have heq : monomialDegree P.M.base A.reindex w=
      n*routingM P.M.base A.reindex+(alpha A-g.2.1)*routingB P.M.base A.reindex := by
    have h1 := congrArg (fun t => t*routingA P.M.base A.reindex)
      (Nat.sub_add_cancel (Nat.le_of_lt hxb))
    have h2 := congrArg (fun t => t*routingB P.M.base A.reindex)
      (Nat.sub_add_cancel (Nat.le_of_lt hgy))
    simp only [Nat.add_mul] at h1 h2
    change g.1*routingA P.M.base A.reindex+g.2.1*routingB P.M.base A.reindex+
      g.2.2*routingC P.M.base A.reindex=v.val at hg
    rw [show g.1=0 from hx] at hg
    simp only [zero_mul,zero_add] at hg
    simp only [monomialDegree,normalizedGrid,w,zero_mul,add_zero]
    omega
  have hwK : monomialDegree P.M.base A.reindex w∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) :=
    ⟨grid_mem_H _ _ w,n,hn,_,
      by simpa [monomialDegree,normalizedGrid] using grid_mem_H P.M.base A.reindex (0,alpha A-g.2.1,0),heq⟩
  have hwstrip : w∈monomialClosure (pureStripGenerators A) := by
    simpa only [pureNormal_fixed A w (pure_alpha_pos A)] using (pure_normal_mem_iff_cut A hk w).mpr hwK
  have hwinit : w∈monomialClosure (pureInitialGenerators A) :=
    (pure_initial_mem_iff A w).mpr (Or.inr hwstrip)
  intro hm
  have hew := hm.2 w hwinit (by simp [w,pureWrap,hx])
    (by simp [w,pureWrap]) (by simp [w,pureWrap,g])
  have hh := congrArg (fun u : Monomial => u.1) hew
  simp only [w,pureWrap,hx,zero_add] at hh
  omega

/-- Genuine additional minima only; raw originals are not counted as wraps. -/
def PureSurvivingWraps (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  {w | PolynomialMinimal (pureInitialGenerators A) w ∧
    w∉({(0,alpha A,0)}∪pureOriginals A)}

def pureSurvivingWrapCount (A : SectorBCriticalRoleBranchA P) : ℕ :=
  Nat.card (PureSurvivingWraps A)

theorem pureAlive_z_or_y_zero (A : SectorBCriticalRoleBranchA P) :
    (pureAlive A).2.2=0 ∨ (pureAlive A).2.1=0 := by
  unfold pureAlive pureAliveRaw
  split_ifs <;> simp [pureNormal]

theorem all_source_plane_of_first_shape (A : SectorBCriticalRoleBranchA P)
    (hs : ∀ v : ModelSources P.M.base A.reindex,
      v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex →
      ((pureSourceNormal A v).1=0 ∧ (pureSourceNormal A v).2.1=0) ∨
        (pureSourceNormal A v).2.2=0)
    (v : ModelSources P.M.base A.reindex) :
    (pureSourceNormal A v).1=0 ∨ (pureSourceNormal A v).2.1=0 ∨
      (pureSourceNormal A v).2.2=0 := by
  by_cases hv : v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex
  · rcases hs v hv with h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inr h)
  · exact pure_nonfirst_source_plane A v hv

theorem surviving_wrap_axes (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1)
    (hs : ∀ v : ModelSources P.M.base A.reindex,
      v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex →
      ((pureSourceNormal A v).1=0 ∧ (pureSourceNormal A v).2.1=0) ∨
        (pureSourceNormal A v).2.2=0)
    {w : Monomial} (hw : w∈PureSurvivingWraps A) : w.2.1=0 ∧ w.2.2=0 := by
  obtain hwmin := polynomialMinimal_mem_generator _ _ hw.1
  rcases hwmin with hlead | horig | ⟨g,hg,hgy,rfl⟩
  · exact (hw.2 (Or.inl hlead)).elim
  · exact (hw.2 (Or.inr horig)).elim
  · refine ⟨rfl,?_⟩
    rcases hg with ⟨v,rfl⟩ | rfl
    · by_contra hgz
      have hz : 0<(pureSourceNormal A v).2.2 := by
        change (pureSourceNormal A v).2.2≠0 at hgz
        omega
      have hx : (pureSourceNormal A v).1=0 := by
        rcases all_source_plane_of_first_shape A hs v with h | h | h
        · exact h
        · omega
        · omega
      have hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
          (routingM_pos _ _)*routingM P.M.base A.reindex := by
        intro hf
        rcases hs v hf with h | h <;> omega
      exact nonfirst_positive_yz_wrap_redundant A hk v hx hgy hz hnf hw.1
    · rcases pureAlive_z_or_y_zero A with h | h
      · exact h
      · omega

theorem pure_surviving_wrap_count_le_one (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1)
    (hs : ∀ v : ModelSources P.M.base A.reindex,
      v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex →
      ((pureSourceNormal A v).1=0 ∧ (pureSourceNormal A v).2.1=0) ∨
        (pureSourceNormal A v).2.2=0) : pureSurvivingWrapCount A≤1 := by
  have : Subsingleton (PureSurvivingWraps A) := ⟨by
    rintro ⟨w,hw⟩ ⟨z,hz⟩
    have ha := surviving_wrap_axes A hk hs hw
    have hb := surviving_wrap_axes A hk hs hz
    apply Subtype.ext
    rcases le_total w.1 z.1 with h | h
    · exact hz.1.2 w hw.1.1 h (by omega) (by omega)
    · exact (hw.1.2 z hz.1.1 h (by omega) (by omega)).symm⟩
  let := this
  by_cases hne : Nonempty (PureSurvivingWraps A)
  · let := hne
    exact (Nat.card_unique (α := PureSurvivingWraps A)).le
  · let : IsEmpty (PureSurvivingWraps A) := ⟨fun x => hne ⟨x⟩⟩
    simp [pureSurvivingWrapCount]

theorem internal_surviving_wrap_budget (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp≠bm)
    (hp : IsPureBoundaryComponent G bp) (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,(componentSupport P.M.base G.internalDegree C).card=1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.internalDegree ∧ A.mixedDegree=G.boundaryDegree ∧
      (∀ v : ModelSources P.M.base A.reindex,
        (pureSourceNormal A v).1=0 ∨ (pureSourceNormal A v).2.1=0 ∨
          (pureSourceNormal A v).2.2=0) ∧ pureSurvivingWrapCount A≤1 := by
  obtain ⟨A,ha,hb,hs⟩ := internal_first_source_shape P G bp bm hne hp hm hi
  have hk : killedCount P.M A.mixedDegree=1 := by rw [hb]; exact G.boundarySignature.2
  exact ⟨A,ha,hb,all_source_plane_of_first_shape A hs,pure_surviving_wrap_count_le_one A hk hs⟩

end NS25Lean.L5A2C4OR43
