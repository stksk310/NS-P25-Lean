import NS25Lean.P2SectorCPureBoundaryTypeBudgetR46
set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR47
open FourGeneratedBridge
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR33 L5A2C4OR35
  L5A2C4OR39 L5A2C4OR40 L5A2C4OR42 L5A2C4OR43 L5A2C4OR44 L5A2C4OR46
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Full support can only occur at the intrinsic first principal source. -/
theorem boundary_first_z_zero_no_full_source (A : SectorBCriticalRoleBranchA P)
    (v : ModelSources P.M.base A.reindex)
    (hv : v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hz : (pureSourceNormal A v).2.2=0) : boundaryFullSourceCount A=0 := by
  let : IsEmpty {u : ModelSources P.M.base A.reindex // FullySupported (pureSourceNormal A u)} :=
    ⟨by
      rintro ⟨u,hu⟩
      have hf := pure_positive_coordinates_full_support A (pureSourceNormal A u)
        hu.1 hu.2.1 hu.2.2
      rw [(pureSourceNormal_spec A u).1] at hf
      have he := model_full_support_source_is_first _ _ u hf
      have huv : u=v := Subtype.ext (he.trans hv.symm)
      subst u
      have hup : 0<(pureSourceNormal A v).2.2 := hu.2.2
      omega⟩
  exact Nat.card_of_isEmpty

theorem boundary_first_z_zero_compensation (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v : ModelSources P.M.base A.reindex)
    (hv : v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hz : (pureSourceNormal A v).2.2=0) :
    boundarySurvivingWrapCount A+boundaryFullSourceCount A≤
      Nat.card {z // z∈boundaryBorderExceptional A} := by
  rw [boundary_first_z_zero_no_surviving_wrap G A hm hk hl v hv hz,
    boundary_first_z_zero_no_full_source A v hv hz]
  exact Nat.zero_le _

/-- A literal normal cut has an original divisor unless a wrapped divisor
can fit both cross coefficients. This is the exact cut dictionary, not a
unique-factorization assumption. -/
theorem boundary_small_cross_cut_original (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (z : Monomial) (hz : z.2.2<d A)
    (hcross : z.1<r A ∨ z.2.1<s A)
    (hcut : monomialDegree P.M.base A.reindex z∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    ∃ g∈boundaryOriginals A, Divides g z := by
  have ht := (boundary_normal_mem_iff_cut A hk z).mpr hcut
  rw [boundaryNormal_fixed A z hz] at ht
  obtain ⟨g,hg,hx,hy,hz'⟩ := ht
  rcases hg with hg | ⟨w,hw,hwz,rfl⟩
  · exact ⟨g,hg,hx,hy,hz'⟩
  · simp only [boundaryWrap] at hx hy
    omega

/-- The inverse internal move supplies the missing c predecessor. -/
theorem boundary_zero_z_neck_divisor_full (A : SectorBCriticalRoleBranchA P)
    (g : Monomial) (hz : g.2.2=0) (hx : r A≤g.1) (hy : s A≤g.2.1) :
    ModelFullSupport P.M.base A.reindex (monomialDegree P.M.base A.reindex g) := by
  have hr := (branchA_symmetricTailData A).r_pos
  have hs := (branchA_symmetricTailData A).s_pos
  let w : Monomial := (g.1-r A,g.2.1-s A,d A)
  have hnorm : boundaryNormal A w=g := by
    ext <;> simp [boundaryNormal,w,Nat.div_self (boundary_d_pos A),
      Nat.sub_add_cancel hx,Nat.sub_add_cancel hy,hz]
  have he := boundaryNormal_degree A w
  rw [hnorm] at he
  have hg := monomial_positive_predecessors P.M.base A.reindex g
  have hw := monomial_positive_predecessors P.M.base A.reindex w
  exact ⟨hg.1 (by omega),hg.2.1 (by omega),he ▸ hw.2.2 (boundary_d_pos A)⟩

theorem boundary_neck_cut_first_zero (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hcut : d A*routingC P.M.base A.reindex∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    ∃ v : ModelSources P.M.base A.reindex,
      v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex ∧
      pureSourceNormal A v=(r A,s A,0) := by
  have hn := boundary_internal_predecessors_not_cut G A hm
  have hrel := (branchA_symmetricTailData A).mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hrel
  have hmin : IsMinimalTailGenerator (routingH P.M.base A.reindex).toAddSubmonoid
      (cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
      (d A*routingC P.M.base A.reindex) := by
    apply (minimalTail_iff_literal _ _ _).mpr
    refine ⟨hcut,literal_minimal_of_generator_predecessors _ _ _ ?_ ?_ ?_⟩
    · intro x hx he; exact hn.1 (by simpa [he] using hx)
    · intro x hx he; exact hn.2.1 (by simpa [he] using hx)
    · intro x hx he; exact hn.2.2 (by simpa [he] using hx)
  let v : ModelSources P.M.base A.reindex := ⟨_,hmin⟩
  have he : monomialDegree P.M.base A.reindex (r A,s A,0)=v.val := by
    simpa [v,monomialDegree,normalizedGrid] using hrel.symm
  have hfull := boundary_zero_z_neck_divisor_full A (r A,s A,0) rfl (le_refl _) (le_refl _)
  rw [he] at hfull
  obtain ⟨_,_,_,_,_,_,_,hsa⟩ := boundary_actual_coefficient_bounds G A hm hk
  have hnormal : pureSourceNormal A v=(r A,s A,0) := pure_tail_normal_unique A
    (pureSourceNormal_spec A v).2 ⟨hsa,boundary_d_pos A⟩
    ((pureSourceNormal_spec A v).1.trans he.symm)
  exact ⟨v,model_full_support_source_is_first _ _ v hfull,hnormal⟩

/-- All zero-z originals lie on the two sides of the neck in the only
remaining branch. Both exclusions use actual cyclic-cut semantics. -/
theorem boundary_plane_original_sides (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (v : ModelSources P.M.base A.reindex)
    (hv : v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvz : 0<(pureSourceNormal A v).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    {g : Monomial} (hg : g∈boundaryOriginals A) (hgz : g.2.2=0) :
    (r A<g.1 ∧ g.2.1<s A) ∨ (g.1<r A ∧ s A<g.2.1) := by
  obtain ⟨_,_,_,hr,_,_,hs,hsa⟩ := boundary_actual_coefficient_bounds G A hm hk
  have hrel := (branchA_symmetricTailData A).mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hrel
  have hnlo : ¬(g.1≤r A ∧ g.2.1≤s A) := by
    rintro ⟨hx,hy⟩
    have hc := cut_add_tail (boundaryStrip_cut A hk (Or.inl hg))
      (grid_mem_H P.M.base A.reindex (r A-g.1,s A-g.2.1,0))
    have he : g+(r A-g.1,s A-g.2.1,0)=(r A,s A,0) := by
      ext <;> simp [hgz,Nat.add_sub_of_le hx,Nat.add_sub_of_le hy]
    rw [←monomialDegree_add,he] at hc
    apply hneck
    simpa [monomialDegree,normalizedGrid,←hrel] using hc
  have hnhi : ¬(r A≤g.1 ∧ s A≤g.2.1) := by
    rintro ⟨hx,hy⟩
    rcases hg with ⟨u,rfl⟩ | rfl
    · have hf := boundary_zero_z_neck_divisor_full A (pureSourceNormal A u) hgz hx hy
      rw [(pureSourceNormal_spec A u).1] at hf
      have he := model_full_support_source_is_first _ _ u hf
      have huv : u=v := Subtype.ext (he.trans hv.symm)
      subst u
      omega
    · change r A≤0 at hx
      omega
  omega

def boundaryPlaneOriginals (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  {g | g∈boundaryOriginals A ∧ g.2.2=0}

theorem boundary_right_cap_exists (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    ∃ x : ℕ, ∃ g∈boundaryPlaneOriginals A, g.1=x ∧ g.2.1<s A := by
  obtain ⟨v,p,_,_,hg⟩ := boundary_pure_x_source A hk
  refine ⟨p,(p,0,0),⟨Or.inl ⟨v,hg⟩,rfl⟩,rfl,?_⟩
  exact (branchA_symmetricTailData A).s_pos

theorem boundary_left_cap_exists (A : SectorBCriticalRoleBranchA P) :
    ∃ y : ℕ, ∃ g∈boundaryPlaneOriginals A, g.2.1=y ∧ g.1<r A := by
  refine ⟨alpha A,(0,alpha A,0),⟨Or.inr rfl,rfl⟩,rfl,?_⟩
  exact (branchA_symmetricTailData A).r_pos

/-- Astar is chosen only from actual zero-z original generators. -/
def boundaryRightCap (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) : ℕ := by
  classical
  exact Nat.find (boundary_right_cap_exists A hk)

/-- Dstar includes the alive pure-y original, including its equality endpoint. -/
def boundaryLeftCap (A : SectorBCriticalRoleBranchA P) : ℕ := by
  classical
  exact Nat.find (boundary_left_cap_exists A)

theorem boundary_right_cap_attained (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    ∃ g∈boundaryPlaneOriginals A, g.1=boundaryRightCap A hk ∧ g.2.1<s A := by
  classical
  exact Nat.find_spec (boundary_right_cap_exists A hk)

theorem boundary_left_cap_attained (A : SectorBCriticalRoleBranchA P) :
    ∃ g∈boundaryPlaneOriginals A, g.2.1=boundaryLeftCap A ∧ g.1<r A := by
  classical
  exact Nat.find_spec (boundary_left_cap_exists A)

theorem boundary_right_cap_le (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    {g : Monomial} (hg : g∈boundaryPlaneOriginals A) (hy : g.2.1<s A) :
    boundaryRightCap A hk≤g.1 := by
  classical
  exact Nat.find_min' (boundary_right_cap_exists A hk) ⟨g,hg,rfl,hy⟩

theorem boundary_left_cap_le (A : SectorBCriticalRoleBranchA P)
    {g : Monomial} (hg : g∈boundaryPlaneOriginals A) (hx : g.1<r A) :
    boundaryLeftCap A≤g.2.1 := by
  classical
  exact Nat.find_min' (boundary_left_cap_exists A) ⟨g,hg,rfl,hx⟩

theorem boundary_actual_cap_bounds (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (v : ModelSources P.M.base A.reindex)
    (hv : v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvz : 0<(pureSourceNormal A v).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    r A<boundaryRightCap A hk ∧ boundaryRightCap A hk<beta A ∧
      s A<boundaryLeftCap A ∧ boundaryLeftCap A≤alpha A := by
  obtain ⟨g,hg,hgx,hgy⟩ := boundary_right_cap_attained A hk
  have hgs := boundary_plane_original_sides G A hm hk v hv hvz hneck hg.1 hg.2
  obtain ⟨t,ht,hty,htx⟩ := boundary_left_cap_attained A
  have hts := boundary_plane_original_sides G A hm hk v hv hvz hneck ht.1 ht.2
  obtain ⟨u,p,hup,_,_,hpb,hs,_⟩ := boundary_actual_coefficient_bounds G A hm hk
  have hright := boundary_right_cap_le A hk
    (g:=(p,0,0)) ⟨Or.inl ⟨u,hup⟩,rfl⟩ hs
  have hleft := boundary_left_cap_le A (g:=(0,alpha A,0))
    ⟨Or.inr rfl,rfl⟩ (branchA_symmetricTailData A).r_pos
  change boundaryRightCap A hk≤p at hright
  change boundaryLeftCap A≤alpha A at hleft
  omega

/-- Exact central-quadrant envelope of the actual plane ideal. -/
theorem boundary_central_plane_envelope (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (v : ModelSources P.M.base A.reindex)
    (hv : v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvz : 0<(pureSourceNormal A v).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    (x y : ℕ) (hx : r A≤x) (hy : s A≤y) :
    (x,y,0)∈monomialClosure (boundaryPlaneOriginals A) ↔
      boundaryRightCap A hk≤x ∨ boundaryLeftCap A≤y := by
  constructor
  · rintro ⟨g,hg,hgx,hgy,_⟩
    change g.2.1≤y at hgy
    rcases boundary_plane_original_sides G A hm hk v hv hvz hneck hg.1 hg.2 with h | h
    · exact Or.inl ((boundary_right_cap_le A hk hg h.2).trans hgx)
    · exact Or.inr ((boundary_left_cap_le A hg h.1).trans hgy)
  · rintro (hr | hl)
    · obtain ⟨g,hg,hgx,hgy⟩ := boundary_right_cap_attained A hk
      exact ⟨g,hg,by omega,show g.2.1≤y from by omega,by simpa using hg.2.le⟩
    · obtain ⟨g,hg,hgy,hgx⟩ := boundary_left_cap_attained A
      exact ⟨g,hg,by omega,show g.2.1≤y from by omega,by simpa using hg.2.le⟩

theorem boundary_central_rectangle_exclusion (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (v : ModelSources P.M.base A.reindex)
    (hv : v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvz : 0<(pureSourceNormal A v).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    (x y : ℕ) (hx : x<boundaryRightCap A hk) (hy : y<boundaryLeftCap A) :
    (x,y,0)∉monomialClosure (boundaryPlaneOriginals A) := by
  rintro ⟨g,hg,hgx,hgy,_⟩
  change g.2.1≤y at hgy
  rcases boundary_plane_original_sides G A hm hk v hv hvz hneck hg.1 hg.2 with h | h
  · have := boundary_right_cap_le A hk hg h.2; omega
  · have := boundary_left_cap_le A hg h.1; omega

theorem boundary_plane_cut_of_small_cross (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (x y : ℕ) (hcross : x<r A ∨ y<s A)
    (hcut : monomialDegree P.M.base A.reindex (x,y,0)∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    (x,y,0)∈monomialClosure (boundaryPlaneOriginals A) := by
  obtain ⟨g,hg,hdiv⟩ := boundary_small_cross_cut_original A hk (x,y,0)
    (boundary_d_pos A) hcross hcut
  have hz : g.2.2=0 := Nat.eq_zero_of_le_zero hdiv.2.2
  exact ⟨g,⟨hg,hz⟩,hdiv⟩

/-- Actual nonfirst xz returns force the strict predecessor of their wrap
into the zero-z plane ideal. -/
theorem boundary_nonfirst_xz_strict_plane (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (v : ModelSources P.M.base A.reindex)
    (hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hx : 0<(pureSourceNormal A v).1) (hy : (pureSourceNormal A v).2.1=0)
    (hz : 0<(pureSourceNormal A v).2.2) :
    ((pureSourceNormal A v).1+r A,s A-1,0)∈monomialClosure (boundaryPlaneOriginals A) := by
  let g := pureSourceNormal A v
  have hg : monomialDegree P.M.base A.reindex g=v.val := (pureSourceNormal_spec A v).1
  have hgz : g.2.2<d A := (pureSourceNormal_spec A v).2.2
  obtain ⟨n,t,hn,_,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ v hnf
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base A.reindex (x,y,z)=t := hfac.symm
  have sep := source_return_coordinate_separation _ _ v g (x,y,z) hg hn
    (he.trans (by rw [hd]))
  have x0 : x=0 := sep.1 hx
  have z0 : z=0 := sep.2.2 hz
  have yp : 0<y := by
    by_contra hnot
    have y0 : y=0 := by omega
    simp [monomialDegree,normalizedGrid,x0,y0,z0] at hd
    omega
  have hrel := (branchA_symmetricTailData A).mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hrel
  have hs := (branchA_symmetricTailData A).s_pos
  have heq : monomialDegree P.M.base A.reindex (g.1+r A,s A-1,0)=
      n*routingM P.M.base A.reindex+monomialDegree P.M.base A.reindex (0,y-1,d A-g.2.2) := by
    have hyy := congrArg (fun t => t*routingB P.M.base A.reindex)
      (Nat.sub_add_cancel (by omega : 1≤y))
    have hss := congrArg (fun t => t*routingB P.M.base A.reindex)
      (Nat.sub_add_cancel (by omega : 1≤s A))
    have hzz := congrArg (fun t => t*routingC P.M.base A.reindex)
      (Nat.sub_add_cancel (Nat.le_of_lt hgz))
    simp only [Nat.add_mul,one_mul] at hyy hss hzz
    simp only [monomialDegree,normalizedGrid,x0,z0,zero_mul,zero_add,add_zero] at hd
    change g.2.1=0 at hy
    simp only [monomialDegree,normalizedGrid,hy,zero_mul,add_zero] at hg
    simp only [monomialDegree,normalizedGrid,Nat.add_mul,zero_mul,zero_add,add_zero]
    omega
  apply boundary_plane_cut_of_small_cross A hk _ _ (Or.inr (by omega))
  exact ⟨grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ _,heq⟩

theorem boundary_nonfirst_yz_strict_plane (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (v : ModelSources P.M.base A.reindex)
    (hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hx : (pureSourceNormal A v).1=0) (hy : 0<(pureSourceNormal A v).2.1)
    (hz : 0<(pureSourceNormal A v).2.2) :
    (r A-1,(pureSourceNormal A v).2.1+s A,0)∈monomialClosure (boundaryPlaneOriginals A) := by
  let g := pureSourceNormal A v
  have hg : monomialDegree P.M.base A.reindex g=v.val := (pureSourceNormal_spec A v).1
  have hgz : g.2.2<d A := (pureSourceNormal_spec A v).2.2
  obtain ⟨n,t,hn,_,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ v hnf
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base A.reindex (x,y,z)=t := hfac.symm
  have sep := source_return_coordinate_separation _ _ v g (x,y,z) hg hn
    (he.trans (by rw [hd]))
  have y0 : y=0 := sep.2.1 hy
  have z0 : z=0 := sep.2.2 hz
  have xp : 0<x := by
    by_contra hnot
    have x0 : x=0 := by omega
    simp [monomialDegree,normalizedGrid,x0,y0,z0] at hd
    omega
  have hrel := (branchA_symmetricTailData A).mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hrel
  have hr := (branchA_symmetricTailData A).r_pos
  have heq : monomialDegree P.M.base A.reindex (r A-1,g.2.1+s A,0)=
      n*routingM P.M.base A.reindex+monomialDegree P.M.base A.reindex (x-1,0,d A-g.2.2) := by
    have hxx := congrArg (fun t => t*routingA P.M.base A.reindex)
      (Nat.sub_add_cancel (by omega : 1≤x))
    have hrr := congrArg (fun t => t*routingA P.M.base A.reindex)
      (Nat.sub_add_cancel (by omega : 1≤r A))
    have hzz := congrArg (fun t => t*routingC P.M.base A.reindex)
      (Nat.sub_add_cancel (Nat.le_of_lt hgz))
    simp only [Nat.add_mul,one_mul] at hxx hrr hzz
    simp only [monomialDegree,normalizedGrid,y0,z0,zero_mul,add_zero] at hd
    change g.1=0 at hx
    simp only [monomialDegree,normalizedGrid,hx,zero_mul,zero_add] at hg
    simp only [monomialDegree,normalizedGrid,Nat.add_mul,zero_mul,add_zero]
    omega
  apply boundary_plane_cut_of_small_cross A hk _ _ (Or.inl (by omega))
  exact ⟨grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ _,heq⟩

theorem boundary_nonfirst_xz_projection_lower (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (v : ModelSources P.M.base A.reindex)
    (hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hx : 0<(pureSourceNormal A v).1) (hy : (pureSourceNormal A v).2.1=0)
    (hz : 0<(pureSourceNormal A v).2.2) :
    boundaryRightCap A hk-r A≤(pureSourceNormal A v).1 := by
  obtain ⟨g,hg,hgx,hgy,_⟩ := boundary_nonfirst_xz_strict_plane A hk v hnf hx hy hz
  change g.2.1≤s A-1 at hgy
  have hs := (branchA_symmetricTailData A).s_pos
  have hgs : g.2.1<s A := by omega
  have hcap := boundary_right_cap_le A hk hg hgs
  omega

theorem boundary_nonfirst_yz_projection_lower (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (v : ModelSources P.M.base A.reindex)
    (hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hx : (pureSourceNormal A v).1=0) (hy : 0<(pureSourceNormal A v).2.1)
    (hz : 0<(pureSourceNormal A v).2.2) :
    boundaryLeftCap A-s A≤(pureSourceNormal A v).2.1 := by
  obtain ⟨g,hg,hgx,hgy,_⟩ := boundary_nonfirst_yz_strict_plane A hk v hnf hx hy hz
  change g.1≤r A-1 at hgx
  change g.2.1≤(pureSourceNormal A v).2.1+s A at hgy
  have hr := (branchA_symmetricTailData A).r_pos
  have hgr : g.1<r A := by omega
  have hcap := boundary_left_cap_le A hg hgr
  omega

theorem boundary_neck_cut_compensation (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (hcut : d A*routingC P.M.base A.reindex∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    boundarySurvivingWrapCount A+boundaryFullSourceCount A≤
      Nat.card {z // z∈boundaryBorderExceptional A} := by
  obtain ⟨v,hv,hg⟩ := boundary_neck_cut_first_zero G A hm hk hcut
  exact boundary_first_z_zero_compensation G A hm hk hl v hv (by rw [hg])

theorem boundary_neck_cut_type_bound (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (hcut : d A*routingC P.M.base A.reindex∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount := by
  have hc := boundary_neck_cut_compensation G A hm hk hl hcut
  have hb := boundary_corrected_type_budget G A hm hk hl
  omega

/-- A zero-z nonfirst source below the pure-x critical exponent has a
genuine small c-only return. The pure-x endpoint uses the alive y axis. -/
theorem boundary_nonfirst_zero_z_small_c_return (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v : ModelSources P.M.base A.reindex)
    (hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hx : 0<(pureSourceNormal A v).1) (hxb : (pureSourceNormal A v).1<beta A)
    (hz : (pureSourceNormal A v).2.2=0) :
    ∃ n j : ℕ, 0<n ∧ 0<j ∧ j<d A ∧ v.val=n*routingM P.M.base A.reindex+j*routingC P.M.base A.reindex := by
  let g := pureSourceNormal A v
  have hg : monomialDegree P.M.base A.reindex g=v.val := (pureSourceNormal_spec A v).1
  change g.2.2=0 at hz
  change 0<g.1 at hx
  change g.1<beta A at hxb
  obtain ⟨n,t,hn,_,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ v hnf
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  obtain ⟨w,hwy,hwz,hew,_⟩ := pure_tail_quotient_normal_exists A ℚ (x,y,z)
  have hd : monomialDegree P.M.base A.reindex w=t := hew.symm.trans hfac.symm
  have sep := source_return_coordinate_separation _ _ v g w hg hn (he.trans (by rw [hd]))
  have wx0 : w.1=0 := sep.1 hx
  have wy0 : w.2.1=0 := by
    by_contra hnot
    have wyp : 0<w.2.1 := Nat.pos_of_ne_zero hnot
    have gy0 : g.2.1=0 := by
      by_contra hgy
      have := sep.2.1 (Nat.pos_of_ne_zero hgy)
      omega
    have hrel := (branchA_symmetricTailData A).pure_relation
    rw [←routingA_eq_n0,←routingB_eq_n1] at hrel
    have heq : (alpha A-w.2.1)*routingB P.M.base A.reindex=
        n*routingM P.M.base A.reindex+
          monomialDegree P.M.base A.reindex (beta A-g.1,0,w.2.2) := by
      have hyy := congrArg (fun t => t*routingB P.M.base A.reindex)
        (Nat.sub_add_cancel hwy.le)
      have hxx := congrArg (fun t => t*routingA P.M.base A.reindex)
        (Nat.sub_add_cancel hxb.le)
      simp only [Nat.add_mul] at hyy hxx
      simp only [monomialDegree,normalizedGrid,wx0,zero_mul,zero_add] at hd
      simp only [monomialDegree,normalizedGrid,gy0,hz,zero_mul,add_zero] at hg
      simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
      omega
    have hc : (alpha A-w.2.1)*routingB P.M.base A.reindex∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) :=
      ⟨by simpa [monomialDegree,normalizedGrid] using grid_mem_H P.M.base A.reindex (0,alpha A-w.2.1,0),
        n,hn,_,grid_mem_H _ _ _,heq⟩
    have := (boundary_axis_cut_bounds G A hm hl).1 _ hc
    omega
  have hj : 0<w.2.2 := by
    by_contra hnot
    have wz0 : w.2.2=0 := by omega
    simp [monomialDegree,normalizedGrid,wx0,wy0,wz0] at hd
    omega
  refine ⟨n,w.2.2,hn,hj,hwz,?_⟩
  have htval : t=w.2.2*routingC P.M.base A.reindex := by
    simpa only [monomialDegree,normalizedGrid,wx0,wy0,zero_mul,zero_add] using hd.symm
  exact he.trans (congrArg (fun t => n*routingM P.M.base A.reindex+t) htval)

theorem boundary_right_small_return_cap (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hv0y : 0<(pureSourceNormal A v0).2.1) (hv0z : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    ∃ v : ModelSources P.M.base A.reindex, ∃ j : ℕ,
      v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex ∧
      0<j ∧ j<d A ∧ pureSourceNormal A v=(boundaryRightCap A hk-r A,0,j) := by
  obtain ⟨g,hg,hgx,hgy⟩ := boundary_right_cap_attained A hk
  have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hv0z hneck
  have hr := (branchA_symmetricTailData A).r_pos
  have hs := (branchA_symmetricTailData A).s_pos
  have hsrc : ∃ t : ModelSources P.M.base A.reindex, pureSourceNormal A t=g := by
    rcases hg.1 with h | h
    · exact h
    · subst g
      change alpha A<s A at hgy
      obtain ⟨_,_,_,_,_,_,_,hsa⟩ := boundary_actual_coefficient_bounds G A hm hk
      omega
  obtain ⟨t,htg⟩ := hsrc
  have hnf : t.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex := by
    intro he
    have ht0 : t=v0 := Subtype.ext (he.trans hv0.symm)
    have hz := hg.2
    rw [←htg,ht0] at hz
    omega
  obtain ⟨n,j,hn,hj,hjd,hret⟩ := boundary_nonfirst_zero_z_small_c_return G A hm hl t hnf
    (by rw [htg,hgx]; omega) (by rw [htg,hgx]; exact hb.2.1) (by rw [htg]; exact hg.2)
  have hrel := (branchA_symmetricTailData A).mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hrel
  let w : Monomial := (boundaryRightCap A hk-r A,0,d A-j)
  have hwz : w.2.2<d A := by dsimp [w]; omega
  have hwcut : monomialDegree P.M.base A.reindex w∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    have hdeg := (pureSourceNormal_spec A t).1
    rw [htg] at hdeg
    have hxx := congrArg (fun t => t*routingA P.M.base A.reindex)
      (Nat.sub_add_cancel (show r A≤boundaryRightCap A hk by omega))
    have hyy := congrArg (fun t => t*routingB P.M.base A.reindex)
      (Nat.sub_add_cancel (show g.2.1≤s A by omega))
    have hzz := congrArg (fun t => t*routingC P.M.base A.reindex) (Nat.sub_add_cancel hjd.le)
    simp only [Nat.add_mul] at hxx hyy hzz
    have heq : monomialDegree P.M.base A.reindex w=
        n*routingM P.M.base A.reindex+monomialDegree P.M.base A.reindex (0,s A-g.2.1,0) := by
      simp only [monomialDegree,normalizedGrid,hg.2,hgx,zero_mul,add_zero] at hdeg
      simp only [monomialDegree,normalizedGrid,w,zero_mul,zero_add,add_zero]
      omega
    exact ⟨grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ _,heq⟩
  obtain ⟨q,hq,hdiv⟩ := boundary_small_cross_cut_original A hk w hwz (Or.inr hs) hwcut
  have qy0 : q.2.1=0 := Nat.eq_zero_of_le_zero hdiv.2.1
  obtain ⟨u,hu⟩ : ∃ u : ModelSources P.M.base A.reindex, pureSourceNormal A u=q := by
    rcases hq with h | h
    · exact h
    · subst q
      change alpha A=0 at qy0
      have := pure_alpha_pos A
      omega
  have ux : 0<(pureSourceNormal A u).1 := by
    by_contra hnot
    have qx0 : q.1=0 := by rw [←hu]; omega
    have hc := u.property.1
    rw [←(pureSourceNormal_spec A u).1,hu] at hc
    have hc' : q.2.2*routingC P.M.base A.reindex∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
      simpa [monomialDegree,normalizedGrid,qx0,qy0] using hc
    have := (boundary_axis_cut_bounds G A hm hl).2 _ hc'
    have hqz := hdiv.2.2
    dsimp [w] at hqz
    omega
  have uz : 0<(pureSourceNormal A u).2.2 := by
    by_contra hnot
    have qz0 : q.2.2=0 := by rw [←hu]; omega
    have hcap := boundary_right_cap_le A hk ⟨hq,qz0⟩ (by rw [qy0]; exact hs)
    have hqx := hdiv.1
    dsimp [w] at hqx
    omega
  have unf : u.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex := by
    intro he
    have he' : u=v0 := Subtype.ext (he.trans hv0.symm)
    have hy : (pureSourceNormal A u).2.1=0 := by rw [hu]; exact qy0
    rw [he'] at hy
    omega
  have uy : (pureSourceNormal A u).2.1=0 := by rw [hu]; exact qy0
  have hlow := boundary_nonfirst_xz_projection_lower A hk u unf ux uy uz
  have heqx : (pureSourceNormal A u).1=boundaryRightCap A hk-r A := by
    rw [hu] at hlow ⊢
    exact Nat.le_antisymm hdiv.1 hlow
  exact ⟨u,(pureSourceNormal A u).2.2,unf,uz,(pureSourceNormal_spec A u).2.2,
    Prod.ext heqx (Prod.ext uy rfl)⟩

theorem boundary_left_small_return_cap (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hv0x : 0<(pureSourceNormal A v0).1) (hv0z : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    ∃ v : ModelSources P.M.base A.reindex, ∃ j : ℕ,
      v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex ∧
      0<j ∧ j<d A ∧ pureSourceNormal A v=(0,boundaryLeftCap A-s A,j) := by
  have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hv0z hneck
  obtain ⟨axis,p,haxis,hr,hrp,hpb,hs,hsa⟩ := boundary_actual_coefficient_bounds G A hm hk
  have hrel := (branchA_symmetricTailData A).mixed_relation
  rw [←routingA_eq_n0,←routingB_eq_n1,←routingC_eq_n2] at hrel
  have hnf_of_zero {t : ModelSources P.M.base A.reindex}
      (hz : (pureSourceNormal A t).2.2=0) :
      t.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex := by
    intro he
    have he' : t=v0 := Subtype.ext (he.trans hv0.symm)
    rw [he'] at hz
    omega
  have hex : ∃ j : ℕ, 0<j ∧ j<d A ∧
      monomialDegree P.M.base A.reindex (0,boundaryLeftCap A-s A,d A-j)∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
    by_cases hstrict : boundaryLeftCap A<alpha A
    · obtain ⟨g,hg,hgy,hgx⟩ := boundary_left_cap_attained A
      obtain ⟨t,htg⟩ : ∃ t : ModelSources P.M.base A.reindex, pureSourceNormal A t=g := by
        rcases hg.1 with h | h
        · exact h
        · subst g
          change alpha A=boundaryLeftCap A at hgy
          omega
      have htx : 0<(pureSourceNormal A t).1 := by
        by_contra hnot
        have gx0 : g.1=0 := by rw [←htg]; omega
        have hc := t.property.1
        rw [←(pureSourceNormal_spec A t).1,htg] at hc
        have hc' : g.2.1*routingB P.M.base A.reindex∈
            cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
          simpa [monomialDegree,normalizedGrid,gx0,hg.2] using hc
        have := (boundary_axis_cut_bounds G A hm hl).1 _ hc'
        omega
      obtain ⟨n,j,hn,hj,hjd,hret⟩ := boundary_nonfirst_zero_z_small_c_return G A hm hl t
        (hnf_of_zero (by rw [htg]; exact hg.2)) htx
        (by rw [htg]; omega) (by rw [htg]; exact hg.2)
      have hdeg := (pureSourceNormal_spec A t).1
      rw [htg] at hdeg
      have hxx := congrArg (fun t => t*routingA P.M.base A.reindex)
        (Nat.sub_add_cancel hgx.le)
      have hyy := congrArg (fun t => t*routingB P.M.base A.reindex)
        (Nat.sub_add_cancel hb.2.2.1.le)
      have hzz := congrArg (fun t => t*routingC P.M.base A.reindex) (Nat.sub_add_cancel hjd.le)
      simp only [Nat.add_mul] at hxx hyy hzz
      have heq : monomialDegree P.M.base A.reindex (0,boundaryLeftCap A-s A,d A-j)=
          n*routingM P.M.base A.reindex+monomialDegree P.M.base A.reindex (r A-g.1,0,0) := by
        simp only [monomialDegree,normalizedGrid,hg.2,hgy,zero_mul,add_zero] at hdeg
        simp only [monomialDegree,normalizedGrid,zero_mul,zero_add,add_zero]
        omega
      exact ⟨j,hj,hjd,grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ _,heq⟩
    · have heqcap : boundaryLeftCap A=alpha A := by omega
      have haxisz : (pureSourceNormal A axis).2.2=0 := by rw [haxis]
      obtain ⟨n,j,hn,hj,hjd,hret⟩ := boundary_nonfirst_zero_z_small_c_return G A hm hl axis
        (hnf_of_zero haxisz) (by rw [haxis]; omega) (by rw [haxis]; exact hpb) haxisz
      have hdeg := (pureSourceNormal_spec A axis).1
      rw [haxis] at hdeg
      have hpure := (branchA_symmetricTailData A).pure_relation
      rw [←routingA_eq_n0,←routingB_eq_n1] at hpure
      have hxx := congrArg (fun t => t*routingA P.M.base A.reindex)
        (Nat.sub_add_cancel (show p≤beta A+r A by omega))
      have hyy := congrArg (fun t => t*routingB P.M.base A.reindex) (Nat.sub_add_cancel hsa.le)
      have hzz := congrArg (fun t => t*routingC P.M.base A.reindex) (Nat.sub_add_cancel hjd.le)
      simp only [Nat.add_mul] at hxx hyy hzz
      have heq : monomialDegree P.M.base A.reindex (0,boundaryLeftCap A-s A,d A-j)=
          n*routingM P.M.base A.reindex+monomialDegree P.M.base A.reindex (beta A+r A-p,0,0) := by
        simp only [monomialDegree,normalizedGrid,zero_mul,add_zero] at hdeg
        simp only [monomialDegree,normalizedGrid,heqcap,zero_mul,zero_add,add_zero]
        omega
      exact ⟨j,hj,hjd,grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ _,heq⟩
  obtain ⟨j,hj,hjd,hwcut⟩ := hex
  let w : Monomial := (0,boundaryLeftCap A-s A,d A-j)
  obtain ⟨q,hq,hdiv⟩ := boundary_small_cross_cut_original A hk w (by dsimp [w]; omega)
    (Or.inl hr) hwcut
  have qx0 : q.1=0 := Nat.eq_zero_of_le_zero hdiv.1
  obtain ⟨u,hu⟩ : ∃ u : ModelSources P.M.base A.reindex, pureSourceNormal A u=q := by
    rcases hq with h | h
    · exact h
    · subst q
      have hqy := hdiv.2.1
      change alpha A≤boundaryLeftCap A-s A at hqy
      omega
  have uy : 0<(pureSourceNormal A u).2.1 := by
    by_contra hnot
    have qy0 : q.2.1=0 := by rw [←hu]; omega
    have hc := u.property.1
    rw [←(pureSourceNormal_spec A u).1,hu] at hc
    have hc' : q.2.2*routingC P.M.base A.reindex∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
      simpa [monomialDegree,normalizedGrid,qx0,qy0] using hc
    have := (boundary_axis_cut_bounds G A hm hl).2 _ hc'
    have hqz := hdiv.2.2
    dsimp [w] at hqz
    omega
  have uz : 0<(pureSourceNormal A u).2.2 := by
    by_contra hnot
    have qz0 : q.2.2=0 := by rw [←hu]; omega
    have hcap := boundary_left_cap_le A ⟨hq,qz0⟩ (by rw [qx0]; exact hr)
    have hqy := hdiv.2.1
    dsimp [w] at hqy
    omega
  have ux : (pureSourceNormal A u).1=0 := by rw [hu]; exact qx0
  have unf : u.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex := by
    intro he
    have he' : u=v0 := Subtype.ext (he.trans hv0.symm)
    rw [he'] at ux
    omega
  have hlow := boundary_nonfirst_yz_projection_lower A hk u unf ux uy uz
  have heqy : (pureSourceNormal A u).2.1=boundaryLeftCap A-s A := by
    rw [hu] at hlow ⊢
    exact Nat.le_antisymm hdiv.2.1 hlow
  exact ⟨u,(pureSourceNormal A u).2.2,unf,uz,(pureSourceNormal_spec A u).2.2,
    Prod.ext ux (Prod.ext heqy rfl)⟩

theorem boundary_nonfirst_wrap_in_plane (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v : ModelSources P.M.base A.reindex)
    (hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hz : 0<(pureSourceNormal A v).2.2) :
    boundaryWrap A (pureSourceNormal A v)∈monomialClosure (boundaryPlaneOriginals A) := by
  have hnpure : ¬((pureSourceNormal A v).1=0 ∧ (pureSourceNormal A v).2.1=0) := by
    rintro ⟨hx,hy⟩
    have hc := v.property.1
    rw [←(pureSourceNormal_spec A v).1] at hc
    have hc' : (pureSourceNormal A v).2.2*routingC P.M.base A.reindex∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
      simpa [monomialDegree,normalizedGrid,hx,hy] using hc
    have := (boundary_axis_cut_bounds G A hm hl).2 _ hc'
    have := (pureSourceNormal_spec A v).2.2
    omega
  rcases pure_nonfirst_source_plane A v hnf with hx | hy | hzz
  · have hyp : 0<(pureSourceNormal A v).2.1 := by omega
    obtain ⟨q,hq,hqx,hqy,hqz⟩ := boundary_nonfirst_yz_strict_plane A hk v hnf hx hyp hz
    refine ⟨q,hq,?_,?_,?_⟩
    · change q.1≤(pureSourceNormal A v).1+r A; change q.1≤r A-1 at hqx; omega
    · exact hqy
    · exact hqz
  · have hxp : 0<(pureSourceNormal A v).1 := by omega
    obtain ⟨q,hq,hqx,hqy,hqz⟩ := boundary_nonfirst_xz_strict_plane A hk v hnf hxp hy hz
    refine ⟨q,hq,hqx,?_,hqz⟩
    change q.2.1≤(pureSourceNormal A v).2.1+s A
    change q.2.1≤s A-1 at hqy
    omega
  · omega

theorem boundary_top_mem_iff_original (A : SectorBCriticalRoleBranchA P) (x y : ℕ) :
    (x,y,d A-1)∈monomialClosure (boundaryInitialGenerators A) ↔
      ∃ g∈boundaryOriginals A, g.1≤x ∧ g.2.1≤y := by
  have hd := boundary_d_pos A
  constructor
  · rintro ⟨g,hg,hgx,hgy,hgz⟩
    change g.2.1≤y at hgy
    change g.2.2≤d A-1 at hgz
    rcases hg with rfl | hg | ⟨q,hq,hqz,rfl⟩
    · change d A≤d A-1 at hgz; omega
    · exact ⟨g,hg,hgx,hgy⟩
    · refine ⟨q,hq,?_,?_⟩
      · change q.1+r A≤x at hgx; omega
      · change q.2.1+s A≤y at hgy; omega
  · rintro ⟨g,hg,hgx,hgy⟩
    refine ⟨g,Or.inr (Or.inl hg),hgx,hgy,?_⟩
    change g.2.2≤d A-1
    have := boundaryOriginals_z_lt A hg
    omega

theorem boundary_small_rectangle_original_is_first (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvz : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    {g : Monomial} (hg : g∈boundaryOriginals A)
    (hx : g.1<boundaryRightCap A hk-r A) (hy : g.2.1<boundaryLeftCap A-s A) :
    g=pureSourceNormal A v0 := by
  have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck
  have hgz : 0<g.2.2 := by
    by_contra hnot
    have hz : g.2.2=0 := by omega
    have hN : (g.1,g.2.1,0)∈monomialClosure (boundaryPlaneOriginals A) :=
      ⟨g,⟨hg,hz⟩,le_rfl,le_rfl,by simp [hz]⟩
    exact boundary_central_rectangle_exclusion G A hm hk v0 hv0 hvz hneck _ _
      (by omega) (by omega) hN
  rcases hg with ⟨v,rfl⟩ | rfl
  · by_cases hv : v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex
    · have he : v=v0 := Subtype.ext (hv.trans hv0.symm)
      rw [he]
    · rcases pure_nonfirst_source_plane A v hv with gx0 | gy0 | gz0
      · have gyp : 0<(pureSourceNormal A v).2.1 := by
          by_contra hnot
          have gy0 : (pureSourceNormal A v).2.1=0 := by omega
          have hc := v.property.1
          rw [←(pureSourceNormal_spec A v).1] at hc
          have hc' : (pureSourceNormal A v).2.2*routingC P.M.base A.reindex∈
              cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
            simpa [monomialDegree,normalizedGrid,gx0,gy0] using hc
          have := (boundary_axis_cut_bounds G A hm hl).2 _ hc'
          have := (pureSourceNormal_spec A v).2.2
          omega
        have := boundary_nonfirst_yz_projection_lower A hk v hv gx0 gyp hgz
        omega
      · have gxp : 0<(pureSourceNormal A v).1 := by
          by_contra hnot
          have gx0 : (pureSourceNormal A v).1=0 := by omega
          have hc := v.property.1
          rw [←(pureSourceNormal_spec A v).1] at hc
          have hc' : (pureSourceNormal A v).2.2*routingC P.M.base A.reindex∈
              cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
            simpa [monomialDegree,normalizedGrid,gx0,gy0] using hc
          have := (boundary_axis_cut_bounds G A hm hl).2 _ hc'
          have := (pureSourceNormal_spec A v).2.2
          omega
        have := boundary_nonfirst_xz_projection_lower A hk v hv gxp gy0 hgz
        omega
      · omega
  · change 0<0 at hgz; omega

theorem boundary_cap_cell_standard_and_wrap (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvz : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    (x y : ℕ) (hx : x<boundaryRightCap A hk-r A) (hy : y<boundaryLeftCap A-s A)
    (hnot : ¬((pureSourceNormal A v0).1≤x ∧ (pureSourceNormal A v0).2.1≤y)) :
    (x,y,d A-1)∉monomialClosure (boundaryInitialGenerators A) ∧
      boundaryWrap A (x,y,d A-1)∉monomialClosure (boundaryStripGenerators A) := by
  have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck
  have hN : (x+r A,y+s A,0)∉monomialClosure (boundaryPlaneOriginals A) :=
    boundary_central_rectangle_exclusion G A hm hk v0 hv0 hvz hneck _ _ (by omega) (by omega)
  refine ⟨?_,?_⟩
  · intro hc
    obtain ⟨g,hg,hgx,hgy⟩ := (boundary_top_mem_iff_original A x y).mp hc
    have he := boundary_small_rectangle_original_is_first G A hm hk hl v0 hv0 hvz hneck hg
      (by omega) (by omega)
    rw [he] at hgx hgy
    exact hnot ⟨hgx,hgy⟩
  · rintro ⟨q,hq,hqx,hqy,hqz⟩
    change q.1≤x+r A at hqx
    change q.2.1≤y+s A at hqy
    change q.2.2≤0 at hqz
    rcases hq with hq | ⟨g,hg,hgz,rfl⟩
    · exact hN ⟨q,⟨hq,Nat.eq_zero_of_le_zero hqz⟩,hqx,hqy,hqz⟩
    · rcases hg with ⟨u,rfl⟩ | rfl
      · by_cases hu : u.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
            (routingM_pos _ _)*routingM P.M.base A.reindex
        · have he : u=v0 := Subtype.ext (hu.trans hv0.symm)
          subst u
          change (pureSourceNormal A v0).1+r A≤x+r A at hqx
          change (pureSourceNormal A v0).2.1+s A≤y+s A at hqy
          exact hnot ⟨by omega,by omega⟩
        · obtain ⟨t,ht,htx,hty,htz⟩ := boundary_nonfirst_wrap_in_plane G A hm hk hl u hu hgz
          exact hN ⟨t,ht,htx.trans hqx,hty.trans hqy,htz.trans hqz⟩
      · change 0<0 at hgz; omega

theorem boundary_right_cap_top_member (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvy : 0<(pureSourceNormal A v0).2.1) (hvz : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) (y : ℕ) :
    (boundaryRightCap A hk-r A,y,d A-1)∈monomialClosure (boundaryInitialGenerators A) := by
  obtain ⟨v,j,_,_,_,hg⟩ := boundary_right_small_return_cap G A hm hk hl v0 hv0 hvy hvz hneck
  apply (boundary_top_mem_iff_original A _ _).mpr
  exact ⟨pureSourceNormal A v,Or.inl ⟨v,rfl⟩,by rw [hg],by rw [hg]; exact Nat.zero_le _⟩

theorem boundary_left_cap_top_member (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvx : 0<(pureSourceNormal A v0).1) (hvz : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) (x : ℕ) :
    (x,boundaryLeftCap A-s A,d A-1)∈monomialClosure (boundaryInitialGenerators A) := by
  obtain ⟨v,j,_,_,_,hg⟩ := boundary_left_small_return_cap G A hm hk hl v0 hv0 hvx hvz hneck
  apply (boundary_top_mem_iff_original A _ _).mpr
  exact ⟨pureSourceNormal A v,Or.inl ⟨v,rfl⟩,by rw [hg]; exact Nat.zero_le _,by rw [hg]⟩

def boundaryRightExceptionalCorner (A : SectorBCriticalRoleBranchA P)
    (v0 : ModelSources P.M.base A.reindex) : Monomial :=
  ((pureSourceNormal A v0).1-1,boundaryLeftCap A-s A-1,d A-1)

def boundaryLeftExceptionalCorner (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (v0 : ModelSources P.M.base A.reindex) : Monomial :=
  (boundaryRightCap A hk-r A-1,(pureSourceNormal A v0).2.1-1,d A-1)

theorem boundary_right_corner_exceptional (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvx : 0<(pureSourceNormal A v0).1) (hvz : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    (hi : (pureSourceNormal A v0).1<boundaryRightCap A hk-r A)
    (hk' : (pureSourceNormal A v0).2.1<boundaryLeftCap A-s A) :
    boundaryRightExceptionalCorner A v0∈boundaryBorderExceptional A := by
  have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck
  have hd := boundary_d_pos A
  have hc := boundary_cap_cell_standard_and_wrap G A hm hk hl v0 hv0 hvz hneck
    ((pureSourceNormal A v0).1-1) (boundaryLeftCap A-s A-1)
    (by omega) (by omega) (by omega)
  refine ⟨⟨hc.1,?_,?_,?_⟩,?_,hc.2⟩
  · apply (boundary_top_mem_iff_original A _ _).mpr
    exact ⟨pureSourceNormal A v0,Or.inl ⟨v0,rfl⟩,by dsimp [boundaryRightExceptionalCorner]; omega,
      by dsimp [boundaryRightExceptionalCorner]; omega⟩
  · have ht := boundary_left_cap_top_member G A hm hk hl v0 hv0 hvx hvz hneck
      ((pureSourceNormal A v0).1-1)
    change ((pureSourceNormal A v0).1-1,boundaryLeftCap A-s A-1+1,d A-1)∈_
    rw [Nat.sub_add_cancel (show 1≤boundaryLeftCap A-s A by omega)]
    exact ht
  · apply (boundary_initial_mem_iff A _).mpr
    exact Or.inl (by dsimp [boundaryRightExceptionalCorner]; omega)
  · change d A-1+1=d A; omega

theorem boundary_left_corner_exceptional (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvy : 0<(pureSourceNormal A v0).2.1) (hvz : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    (hi : (pureSourceNormal A v0).1<boundaryRightCap A hk-r A)
    (hk' : (pureSourceNormal A v0).2.1<boundaryLeftCap A-s A) :
    boundaryLeftExceptionalCorner A hk v0∈boundaryBorderExceptional A := by
  have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck
  have hd := boundary_d_pos A
  have hc := boundary_cap_cell_standard_and_wrap G A hm hk hl v0 hv0 hvz hneck
    (boundaryRightCap A hk-r A-1) ((pureSourceNormal A v0).2.1-1)
    (by omega) (by omega) (by omega)
  refine ⟨⟨hc.1,?_,?_,?_⟩,?_,hc.2⟩
  · have ht := boundary_right_cap_top_member G A hm hk hl v0 hv0 hvy hvz hneck
      ((pureSourceNormal A v0).2.1-1)
    change (boundaryRightCap A hk-r A-1+1,(pureSourceNormal A v0).2.1-1,d A-1)∈_
    rw [Nat.sub_add_cancel (show 1≤boundaryRightCap A hk-r A by omega)]
    exact ht
  · apply (boundary_top_mem_iff_original A _ _).mpr
    exact ⟨pureSourceNormal A v0,Or.inl ⟨v0,rfl⟩,by dsimp [boundaryLeftExceptionalCorner]; omega,
      by dsimp [boundaryLeftExceptionalCorner]; omega⟩
  · apply (boundary_initial_mem_iff A _).mpr
    exact Or.inl (by dsimp [boundaryLeftExceptionalCorner]; omega)
  · change d A-1+1=d A; omega

theorem boundary_rect_corner_exceptional (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvx : 0<(pureSourceNormal A v0).1) (hvy : 0<(pureSourceNormal A v0).2.1)
    (hvz : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    (hout : boundaryRightCap A hk-r A≤(pureSourceNormal A v0).1 ∨
      boundaryLeftCap A-s A≤(pureSourceNormal A v0).2.1) :
    (boundaryRightCap A hk-r A-1,boundaryLeftCap A-s A-1,d A-1)∈boundaryBorderExceptional A := by
  have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck
  have hd := boundary_d_pos A
  have hc := boundary_cap_cell_standard_and_wrap G A hm hk hl v0 hv0 hvz hneck
    (boundaryRightCap A hk-r A-1) (boundaryLeftCap A-s A-1)
    (by omega) (by omega) (by omega)
  refine ⟨⟨hc.1,?_,?_,?_⟩,?_,hc.2⟩
  · have ht := boundary_right_cap_top_member G A hm hk hl v0 hv0 hvy hvz hneck
      (boundaryLeftCap A-s A-1)
    change (boundaryRightCap A hk-r A-1+1,boundaryLeftCap A-s A-1,d A-1)∈_
    rw [Nat.sub_add_cancel (show 1≤boundaryRightCap A hk-r A by omega)]
    exact ht
  · have ht := boundary_left_cap_top_member G A hm hk hl v0 hv0 hvx hvz hneck
      (boundaryRightCap A hk-r A-1)
    change (boundaryRightCap A hk-r A-1,boundaryLeftCap A-s A-1+1,d A-1)∈_
    rw [Nat.sub_add_cancel (show 1≤boundaryLeftCap A-s A by omega)]
    exact ht
  · apply (boundary_initial_mem_iff A _).mpr
    exact Or.inl (by dsimp; omega)
  · change d A-1+1=d A; omega

theorem boundary_surviving_first_inside_caps (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hvz : 0<(pureSourceNormal A v0).2.2)
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    (w : BoundarySurvivingWraps A) :
    (pureSourceNormal A v0).1<boundaryRightCap A hk-r A ∧
      (pureSourceNormal A v0).2.1<boundaryLeftCap A-s A := by
  obtain ⟨u,hu,_,hw⟩ := boundary_surviving_wrap_is_first G A hm hk hl w.property
  have he : u=v0 := Subtype.ext (hu.trans hv0.symm)
  subst u
  have hn : w.val∉monomialClosure (boundaryPlaneOriginals A) := by
    rintro ⟨q,hq,hqx,hqy,hqz⟩
    have hqi : q∈monomialClosure (boundaryInitialGenerators A) :=
      ⟨q,Or.inr (Or.inl hq.1),le_rfl,le_rfl,le_rfl⟩
    have hqw := w.property.1.2 q hqi hqx hqy hqz
    apply w.property.2
    exact Or.inr (hqw ▸ hq.1)
  have henv := boundary_central_plane_envelope G A hm hk v0 hv0 hvz hneck
    ((pureSourceNormal A v0).1+r A) ((pureSourceNormal A v0).2.1+s A)
    (by omega) (by omega)
  have hnot : ¬(boundaryRightCap A hk≤(pureSourceNormal A v0).1+r A ∨
      boundaryLeftCap A≤(pureSourceNormal A v0).2.1+s A) := by
    intro h
    apply hn
    rw [hw]
    exact henv.mpr h
  have hb := boundary_actual_cap_bounds G A hm hk v0 hv0 hvz hneck
  omega

theorem boundary_exceptional_finite (A : SectorBCriticalRoleBranchA P)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent) :
    (boundaryBorderExceptional A).Finite := by
  obtain ⟨a,b,c,_,_,_,ha,hb,hc⟩ := boundary_initial_axes A hk
  exact (monomialSocle_finite (boundaryInitialGenerators A) a b c ha hb hc).subset
    (fun _ h => h.1)

theorem boundary_full_first_two_seats (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hfull : FullySupported (pureSourceNormal A v0))
    (hneck : d A*routingC P.M.base A.reindex∉
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex))
    (hi : (pureSourceNormal A v0).1<boundaryRightCap A hk-r A)
    (hk' : (pureSourceNormal A v0).2.1<boundaryLeftCap A-s A) :
    2≤Nat.card {z // z∈boundaryBorderExceptional A} := by
  classical
  have hr := boundary_right_corner_exceptional G A hm hk hl v0 hv0 hfull.1 hfull.2.2 hneck hi hk'
  have hl' := boundary_left_corner_exceptional G A hm hk hl v0 hv0 hfull.2.1 hfull.2.2 hneck hi hk'
  have hne : boundaryRightExceptionalCorner A v0≠boundaryLeftExceptionalCorner A hk v0 := by
    intro he
    have hx := congrArg (fun z : Monomial => z.1) he
    change (pureSourceNormal A v0).1-1=boundaryRightCap A hk-r A-1 at hx
    have hp : 0<(pureSourceNormal A v0).1 := hfull.1
    omega
  let f : Fin 2 → {z // z∈boundaryBorderExceptional A} := fun n =>
    if n=0 then ⟨boundaryRightExceptionalCorner A v0,hr⟩ else ⟨boundaryLeftExceptionalCorner A hk v0,hl'⟩
  have hf : Function.Injective f := by
    intro x y he
    by_cases hx : x=0 <;> by_cases hy : y=0
    · exact hx.trans hy.symm
    · have hh := congrArg Subtype.val he
      simp only [f,ite_eq_left hx,ite_eq_right hy] at hh
      exact (hne hh).elim
    · have hh := congrArg Subtype.val he
      simp only [f,ite_eq_right hx,ite_eq_left hy] at hh
      exact (hne hh.symm).elim
    · apply Fin.ext
      have hxx : x.val≠0 := fun h => hx (Fin.ext h)
      have hyy : y.val≠0 := fun h => hy (Fin.ext h)
      omega
  let : Finite {z // z∈boundaryBorderExceptional A} := boundary_exceptional_finite A hk
  simpa using Nat.card_le_card_of_injective f hf

theorem boundary_first_not_full_no_full_source (A : SectorBCriticalRoleBranchA P)
    (v0 : ModelSources P.M.base A.reindex)
    (hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex)
    (hnot : ¬FullySupported (pureSourceNormal A v0)) : boundaryFullSourceCount A=0 := by
  let : IsEmpty {u : ModelSources P.M.base A.reindex // FullySupported (pureSourceNormal A u)} :=
    ⟨by
      rintro ⟨u,hu⟩
      have hf := pure_positive_coordinates_full_support A (pureSourceNormal A u) hu.1 hu.2.1 hu.2.2
      rw [(pureSourceNormal_spec A u).1] at hf
      have he := model_full_support_source_is_first _ _ u hf
      have huv : u=v0 := Subtype.ext (he.trans hv0.symm)
      exact hnot (huv ▸ hu)⟩
  exact Nat.card_of_isEmpty

/-- A8--A11, on every actually matching A. The two surcharge terms are
compensated by distinct true exceptional seats, never by private fake owners. -/
theorem boundary_exceptional_compensation (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hm : A.mixedDegree=G.internalDegree)
    (hk : BoundaryKilled P.M A.pairDegree A.pair.leftComponent)
    (hl : ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent) :
    boundarySurvivingWrapCount A+boundaryFullSourceCount A≤
      Nat.card {z // z∈boundaryBorderExceptional A} := by
  classical
  let v0 : ModelSources P.M.base A.reindex :=
    ⟨firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex,
      firstPrincipal_minimal_cut_source _ _ (routingM_pos _ _)⟩
  have hv0 : v0.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
      (routingM_pos _ _)*routingM P.M.base A.reindex := rfl
  by_cases hz : (pureSourceNormal A v0).2.2=0
  · exact boundary_first_z_zero_compensation G A hm hk hl v0 hv0 hz
  have hvz : 0<(pureSourceNormal A v0).2.2 := Nat.pos_of_ne_zero hz
  by_cases hcut : d A*routingC P.M.base A.reindex∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
  · exact boundary_neck_cut_compensation G A hm hk hl hcut
  have hB := boundary_surviving_wrap_count_le_one G A hm hk hl
  have hK := boundary_full_source_count_le_one A
  have hEpos {z : Monomial} (hz : z∈boundaryBorderExceptional A) :
      1≤Nat.card {z // z∈boundaryBorderExceptional A} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨z,hz⟩⟩,boundary_exceptional_finite A hk⟩
  have hBseat (hne : boundarySurvivingWrapCount A≠0) : Nonempty (BoundarySurvivingWraps A) :=
    (Nat.card_pos_iff.mp (show 0<Nat.card (BoundarySurvivingWraps A) from Nat.pos_of_ne_zero hne)).1
  by_cases hfull : FullySupported (pureSourceNormal A v0)
  · by_cases hin : (pureSourceNormal A v0).1<boundaryRightCap A hk-r A ∧
        (pureSourceNormal A v0).2.1<boundaryLeftCap A-s A
    · have := boundary_full_first_two_seats G A hm hk hl v0 hv0 hfull hcut hin.1 hin.2
      omega
    · have hB0 : boundarySurvivingWrapCount A=0 := by
        by_contra hnot
        obtain ⟨w⟩ := hBseat hnot
        exact hin (boundary_surviving_first_inside_caps G A hm hk hl v0 hv0 hvz hcut w)
      have hz := boundary_rect_corner_exceptional G A hm hk hl v0 hv0 hfull.1 hfull.2.1 hfull.2.2
        hcut (by omega)
      have := hEpos hz
      omega
  · have hK0 := boundary_first_not_full_no_full_source A v0 hv0 hfull
    by_cases hB0 : boundarySurvivingWrapCount A=0
    · omega
    obtain ⟨w⟩ := hBseat hB0
    have hin := boundary_surviving_first_inside_caps G A hm hk hl v0 hv0 hvz hcut w
    by_cases hx : 0<(pureSourceNormal A v0).1
    · have := hEpos (boundary_right_corner_exceptional G A hm hk hl v0 hv0 hx hvz hcut hin.1 hin.2)
      omega
    · have hy : 0<(pureSourceNormal A v0).2.1 := by
        by_contra hnot
        have hx0 : (pureSourceNormal A v0).1=0 := by omega
        have hy0 : (pureSourceNormal A v0).2.1=0 := by omega
        have hc := v0.property.1
        rw [←(pureSourceNormal_spec A v0).1] at hc
        have hc' : (pureSourceNormal A v0).2.2*routingC P.M.base A.reindex∈
            cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
          simpa [monomialDegree,normalizedGrid,hx0,hy0] using hc
        have := (boundary_axis_cut_bounds G A hm hl).2 _ hc'
        have := (pureSourceNormal_spec A v0).2.2
        omega
      have := hEpos (boundary_left_corner_exceptional G A hm hk hl v0 hv0 hy hvz hcut hin.1 hin.2)
      omega

theorem boundary_all_pure_exceptional_compensation (P : P2Data Gamma) (G : SectorCActualFibers P)
    (h : ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.boundaryDegree ∧ A.mixedDegree=G.internalDegree ∧
      BoundaryKilled P.M A.pairDegree A.pair.leftComponent ∧
      ¬BoundaryKilled P.M A.pairDegree A.pair.rightComponent ∧
      boundarySurvivingWrapCount A+boundaryFullSourceCount A≤
        Nat.card {z // z∈boundaryBorderExceptional A} := by
  obtain ⟨A,hp,hm,hk,hl,_⟩ := boundary_all_pure_checkpoint P G h
  exact ⟨A,hp,hm,hk,hl,boundary_exceptional_compensation G A hm hk hl⟩

theorem boundary_all_pure_type_bound (P : P2Data Gamma) (G : SectorCActualFibers P)
    (h : ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount := by
  obtain ⟨A,_,hm,hk,hl,_,_,_,hb⟩ := boundary_all_pure_checkpoint P G h
  have hc := boundary_exceptional_compensation G A hm hk hl
  omega

theorem sectorC_type_bound (P : P2Data Gamma) (hC : SectorC P.M) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount := by
  rcases L5A2C4OR38.sectorC_type_bound_or_pure_geometry P hC with hB | hI | hdone
  · obtain ⟨G,h⟩ := hB
    exact boundary_all_pure_type_bound P G h
  · obtain ⟨G,bp,bm,hne,hp,hm,hi⟩ := hI
    exact L5A2C4OR45.internal_all_pure_type_bound P G bp bm hne hp hm hi
  · exact hdone

end NS25Lean.L5A2C4OR47
