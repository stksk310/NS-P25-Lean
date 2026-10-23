import NS25Lean.P2SectorCPureInternalMinimalBudgetR44
set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.L5A2C4OR45
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR33 L5A2C4OR35 L5A2C4OR39 L5A2C4OR40
  L5A2C4OR41 L5A2C4OR42 L5A2C4OR43 L5A2C4OR44 FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- Same-A first-principal shape from actual role components. The arbitrary
matching role packet is not replaced by the existential geometry witness. -/
theorem matching_first_source_shape (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) :
    ∀ v : ModelSources P.M.base A.reindex,
      v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex →
      ((pureSourceNormal A v).1=0 ∧ (pureSourceNormal A v).2.1=0) ∨
        (pureSourceNormal A v).2.2=0 := by
  have hk : killedCount P.M A.mixedDegree=1 := by rw [hb]; exact G.boundarySignature.2
  obtain hpk | hmk := boundary_has_killed_endpoint A hk
  · obtain ⟨v,hv,hx,hy⟩ := pure_killed_first_source A hpk
      (fun hh => boundary_not_both_killed A hk ⟨hpk,hh⟩)
    intro w hw
    have he : w=v := Subtype.ext (hw.trans hv.symm)
    subst w
    exact Or.inl ⟨hx,hy⟩
  · obtain ⟨v,hv,hz⟩ := mixed_killed_first_source G A ha hmk
      (fun hh => boundary_not_both_killed A hk ⟨hh,hmk⟩)
    intro w hw
    have he : w=v := Subtype.ext (hw.trans hv.symm)
    subst w
    exact Or.inr hz

/-- An actual cut in the short YZ plane has an actual zero-x original divisor.
The exact R42 normal-strip theorem includes every candidate wrap. -/
theorem yz_cut_original (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (ha : A.pairDegree=G.internalDegree) (hb : A.mixedDegree=G.boundaryDegree)
    {y z : ℕ} (hy : y<alpha A)
    (hc : monomialDegree P.M.base A.reindex (0,y,z) ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    ∃ t∈pureOriginals A, t.1=0 ∧ 0<t.2.2 ∧ t.2.2≤z := by
  have hk : killedCount P.M A.mixedDegree=1 := by rw [hb]; exact G.boundarySignature.2
  have hm := (pure_normal_mem_iff_cut A hk (0,y,z)).mpr hc
  rw [pureNormal_fixed A _ hy] at hm
  obtain ⟨t,ht,hx,hty,htz⟩ := hm
  have hx0 : t.1=0 := by simpa using hx
  rcases ht with ht | ⟨g,hg,hgy,he⟩
  · have hp : 0<t.2.2 := by
      by_contra hn
      have hz0 : t.2.2=0 := by omega
      have hcut := pureStrip_cut A hk (Or.inl ht)
      have hbound := (internal_axis_cut_bounds G A ha).2 t.2.1
        (by simpa [monomialDegree,normalizedGrid,hx0,hz0] using hcut)
      dsimp at hty
      omega
    exact ⟨t,ht,hx0,hp,htz⟩
  · have hxp := pure_beta_pos A
    rw [he] at hx0
    change g.1+beta A=0 at hx0
    omega

/-- Cyclic small-return conjugation, not a generic monomial-ideal assertion. -/
theorem xz_source_zero_x_original (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) (v : ModelSources P.M.base A.reindex)
    (hx : 0<(pureSourceNormal A v).1) (hy : (pureSourceNormal A v).2.1=0)
    (hz : 0<(pureSourceNormal A v).2.2) :
    ∃ t∈pureOriginals A, t.1=0 ∧ 0<t.2.2 ∧ t.2.2≤(pureSourceNormal A v).2.2 := by
  let g := pureSourceNormal A v
  have hg := (pureSourceNormal_spec A v).1
  change monomialDegree P.M.base A.reindex g=v.val at hg
  have hnf : v.val≠firstPrincipal (routingH P.M.base A.reindex)
      (routingM P.M.base A.reindex) (routingM_pos _ _)*routingM P.M.base A.reindex := by
    intro hf
    rcases matching_first_source_shape G A ha hb v hf with h | h <;> omega
  obtain ⟨n,t,hn,_,ht,htpos,he⟩ := model_nonfirst_source_small_return _ _ v hnf
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base A.reindex (x,y,z)=t := hfac.symm
  have sep := source_return_coordinate_separation _ _ v g (x,y,z) hg hn
    (he.trans (by rw [hd]))
  have hx0 : x=0 := sep.1 hx
  have hz0 : z=0 := sep.2.2 hz
  have htb : t=y*routingB P.M.base A.reindex := by
    simpa [monomialDegree,normalizedGrid,hx0,hz0] using hd.symm
  have hyp : 0<y := by
    by_contra hn
    have hy0 : y=0 := by omega
    simp [hy0] at htb
    omega
  have hr := (branchA_symmetricTailData A).pure_relation
  rw [←routingA_eq_n0,←routingB_eq_n1] at hr
  have hylt : y<alpha A := by
    by_contra hbad
    have hm := congrArg (fun q => q*routingB P.M.base A.reindex)
      (Nat.sub_add_cancel (show alpha A≤y by omega))
    simp only [Nat.add_mul] at hm
    have hnew : monomialDegree P.M.base A.reindex (beta A,y-alpha A,0)=t := by
      simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
      omega
    have hs := source_return_coordinate_separation _ _ v g (beta A,y-alpha A,0) hg hn
      (he.trans (by rw [hnew]))
    have := hs.1 hx
    have := pure_beta_pos A
    omega
  have hxlt : g.1<beta A := by
    by_contra hbad
    have hm := congrArg (fun q => q*routingA P.M.base A.reindex)
      (Nat.sub_add_cancel (show beta A≤g.1 by omega))
    simp only [Nat.add_mul] at hm
    have hnew : monomialDegree P.M.base A.reindex (g.1-beta A,alpha A,g.2.2)=v.val := by
      change g.1*routingA P.M.base A.reindex+g.2.1*routingB P.M.base A.reindex+
        g.2.2*routingC P.M.base A.reindex=v.val at hg
      have hy0 : g.2.1=0 := hy
      rw [hy0] at hg
      simp only [monomialDegree,normalizedGrid,zero_mul,add_zero] at hg ⊢
      omega
    have hs := source_return_coordinate_separation _ _ v (g.1-beta A,alpha A,g.2.2)
      (0,y,0) hnew hn (by simpa [monomialDegree,normalizedGrid,htb] using he)
    have hzero : y=0 := hs.2.1 (pure_alpha_pos A)
    omega
  have hconj : monomialDegree P.M.base A.reindex (0,alpha A-y,g.2.2)=
      n*routingM P.M.base A.reindex+(beta A-g.1)*routingA P.M.base A.reindex := by
    have hm1 := congrArg (fun q => q*routingB P.M.base A.reindex)
      (Nat.sub_add_cancel (Nat.le_of_lt hylt))
    have hm2 := congrArg (fun q => q*routingA P.M.base A.reindex)
      (Nat.sub_add_cancel (Nat.le_of_lt hxlt))
    simp only [Nat.add_mul] at hm1 hm2
    have hy0 : g.2.1=0 := hy
    simp only [monomialDegree,normalizedGrid,hy0,zero_mul,add_zero,zero_add] at hg ⊢
    omega
  apply yz_cut_original G A ha hb (by omega : alpha A-y<alpha A)
  exact ⟨grid_mem_H _ _ _,n,hn,_,
    by simpa [monomialDegree,normalizedGrid] using grid_mem_H P.M.base A.reindex (beta A-g.1,0,0),hconj⟩

/-- Least positive z among actual originals is attained at zero x. -/
theorem least_z_zero_x_original (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) :
    ∃ k : ℕ, 0<k ∧ (∃ t∈pureOriginals A, t.1=0 ∧ t.2.2=k) ∧
      ∀ t∈pureOriginals A, 0<t.2.2 → k≤t.2.2 := by
  classical
  have hex : ∃ k : ℕ, ∃ t∈pureOriginals A, 0<t.2.2 ∧ t.2.2=k := by
    have hc : monomialDegree P.M.base A.reindex (0,0,routingM P.M.base A.reindex)∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) :=
      ⟨grid_mem_H _ _ _,routingC P.M.base A.reindex,routingC_positive _ _,0,
        (routingH _ _).zero_mem,by simp [monomialDegree,normalizedGrid,Nat.mul_comm]⟩
    obtain ⟨t,ht,_,hp,_⟩ := yz_cut_original G A ha hb (pure_alpha_pos A) hc
    exact ⟨t.2.2,t,ht,hp,rfl⟩
  let k := Nat.find hex
  obtain ⟨g,hg,hgp,hgk⟩ := Nat.find_spec hex
  have hmin : ∀ t∈pureOriginals A, 0<t.2.2 → k≤t.2.2 := by
    intro t ht hp
    exact Nat.find_min' hex ⟨t,ht,hp,rfl⟩
  refine ⟨k,by dsimp [k]; omega,?_,hmin⟩
  by_cases hx : g.1=0
  · exact ⟨g,hg,hx,hgk⟩
  rcases hg with ⟨v,rfl⟩ | rfl
  · have hs := all_source_plane_of_first_shape A (matching_first_source_shape G A ha hb) v
    have hy : (pureSourceNormal A v).2.1=0 := by omega
    obtain ⟨t,ht,htx,htp,htz⟩ := xz_source_zero_x_original G A ha hb v (by omega) hy hgp
    exact ⟨t,ht,htx,by have := hmin t ht htp; omega⟩
  · have hh : (pureAlive A).1=0 ∨ (pureAlive A).2.2=0 := by
      unfold pureAlive pureAliveRaw
      split_ifs <;> simp [pureNormal]
    omega

/-- Literal polynomial minimality excludes every original pure-x divisor. -/
theorem pure_x_original_above_surviving (A : SectorBCriticalRoleBranchA P)
    {w : Monomial} (hw : w∈PureSurvivingWraps A) (hwy : w.2.1=0) (hwz : w.2.2=0)
    {t : Monomial} (ht : t∈pureOriginals A) (hty : t.2.1=0) (htz : t.2.2=0) :
    w.1<t.1 := by
  by_contra hn
  have he := hw.1.2 t ⟨t,Or.inr (Or.inl ht),le_rfl,le_rfl,le_rfl⟩
    (by omega) (by omega) (by omega)
  exact hw.2 (Or.inr (he ▸ ht))

/-- All candidate wraps are audited here, not only surviving minima. -/
theorem low_z_wrap_standard (A : SectorBCriticalRoleBranchA P)
    {w g : Monomial} (hw : w∈PureSurvivingWraps A) (_hg : g∈pureOriginals A)
    (hgz : g.2.2=0) (hwg : w=pureWrap A g)
    (hI : ∀ t∈pureOriginals A, 0<t.2.1 → t.2.2=0 → g.1≤t.1)
    {k : ℕ} (hk : 0<k)
    (hmin : ∀ t∈pureOriginals A, 0<t.2.2 → k≤t.2.2) :
    (g.1+beta A-1,0,k-1)∉monomialClosure (pureStripGenerators A) := by
  rintro ⟨t,ht,hx,hy,hz⟩
  have hwy : w.2.1=0 := by simp [hwg,pureWrap]
  have hwz : w.2.2=0 := by simp [hwg,pureWrap,hgz]
  have hwx : w.1=g.1+beta A := by simp [hwg,pureWrap]
  rcases ht with ht | ⟨s,hs,hsy,rfl⟩
  · have hty : t.2.1=0 := by simpa using hy
    have htz : t.2.2=0 := by
      by_contra hn
      have := hmin t ht (by omega)
      dsimp at hz
      omega
    have := pure_x_original_above_surviving A hw hwy hwz ht hty htz
    dsimp at hx
    omega
  · have hsz : s.2.2=0 := by
      by_contra hn
      have := hmin s hs (by omega)
      change s.2.2≤k-1 at hz
      omega
    have := hI s hs hsy hsz
    change s.1+beta A≤g.1+beta A-1 at hx
    have := pure_beta_pos A
    omega

/-- The concrete corner (I-1,alpha-1,k-1) is a literal R42 exceptional socle
monomial, including I=1 and k=1. Zero-center or raw histories are not used. -/
theorem exceptional_corner_of_surviving (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) {w : Monomial} (hw : w∈PureSurvivingWraps A) :
    ∃ z, z∈pureBorderExceptional A := by
  have hs := matching_first_source_shape G A ha hb
  obtain ⟨g,hg,hgx,hgy,hgz,hwg,hI⟩ := surviving_wrap_minimal_producer G A ha hb hs hw
  obtain ⟨k,hkp,⟨t,ht,htx,htz⟩,hmin⟩ := least_z_zero_x_original G A ha hb
  have hap := pure_alpha_pos A
  have hgylt := pureOriginals_y_lt A hg
  have htylt := pureOriginals_y_lt A ht
  let z : Monomial := (g.1-1,alpha A-1,k-1)
  have hstandard : z∉monomialClosure (pureInitialGenerators A) := by
    rintro ⟨s,hs,hx,hy,hz⟩
    rcases hs with rfl | hs | ⟨u,hu,huy,rfl⟩
    · change alpha A≤alpha A-1 at hy
      omega
    · have hsz : s.2.2=0 := by
        by_contra hn
        have := hmin s hs (by omega)
        change s.2.2≤k-1 at hz
        omega
      by_cases hsy : 0<s.2.1
      · have := hI s hs hsy hsz
        change s.1≤g.1-1 at hx
        omega
      · have hsy0 : s.2.1=0 := by omega
        have hwy : w.2.1=0 := by simp [hwg,pureWrap]
        have hwz : w.2.2=0 := by simp [hwg,pureWrap,hgz]
        have hh := pure_x_original_above_surviving A hw hwy hwz hs hsy0 hsz
        have hwx : w.1=g.1+beta A := by simp [hwg,pureWrap]
        change s.1≤g.1-1 at hx
        omega
    · have huz : u.2.2=0 := by
        by_contra hn
        have := hmin u hu (by omega)
        change u.2.2≤k-1 at hz
        omega
      have := hI u hu huy huz
      change u.1+beta A≤g.1-1 at hx
      omega
  have hsoc : MonomialSocle (pureInitialGenerators A) z := by
    refine ⟨hstandard,?_,?_,?_⟩
    · refine ⟨g,Or.inr (Or.inl hg),?_,?_,?_⟩
      · change g.1≤g.1-1+1; omega
      · change g.2.1≤alpha A-1; omega
      · change g.2.2≤k-1; omega
    · refine ⟨(0,alpha A,0),Or.inl rfl,Nat.zero_le _,?_,Nat.zero_le _⟩
      change alpha A≤alpha A-1+1
      omega
    · refine ⟨t,Or.inr (Or.inl ht),?_,?_,?_⟩
      · change t.1≤g.1-1; omega
      · change t.2.1≤alpha A-1; omega
      · change t.2.2≤k-1+1; omega
  refine ⟨z,hsoc,?_,?_⟩
  · change alpha A-1+1=alpha A
    omega
  · have hwrap : pureWrap A z=(g.1+beta A-1,0,k-1) := by
      ext <;> simp only [pureWrap,z] <;> omega
    rw [hwrap]
    exact low_z_wrap_standard A hw hg hgz hwg hI hkp hmin

/-- B5 on the original universally quantified matching G,A binder. -/
theorem internal_exceptional_compensation (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) :
    pureSurvivingWrapCount A≤Nat.card {z // z∈pureBorderExceptional A} := by
  have hk : killedCount P.M A.mixedDegree=1 := by rw [hb]; exact G.boundarySignature.2
  have hB := pure_surviving_wrap_count_le_one A hk (matching_first_source_shape G A ha hb)
  by_cases hzero : pureSurvivingWrapCount A=0
  · omega
  have hpos : 0<Nat.card (PureSurvivingWraps A) := by change 0<pureSurvivingWrapCount A; omega
  obtain ⟨hwne,_⟩ := Nat.card_pos_iff.mp hpos
  obtain ⟨w⟩ := hwne
  obtain ⟨z,hz⟩ := exceptional_corner_of_surviving G A ha hb w.property
  obtain ⟨a,b,c,_,_,_,hax,hay,haz⟩ := pure_initial_axes A hk
  have hfin := (monomialSocle_finite (pureInitialGenerators A) a b c hax hay haz).subset
    (show pureBorderExceptional A⊆{z | MonomialSocle (pureInitialGenerators A) z} from fun _ h => h.1)
  have hE : 0<Nat.card {z // z∈pureBorderExceptional A} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨z,hz⟩⟩,hfin⟩
  omega

/-- Original internal-all-pure type bound. The frozen corrected socle budget
and B5 are applied to the same actual A. No boundary/global closure is claimed. -/
theorem internal_all_pure_type_bound (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp≠bm)
    (hp : IsPureBoundaryComponent G bp) (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,(componentSupport P.M.base G.internalDegree C).card=1) :
    Gamma.asRelativeIdeal.idealType≤P.sourceCount := by
  obtain ⟨A,ha,hb,_,_,hbudget⟩ := internal_minimal_and_corrected_socle_budget P G bp bm hne hp hm hi
  have hcomp := internal_exceptional_compensation G A ha hb
  omega

end NS25Lean.L5A2C4OR45

