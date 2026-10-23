import NS25Lean.P2SectorCM7OneBinomialBorderR35
set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4OR36
open L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR5
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 L5A2C4OR29
  L5A2C4OR32 L5A2C4OR33 L5A2C4OR35 FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

def firstSourceDegree (R : ActualRolePacket P) : ℕ :=
  firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e)
    (routingM_pos P.M.base R.e)*routingM P.M.base R.e

def firstSource (R : ActualRolePacket P) : ModelSources P.M.base R.e :=
  ⟨firstSourceDegree R,firstPrincipal_minimal_cut_source _ _ (routingM_pos _ _)⟩

theorem monomial_positive_predecessors (R : ActualRolePacket P) (z : Monomial) :
    (0<z.1 → ∃ y ∈ routingH P.M.base R.e,
      monomialDegree P.M.base R.e z=y+routingA P.M.base R.e) ∧
    (0<z.2.1 → ∃ y ∈ routingH P.M.base R.e,
      monomialDegree P.M.base R.e z=y+routingB P.M.base R.e) ∧
    (0<z.2.2 → ∃ y ∈ routingH P.M.base R.e,
      monomialDegree P.M.base R.e z=y+routingC P.M.base R.e) := by
  rcases z with ⟨x,y,z⟩
  refine ⟨?_,?_,?_⟩
  · intro hx
    refine ⟨monomialDegree P.M.base R.e (x-1,y,z),grid_mem_H _ _ _,?_⟩
    have h := congrArg (fun n => n*routingA P.M.base R.e) (show x-1+1=x by omega)
    simp only [Nat.add_mul,one_mul] at h
    simp only [monomialDegree,normalizedGrid]
    omega
  · intro hy
    change 0 < y at hy
    refine ⟨monomialDegree P.M.base R.e (x,y-1,z),grid_mem_H _ _ _,?_⟩
    have h := congrArg (fun n => n*routingB P.M.base R.e) (show y-1+1=y by omega)
    simp only [Nat.add_mul,one_mul] at h
    simp only [monomialDegree,normalizedGrid]
    omega
  · intro hz
    change 0 < z at hz
    refine ⟨monomialDegree P.M.base R.e (x,y,z-1),grid_mem_H _ _ _,?_⟩
    have h := congrArg (fun n => n*routingC P.M.base R.e) (show z-1+1=z by omega)
    simp only [Nat.add_mul,one_mul] at h
    simp only [monomialDegree,normalizedGrid]
    omega

theorem full_support_source_is_first (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (hf : FullySupported (sourceNormal R s)) :
    s.val=firstSourceDegree R := by
  have hp := monomial_positive_predecessors R (sourceNormal R s)
  apply model_full_support_source_is_first P.M.base R.e s
  rw [←(sourceNormal_spec R s).1]
  exact ⟨hp.1 hf.1,hp.2.1 hf.2.1,hp.2.2 hf.2.2⟩

theorem fullSupportSourceCount_le_one (R : ActualRolePacket P) :
    Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤1 := by
  let : Subsingleton {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} :=
    ⟨fun s t => Subtype.ext (Subtype.ext
      ((full_support_source_is_first R s.val s.property).trans
        (full_support_source_is_first R t.val t.property).symm))⟩
  simpa using Nat.card_le_card_of_injective (fun _ : {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} => ()) (fun _ _ _ => Subsingleton.elim _ _)

theorem source_return_coordinate_separation (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (g t : Monomial)
    (hg : monomialDegree P.M.base R.e g=s.val) {n : ℕ} (hn : 0<n)
    (ht : s.val=n*routingM P.M.base R.e+monomialDegree P.M.base R.e t) :
    (0<g.1 → t.1=0) ∧ (0<g.2.1 → t.2.1=0) ∧ (0<g.2.2 → t.2.2=0) := by
  have gp := monomial_positive_predecessors R g
  have tp := monomial_positive_predecessors R t
  have common {a : ℕ} (ha : 0<a) (haH : a ∈ routingH P.M.base R.e)
      (hgp : ∃ y ∈ routingH P.M.base R.e, monomialDegree P.M.base R.e g=y+a)
      (htp : ∃ y ∈ routingH P.M.base R.e, monomialDegree P.M.base R.e t=y+a) : False := by
    obtain ⟨y,hy,hgy⟩ := hgp
    obtain ⟨z,hz,htz⟩ := htp
    have hh := model_source_return_no_common_summand P.M.base R.e s hn hz hy haH
      (hg.symm.trans hgy) (ht.trans (by rw [htz]))
    omega
  refine ⟨?_,?_,?_⟩
  · intro hg0
    by_contra ht0
    exact common (routingA_pos _ _) (by simpa [monomialDegree, normalizedGrid] using grid_mem_H P.M.base R.e (1,0,0)) (gp.1 hg0) (tp.1 (by omega))
  · intro hg1
    by_contra ht1
    exact common (routingB_positive _ _) (by simpa [monomialDegree, normalizedGrid] using grid_mem_H P.M.base R.e (0,1,0)) (gp.2.1 hg1) (tp.2.1 (by omega))
  · intro hg2
    by_contra ht2
    exact common (routingC_positive _ _) (by simpa [monomialDegree, normalizedGrid] using grid_mem_H P.M.base R.e (0,0,1)) (gp.2.2 hg2) (tp.2.2 (by omega))

theorem surviving_wrap_source_is_first (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (hi : 0<(sourceNormal R s).2.1)
    (hmin : InitialMinimal R (sourceWrap R (sourceNormal R s))) :
    s.val=firstSourceDegree R := by
  by_contra hfirst
  obtain ⟨n,t,hn,_,ht,htpos,heq⟩ := model_nonfirst_source_small_return _ _ s hfirst
  obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
  have hd : monomialDegree P.M.base R.e (x,y,z)=t := hfac.symm
  have sep := source_return_coordinate_separation R s (sourceNormal R s) (x,y,z)
    (sourceNormal_spec R s).1 hn (heq.trans (by rw [hd]))
  have hy : y=0 := sep.2.1 hi
  have hC := (sourceNormal_spec R s).2.1
  have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
  have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
  have hr := (coherent_normalized_relations _ _ R.HD).2.1
  have hs := (sourceNormal_spec R s).1
  have hsub := congrArg (fun k => k*routingB P.M.base R.e)
    (Nat.sub_add_cancel (Nat.le_of_lt hC))
  by_cases hxg : 0<(sourceNormal R s).1
  · have hx : x=0 := sep.1 hxg
    have hz : 0<z := by
      simp only [monomialDegree,normalizedGrid,hx,hy,zero_mul,zero_add] at hd
      by_contra hh
      have : z=0 := by omega
      simp [this] at hd
      omega
    let p : Monomial := ((sourceNormal R s).1+cr21 R.HD,0,
      (sourceNormal R s).2.2+cr23 R.HD-1)
    have hsz : (sourceNormal R s).2.2=0 := by
      by_contra hh
      have := sep.2.2 (by omega)
      change z=0 at this
      omega
    have hzm := congrArg (fun k => k*routingC P.M.base R.e) (show z-1+1=z by omega)
    have hvm := congrArg (fun k => k*routingC P.M.base R.e) (show cr23 R.HD-1+1=cr23 R.HD by omega)
    have hpdeg : monomialDegree P.M.base R.e p = n*routingM P.M.base R.e+
        monomialDegree P.M.base R.e (0,c2 P.M.base R.e-(sourceNormal R s).2.1,z-1) := by
      simp only [monomialDegree,normalizedGrid,hx,hy,hsz,zero_mul,zero_add] at hs hd
      simp only [Nat.add_mul,one_mul] at hsub hzm hvm
      simp only [p,monomialDegree,normalizedGrid,hsz,zero_add,zero_mul,Nat.add_mul]
      nlinarith only [hs,hd,heq,hr,hsub,hzm,hvm]
    have hpH := grid_mem_H P.M.base R.e p
    have hpcut : monomialDegree P.M.base R.e p ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) :=
      ⟨hpH,n,hn,_,grid_mem_H _ _ _,hpdeg⟩
    have hpmem := (initial_mem_iff R p).mpr (Or.inr ((strip_mem_iff_cut R p (by simpa [p] using herzogC_positive P.M.base R.e 1)).mpr hpcut))
    have hpe := hmin.2 p hpmem (by dsimp [Divides,p,sourceWrap]; omega)
    have := congrArg (fun t : Monomial => t.2.2) hpe
    dsimp [p,sourceWrap] at this
    omega
  · have hx0 : (sourceNormal R s).1=0 := by omega
    have hzg : 0<(sourceNormal R s).2.2 := by
      by_contra hh
      have hz0 : (sourceNormal R s).2.2=0 := by omega
      exact source_not_divides_yC R s (by dsimp [Divides]; exact ⟨by omega,by omega,by omega⟩)
    have hz : z=0 := sep.2.2 hzg
    have hx : 0<x := by
      simp only [monomialDegree,normalizedGrid,hy,hz,zero_mul,add_zero] at hd
      by_contra hh
      have : x=0 := by omega
      simp [this] at hd
      omega
    let p : Monomial := (cr21 R.HD-1,0,(sourceNormal R s).2.2+cr23 R.HD)
    have hxm := congrArg (fun k => k*routingA P.M.base R.e) (show x-1+1=x by omega)
    have hum := congrArg (fun k => k*routingA P.M.base R.e) (show cr21 R.HD-1+1=cr21 R.HD by omega)
    have hpdeg : monomialDegree P.M.base R.e p = n*routingM P.M.base R.e+
        monomialDegree P.M.base R.e (x-1,c2 P.M.base R.e-(sourceNormal R s).2.1,0) := by
      simp only [monomialDegree,normalizedGrid,hx0,hy,hz,zero_mul,zero_add,add_zero] at hs hd
      simp only [Nat.add_mul,one_mul] at hsub hxm hum
      simp only [p,monomialDegree,normalizedGrid,zero_mul,add_zero,Nat.add_mul]
      nlinarith only [hs,hd,heq,hr,hsub,hxm,hum]
    have hpcut : monomialDegree P.M.base R.e p ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) :=
      ⟨grid_mem_H _ _ _,n,hn,_,grid_mem_H _ _ _,hpdeg⟩
    have hpmem := (initial_mem_iff R p).mpr (Or.inr ((strip_mem_iff_cut R p (by simpa [p] using herzogC_positive P.M.base R.e 1)).mpr hpcut))
    have hpe := hmin.2 p hpmem (by dsimp [Divides,p,sourceWrap]; omega)
    have := congrArg (fun t : Monomial => t.1) hpe
    dsimp [p,sourceWrap] at this
    omega

theorem survivingWrapCount_le_one (R : ActualRolePacket P) : survivingWrapCount R≤1 := by
  have hsub : Subsingleton (survivingSourceWraps R) := by
    constructor
    intro g h
    obtain ⟨s,hs,hgs⟩ := g.property.1
    obtain ⟨t,ht,hht⟩ := h.property.1
    have hsf := surviving_wrap_source_is_first R s hs (hgs ▸ g.property.2.1)
    have htf := surviving_wrap_source_is_first R t ht (hht ▸ h.property.2.1)
    have hst : s=t := Subtype.ext (hsf.trans htf.symm)
    apply Subtype.ext
    exact hgs.trans (hst ▸ hht.symm)
  let := hsub
  simpa [survivingWrapCount] using Nat.card_le_card_of_injective (fun _ : survivingSourceWraps R => ()) (fun _ _ _ => Subsingleton.elim _ _)

theorem wrap_and_full_support_count_le_two (R : ActualRolePacket P) :
    survivingWrapCount R + Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤2 := by
  have := survivingWrapCount_le_one R
  have := fullSupportSourceCount_le_one R
  omega

theorem full_support_source_eq_first (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (hf : FullySupported (sourceNormal R s)) :
    s=firstSource R := Subtype.ext (full_support_source_is_first R s hf)

theorem surviving_wrap_eq_first_wrap (R : ActualRolePacket P)
    (g : survivingSourceWraps R) : g.val=sourceWrap R (sourceNormal R (firstSource R)) := by
  obtain ⟨s,hs,hgs⟩ := g.property.1
  have hs0 : s=firstSource R := Subtype.ext
    (surviving_wrap_source_is_first R s hs (hgs ▸ g.property.2.1))
  simpa [hs0] using hgs

theorem surviving_wrap_y_zero (R : ActualRolePacket P)
    (g : survivingSourceWraps R) : g.val.2.1=0 := by
  rw [surviving_wrap_eq_first_wrap R g]
  rfl

theorem first_source_y_zero_counts (R : ActualRolePacket P)
    (hy : (sourceNormal R (firstSource R)).2.1=0) :
    survivingWrapCount R=0 ∧
      Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}=0 := by
  have hempty : IsEmpty (survivingSourceWraps R) := by
    constructor
    intro g
    obtain ⟨s,hs,hgs⟩ := g.property.1
    have hs0 : s=firstSource R := Subtype.ext
      (surviving_wrap_source_is_first R s hs (hgs ▸ g.property.2.1))
    simp [hs0,hy] at hs
  have hfull : IsEmpty {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} := by
    constructor
    intro s
    have hs0 := full_support_source_eq_first R s.val s.property
    have := s.property.2.1
    simp [hs0,hy] at this
  let := hempty
  let := hfull
  exact ⟨by simp [survivingWrapCount],by simp⟩

theorem compensation_of_first_source_y_zero (R : ActualRolePacket P)
    (hy : (sourceNormal R (firstSource R)).2.1=0) :
    survivingWrapCount R + Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
      Nat.card {z // z ∈ borderExceptional R} := by
  obtain ⟨hB,hk⟩ := first_source_y_zero_counts R hy
  simp [hB,hk]

theorem internal_cut_source (R : ActualRolePacket P)
    (hcut : c2 P.M.base R.e*routingB P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    IsMinimalTailGenerator (routingH P.M.base R.e).toAddSubmonoid
      (cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
      (c2 P.M.base R.e*routingB P.M.base R.e) := by
  apply (minimalTail_iff_literal _ _ _).mpr
  refine ⟨hcut,literal_minimal_of_generator_predecessors _ _ _ ?_ ?_ ?_⟩
  · intro x hx he
    exact (actual_normalized_internal_live R).1 (by simpa [he] using hx)
  · intro x hx he
    exact (actual_normalized_internal_live R).2.1 (by simpa [he] using hx)
  · intro x hx he
    exact (actual_normalized_internal_live R).2.2 (by simpa [he] using hx)

theorem internal_cut_first_normal (R : ActualRolePacket P)
    (hcut : c2 P.M.base R.e*routingB P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    sourceNormal R (firstSource R)=(cr21 R.HD,0,cr23 R.HD) := by
  let s : ModelSources P.M.base R.e := ⟨_,internal_cut_source R hcut⟩
  have hd : monomialDegree P.M.base R.e (cr21 R.HD,0,cr23 R.HD)=s.val := by
    simpa [s,monomialDegree,normalizedGrid] using
      (coherent_normalized_relations _ _ R.HD).2.1.symm
  have hs : s=firstSource R := by
    apply Subtype.ext
    apply model_full_support_source_is_first
    have hp := monomial_positive_predecessors R (cr21 R.HD,0,cr23 R.HD)
    have hq := monomial_positive_predecessors R (0,c2 P.M.base R.e,0)
    have hu := (coherent_coefficients_positive _ _ R.HD).2.2.1
    have hv := (coherent_coefficients_positive _ _ R.HD).2.2.2.1
    refine ⟨?_,?_,?_⟩
    · rw [←hd]; exact hp.1 hu
    · have hd' : monomialDegree P.M.base R.e (0,c2 P.M.base R.e,0)=s.val := by
        simp [s,monomialDegree,normalizedGrid]
      rw [←hd']; exact hq.2.1 (herzogC_positive _ _ 1)
    · rw [←hd]; exact hp.2.2 hv
  have hn := (sourceNormal_spec R s).2.2 _ hd
  rw [hs] at hn
  simpa [f2Normal] using hn.symm

theorem internal_cut_compensation (R : ActualRolePacket P)
    (hcut : c2 P.M.base R.e*routingB P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    survivingWrapCount R + Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
      Nat.card {z // z ∈ borderExceptional R} :=
  compensation_of_first_source_y_zero R (by rw [internal_cut_first_normal R hcut])

theorem subcritical_pure_c_fiber (R : ActualRolePacket P)
    {D r i j : ℕ} (hD : D<c3 P.M.base R.e)
    (he : monomialDegree P.M.base R.e (r,i,j)=D*routingC P.M.base R.e) :
    r=0 ∧ i=0 ∧ j=D := by
  have ha := routingA_pos P.M.base R.e
  have hb := routingB_positive P.M.base R.e
  have hc := routingC_positive P.M.base R.e
  simp only [monomialDegree,normalizedGrid] at he
  have hj : j≤D := by nlinarith
  have hjD : j=D := by
    by_contra hh
    have hpos : 0<D-j := by omega
    have hm := congrArg (fun t => t*routingC P.M.base R.e) (Nat.sub_add_cancel hj)
    simp only [Nat.add_mul] at hm
    have hmin := (actual_normalized_critical_minima R).2.2 (D-j) r i hpos
      (by nlinarith only [he,hm])
    omega
  exact ⟨by nlinarith [he],by nlinarith [he],hjD⟩

theorem killed_pure_c_source (R : ActualRolePacket P)
    (hkill : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    ∃ s : ModelSources P.M.base R.e, ∃ D : ℕ,
      0<D ∧ D<c3 P.M.base R.e ∧ sourceNormal R s=(0,0,D) := by
  classical
  let c := routingC P.M.base R.e
  let K := cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
  have hc3 : 0<c3 P.M.base R.e := herzogC_positive _ _ 2
  have hex : ∃ D : ℕ, D*c∈K :=
    ⟨c3 P.M.base R.e-1,by simpa only [Nat.sub_mul,one_mul] using hkill⟩
  let D := Nat.find hex
  have hK : D*c∈K := Nat.find_spec hex
  have hle : D≤c3 P.M.base R.e-1 := Nat.find_min' hex
    (by simpa only [Nat.sub_mul,one_mul] using hkill)
  have hlt : D<c3 P.M.base R.e := by omega
  have hpos : 0<D := by
    obtain ⟨_,n,hn,y,_,heq⟩ := hK
    have hm := routingM_pos P.M.base R.e
    change D*c=n*routingM P.M.base R.e+y at heq
    nlinarith
  have hs : IsMinimalTailGenerator (routingH P.M.base R.e).toAddSubmonoid K (D*c) := by
    apply (minimalTail_iff_literal _ _ _).mpr
    refine ⟨hK,?_⟩
    intro y h hy hh heq
    obtain ⟨r,i,j,hyfac⟩ := L5A2C4OR6.routingH_factorization _ _ hy.1
    obtain ⟨r',i',j',hhfac⟩ := L5A2C4OR6.routingH_factorization _ _ hh
    have hf : monomialDegree P.M.base R.e (r+r',i+i',j+j')=D*c := by
      change monomialDegree P.M.base R.e ((r,i,j)+(r',i',j'))=D*c
      rw [monomialDegree_add]
      change normalizedGrid P.M.base R.e r i j+normalizedGrid P.M.base R.e r' i' j'=D*c
      simpa only [normalizedGrid,←hyfac,←hhfac] using heq.symm
    obtain ⟨hr,hi,hj⟩ := subcritical_pure_c_fiber R hlt hf
    have hr0 : r=0 ∧ r'=0 := by omega
    have hi0 : i=0 ∧ i'=0 := by omega
    have hyD : y=j*c := by simpa [normalizedGrid,hr0.1,hi0.1] using hyfac
    have hjmin : D≤j := Nat.find_min' hex (by rwa [←hyD])
    have hj' : j'=0 := by omega
    simpa [normalizedGrid,hr0.2,hi0.2,hj'] using hhfac
  let s : ModelSources P.M.base R.e := ⟨D*c,hs⟩
  have hn := (sourceNormal_spec R s).2.2 (0,0,D)
    (by simp [s,c,monomialDegree,normalizedGrid])
  exact ⟨s,D,hpos,hlt,by simpa [f2Normal] using hn.symm⟩

theorem mixed_alive_first_source_y_zero (R : ActualRolePacket P)
    (halive : c3 P.M.base R.e*routingC P.M.base R.e-routingA P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) ∧
      c3 P.M.base R.e*routingC P.M.base R.e-routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    (sourceNormal R (firstSource R)).2.1=0 := by
  have hkill : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    rcases actual_normalized_boundary_dichotomy R with h | h
    · exact h.1
    · exact False.elim (h.2.elim halive.1 halive.2)
  obtain ⟨s,D,hD,hDc,hs⟩ := killed_pure_c_source R hkill
  have hfirst : s=firstSource R := by
    apply Subtype.ext
    by_contra hh
    obtain ⟨n,t,hn,_,ht,htpos,heq⟩ := model_nonfirst_source_small_return _ _ s hh
    obtain ⟨x,y,z,hfac⟩ := L5A2C4OR6.routingH_factorization _ _ ht
    have hdeg : monomialDegree P.M.base R.e (x,y,z)=t := hfac.symm
    have hsdeg : s.val=D*routingC P.M.base R.e := by
      rw [←(sourceNormal_spec R s).1,hs]; simp [monomialDegree,normalizedGrid]
    have sep := source_return_coordinate_separation R s (sourceNormal R s) (x,y,z)
      (sourceNormal_spec R s).1 hn (heq.trans (by rw [hdeg]))
    have hz : z=0 := sep.2.2 (by simpa [hs] using hD)
    have hsmall := congrArg (fun t => t*routingC P.M.base R.e)
      (Nat.sub_add_cancel (Nat.le_of_lt hDc))
    simp only [Nat.add_mul] at hsmall
    have hparent : c3 P.M.base R.e*routingC P.M.base R.e=
        n*routingM P.M.base R.e+monomialDegree P.M.base R.e (x,y,c3 P.M.base R.e-D) := by
      simp only [monomialDegree,normalizedGrid,hz,zero_mul,add_zero] at hdeg
      simp only [monomialDegree,normalizedGrid]
      omega
    by_cases hx : 0<x
    · obtain ⟨v,hv,hvdeg⟩ := (monomial_positive_predecessors R (x,y,c3 P.M.base R.e-D)).1 hx
      have hsub : c3 P.M.base R.e*routingC P.M.base R.e-routingA P.M.base R.e=
          n*routingM P.M.base R.e+v := by omega
      apply halive.1
      refine ⟨?_,n,hn,v,hv,hsub⟩
      have hr := (coherent_normalized_relations _ _ R.HD).2.2
      have hpos := (coherent_coefficients_positive _ _ R.HD).2.2.2.2.1
      have hm := congrArg (fun t => t*routingA P.M.base R.e) (show cr31 R.HD-1+1=cr31 R.HD by omega)
      simp only [Nat.add_mul,one_mul] at hm
      convert grid_mem_H P.M.base R.e (cr31 R.HD-1,cr32 R.HD,0) using 1
      simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
      omega
    · have hy : 0<y := by
        have hx0 : x=0 := by omega
        simp only [monomialDegree,normalizedGrid,hx0,hz,zero_mul,zero_add,add_zero] at hdeg
        by_contra hh
        have : y=0 := by omega
        simp [this] at hdeg
        omega
      obtain ⟨v,hv,hvdeg⟩ := (monomial_positive_predecessors R (x,y,c3 P.M.base R.e-D)).2.1 hy
      have hsub : c3 P.M.base R.e*routingC P.M.base R.e-routingB P.M.base R.e=
          n*routingM P.M.base R.e+v := by omega
      apply halive.2
      refine ⟨?_,n,hn,v,hv,hsub⟩
      have hr := (coherent_normalized_relations _ _ R.HD).2.2
      have hpos := (coherent_coefficients_positive _ _ R.HD).2.2.2.2.2
      have hm := congrArg (fun t => t*routingB P.M.base R.e) (show cr32 R.HD-1+1=cr32 R.HD by omega)
      simp only [Nat.add_mul,one_mul] at hm
      convert grid_mem_H P.M.base R.e (cr31 R.HD,cr32 R.HD-1,0) using 1
      simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
      omega
  rw [←hfirst,hs]

theorem mixed_alive_compensation (R : ActualRolePacket P)
    (halive : c3 P.M.base R.e*routingC P.M.base R.e-routingA P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) ∧
      c3 P.M.base R.e*routingC P.M.base R.e-routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    survivingWrapCount R + Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)}≤
      Nat.card {z // z ∈ borderExceptional R} :=
  compensation_of_first_source_y_zero R (mixed_alive_first_source_y_zero R halive)
end NS25Lean.L5A2C4OR36
