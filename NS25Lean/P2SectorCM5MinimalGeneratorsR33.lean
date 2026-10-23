import NS25Lean.P2SectorCNormalStripR32

set_option linter.style.header false
set_option linter.style.whitespace false
noncomputable section
namespace NS25Lean.L5A2C4OR33
open L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR5
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 L5A2C4OR29 L5A2C4OR32 FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

/-- Exact promotion of the R32 first-missing definition. -/
def rawGenerators {P : P2Data Gamma} (R : ActualRolePacket P) : Set Monomial :=
  {(0,c2 P.M.base R.e,0)} ∪ Set.range (sourceNormal R) ∪ {boundaryAliveMonomial R}

def Divides (w g : Monomial) : Prop := w.1≤g.1 ∧ w.2.1≤g.2.1 ∧ w.2.2≤g.2.2

theorem grid_mem_H (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (z : Monomial) :
    monomialDegree B e z ∈ routingH B e :=
  (mem_generatedThree_iff _ _ _ _).mpr ⟨z.1,z.2.1,z.2.2,rfl⟩

theorem cut_add_H {H : NumericalSemigroup} {m x h : ℕ}
    (hx : x ∈ cyclicCut H m) (hh : h ∈ H) : x+h ∈ cyclicCut H m := by
  obtain ⟨hxH,n,hn,t,ht,heq⟩ := hx
  exact ⟨H.toAddSubmonoid.add_mem hxH hh,n,hn,t+h,
    H.toAddSubmonoid.add_mem ht hh,by omega⟩

theorem degree_divisor_reconstruct (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {w g : Monomial} (h : Divides w g) :
    monomialDegree B e g = monomialDegree B e w+
      monomialDegree B e (g.1-w.1,g.2.1-w.2.1,g.2.2-w.2.2) := by
  have ha := congrArg (fun n => n*routingA B e) (Nat.sub_add_cancel h.1)
  have hb := congrArg (fun n => n*routingB B e) (Nat.sub_add_cancel h.2.1)
  have hc := congrArg (fun n => n*routingC B e) (Nat.sub_add_cancel h.2.2)
  simp only [Nat.add_mul] at ha hb hc
  simp only [monomialDegree,normalizedGrid]
  omega

theorem degree_divisor_eq (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {w g : Monomial} (h : Divides w g)
    (hd : monomialDegree B e w = monomialDegree B e g) : w=g := by
  have hr := degree_divisor_reconstruct B e h
  have ha := routingA_pos B e
  have hb := routingB_positive B e
  have hc := routingC_positive B e
  have hz : monomialDegree B e (g.1-w.1,g.2.1-w.2.1,g.2.2-w.2.2)=0 := by omega
  simp only [monomialDegree,normalizedGrid] at hz
  have h1 : g.1-w.1=0 := by nlinarith
  have h2 : g.2.1-w.2.1=0 := by nlinarith
  have h3 : g.2.2-w.2.2=0 := by nlinarith
  rcases h with ⟨h1le,h2le,h3le⟩
  apply Prod.ext
  · omega
  · apply Prod.ext <;> omega

theorem monomial_cut_upward (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {w g : Monomial} (h : Divides w g)
    (hw : monomialDegree B e w ∈ cyclicCut (routingH B e) (routingM B e)) :
    monomialDegree B e g ∈ cyclicCut (routingH B e) (routingM B e) := by
  rw [degree_divisor_reconstruct B e h]
  exact cut_add_H hw (grid_mem_H B e _)

theorem source_divisor_eq {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) {w : Monomial}
    (h : Divides w (sourceNormal R s))
    (hw : monomialDegree P.M.base R.e w ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    w=sourceNormal R s := by
  have hr := degree_divisor_reconstruct P.M.base R.e h
  have hm := ((minimalTail_iff_literal _ _ _).mp s.property).2
    (monomialDegree P.M.base R.e w)
    (monomialDegree P.M.base R.e ((sourceNormal R s).1-w.1,
      (sourceNormal R s).2.1-w.2.1,(sourceNormal R s).2.2-w.2.2))
    hw (grid_mem_H _ _ _) ((sourceNormal_spec R s).1.symm.trans hr)
  apply degree_divisor_eq P.M.base R.e h
  omega

theorem boundary_ne_source {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) : boundaryAliveMonomial R ≠ sourceNormal R s := by
  intro he
  apply source_no_cWrap_rewrite R s 0 0 (c3 P.M.base R.e) le_rfl
  simpa [monomialDegree,normalizedGrid] using
    (boundaryAliveMonomial_degree R).symm.trans (he ▸ (sourceNormal_spec R s).1)

theorem sourceWrap_degree_increment {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) :
    monomialDegree P.M.base R.e (sourceWrap R (sourceNormal R s)) =
      s.val+(c2 P.M.base R.e-(sourceNormal R s).2.1)*routingB P.M.base R.e := by
  have hs := (sourceNormal_spec R s).1
  have hlt := (sourceNormal_spec R s).2.1
  have hr := (coherent_normalized_relations P.M.base R.e R.HD).2.1
  have hm := congrArg (fun n => n*routingB P.M.base R.e)
    (Nat.sub_add_cancel (Nat.le_of_lt hlt))
  simp only [sourceWrap,monomialDegree,normalizedGrid,Nat.add_mul] at hs hm ⊢
  nlinarith only [hs,hm,hr]

theorem sourceWrap_not_divides_source {P : P2Data Gamma} (R : ActualRolePacket P)
    (s t : ModelSources P.M.base R.e)
    (h : Divides (sourceWrap R (sourceNormal R t)) (sourceNormal R s)) : False := by
  have hr := degree_divisor_reconstruct P.M.base R.e h
  have hw := sourceWrap_degree_increment R t
  have hlt := (sourceNormal_spec R t).2.1
  have hb := routingB_positive P.M.base R.e
  let d : Monomial := ((sourceNormal R s).1-(sourceWrap R (sourceNormal R t)).1,
    (sourceNormal R s).2.1-(sourceWrap R (sourceNormal R t)).2.1,
    (sourceNormal R s).2.2-(sourceWrap R (sourceNormal R t)).2.2)
  have hK := ((minimalTail_iff_literal _ _ _).mp t.property).1
  have hH : (c2 P.M.base R.e-(sourceNormal R t).2.1)*routingB P.M.base R.e+
      monomialDegree P.M.base R.e d ∈ routingH P.M.base R.e := by
    apply (routingH _ _).toAddSubmonoid.add_mem
    · simpa [monomialDegree,normalizedGrid] using grid_mem_H P.M.base R.e
        (0,c2 P.M.base R.e-(sourceNormal R t).2.1,0)
    · exact grid_mem_H _ _ d
  have hz := ((minimalTail_iff_literal _ _ _).mp s.property).2 t.val _ hK hH
    (by rw [←(sourceNormal_spec R s).1,hr,hw]; simp only [d]; omega)
  nlinarith [Nat.sub_pos_of_lt hlt]

theorem boundary_divisor_eq_of_cut {P : P2Data Gamma} (R : ActualRolePacket P)
    {w : Monomial} (h : Divides w (boundaryAliveMonomial R))
    (hw : monomialDegree P.M.base R.e w ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    w=boundaryAliveMonomial R := by
  classical
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hr := (coherent_normalized_relations P.M.base R.e R.HD).2.2
  by_cases hc : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
  · simp only [boundaryAliveMonomial,if_pos hc] at h ⊢
    rcases h with ⟨hx,hy,hz⟩
    simp only [Prod.fst,Prod.snd] at hx hy hz
    have hx0 : w.1=0 := by simpa using hx
    have hy0 : w.2.1=0 := by simpa using hy
    have he : w.2.2=c3 P.M.base R.e := by
      by_contra hn
      have hk := monomial_cut_upward P.M.base R.e
        (g := (0,0,c3 P.M.base R.e-1))
        (show Divides w (0,0,c3 P.M.base R.e-1) by
          exact ⟨by simpa [hx0],by simpa [hy0],by simp only [Prod.snd]; omega⟩) hw
      apply hc
      simpa [monomialDegree,normalizedGrid,Nat.sub_mul] using hk
    exact Prod.ext hx0 (Prod.ext hy0 he)
  · simp only [boundaryAliveMonomial,if_neg hc] at h ⊢
    rcases h with ⟨hx,hy,hz⟩
    simp only [Prod.fst,Prod.snd] at hx hy hz
    have hz0 : w.2.2=0 := by simpa using hz
    have hl := actual_normalized_boundary_dichotomy R
    have hab :
        c3 P.M.base R.e*routingC P.M.base R.e-routingA P.M.base R.e ∉
          cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) ∧
        c3 P.M.base R.e*routingC P.M.base R.e-routingB P.M.base R.e ∉
          cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
      rcases hl with hh | hh
      · exact hh.2
      · exact (hc hh.1).elim
    have hxEq : w.1=cr31 R.HD := by
      by_contra hn
      have hk := monomial_cut_upward P.M.base R.e
        (g := (cr31 R.HD-1,cr32 R.HD,0))
        (show Divides w (cr31 R.HD-1,cr32 R.HD,0) by
          exact ⟨by simp only [Prod.fst]; omega,hy,by simpa [hz0]⟩) hw
      have he : monomialDegree P.M.base R.e (cr31 R.HD-1,cr32 R.HD,0)=
          c3 P.M.base R.e*routingC P.M.base R.e-routingA P.M.base R.e := by
        have hs := congrArg (fun n => n*routingA P.M.base R.e)
          (Nat.sub_add_cancel (show 1≤cr31 R.HD by omega))
        simp only [Nat.add_mul,one_mul] at hs
        simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
        omega
      exact hab.1 (he ▸ hk)
    have hyEq : w.2.1=cr32 R.HD := by
      by_contra hn
      have hk := monomial_cut_upward P.M.base R.e
        (g := (cr31 R.HD,cr32 R.HD-1,0))
        (show Divides w (cr31 R.HD,cr32 R.HD-1,0) by
          exact ⟨hx,by simp only [Prod.fst,Prod.snd]; omega,by simpa [hz0]⟩) hw
      have he : monomialDegree P.M.base R.e (cr31 R.HD,cr32 R.HD-1,0)=
          c3 P.M.base R.e*routingC P.M.base R.e-routingB P.M.base R.e := by
        have hs := congrArg (fun n => n*routingB P.M.base R.e)
          (Nat.sub_add_cancel (show 1≤cr32 R.HD by omega))
        simp only [Nat.add_mul,one_mul] at hs
        simp only [monomialDegree,normalizedGrid,zero_mul,add_zero]
        omega
      exact hab.2 (he ▸ hk)
    exact Prod.ext hxEq (Prod.ext hyEq hz0)

theorem source_not_divides_yC {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e)
    (h : Divides (sourceNormal R s) (0,c2 P.M.base R.e,0)) : False := by
  have hy := (sourceNormal_spec R s).2.1
  have hK := ((minimalTail_iff_literal _ _ _).mp s.property).1
  have hk := monomial_cut_upward P.M.base R.e
    (show Divides (sourceNormal R s) (0,c2 P.M.base R.e-1,0) by
      exact ⟨h.1,by simp only [Prod.fst,Prod.snd]; omega,h.2.2⟩)
    (by rwa [(sourceNormal_spec R s).1])
  apply (actual_normalized_internal_live R).2.1
  simpa [monomialDegree,normalizedGrid,Nat.sub_mul] using hk

theorem boundary_not_divides_yC {P : P2Data Gamma} (R : ActualRolePacket P)
    (h : Divides (boundaryAliveMonomial R) (0,c2 P.M.base R.e,0)) : False := by
  classical
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hc3 : 0<c3 P.M.base R.e := herzogC_positive P.M.base R.e 2
  by_cases hc : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
  · simp only [boundaryAliveMonomial,if_pos hc] at h
    have hz : c3 P.M.base R.e≤0 := h.2.2
    omega
  · simp only [boundaryAliveMonomial,if_neg hc] at h
    have hx : cr31 R.HD≤0 := h.1
    omega

theorem sourceWrap_not_divides_yC {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e)
    (h : Divides (sourceWrap R (sourceNormal R s)) (0,c2 P.M.base R.e,0)) : False := by
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hx := h.1
  simp only [sourceWrap,Prod.fst] at hx
  omega

theorem sourceWrap_not_divides_boundary {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e)
    (h : Divides (sourceWrap R (sourceNormal R s)) (boundaryAliveMonomial R)) : False := by
  classical
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  by_cases hc : c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
  · simp only [boundaryAliveMonomial,if_pos hc] at h
    have hx : (sourceNormal R s).1+cr21 R.HD≤0 := h.1
    omega
  · simp only [boundaryAliveMonomial,if_neg hc] at h
    have hz : (sourceNormal R s).2.2+cr23 R.HD≤0 := h.2.2
    omega

theorem boundary_y_lt {P : P2Data Gamma} (R : ActualRolePacket P) :
    (boundaryAliveMonomial R).2.1<c2 P.M.base R.e := by
  classical
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hr := (coherent_coefficients P.M.base R.e R.HD).2.1
  have hc := herzogC_positive P.M.base R.e 1
  unfold boundaryAliveMonomial
  split_ifs <;> simp only [Prod.fst,Prod.snd] <;> omega

theorem initial_divisor_of_raw_eq {P : P2Data Gamma} (R : ActualRolePacket P)
    {w g : Monomial} (hg : g ∈ rawGenerators R)
    (hw : w ∈ initialGenerators R) (h : Divides w g) : w=g := by
  simp only [rawGenerators,initialGenerators,M4Generators,Set.mem_union,
    Set.mem_singleton_iff,Set.mem_range,Set.mem_setOf_eq] at hg hw
  rcases hg with (rfl | ⟨s,rfl⟩) | rfl
  · rcases hw with rfl | ((⟨t,rfl⟩ | rfl) | ⟨t,ht,rfl⟩)
    · rfl
    · exact (source_not_divides_yC R t h).elim
    · exact (boundary_not_divides_yC R h).elim
    · exact (sourceWrap_not_divides_yC R t h).elim
  · rcases hw with rfl | ((⟨t,rfl⟩ | rfl) | ⟨t,ht,rfl⟩)
    · have hy := (sourceNormal_spec R s).2.1
      have hh : c2 P.M.base R.e≤(sourceNormal R s).2.1 := h.2.1
      omega
    · exact source_divisor_eq R s h (by
        rw [(sourceNormal_spec R t).1]
        exact ((minimalTail_iff_literal _ _ _).mp t.property).1)
    · exact (boundary_ne_source R s
        (source_divisor_eq R s h (by
          rw [boundaryAliveMonomial_degree]; exact actual_boundary_degree_in_cut R))).elim
    · exact (sourceWrap_not_divides_source R s t h).elim
  · rcases hw with rfl | ((⟨t,rfl⟩ | rfl) | ⟨t,ht,rfl⟩)
    · have hy := boundary_y_lt R
      have hh : c2 P.M.base R.e≤(boundaryAliveMonomial R).2.1 := h.2.1
      omega
    · have he := boundary_divisor_eq_of_cut R h (by
        rw [(sourceNormal_spec R t).1]
        exact ((minimalTail_iff_literal _ _ _).mp t.property).1)
      exact (boundary_ne_source R t he.symm).elim
    · rfl
    · exact (sourceWrap_not_divides_boundary R t h).elim

theorem raw_subset_initial {P : P2Data Gamma} (R : ActualRolePacket P) :
    rawGenerators R ⊆ initialGenerators R := by
  intro g hg
  simp only [rawGenerators,initialGenerators,M4Generators,Set.mem_union,
    Set.mem_singleton_iff] at hg ⊢
  tauto

/-- Original R32 benchmark, on every actual role packet, with no free gate. -/
theorem original_initial_generators_minimal :
    ∀ {Gamma : NumericalSemigroup} {P : P2Data Gamma} (R : ActualRolePacket P)
      (g : Monomial), g ∈ rawGenerators R →
      g ∈ monomialClosure (initialGenerators R) ∧
      ∀ z ∈ monomialClosure (initialGenerators R),
        z.1≤g.1 → z.2.1≤g.2.1 → z.2.2≤g.2.2 → z=g := by
  intro Gamma P R g hg
  refine ⟨⟨g,raw_subset_initial R hg,le_rfl,le_rfl,le_rfl⟩,?_⟩
  rintro z ⟨w,hw,hw1,hw2,hw3⟩ hz1 hz2 hz3
  have he := initial_divisor_of_raw_eq R hg hw
    ⟨hw1.trans hz1,hw2.trans hz2,hw3.trans hz3⟩
  subst w
  apply Prod.ext
  · omega
  · apply Prod.ext <;> omega

/-- Minimal exponents of the WHOLE initial closure, not J membership. -/
def InitialMinimal {P : P2Data Gamma} (R : ActualRolePacket P) (g : Monomial) : Prop :=
  g ∈ monomialClosure (initialGenerators R) ∧
    ∀ z ∈ monomialClosure (initialGenerators R), Divides z g → z=g

def initialMinimalGenerators {P : P2Data Gamma} (R : ActualRolePacket P) : Set Monomial :=
  {g | InitialMinimal R g}

def sourceWraps {P : P2Data Gamma} (R : ActualRolePacket P) : Set Monomial :=
  {g | ∃ s : ModelSources P.M.base R.e,
    0<(sourceNormal R s).2.1 ∧ g=sourceWrap R (sourceNormal R s)}

/-- Distinct exponent seats, not source labels; only genuinely minimal wraps survive. -/
def survivingSourceWraps {P : P2Data Gamma} (R : ActualRolePacket P) : Set Monomial :=
  {g | g ∈ sourceWraps R ∧ InitialMinimal R g ∧ g ∉ rawGenerators R}

def survivingWrapCount {P : P2Data Gamma} (R : ActualRolePacket P) : ℕ :=
  Nat.card (survivingSourceWraps R)

theorem raw_is_minimal {P : P2Data Gamma} (R : ActualRolePacket P)
    {g : Monomial} (hg : g ∈ rawGenerators R) : InitialMinimal R g := by
  obtain ⟨hmem,hmin⟩ := original_initial_generators_minimal R g hg
  exact ⟨hmem,fun z hz h => hmin z hz h.1 h.2.1 h.2.2⟩

theorem minimal_mem_initial {P : P2Data Gamma} (R : ActualRolePacket P)
    {g : Monomial} (hg : InitialMinimal R g) : g ∈ initialGenerators R := by
  obtain ⟨w,hw,h1,h2,h3⟩ := hg.1
  have he := hg.2 w ⟨w,hw,le_rfl,le_rfl,le_rfl⟩ ⟨h1,h2,h3⟩
  rwa [he] at hw

theorem initial_eq_raw_union_wraps {P : P2Data Gamma} (R : ActualRolePacket P) :
    initialGenerators R = rawGenerators R ∪ sourceWraps R := by
  ext g
  simp only [initialGenerators,M4Generators,rawGenerators,sourceWraps,
    Set.mem_union,Set.mem_singleton_iff,Set.mem_setOf_eq]
  tauto

theorem initial_minimal_partition {P : P2Data Gamma} (R : ActualRolePacket P) :
    initialMinimalGenerators R = rawGenerators R ∪ survivingSourceWraps R := by
  ext g
  constructor
  · intro hg
    have hi := minimal_mem_initial R hg
    rw [initial_eq_raw_union_wraps] at hi
    by_cases hr : g ∈ rawGenerators R
    · exact Or.inl hr
    · exact Or.inr ⟨hi.resolve_left hr,hg,hr⟩
  · rintro (hg | hg)
    · exact raw_is_minimal R hg
    · exact hg.2.1

theorem raw_survivor_disjoint {P : P2Data Gamma} (R : ActualRolePacket P) :
    Disjoint (rawGenerators R) (survivingSourceWraps R) := by
  exact Set.disjoint_left.mpr (fun g hr hs => hs.2.2 hr)

theorem rawGenerators_finite {P : P2Data Gamma} (R : ActualRolePacket P) :
    (rawGenerators R).Finite := by
  letI := actual_model_sources_finite R
  exact ((Set.finite_singleton _).union (Set.finite_range _)).union (Set.finite_singleton _)

theorem sourceWraps_finite {P : P2Data Gamma} (R : ActualRolePacket P) :
    (sourceWraps R).Finite := by
  letI := actual_model_sources_finite R
  apply (Set.finite_range (fun s : ModelSources P.M.base R.e =>
    sourceWrap R (sourceNormal R s))).subset
  rintro g ⟨s,_,rfl⟩
  exact ⟨s,rfl⟩

theorem survivingSourceWraps_finite {P : P2Data Gamma} (R : ActualRolePacket P) :
    (survivingSourceWraps R).Finite :=
  (sourceWraps_finite R).subset (fun _ hg => hg.1)

theorem initialMinimalGenerators_finite {P : P2Data Gamma} (R : ActualRolePacket P) :
    (initialMinimalGenerators R).Finite := by
  rw [initial_minimal_partition]
  exact (rawGenerators_finite R).union (survivingSourceWraps_finite R)

theorem yC_not_source_range {P : P2Data Gamma} (R : ActualRolePacket P) :
    (0,c2 P.M.base R.e,0) ∉ Set.range (sourceNormal R) := by
  rintro ⟨s,hs⟩
  apply source_not_divides_yC R s
  rw [hs]
  exact ⟨le_rfl,le_rfl,le_rfl⟩

theorem boundary_not_source_range {P : P2Data Gamma} (R : ActualRolePacket P) :
    boundaryAliveMonomial R ∉ Set.range (sourceNormal R) := by
  rintro ⟨s,hs⟩
  exact boundary_ne_source R s hs.symm

theorem boundary_ne_yC {P : P2Data Gamma} (R : ActualRolePacket P) :
    boundaryAliveMonomial R ≠ (0,c2 P.M.base R.e,0) := by
  intro he
  apply boundary_not_divides_yC R
  rw [he]
  exact ⟨le_rfl,le_rfl,le_rfl⟩

theorem rawGenerators_card {P : P2Data Gamma} (R : ActualRolePacket P) :
    Nat.card (rawGenerators R)=P.sourceCount+2 := by
  letI := actual_model_sources_finite R
  have hsf : (Set.range (sourceNormal R)).Finite := Set.finite_range _
  have he : rawGenerators R = insert (0,c2 P.M.base R.e,0)
      (insert (boundaryAliveMonomial R) (Set.range (sourceNormal R))) := by
    ext g
    simp only [rawGenerators,Set.mem_union,Set.mem_singleton_iff,Set.mem_insert_iff]
    tauto
  have hy : (0,c2 P.M.base R.e,0) ∉
      insert (boundaryAliveMonomial R) (Set.range (sourceNormal R)) := by
    simp only [Set.mem_insert_iff,not_or]
    exact ⟨Ne.symm (boundary_ne_yC R),yC_not_source_range R⟩
  change (rawGenerators R).ncard=P.sourceCount+2
  rw [he,Set.ncard_insert_of_notMem hy (hsf.insert _),
    Set.ncard_insert_of_notMem (boundary_not_source_range R) hsf]
  have hs : (Set.range (sourceNormal R)).ncard=P.sourceCount :=
    sourceNormalRepresentatives_card R
  omega

/-- Exact M5 count μ(L)=S+2+B. B counts actual minimal distinct wraps. -/
theorem initial_minimal_count {P : P2Data Gamma} (R : ActualRolePacket P) :
    Nat.card (initialMinimalGenerators R)=P.sourceCount+2+survivingWrapCount R := by
  change (initialMinimalGenerators R).ncard=P.sourceCount+2+(survivingSourceWraps R).ncard
  rw [initial_minimal_partition,
    Set.ncard_union_eq (raw_survivor_disjoint R) (rawGenerators_finite R)
      (survivingSourceWraps_finite R)]
  exact congrArg (fun n => n+(survivingSourceWraps R).ncard) (rawGenerators_card R)

theorem divides_trans {x y z : Monomial} (h : Divides x y) (h' : Divides y z) :
    Divides x z := ⟨h.1.trans h'.1,h.2.1.trans h'.2.1,h.2.2.trans h'.2.2⟩

/-- Generic terminating divisor descent. No minimality/existence premise. -/
theorem closure_has_minimal_divisor (G : Set Monomial) (g : Monomial)
    (hg : g ∈ monomialClosure G) :
    ∃ w, w ∈ monomialClosure G ∧
      (∀ z ∈ monomialClosure G, Divides z w → z=w) ∧ Divides w g := by
  classical
  by_cases hm : ∀ z ∈ monomialClosure G, Divides z g → z=g
  · exact ⟨g,hg,hm,le_rfl,le_rfl,le_rfl⟩
  · push_neg at hm
    obtain ⟨z,hz,hd,hne⟩ := hm
    obtain ⟨w,hw,hmin,hwd⟩ := closure_has_minimal_divisor G z hz
    exact ⟨w,hw,hmin,divides_trans hwd hd⟩
termination_by g.1+g.2.1+g.2.2
decreasing_by
  rcases hd with ⟨h1,h2,h3⟩
  have he : z.1+z.2.1+z.2.2 < g.1+g.2.1+g.2.2 := by
    by_contra hn
    have hzEq : z=g := by
      apply Prod.ext
      · omega
      · apply Prod.ext <;> omega
    exact hne hzEq
  exact he

theorem minimal_generators_generate {P : P2Data Gamma} (R : ActualRolePacket P) :
    monomialClosure (initialMinimalGenerators R)=monomialClosure (initialGenerators R) := by
  ext g
  constructor
  · rintro ⟨w,hw,h1,h2,h3⟩
    exact monomialClosure_upward hw.1 h1 h2 h3
  · intro hg
    obtain ⟨w,hw,hm,hd⟩ := closure_has_minimal_divisor (initialGenerators R) g hg
    exact ⟨w,⟨hw,hm⟩,hd⟩

def initialMinimalFinset {P : P2Data Gamma} (R : ActualRolePacket P) : Finset Monomial :=
  (initialMinimalGenerators_finite R).toFinset

@[simp] theorem mem_initialMinimalFinset {P : P2Data Gamma} (R : ActualRolePacket P)
    (g : Monomial) : g ∈ initialMinimalFinset R ↔ InitialMinimal R g :=
  (initialMinimalGenerators_finite R).mem_toFinset

theorem initialMinimalFinset_closure {P : P2Data Gamma} (R : ActualRolePacket P) :
    monomialClosure (initialMinimalFinset R : Set Monomial)=
      monomialClosure (initialGenerators R) := by
  have he : (initialMinimalFinset R : Set Monomial)=initialMinimalGenerators R := by
    ext g
    exact mem_initialMinimalFinset R g
  rw [he,minimal_generators_generate]

theorem initialMinimalFinset_card {P : P2Data Gamma} (R : ActualRolePacket P) :
    (initialMinimalFinset R).card=P.sourceCount+2+survivingWrapCount R := by
  unfold initialMinimalFinset
  rw [← Set.ncard_eq_toFinset_card (initialMinimalGenerators R)
    (initialMinimalGenerators_finite R)]
  exact initial_minimal_count R

theorem initial_proper {P : P2Data Gamma} (R : ActualRolePacket P) :
    (0,0,0) ∉ monomialClosure (initialGenerators R) := by
  intro h
  have hm := (original_initial_generators_minimal R (0,c2 P.M.base R.e,0)
    (Or.inl (Or.inl rfl))).2 (0,0,0) h (by simp) (by simp) (by simp)
  have hc : 0<c2 P.M.base R.e := herzogC_positive _ _ 1
  have he := congrArg (fun z : Monomial => z.2.1) hm
  simp only [Prod.fst,Prod.snd] at he
  omega

/-- Literal agreement with the frozen T6 notion of polynomial minimality. -/
theorem polynomialMinimal_iff {P : P2Data Gamma} (R : ActualRolePacket P)
    (g : Monomial) :
    L5A2C4OR23.PolynomialMinimal (initialGenerators R) g ↔ InitialMinimal R g := by
  constructor
  · rintro ⟨hm,h⟩
    exact ⟨hm,fun w hw hd => h w hw hd.1 hd.2.1 hd.2.2⟩
  · rintro ⟨hm,h⟩
    exact ⟨hm,fun w hw h1 h2 h3 => h w hw ⟨h1,h2,h3⟩⟩

theorem normal_cut_mem_initial {P : P2Data Gamma} (R : ActualRolePacket P)
    (z : Monomial) (hy : z.2.1<c2 P.M.base R.e)
    (hk : monomialDegree P.M.base R.e z ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    z ∈ monomialClosure (initialGenerators R) := by
  have hJ : roleMonomial ℚ R.e z ∈ P.M.base.J ℚ := by
    rw [←actual_source_quotient_eq ℚ R]
    apply actual_cut_monomial_mem_sourceQuotient ℚ R (roleExponent R.e z)
    rw [roleExponent_weight]
    exact (actual_scaled_cut_iff _ _ _).mp hk
  obtain ⟨w,hw,h1,h2,h3⟩ := (source_initial_normal_strip R ℚ z hy).mp hJ
  exact ⟨w,Or.inr hw,h1,h2,h3⟩

/-- Actual Artinian axes; no caller-supplied height or cofinite hypothesis. -/
theorem initial_axes {P : P2Data Gamma} (R : ActualRolePacket P) :
    ∃ a b c : ℕ, 0<a ∧ 0<b ∧ 0<c ∧
      (a,0,0) ∈ monomialClosure (initialGenerators R) ∧
      (0,b,0) ∈ monomialClosure (initialGenerators R) ∧
      (0,0,c) ∈ monomialClosure (initialGenerators R) := by
  obtain ⟨s,A,hA,_,hs⟩ := actual_pure_a_source R
  have hc : 0<c2 P.M.base R.e := herzogC_positive _ _ 1
  refine ⟨A,c2 P.M.base R.e,routingM P.M.base R.e,hA,hc,routingM_pos _ _,?_,?_,?_⟩
  · refine ⟨sourceNormal R s,Or.inr (Or.inl (Or.inl ⟨s,rfl⟩)),?_,?_,?_⟩ <;>
      simp [hs]
  · exact ⟨(0,c2 P.M.base R.e,0),Or.inl rfl,le_rfl,le_rfl,le_rfl⟩
  · apply normal_cut_mem_initial R _ (by simpa using hc)
    refine ⟨grid_mem_H _ _ _,routingC P.M.base R.e,routingC_positive _ _,0,
      (routingH _ _).toAddSubmonoid.zero_mem,?_⟩
    simp [monomialDegree,normalizedGrid,Nat.mul_comm]

end NS25Lean.L5A2C4OR33
