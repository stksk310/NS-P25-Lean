import NS25Lean.P2SectorCT9RightEnvelopeR26
set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.L5A2C4OR27
open L2B FourGeneratedBridge L5A2C4A L5A2C4C L5A2C4D L5A2C4H
 L5A2C4OR1 L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
 L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 L5A2C4OR25 L5A2C4OR26
variable {Gamma : NumericalSemigroup}

theorem pb_minimal (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
 (HD : CoherentHerzogData B e) (heps : PB_epsilon B e HD=1) :
 ChartMinimal B e HD (principalPB B e HD) := by
 unfold PB_epsilon at heps
 split_ifs at heps with h
 exact h

theorem principal_generators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
 (HD : CoherentHerzogData B e) :
 principalVector B e HD ∈ canonicalIdealGenerators B e HD ∧
 principalPB B e HD ∈ canonicalIdealGenerators B e HD := by
 have hs := principalVector_spec B e HD
 constructor
 · exact Or.inr (Or.inr ⟨_,_,_,hs.1,hs.2.symm,Or.inl rfl⟩)
 · exact Or.inr (Or.inr ⟨_,_,_,hs.1,hs.2.symm,Or.inr (Or.inl rfl)⟩)

theorem pb_origin_strict (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
 (HD : CoherentHerzogData B e) (heps : PB_epsilon B e HD=1) :
 (principalVector B e HD).1+cr21 HD < H0 B e := by
 have hPB := pb_minimal B e HD heps
 have hp := coherent_coefficients_positive B e HD
 by_contra h
 have heq := hPB.2 (H0 B e,0,0)
   ⟨_,Or.inl (Or.inl rfl),le_rfl,le_rfl,le_rfl⟩
   (by simp only [principalPB,Prod.fst]; omega) (by simp [principalPB])
   (by simp [principalPB])
 have hz := congrArg (fun z : Monomial => z.2.2) heq
 simp only [principalPB,Prod.fst,Prod.snd] at hz
 omega

theorem actual_origin_return_of_principal_b_pos {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hU : 0 < (principalVector P.M.base R.e R.HD).2.1) :
    ∃ n : ℕ, 0 < n ∧
      n < firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e) (routingM_pos P.M.base R.e) ∧
      rawCandidate P.M.base R.e n 0 ≤ (H0 P.M.base R.e : ℤ) := by
  classical
  have hx : normalizedGrid P.M.base R.e (H0 P.M.base R.e) 0 0 ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    apply (actual_cyclicCut_iff_routingI _ _ _).mpr
    exact (normalizedGrid_mem_iff_eta_le _ _ _ _ _).mpr le_rfl
  obtain ⟨_,n,hpos,hle,y,hy,heq⟩ := (cyclicCut_finite_principal_reduction _ _ (routingM_pos _ _) _).mp hx
  have hnlt : n < firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e) (routingM_pos P.M.base R.e) := by
    by_contra h
    have hnEq : n=firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e) (routingM_pos P.M.base R.e) := by omega
    have hspec := (principalVector_spec P.M.base R.e R.HD).2
    rw [←hnEq] at hspec
    obtain ⟨r,u,v,hfac⟩ := routingH_factorization P.M.base R.e hy
    rw [hfac,←hspec] at heq
    simp only [monomialDegree,normalizedGrid,zero_mul,add_zero,Prod.fst,Prod.snd] at heq
    have ha := routingA_pos P.M.base R.e
    have hb := routingB_positive P.M.base R.e
    have hleX : (principalVector P.M.base R.e R.HD).1+r ≤ H0 P.M.base R.e := by
      have hmuleq := Nat.add_mul (principalVector P.M.base R.e R.HD).1 r (routingA P.M.base R.e)
      have hmul : ((principalVector P.M.base R.e R.HD).1+r)*routingA P.M.base R.e ≤ H0 P.M.base R.e*routingA P.M.base R.e := by omega
      exact Nat.le_of_mul_le_mul_right hmul ha
    have hf : (H0 P.M.base R.e-((principalVector P.M.base R.e R.HD).1+r))*routingA P.M.base R.e=
        ((principalVector P.M.base R.e R.HD).2.1+u)*routingB P.M.base R.e+
        ((principalVector P.M.base R.e R.HD).2.2+v)*routingC P.M.base R.e := by
      have hd := congrArg (fun z => z*routingA P.M.base R.e) (Nat.sub_add_cancel hleX)
      simp only [Nat.add_mul] at hd ⊢
      nlinarith only [hd,heq]
    have hpositive : 0 < H0 P.M.base R.e-((principalVector P.M.base R.e R.HD).1+r) := by
      by_contra hz
      have hzero : H0 P.M.base R.e-((principalVector P.M.base R.e R.HD).1+r)=0 := by omega
      rw [hzero] at hf
      have hproduct := Nat.mul_pos (show 0 < (principalVector P.M.base R.e R.HD).2.1+u by omega) hb
      omega
    have hmin := normalized_a_critical_min P.M.base R.e hpositive hf
    have hG0 := (normalized_mixed_notch_G0_G4 R hm hn).1
    omega
  refine ⟨n,hpos,hnlt,?_⟩
  apply (rawCandidate_threshold P.M.base R.e 0 hpos (H0 P.M.base R.e)).mp
  have heqZ : (routingA P.M.base R.e : ℤ)*H0 P.M.base R.e-(n : ℤ)*routingM P.M.base R.e=y := by
    simp only [normalizedGrid,zero_mul,add_zero] at heq
    have hh : (routingA P.M.base R.e : ℤ)*H0 P.M.base R.e=(n : ℤ)*routingM P.M.base R.e+y := by
      exact_mod_cast (show routingA P.M.base R.e*H0 P.M.base R.e=n*routingM P.M.base R.e+y by nlinarith only [heq])
    omega
  rw [physicalAlpha_zero,zero_add,heqZ]
  exact ⟨y,hy,rfl⟩

theorem actual_near_nonempty_of_delta_pos {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hdelta : 0 < (principalVector P.M.base R.e R.HD).1) :
    (nearHeights P.M.base R.e R.HD).Nonempty := by
  classical
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hgates := normalized_mixed_notch_G0_G4 R hm hn
  have hzero := hgates.2.1
  have hd : HerzogLShapeDomain R.HD (cr12 R.HD) (cr13 R.HD-1) :=
    ⟨by omega,by omega,Or.inr (by omega)⟩
  have hx := (chart_threshold_iff R hm hn 0 _ _ hd).mpr (by omega : eta P.M.base R.e (cr12 R.HD) (cr13 R.HD-1) ≤ 0)
  obtain ⟨g,hg,hgr,hgi,hgj⟩ := (chart_on_domain_iff _ _ _ _ hd).mp hx
  rcases hg with hg | hg | hg
  · subst g
    simp only [Prod.fst,Prod.snd] at hgr
    have hpos : 0 < H0 P.M.base R.e := by
      have hmono := eta_antitone_left P.M.base R.e 0 0 (c2 P.M.base R.e-1)
      simp only [zero_add] at hmono
      change eta P.M.base R.e (c2 P.M.base R.e-1) 0 ≤ H0 P.M.base R.e at hmono
      have hG2 := hgates.2.2.1
      omega
    omega
  · obtain ⟨n,i,j,d,hpos,hpre,hdepth,heq,hcases,hgen⟩ := hg
    have hnear : j < cr13 R.HD := by
      rcases hcases with hc | hc | hc
      · exact hc.2.2.2.1
      · simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_right (by omega : ¬j < cr13 R.HD),Set.mem_ofPred_eq] at hgen
        rcases hgen with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
      · exact hc.2.2.2.1
    refine ⟨j,Finset.mem_image.mpr ⟨(d,i,j),Finset.mem_filter.mpr ⟨?_,hnear⟩,rfl⟩⟩
    exact (mem_preSchedule _ _ _ _).mpr ⟨n,hpos,hpre,hdepth,heq,hcases⟩
  · obtain ⟨delta,U,V,hdom,hdegree,hgen⟩ := hg
    have hspec := principalVector_spec P.M.base R.e R.HD
    have heq : principalVector P.M.base R.e R.HD=(delta,U,V) :=
      canonical_monomial_unique _ _ _ hspec.1 hdom (hspec.2.trans hdegree)
    rw [heq] at hdelta
    change 0 < delta at hdelta
    rcases hgen with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega

theorem actual_first_zero_of_delta_pos {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hdelta : 0 < (principalVector P.M.base R.e R.HD).1) :
    ∃ h : ℕ, 0 < h ∧ h < cr13 R.HD ∧ rightHeight P.M.base R.e h=0 ∧
      h ∈ nearHeights P.M.base R.e R.HD ∧
      ∀ j ∈ nearHeights P.M.base R.e R.HD, h ≤ j := by
  classical
  have hne := actual_near_nonempty_of_delta_pos R hm hn hdelta
  let h := (nearHeights P.M.base R.e R.HD).min' hne
  have hmem : h ∈ nearHeights P.M.base R.e R.HD := Finset.min'_mem _ _
  have hb := nearHeights_bounds _ _ _ hmem
  refine ⟨h,hb.1,hb.2,?_,hmem,?_⟩
  · obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hmem
    obtain ⟨hpre,_⟩ := Finset.mem_filter.mp hz
    obtain ⟨n,_,_,_,_,hcases⟩ := (mem_preSchedule _ _ _ _).mp hpre
    have hi : z.2.1 < c2 P.M.base R.e := by
      have hs := coherent_coefficients P.M.base R.e R.HD
      have hp := coherent_coefficients_positive P.M.base R.e R.HD
      rcases hcases with hc | hc | hc <;> omega
    have hx : (0,c2 P.M.base R.e-1,h) ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) :=
      ⟨(0,z.2.1,z.2.2),Or.inl (preSchedule_zero_generator _ _ _ hpre),le_rfl,
        by simp only [Prod.fst,Prod.snd]; omega,by simp only [Prod.fst,Prod.snd]; omega⟩
    have h := (chart_threshold_iff R hm hn _ _ _ (right_boundary_domain _ _ _ hb.2)).mp hx
    change rightHeight P.M.base R.e _ ≤ 0 at h
    omega
  · exact fun j hj => Finset.min'_le _ j hj

theorem schedule_extrema_bounds (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {D h n i j d : ℕ}
    (hmax : ∀ d ∈ leftDepths B e HD, d ≤ D)
    (hmin : ∀ j ∈ nearHeights B e HD, h ≤ j)
    (hn : 0 < n) (hpre : n < firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e))
    (hd : 0 < d) (heq : n*routingM B e+d*routingA B e=i*routingB B e+j*routingC B e)
    (hcases : PreprincipalCases B e HD i j d) :
    (i < cr12 HD → d ≤ D) ∧ (j < cr13 HD → h ≤ j) := by
  classical
  have hmem := (mem_preSchedule B e HD (d,i,j)).mpr ⟨n,hn,hpre,hd,heq,hcases⟩
  constructor
  · intro hi
    exact hmax d (Finset.mem_image.mpr ⟨(d,i,j),Finset.mem_filter.mpr ⟨hmem,hi⟩,rfl⟩)
  · intro hj
    exact hmin j (Finset.mem_image.mpr ⟨(d,i,j),Finset.mem_filter.mpr ⟨hmem,hj⟩,rfl⟩)

theorem right_generator_lower {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    {D h j : ℕ} (hmax : ∀ d ∈ leftDepths P.M.base R.e R.HD, d ≤ D)
    (hmin : ∀ j ∈ nearHeights P.M.base R.e R.HD, h ≤ j)
    (hfloor : cr21 R.HD+(cr31 R.HD-D) ≤ H0 P.M.base R.e)
    (hh : h < cr13 R.HD) (hj : j < h) {g : Monomial} (hg : g ∈ canonicalIdealGenerators P.M.base R.e R.HD)
    (hgj : g.2.2 ≤ j) :
    (if (principalVector P.M.base R.e R.HD).2.2 ≤ j
      then min (cr31 R.HD-D) (principalVector P.M.base R.e R.HD).1 else cr31 R.HD-D) ≤ g.1 := by
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  let t := if (principalVector P.M.base R.e R.HD).2.2 ≤ j
      then min (cr31 R.HD-D) (principalVector P.M.base R.e R.HD).1 else cr31 R.HD-D
  change t ≤ g.1
  have htL : t ≤ cr31 R.HD-D := by dsimp [t]; split_ifs <;> omega
  have htP : (principalVector P.M.base R.e R.HD).2.2 ≤ j → t ≤ (principalVector P.M.base R.e R.HD).1 := by
    intro h; simp only [t,ite_eq_left h]; exact Nat.min_le_right _ _
  rcases hg with rfl | hc | hc
  · simpa only [Prod.fst] using htL.trans (by omega)
  · obtain ⟨n,i,v,d,hn,hpre,hd,heq,hcases,hg⟩ := hc
    have hb := schedule_extrema_bounds _ _ R.HD hmax hmin hn hpre hd heq hcases
    rcases hcases with hc | hc | hc
    · have hD := hb.1 hc.2.1
      have hv := hb.2 hc.2.2.2.1
      simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_left hc.2.2.2.1,Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
    · have hD := hb.1 hc.2.1
      simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_right (by omega : ¬v < cr13 R.HD),Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl | rfl <;> simp_all only [Prod.fst,Prod.snd] <;> omega
    · have hv := hb.2 hc.2.2.2.1
      simp only [colonMonomials,ite_eq_right (by omega : ¬i < cr12 R.HD),Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl | rfl <;> simp_all only [Prod.fst,Prod.snd] <;> omega
  · obtain ⟨delta,U,V,hdom,hdegree,hg⟩ := hc
    have hspec := principalVector_spec P.M.base R.e R.HD
    have heq : principalVector P.M.base R.e R.HD=(delta,U,V) :=
      canonical_monomial_unique _ _ _ hspec.1 hdom (hspec.2.trans hdegree)
    have htP' : V ≤ j → t ≤ delta := by simpa only [heq,Prod.fst,Prod.snd] using htP
    rcases hg with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at *
    · exact htP' hgj
    · have hV : V ≤ j := by omega
      have ht := htP' hV
      omega
    · omega

theorem opposite_generator_lower {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hU : 0 < (principalVector P.M.base R.e R.HD).2.1)
    {D h j : ℕ} (hmax : ∀ d ∈ leftDepths P.M.base R.e R.HD, d ≤ D)
    (hmin : ∀ j ∈ nearHeights P.M.base R.e R.HD, h ≤ j)
    (hfloor : cr21 R.HD+(cr31 R.HD-D) ≤ H0 P.M.base R.e)
    (hj : j < h) {g : Monomial} (hg : g ∈ canonicalIdealGenerators P.M.base R.e R.HD)
    (hgi : g.2.1=0) (hgj : g.2.2 ≤ cr23 R.HD+j) :
    cr21 R.HD+(if (principalVector P.M.base R.e R.HD).2.2 ≤ j
      then min (cr31 R.HD-D) (principalVector P.M.base R.e R.HD).1 else cr31 R.HD-D) ≤ g.1 := by
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  let t := if (principalVector P.M.base R.e R.HD).2.2 ≤ j
      then min (cr31 R.HD-D) (principalVector P.M.base R.e R.HD).1 else cr31 R.HD-D
  change cr21 R.HD+t ≤ g.1
  have htL : t ≤ cr31 R.HD-D := by dsimp [t]; split_ifs <;> omega
  by_cases hgj0 : g.2.2=0
  · have hcut := canonicalIdealGenerators_degree_mem_cut P.M.base R.e R.HD hg
    have heq : g=(g.1,0,0) := Prod.ext rfl (Prod.ext hgi hgj0)
    rw [heq] at hcut
    have hI := (actual_cyclicCut_iff_routingI _ _ _).mp hcut
    have hx := (normalizedGrid_mem_iff_eta_le P.M.base R.e g.1 0 0).mp hI
    change H0 P.M.base R.e ≤ g.1 at hx
    omega
  have htP : (principalVector P.M.base R.e R.HD).2.2 ≤ j → t ≤ (principalVector P.M.base R.e R.HD).1 := by
    intro h; simp only [t,ite_eq_left h]; exact Nat.min_le_right _ _
  rcases hg with rfl | hc | hc
  · simp only [Prod.fst]; omega
  · obtain ⟨n,i,v,d,hn,hpre,hd,heq,hcases,hg⟩ := hc
    have hb := schedule_extrema_bounds _ _ R.HD hmax hmin hn hpre hd heq hcases
    rcases hcases with hc | hc | hc
    · have hD := hb.1 hc.2.1
      have hv := hb.2 hc.2.2.2.1
      simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_left hc.2.2.2.1,Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
    · have hD := hb.1 hc.2.1
      simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_right (by omega : ¬v < cr13 R.HD),Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
    · have hv := hb.2 hc.2.2.2.1
      simp only [colonMonomials,ite_eq_right (by omega : ¬i < cr12 R.HD),Set.mem_ofPred_eq] at hg
      rcases hg with hzero | haxis | hpure
      · rw [hzero] at hgi
        simp only [Prod.fst,Prod.snd] at hgi
        omega
      · rw [haxis] at hgj
        simp only [Prod.fst,Prod.snd] at hgj
        omega
      · have hgz : g.2.2=0 := by rw [hpure]
        exact False.elim (hgj0 hgz)
  · obtain ⟨delta,U,V,hdom,hdegree,hg⟩ := hc
    have hspec := principalVector_spec P.M.base R.e R.HD
    have heq : principalVector P.M.base R.e R.HD=(delta,U,V) :=
      canonical_monomial_unique _ _ _ hspec.1 hdom (hspec.2.trans hdegree)
    rw [heq] at hU
    change 0 < U at hU
    have htP' : V ≤ j → t ≤ delta := by simpa only [heq,Prod.fst,Prod.snd] using htP
    rcases hg with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at *
    · omega
    · have ht := htP' (by omega)
      omega
    · omega

theorem left_axis_generators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {D : ℕ} (hD : D ∈ leftDepths B e HD) :
    (∃ i : ℕ, i ≤ c2 B e-1 ∧ (cr31 HD-D,i,0) ∈ canonicalIdealGenerators B e HD) ∧
    ∃ v : ℕ, v < cr23 HD ∧ (c1 B e-D,0,v) ∈ canonicalIdealGenerators B e HD := by
  classical
  obtain ⟨z,hz,hd⟩ := Finset.mem_image.mp hD
  obtain ⟨hz,hi⟩ := Finset.mem_filter.mp hz
  obtain ⟨n,hn,hpre,hdepth,heq,hcases⟩ := (mem_preSchedule _ _ _ _).mp hz
  have hs := coherent_coefficients B e HD
  have hp := coherent_coefficients_positive B e HD
  have hgen : ∀ g ∈ colonMonomials B e HD z.2.1 z.2.2 z.1, g ∈ canonicalIdealGenerators B e HD :=
    fun g hg => Or.inr (Or.inl ⟨n,z.2.1,z.2.2,z.1,hn,hpre,hdepth,heq,hcases,hg⟩)
  rcases hcases with hc | hc | hc
  · refine ⟨⟨z.2.1+cr32 HD,by omega,hgen _ ?_⟩,0,hp.2.2.2.1,hgen _ ?_⟩
    all_goals rw [←hd]; simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_left hc.2.2.2.1,Set.mem_ofPred_eq]; tauto
  · refine ⟨⟨z.2.1+cr32 HD,by omega,hgen _ ?_⟩,z.2.2-cr13 HD,by omega,hgen _ ?_⟩
    all_goals rw [←hd]; simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_right (by omega : ¬z.2.2 < cr13 HD),Set.mem_ofPred_eq]; tauto
  · omega

theorem near_axis_generator (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {h : ℕ} (hh : h ∈ nearHeights B e HD) :
    ∃ r : ℕ, r < cr21 HD ∧ (r,0,h+cr23 HD) ∈ canonicalIdealGenerators B e HD := by
  classical
  obtain ⟨z,hz,heqh⟩ := Finset.mem_image.mp hh
  obtain ⟨hz,hnear⟩ := Finset.mem_filter.mp hz
  obtain ⟨n,hn,hpre,hdepth,heq,hcases⟩ := (mem_preSchedule _ _ _ _).mp hz
  have hgen : ∀ g ∈ colonMonomials B e HD z.2.1 z.2.2 z.1, g ∈ canonicalIdealGenerators B e HD :=
    fun g hg => Or.inr (Or.inl ⟨n,z.2.1,z.2.2,z.1,hn,hpre,hdepth,heq,hcases,hg⟩)
  rcases hcases with hc | hc | hc
  · refine ⟨cr21 HD-z.1,by omega,hgen _ ?_⟩
    rw [←heqh]
    simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_left hc.2.2.2.1,Set.mem_ofPred_eq]
    tauto
  · omega
  · refine ⟨cr21 HD-z.1,by omega,hgen _ ?_⟩
    rw [←heqh]
    simp only [colonMonomials,ite_eq_right (by omega : ¬z.2.1 < cr12 HD),Set.mem_ofPred_eq]
    tauto


theorem schedule_c_axis (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
 (HD : CoherentHerzogData B e) {z : Monomial} (hz : z ∈ preSchedule B e HD)
 (hj : z.2.2 < cr13 HD) :
 (cr21 HD-z.1,0,z.2.2+cr23 HD) ∈ canonicalIdealGenerators B e HD := by
 obtain ⟨n,hn,hpre,hd,heq,hcases⟩ := (mem_preSchedule _ _ _ _).mp hz
 refine Or.inr (Or.inl ⟨n,z.2.1,z.2.2,z.1,hn,hpre,hd,heq,hcases,?_⟩)
 by_cases hi : z.2.1 < cr12 HD <;> simp [colonMonomials,hi,hj]

theorem all_pre_j_gt_V {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1)
 {z : Monomial} (hz : z ∈ preSchedule P.M.base R.e R.HD) :
 (principalVector P.M.base R.e R.HD).2.2 < z.2.2 := by
 have hV := (actual_boundary_principal_cases R hm hn hiota heps).2.1
 have hPB := pb_minimal _ _ R.HD heps
 obtain ⟨n,_,_,hd,_,hc⟩ := (mem_preSchedule _ _ _ _).mp hz
 by_cases hj : z.2.2 < cr13 R.HD
 · have hdk : z.1 < cr21 R.HD := by rcases hc with hc | hc | hc <;> omega
   by_contra h
   have hg := schedule_c_axis _ _ R.HD hz hj
   have heq := hPB.2 (cr21 R.HD-z.1,0,z.2.2+cr23 R.HD)
     ⟨_,Or.inl hg,le_rfl,le_rfl,le_rfl⟩
     (by simp only [principalPB,Prod.fst]; omega) (by simp [principalPB])
     (by simp only [principalPB,Prod.fst,Prod.snd]; omega)
   have hx := congrArg Prod.fst heq
   simp only [principalPB,Prod.fst,Prod.snd] at hx
   omega
 · omega

theorem t10a_right_seam_excluded {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1)
 (hdelta : (principalVector P.M.base R.e R.HD).1=0)
 {z : Monomial} (hz : z ∈ preSchedule P.M.base R.e R.HD) :
 z.2.1 ≠ cr12 R.HD := by
 classical
 intro hi
 obtain ⟨n,hpos,hpre,hdepth,heq,hcases⟩ := (mem_preSchedule _ _ _ _).mp hz
 have hp := coherent_coefficients_positive P.M.base R.e R.HD
 have hs := coherent_coefficients P.M.base R.e R.HD
 have hcoef := (coherent_normalized_relations P.M.base R.e R.HD).1
 have hj : 0 < z.2.2 ∧ z.2.2 < cr13 R.HD ∧ z.1 < cr21 R.HD := by
   rcases hcases with hc | hc | hc <;> omega
 have hVj := all_pre_j_gt_V R hm hn hiota heps hz
 have horigin := pb_origin_strict _ _ R.HD heps
 have hcutgen : (c1 P.M.base R.e-z.1,0,0) ∈ canonicalIdealGenerators P.M.base R.e R.HD := by
   refine Or.inr (Or.inl ⟨n,z.2.1,z.2.2,z.1,hpos,hpre,hdepth,heq,hcases,?_⟩)
   simp only [colonMonomials,ite_eq_right (by omega : ¬z.2.1 < cr12 R.HD),Set.mem_ofPred_eq]
   right; right
   simp [hi]
 have hcut := canonicalIdealGenerators_degree_mem_cut _ _ R.HD hcutgen
 have hx := (normalizedGrid_mem_iff_eta_le _ _ _ 0 0).mp ((actual_cyclicCut_iff_routingI _ _ _).mp hcut)
 change H0 P.M.base R.e ≤ c1 P.M.base R.e-z.1 at hx
 have hdl : z.1 < cr31 R.HD := by omega
 let q0 := firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e) (routingM_pos P.M.base R.e)
 let nf := q0-n
 let jf := cr13 R.HD+(principalVector P.M.base R.e R.HD).2.2-z.2.2
 have hnf : 0 < nf ∧ nf < q0 := by dsimp [nf,q0]; omega
 have hjf : 0 < jf ∧ jf < cr13 R.HD := by dsimp [jf]; omega
 have hdom : HerzogLShapeDomain R.HD (principalVector P.M.base R.e R.HD).2.1 jf :=
   ⟨(principalVector_spec _ _ _).1.1,by omega,Or.inr hjf.2⟩
 have heqf : nf*routingM P.M.base R.e+(c1 P.M.base R.e-z.1)*routingA P.M.base R.e=
     (principalVector P.M.base R.e R.HD).2.1*routingB P.M.base R.e+jf*routingC P.M.base R.e := by
   have hprincipal := (principalVector_spec P.M.base R.e R.HD).2
   simp only [monomialDegree,normalizedGrid,hdelta,zero_mul,zero_add] at hprincipal
   have hns : nf+n=q0 := by dsimp [nf]; omega
   have hds : c1 P.M.base R.e-z.1+z.1=c1 P.M.base R.e := by omega
   have hjs : jf+z.2.2=cr13 R.HD+(principalVector P.M.base R.e R.HD).2.2 := by dsimp [jf]; omega
   have hnsm := congrArg (fun x => x*routingM P.M.base R.e) hns
   have hdsa := congrArg (fun x => x*routingA P.M.base R.e) hds
   have hjsc := congrArg (fun x => x*routingC P.M.base R.e) hjs
   rw [hi] at heq
   simp only [Nat.add_mul] at hnsm hdsa hjsc
   dsimp [q0] at hnsm
   nlinarith only [hnsm,hdsa,hjsc,hcoef,heq,hprincipal]
 obtain ⟨i',j',d',hdom',hd',heq',hc'⟩ := actual_mixed_notch_preprincipal R hm hn hnf.1 hnf.2
 have hu := preSchedule_coordinate_unique _ _ R.HD hdom hdom' heqf heq'
 have hdk : d' < cr21 R.HD := by rcases hc' with hc | hc | hc <;> omega
 omega

theorem t10a_origin_left {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1)
 (hdelta : (principalVector P.M.base R.e R.HD).1=0) :
 ∃ n i j d : ℕ, 0 < n ∧
 n < firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e) (routingM_pos P.M.base R.e) ∧
 (d,i,j) ∈ preSchedule P.M.base R.e R.HD ∧ i < cr12 R.HD ∧
 n*routingM P.M.base R.e+d*routingA P.M.base R.e=i*routingB P.M.base R.e+j*routingC P.M.base R.e ∧
 rawCandidate P.M.base R.e n 0 ≤ (H0 P.M.base R.e : ℤ) := by
 have hU := (actual_boundary_principal_cases R hm hn hiota heps).1
 obtain ⟨n,hpos,hpre,hraw⟩ := actual_origin_return_of_principal_b_pos R hm hn hU
 obtain ⟨i,j,d,hdom,hd,heq,hcases⟩ := actual_mixed_notch_preprincipal R hm hn hpos hpre
 have hmem : (d,i,j) ∈ preSchedule P.M.base R.e R.HD :=
   (mem_preSchedule _ _ _ _).mpr ⟨n,hpos,hpre,hd,heq,hcases⟩
 have hleft : i < cr12 R.HD := by
   by_contra h
   have hne := t10a_right_seam_excluded R hm hn hiota heps hdelta hmem
   have hi : cr12 R.HD < i := by change i ≠ cr12 R.HD at hne; omega
   have hdk : d < cr21 R.HD := by rcases hcases with hc | hc | hc <;> omega
   have hposij : 0 < i ∧ 0 < j := by
     have hp := coherent_coefficients_positive P.M.base R.e R.HD
     rcases hcases with hc | hc | hc <;> omega
   have hcarry := (preprincipal_origin_carry_bounds _ _ R.HD n i j d hposij.1 hposij.2 heq).2.1 hi
   have hG0 := (normalized_mixed_notch_G0_G4 R hm hn).1
   have hdkZ : (d : ℤ) < cr21 R.HD := by exact_mod_cast hdk
   have hgZ : (H0 P.M.base R.e : ℤ) < c1 P.M.base R.e := by exact_mod_cast hG0
   omega
 exact ⟨n,i,j,d,hpos,hpre,hmem,hleft,heq,hraw⟩

theorem t10a_left_max {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1)
 (hdelta : (principalVector P.M.base R.e R.HD).1=0) :
 ∃ D : ℕ, D ∈ leftDepths P.M.base R.e R.HD ∧ 0 < D ∧ D < cr31 R.HD ∧
 (∀ d ∈ leftDepths P.M.base R.e R.HD, d ≤ D) ∧
 cr21 R.HD+(cr31 R.HD-D) ≤ H0 P.M.base R.e := by
 classical
 obtain ⟨n,i,j,d,hpos,hpre,hmem,hleft,heq,hraw⟩ := t10a_origin_left R hm hn hiota heps hdelta
 have hdmem : d ∈ leftDepths P.M.base R.e R.HD :=
   Finset.mem_image.mpr ⟨(d,i,j),Finset.mem_filter.mpr ⟨hmem,hleft⟩,rfl⟩
 have hne : (leftDepths P.M.base R.e R.HD).Nonempty := ⟨d,hdmem⟩
 let D := (leftDepths P.M.base R.e R.HD).max' hne
 have hDmem : D ∈ leftDepths P.M.base R.e R.HD := Finset.max'_mem _ _
 have hb := leftDepths_bounds _ _ R.HD hDmem
 have hmax : ∀ d ∈ leftDepths P.M.base R.e R.HD, d ≤ D := fun d hd => Finset.le_max' _ d hd
 refine ⟨D,hDmem,hb.1,hb.2,hmax,?_⟩
 obtain ⟨_,_,_,_,_,hcases⟩ := (mem_preSchedule _ _ _ _).mp hmem
 simp only [Prod.fst,Prod.snd] at hcases
 have hp := coherent_coefficients_positive P.M.base R.e R.HD
 have hposij : 0 < i ∧ 0 < j := by rcases hcases with hc | hc | hc <;> omega
 have hcarry := (preprincipal_origin_carry_bounds _ _ R.HD n i j d hposij.1 hposij.2 heq).1
 have hs := coherent_coefficients P.M.base R.e R.HD
 have hsZ : (c1 P.M.base R.e : ℤ)=cr21 R.HD+cr31 R.HD := by exact_mod_cast hs.1
 have hmaxZ : (d : ℤ) ≤ D := by exact_mod_cast hmax d hdmem
 have hsubZ : (cr31 R.HD-D : ℕ)+(D : ℤ)=cr31 R.HD := by exact_mod_cast (show cr31 R.HD-D+D=cr31 R.HD by omega)
 exact_mod_cast (show (cr21 R.HD : ℤ)+(cr31 R.HD-D : ℕ) ≤ H0 P.M.base R.e by omega)

theorem t10a_boundary_triple {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1)
 (hdelta : (principalVector P.M.base R.e R.HD).1=0)
 (hVpos : 0 < (principalVector P.M.base R.e R.HD).2.2) :
 ∃ L : ℕ, 0 < L ∧
 rightHeight P.M.base R.e ((principalVector P.M.base R.e R.HD).2.2-1)=L ∧
 rightHeight P.M.base R.e (principalVector P.M.base R.e R.HD).2.2=0 ∧
 oppositeHeight P.M.base R.e R.HD ((principalVector P.M.base R.e R.HD).2.2-1)=cr21 R.HD+L := by
 classical
 have hc := actual_boundary_principal_cases R hm hn hiota heps
 have hU := hc.1
 have hVlt := hc.2.1
 have hs := coherent_coefficients P.M.base R.e R.HD
 obtain ⟨D,hD,hDpos,hDlt,hmax,hfloor⟩ := t10a_left_max R hm hn hiota heps hdelta
 let L := cr31 R.HD-D
 let V := (principalVector P.M.base R.e R.HD).2.2
 have hLpos : 0 < L := by dsimp [L]; omega
 have hmin : ∀ j ∈ nearHeights P.M.base R.e R.HD, V ≤ j := by
   intro j hj
   obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hj
   exact Nat.le_of_lt (all_pre_j_gt_V R hm hn hiota heps (Finset.mem_filter.mp hz).1)
 obtain ⟨⟨i,hi,hrightgen⟩,v,hv,hopgen⟩ := left_axis_generators _ _ R.HD hD
 have hsum : c1 P.M.base R.e-D=cr21 R.HD+L := by dsimp [L]; omega
 have hdom := right_boundary_domain P.M.base R.e R.HD (j:=V-1) (by dsimp [V]; omega)
 have hupper : rightHeight P.M.base R.e (V-1) ≤ L := by
   apply (chart_threshold_iff R hm hn L _ _ hdom).mp
   exact ⟨(L,i,0),Or.inl hrightgen,le_rfl,hi,Nat.zero_le _⟩
 have hright : rightHeight P.M.base R.e (V-1)=L := by
   have hx := (chart_threshold_iff R hm hn (rightHeight P.M.base R.e (V-1)) _ _ hdom).mpr le_rfl
   obtain ⟨g,hg,hgr,hgi,hgj⟩ := (chart_on_domain_iff _ _ _ _ hdom).mp hx
   have hlo := right_generator_lower R hmax hmin hfloor hVlt (show V-1<V by dsimp [V]; omega) hg hgj
   rw [ite_eq_right (by dsimp [V]; omega)] at hlo
   exact Nat.le_antisymm hupper (hlo.trans hgr)
 have hzero : rightHeight P.M.base R.e V=0 := by
   have hPV := (principalVector_spec P.M.base R.e R.HD).1
   have hUbound := hPV.1
   have hmem : (0,c2 P.M.base R.e-1,V) ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) :=
     ⟨_,Or.inl (principal_generators _ _ R.HD).1,by simp only [Prod.fst]; omega,
       by simp only [Prod.fst,Prod.snd]; omega,le_rfl⟩
   have ht := (chart_threshold_iff R hm hn _ _ _ (right_boundary_domain _ _ R.HD hVlt)).mp hmem
   change rightHeight P.M.base R.e V ≤ 0 at ht
   omega
 have hdomO := opposite_boundary_domain P.M.base R.e R.HD (j:=V-1) (by dsimp [V]; omega)
 have hopupper : oppositeHeight P.M.base R.e R.HD (V-1) ≤ cr21 R.HD+L := by
   apply (chart_threshold_iff R hm hn _ _ _ hdomO).mp
   refine ⟨(c1 P.M.base R.e-D,0,v),Or.inl hopgen,?_,le_rfl,?_⟩
   · simp only [Prod.fst]; omega
   · simp only [Prod.fst,Prod.snd]; omega
 have hop : oppositeHeight P.M.base R.e R.HD (V-1)=cr21 R.HD+L := by
   have hx := (chart_threshold_iff R hm hn (oppositeHeight P.M.base R.e R.HD (V-1)) _ _ hdomO).mpr le_rfl
   obtain ⟨g,hg,hgr,hgi,hgj⟩ := (chart_on_domain_iff _ _ _ _ hdomO).mp hx
   simp only [Prod.fst,Prod.snd] at hgr hgi hgj
   have hlo := opposite_generator_lower R hU hmax hmin hfloor (show V-1<V by dsimp [V]; omega) hg (by omega) hgj
   rw [ite_eq_right (by dsimp [V]; omega)] at hlo
   exact Nat.le_antisymm hopupper (hlo.trans hgr)
 exact ⟨L,hLpos,hright,hzero,hop⟩

theorem pb_left_strict (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
 (HD : CoherentHerzogData B e) (heps : PB_epsilon B e HD=1)
 (hV0 : (principalVector B e HD).2.2=0) {z : Monomial}
 (hz : z ∈ preSchedule B e HD) (hi : z.2.1 < cr12 HD) :
 (principalVector B e HD).1+cr21 HD < c1 B e-z.1 := by
 classical
 have hmem : z.1 ∈ leftDepths B e HD :=
   Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,hi⟩,rfl⟩
 obtain ⟨_,v,hv,hgen⟩ := left_axis_generators B e HD hmem
 have hPB := pb_minimal B e HD heps
 by_contra h
 have heq := hPB.2 (c1 B e-z.1,0,v)
   ⟨_,Or.inl hgen,le_rfl,le_rfl,le_rfl⟩
   (by simp only [principalPB,Prod.fst]; omega) (by simp [principalPB])
   (by simp only [principalPB,Prod.fst,Prod.snd]; omega)
 have hvEq := congrArg (fun g : Monomial => g.2.2) heq
 simp only [principalPB,Prod.fst,Prod.snd] at hvEq
 omega

theorem t10b_right_lower {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (heps : PB_epsilon P.M.base R.e R.HD=1)
 (hV0 : (principalVector P.M.base R.e R.HD).2.2=0)
 {h j : ℕ} (hmin : ∀ v ∈ nearHeights P.M.base R.e R.HD, h ≤ v)
 (hh : h < cr13 R.HD)
 (hj : j < h) {g : Monomial} (hg : g ∈ canonicalIdealGenerators P.M.base R.e R.HD)
 (hgj : g.2.2 ≤ j) : (principalVector P.M.base R.e R.HD).1 ≤ g.1 := by
 classical
 have hp := coherent_coefficients_positive P.M.base R.e R.HD
 have hs := coherent_coefficients P.M.base R.e R.HD
 have hH := pb_origin_strict _ _ R.HD heps
 have hG0 := (normalized_mixed_notch_G0_G4 R hm hn).1
 have hδl : (principalVector P.M.base R.e R.HD).1 < cr31 R.HD := by omega
 rcases hg with rfl | hc | hc
 · simp only [Prod.fst]; omega
 · obtain ⟨n,i,v,d,hpos,hpre,hd,heq,hcases,hgen⟩ := hc
   have hmem : (d,i,v) ∈ preSchedule P.M.base R.e R.HD :=
     (mem_preSchedule _ _ _ _).mpr ⟨n,hpos,hpre,hd,heq,hcases⟩
   have hnear : v < cr13 R.HD → h ≤ v := by
     intro hv
     exact hmin v (Finset.mem_image.mpr ⟨(d,i,v),Finset.mem_filter.mpr ⟨hmem,hv⟩,rfl⟩)
   rcases hcases with hc | hc | hc
   · have hstrict := pb_left_strict _ _ R.HD heps hV0 hmem hc.2.1
     have hv := hnear hc.2.2.2.1
     simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_left hc.2.2.2.1,Set.mem_ofPred_eq] at hgen
     rcases hgen with rfl | rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
   · have hstrict := pb_left_strict _ _ R.HD heps hV0 hmem hc.2.1
     simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_right (by omega : ¬v < cr13 R.HD),Set.mem_ofPred_eq] at hgen
     rcases hgen with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
   · have hv := hnear hc.2.2.2.1
     simp only [colonMonomials,ite_eq_right (by omega : ¬i < cr12 R.HD),Set.mem_ofPred_eq] at hgen
     rcases hgen with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
 · obtain ⟨delta,U,V,hdom,hdegree,hgen⟩ := hc
   have hspec := principalVector_spec P.M.base R.e R.HD
   have heq : principalVector P.M.base R.e R.HD=(delta,U,V) :=
     canonical_monomial_unique _ _ _ hspec.1 hdom (hspec.2.trans hdegree)
   rw [heq]
   rcases hgen with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] <;> omega

theorem t10b_opposite_lower {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hU : 0 < (principalVector P.M.base R.e R.HD).2.1)
 (heps : PB_epsilon P.M.base R.e R.HD=1)
 (hV0 : (principalVector P.M.base R.e R.HD).2.2=0)
 {h j : ℕ} (hmin : ∀ v ∈ nearHeights P.M.base R.e R.HD, h ≤ v)
 (hj : j < h) {g : Monomial} (hg : g ∈ canonicalIdealGenerators P.M.base R.e R.HD)
 (hgi : g.2.1=0) (hgj : g.2.2 ≤ cr23 R.HD+j) :
 cr21 R.HD+(principalVector P.M.base R.e R.HD).1 ≤ g.1 := by
 classical
 have hp := coherent_coefficients_positive P.M.base R.e R.HD
 have hH := pb_origin_strict _ _ R.HD heps
 by_cases hz : g.2.2=0
 · have hcut := canonicalIdealGenerators_degree_mem_cut _ _ R.HD hg
   have heq : g=(g.1,0,0) := Prod.ext rfl (Prod.ext hgi hz)
   rw [heq] at hcut
   have hx := (normalizedGrid_mem_iff_eta_le _ _ _ 0 0).mp ((actual_cyclicCut_iff_routingI _ _ _).mp hcut)
   change H0 P.M.base R.e ≤ g.1 at hx
   omega
 rcases hg with rfl | hc | hc
 · simp only [Prod.fst]; omega
 · obtain ⟨n,i,v,d,hpos,hpre,hd,heq,hcases,hgen⟩ := hc
   have hmem : (d,i,v) ∈ preSchedule P.M.base R.e R.HD :=
     (mem_preSchedule _ _ _ _).mpr ⟨n,hpos,hpre,hd,heq,hcases⟩
   have hnear : v < cr13 R.HD → h ≤ v := by
     intro hv
     exact hmin v (Finset.mem_image.mpr ⟨(d,i,v),Finset.mem_filter.mpr ⟨hmem,hv⟩,rfl⟩)
   rcases hcases with hc | hc | hc
   · have hstrict := pb_left_strict _ _ R.HD heps hV0 hmem hc.2.1
     have hv := hnear hc.2.2.2.1
     simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_left hc.2.2.2.1,Set.mem_ofPred_eq] at hgen
     rcases hgen with rfl | rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
   · have hstrict := pb_left_strict _ _ R.HD heps hV0 hmem hc.2.1
     simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_right (by omega : ¬v < cr13 R.HD),Set.mem_ofPred_eq] at hgen
     rcases hgen with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
   · have hv := hnear hc.2.2.2.1
     simp only [colonMonomials,ite_eq_right (by omega : ¬i < cr12 R.HD),Set.mem_ofPred_eq] at hgen
     rcases hgen with hzero | haxis | hpure
     · rw [hzero] at hgi
       simp only [Prod.fst,Prod.snd] at hgi
       have hpp : 0 < cr12 R.HD := hp.1
       omega
     · rw [haxis] at hgj
       simp only [Prod.fst,Prod.snd] at hgj
       omega
     · have hgz : g.2.2=0 := by rw [hpure]
       exact False.elim (hz hgz)
 · obtain ⟨delta,U,V,hdom,hdegree,hgen⟩ := hc
   have hspec := principalVector_spec P.M.base R.e R.HD
   have heq : principalVector P.M.base R.e R.HD=(delta,U,V) :=
     canonical_monomial_unique _ _ _ hspec.1 hdom (hspec.2.trans hdegree)
   rw [heq] at hU ⊢
   change 0 < U at hU
   rcases hgen with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega

theorem t10b_boundary_envelope {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1)
 (hV0 : (principalVector P.M.base R.e R.HD).2.2=0)
 (hdelta : 0 < (principalVector P.M.base R.e R.HD).1) :
 ∃ h : ℕ, 0 < h ∧ h < cr13 R.HD ∧ rightHeight P.M.base R.e h=0 ∧
 (∀ j : ℕ, j < h → rightHeight P.M.base R.e j=(principalVector P.M.base R.e R.HD).1) ∧
 (∀ j : ℕ, j < h → oppositeHeight P.M.base R.e R.HD j=cr21 R.HD+(principalVector P.M.base R.e R.HD).1) := by
 have hU := (actual_boundary_principal_cases R hm hn hiota heps).1
 obtain ⟨h,hpos,hlt,hzero,hmem,hmin⟩ := actual_first_zero_of_delta_pos R hm hn hdelta
 have hPV := (principalVector_spec P.M.base R.e R.HD).1
 have hUbound := hPV.1
 have hgens := principal_generators P.M.base R.e R.HD
 refine ⟨h,hpos,hlt,hzero,?_,?_⟩
 · intro j hj
   have hdom := right_boundary_domain _ _ R.HD (j:=j) (by omega)
   have hupper := (chart_threshold_iff R hm hn (principalVector P.M.base R.e R.HD).1 _ _ hdom).mp
     ⟨_,Or.inl hgens.1,le_rfl,by simp only [Prod.fst,Prod.snd]; omega,by simp only [Prod.fst,Prod.snd]; omega⟩
   have hx := (chart_threshold_iff R hm hn (rightHeight P.M.base R.e j) _ _ hdom).mpr le_rfl
   obtain ⟨g,hg,hgr,hgi,hgj⟩ := (chart_on_domain_iff _ _ _ _ hdom).mp hx
   have hlo := t10b_right_lower R hm hn heps hV0 hmin hlt hj hg hgj
   exact Nat.le_antisymm hupper (hlo.trans hgr)
 · intro j hj
   have hdom := opposite_boundary_domain _ _ R.HD (j:=j) (by omega)
   have hupper := (chart_threshold_iff R hm hn (cr21 R.HD+(principalVector P.M.base R.e R.HD).1) _ _ hdom).mp
     ⟨_,Or.inl hgens.2,by simp only [principalPB,Prod.fst]; omega,le_rfl,
       by simp only [principalPB,Prod.fst,Prod.snd]; omega⟩
   have hx := (chart_threshold_iff R hm hn (oppositeHeight P.M.base R.e R.HD j) _ _ hdom).mpr le_rfl
   obtain ⟨g,hg,hgr,hgi,hgj⟩ := (chart_on_domain_iff _ _ _ _ hdom).mp hx
   simp only [Prod.fst,Prod.snd] at hgr hgi hgj
   have hlo := t10b_opposite_lower R hU heps hV0 hmin hj hg (by omega) hgj
   exact Nat.le_antisymm hupper (hlo.trans hgr)

theorem actual_boundary_principal_tight_witness {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1) :
 Nonempty (TightRightIndex P.M.base R.e R.HD) := by
 have hc := actual_boundary_principal_cases R hm hn hiota heps
 rcases hc.2.2 with ⟨hδ,hV⟩ | ⟨hV,hδ⟩
 · obtain ⟨L,hL,hr,hzero,hop⟩ := t10a_boundary_triple R hm hn hiota heps hδ hV
   let V := (principalVector P.M.base R.e R.HD).2.2
   have hstep : V-1+1=V := by dsimp [V]; omega
   refine ⟨⟨V-1,?_⟩⟩
   rw [hstep]
   exact ⟨hc.2.1,by dsimp [V]; omega,by dsimp [V]; omega,by dsimp [V]; omega⟩
 · obtain ⟨h,hpos,hlt,hzero,hr,hop⟩ := t10b_boundary_envelope R hm hn hiota heps hV hδ
   have hstep : h-1+1=h := by omega
   have hj : h-1<h := by omega
   have hright := hr _ hj
   have hopp := hop _ hj
   refine ⟨⟨h-1,?_⟩⟩
   rw [hstep]
   exact ⟨hlt,by omega,by omega,by omega⟩

theorem actual_boundary_principal_tight_count {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1) :
 1 ≤ Nat.card (TightRightIndex P.M.base R.e R.HD) := by
 letI := tight_right_indices_finite P.M.base R.e R.HD
 obtain ⟨w⟩ := actual_boundary_principal_tight_witness R hm hn hiota heps
 have hinj : Function.Injective (fun _ : Fin 1 => w) := by
   intro x y _; exact Subsingleton.elim x y
 have hc := Nat.card_le_card_of_injective _ hinj
 simpa only [Nat.card_fin] using hc

theorem actual_boundary_principal_type_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1) :
 Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
 have hc := actual_correction_count R hm hn
 have ht := actual_boundary_principal_tight_count R hm hn hiota heps
 have hs := L5A2C4OR24.actual_T5_T6_socle_source_bound R hm hn
 omega

theorem actual_indicator_correction_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
 principal_iota P.M.base R.e R.HD+PB_epsilon P.M.base R.e R.HD ≤
 Nat.card (TightRightIndex P.M.base R.e R.HD) := by
 rcases principal_iota_zero_or_one P.M.base R.e R.HD with hi | hi
 · rcases PB_epsilon_zero_or_one P.M.base R.e R.HD with he | he
   · omega
   · have h := actual_boundary_principal_tight_count R hm hn hi he; omega
 · exact actual_interior_principal_tight_count R hm hn hi

theorem actual_mixed_notch_type_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
 Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
 have hc := actual_correction_count R hm hn
 have ht := actual_indicator_correction_bound R hm hn
 have hs := L5A2C4OR24.actual_T5_T6_socle_source_bound R hm hn
 omega

theorem actual_type_source_accounting_identity (P : L5A1.P2Data Gamma) (e : Fin 3 ≃ Fin 3) :
 letI : NeZero (routingA P.M.base e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
 let D := routingData P.M.base e
 Gamma.asRelativeIdeal.idealType+L5A2C4N.E P.M.base e+L5A2C4M.ResidueData.U D=
 P.sourceCount+L5A2C4M.ResidueData.Cbr D := by
 letI : NeZero (routingA P.M.base e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base e)⟩
 let D := routingData P.M.base e
 obtain ⟨ha,hsource,hsink,hout,hin⟩ := exists_actualRoutingCore P e
 obtain ⟨ha',hactual,_⟩ := exists_actualRouting_with_exact_actualSinkCount P e
 have hfull := fullSinkCount_eq_actual_add_fake (routingI P.M.base e)
   (routingA P.M.base e) (routingB P.M.base e) (routingC P.M.base e)
   (routingHB P.M.base e) (routingHC P.M.base e)
 change D.sinkCount=actualSinkCount (routingI P.M.base e) (routingA P.M.base e)
   (routingB P.M.base e) (routingC P.M.base e) (routingHB P.M.base e) (routingHC P.M.base e)+
   L5A2C4N.E P.M.base e at hfull
 rw [hactual] at hfull
 have hdecomp := L5A2C4J.actual_raw_decomposition P.M.base e
 change D.branchCount=L5A2C4J.ResidueData.pairedZeroDiamondCount D+L5A2C4M.ResidueData.Cbr D ∧
   D.mergeCount=L5A2C4J.ResidueData.pairedZeroDiamondCount D+L5A2C4M.ResidueData.U D at hdecomp
 dsimp [D] at hfull hdecomp ⊢
 omega

theorem actual_cm_global_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
 letI : NeZero (routingA P.M.base R.e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base R.e)⟩
 let D := routingData P.M.base R.e
 L5A2C4M.ResidueData.Cbr D ≤ L5A2C4M.ResidueData.U D+L5A2C4N.E P.M.base R.e := by
 letI : NeZero (routingA P.M.base R.e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base R.e)⟩
 have ht := actual_mixed_notch_type_bound R hm hn
 have hc := actual_type_source_accounting_identity P R.e
 omega

theorem actual_cm_residual_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
 letI : NeZero (routingA P.M.base R.e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base R.e)⟩
 let D := routingData P.M.base R.e
 L5A2C4M.ResidueData.Nb D ≤ L5A2C4M.ResidueData.UexB D+L5A2C4N.E P.M.base R.e := by
 letI : NeZero (routingA P.M.base R.e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base R.e)⟩
 exact (L5A2C4M.ResidueData.residual_inequality_iff (routingData P.M.base R.e)
   (L5A2C4N.E P.M.base R.e)).2 (actual_cm_global_bound R hm hn)

theorem actual_cm_residual_injection {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
 letI : NeZero (routingA P.M.base R.e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base R.e)⟩
 let D := routingData P.M.base R.e
 ∃ f : L5A2C4I.ResidueData.BExceptionalBranches D → L5A2C4N.ActualResidualResourceSeats P.M.base R.e,
 Function.Injective f := by
 exact L5A2C4O.actual_exists_injective_discharge_of_global_bound P.M.base R.e (actual_cm_global_bound R hm hn)

theorem actual_cm_closes_through_c4n {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
 letI : NeZero (routingA P.M.base R.e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base R.e)⟩
 let D := routingData P.M.base R.e
 L5A2C4M.ResidueData.Cbr D ≤ L5A2C4M.ResidueData.U D+L5A2C4N.E P.M.base R.e := by
 letI : NeZero (routingA P.M.base R.e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base R.e)⟩
 obtain ⟨f,hf⟩ := actual_cm_residual_injection R hm hn
 exact L5A2C4N.actual_injective_discharge_closes P.M.base R.e f hf

theorem actual_boundary_q_gt_one {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
 (hiota : principal_iota P.M.base R.e R.HD=0)
 (heps : PB_epsilon P.M.base R.e R.HD=1) : 1 < cr13 R.HD := by
 obtain ⟨j⟩ := actual_boundary_principal_tight_witness R hm hn hiota heps
 have h := j.property.1
 omega

theorem actual_cm_branch_merge_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
 (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
 (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
 letI : NeZero (routingA P.M.base R.e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base R.e)⟩
 let D := routingData P.M.base R.e
 D.branchCount ≤ D.mergeCount+L5A2C4N.E P.M.base R.e := by
 letI : NeZero (routingA P.M.base R.e) := ⟨Nat.ne_of_gt (routingA_pos P.M.base R.e)⟩
 have h := actual_cm_global_bound R hm hn
 have hdecomp := L5A2C4J.actual_raw_decomposition P.M.base R.e
 change (routingData P.M.base R.e).branchCount=L5A2C4J.ResidueData.pairedZeroDiamondCount (routingData P.M.base R.e)+L5A2C4M.ResidueData.Cbr (routingData P.M.base R.e) ∧
   (routingData P.M.base R.e).mergeCount=L5A2C4J.ResidueData.pairedZeroDiamondCount (routingData P.M.base R.e)+L5A2C4M.ResidueData.U (routingData P.M.base R.e) at hdecomp
 omega

end NS25Lean.L5A2C4OR27



