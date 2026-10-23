import NS25Lean.P2SectorCT7NonactualSocleR25

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.L5A2C4OR26
open L2B FourGeneratedBridge L5A2C4A L5A2C4C L5A2C4D L5A2C4H
  L5A2C4OR1 L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 L5A2C4OR25
variable {Gamma : NumericalSemigroup}

/-- Actual return coordinates (depth,i,j), with no envelope or counting field. -/
def preSchedule (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Finset Monomial := by
  classical
  exact ((Finset.range (c1 B e)).product
    ((Finset.range (c2 B e)).product (Finset.range (c3 B e)))).filter
      (fun z => ∃ n : ℕ, 0 < n ∧
        n < firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) ∧
        0 < z.1 ∧ n*routingM B e+z.1*routingA B e=
          z.2.1*routingB B e+z.2.2*routingC B e ∧ PreprincipalCases B e HD z.2.1 z.2.2 z.1)

theorem mem_preSchedule (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) :
    z ∈ preSchedule B e HD ↔ ∃ n : ℕ, 0 < n ∧
      n < firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) ∧
      0 < z.1 ∧ n*routingM B e+z.1*routingA B e=
        z.2.1*routingB B e+z.2.2*routingC B e ∧ PreprincipalCases B e HD z.2.1 z.2.2 z.1 := by
  classical
  have hp := coherent_coefficients_positive B e HD
  have hs := coherent_coefficients B e HD
  rcases z with ⟨d,i,j⟩
  simp only [preSchedule,Finset.mem_filter,Finset.mem_product,Finset.mem_range]
  constructor
  · exact And.right
  · intro hz
    obtain ⟨n,hn,hpre,hd,heq,hcases⟩ := hz
    refine ⟨?_,n,hn,hpre,hd,heq,hcases⟩
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr ?_,Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,Finset.mem_range.mpr ?_⟩⟩
    all_goals rcases hcases with hc | hc | hc <;> simp only [Prod.fst,Prod.snd] at * <;> omega

theorem actual_preSchedule_coordinate {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    {n : ℕ} (hpos : 0 < n)
    (hpre : n < firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e) (routingM_pos P.M.base R.e)) :
    ∃ i j d : ℕ, (d,i,j) ∈ preSchedule P.M.base R.e R.HD ∧
      n*routingM P.M.base R.e+d*routingA P.M.base R.e=i*routingB P.M.base R.e+j*routingC P.M.base R.e := by
  obtain ⟨i,j,d,_,hd,heq,hcases⟩ := actual_mixed_notch_preprincipal R hm hn hpos hpre
  exact ⟨i,j,d,(mem_preSchedule _ _ _ _).mpr ⟨n,hpos,hpre,hd,heq,hcases⟩,heq⟩

def leftDepths (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Finset ℕ := by
  classical
  exact ((preSchedule B e HD).filter (fun z => z.2.1 < cr12 HD)).image Prod.fst

def nearHeights (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Finset ℕ := by
  classical
  exact ((preSchedule B e HD).filter (fun z => z.2.2 < cr13 HD)).image (fun z => z.2.2)

theorem nearHeights_bounds (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {j : ℕ} (hj : j ∈ nearHeights B e HD) : 0 < j ∧ j < cr13 HD := by
  classical
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hj
  obtain ⟨hmem,hnear⟩ := Finset.mem_filter.mp hz
  obtain ⟨n,_,_,_,_,hc⟩ := (mem_preSchedule B e HD z).mp hmem
  rcases hc with hc | hc | hc <;> omega

theorem leftDepths_bounds (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {d : ℕ} (hd : d ∈ leftDepths B e HD) : 0 < d ∧ d < cr31 HD := by
  classical
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hmem,hleft⟩ := Finset.mem_filter.mp hz
  obtain ⟨n,_,_,hpos,_,hc⟩ := (mem_preSchedule B e HD z).mp hmem
  rcases hc with hc | hc | hc <;> omega

theorem actual_nearHeights_nonempty {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=1) :
    (nearHeights P.M.base R.e R.HD).Nonempty := by
  classical
  have hP : FullySupported (principalVector P.M.base R.e R.HD) := by
    unfold principal_iota at hiota
    split_ifs at hiota with h
    exact h
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
    rw [heq] at hP
    change 0 < delta ∧ 0 < U ∧ 0 < V at hP
    rcases hgen with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega

theorem preSchedule_zero_generator (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {z : Monomial} (hz : z ∈ preSchedule B e HD) :
    (0,z.2.1,z.2.2) ∈ canonicalIdealGenerators B e HD := by
  obtain ⟨n,hn,hpre,hd,heq,hcases⟩ := (mem_preSchedule _ _ _ _).mp hz
  refine Or.inr (Or.inl ⟨n,z.2.1,z.2.2,z.1,hn,hpre,hd,heq,hcases,?_⟩)
  by_cases hi : z.2.1 < cr12 HD <;> by_cases hj : z.2.2 < cr13 HD <;>
    simp [colonMonomials,hi,hj]

theorem actual_first_zero_cut {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=1) :
    ∃ h : ℕ, 0 < h ∧ h < cr13 R.HD ∧ rightHeight P.M.base R.e h=0 ∧
      h ∈ nearHeights P.M.base R.e R.HD ∧
      ∀ j ∈ nearHeights P.M.base R.e R.HD, h ≤ j := by
  classical
  have hne := actual_nearHeights_nonempty R hm hn hiota
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

theorem normalized_a_critical_min (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {r u v : ℕ} (hr : 0 < r)
    (heq : r*routingA B e=u*routingB B e+v*routingC B e) : c1 B e ≤ r := by
  have ha : routingD B e*routingA B e=weights B (e 0) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale B e 1 0 0
  have hb : routingD B e*routingB B e=weights B (e 1) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 1 0
  have hc : routingD B e*routingC B e=weights B (e 2) := by
    simpa [normalizedGrid,gridDegree] using normalizedGrid_scale B e 0 0 1
  apply criticalExponent_min B (e 0) r
  refine ⟨hr,Finsupp.single (e 1) u+Finsupp.single (e 2) v,by simp,?_⟩
  have hf : r*weights B (e 0)=u*weights B (e 1)+v*weights B (e 2) := by
    nlinarith only [ha,hb,hc,heq]
  simpa [map_add,weight_single] using hf.symm

theorem actual_origin_preprincipal_return {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=1) :
    ∃ n : ℕ, 0 < n ∧
      n < firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e) (routingM_pos P.M.base R.e) ∧
      rawCandidate P.M.base R.e n 0 ≤ (H0 P.M.base R.e : ℤ) := by
  classical
  have hP : FullySupported (principalVector P.M.base R.e R.HD) := by
    unfold principal_iota at hiota
    split_ifs at hiota with h
    exact h
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
    change 0 < (principalVector P.M.base R.e R.HD).1 ∧
      0 < (principalVector P.M.base R.e R.HD).2.1 ∧
      0 < (principalVector P.M.base R.e R.HD).2.2 at hP
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

theorem actual_leftDepths_nonempty {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=1) :
    (leftDepths P.M.base R.e R.HD).Nonempty := by
  classical
  obtain ⟨n,hpos,hpre,hraw⟩ := actual_origin_preprincipal_return R hm hn hiota
  obtain ⟨i,j,d,hdomain,hdepth,heq,hcases⟩ := actual_mixed_notch_preprincipal R hm hn hpos hpre
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hcap := actual_interior_principal_origin_cap R hm hn hiota
  have hleft : i < cr12 R.HD := by
    by_contra h
    have hd : d < cr21 R.HD := by rcases hcases with hc | hc | hc <;> omega
    have hposij : 0 < i ∧ 0 < j := by rcases hcases with hc | hc | hc <;> omega
    have hcarry := (preprincipal_origin_carry_bounds _ _ R.HD n i j d hposij.1 hposij.2 heq).1
    have hsZ : (c1 P.M.base R.e : ℤ)=cr21 R.HD+cr31 R.HD := by exact_mod_cast hs.1
    have hdZ : (d : ℤ) < cr21 R.HD := by exact_mod_cast hd
    have hcapZ : (H0 P.M.base R.e : ℤ) ≤ cr31 R.HD := by exact_mod_cast hcap
    omega
  refine ⟨d,Finset.mem_image.mpr ⟨(d,i,j),Finset.mem_filter.mpr ⟨?_,hleft⟩,rfl⟩⟩
  exact (mem_preSchedule _ _ _ _).mpr ⟨n,hpos,hpre,hdepth,heq,hcases⟩

theorem actual_left_depth_max {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=1) :
    ∃ D : ℕ, D ∈ leftDepths P.M.base R.e R.HD ∧ 0 < D ∧ D < cr31 R.HD ∧
      (∀ d ∈ leftDepths P.M.base R.e R.HD, d ≤ D) ∧
      cr21 R.HD+(cr31 R.HD-D) ≤ H0 P.M.base R.e := by
  classical
  have hne := actual_leftDepths_nonempty R hm hn hiota
  let D := (leftDepths P.M.base R.e R.HD).max' hne
  have hmem : D ∈ leftDepths P.M.base R.e R.HD := Finset.max'_mem _ _
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hb := leftDepths_bounds _ _ _ hmem
  have hmax : ∀ d ∈ leftDepths P.M.base R.e R.HD, d ≤ D := fun d hd => Finset.le_max' _ d hd
  refine ⟨D,hmem,hb.1,hb.2,hmax,?_⟩
  obtain ⟨n,hpos,hpre,hraw⟩ := actual_origin_preprincipal_return R hm hn hiota
  obtain ⟨i,j,d,_,hdepth,heq,hcases⟩ := actual_mixed_notch_preprincipal R hm hn hpos hpre
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hcap := actual_interior_principal_origin_cap R hm hn hiota
  have hposij : 0 < i ∧ 0 < j := by rcases hcases with hc | hc | hc <;> omega
  have hcarry := (preprincipal_origin_carry_bounds _ _ R.HD n i j d hposij.1 hposij.2 heq).1
  have hsZ : (c1 P.M.base R.e : ℤ)=cr21 R.HD+cr31 R.HD := by exact_mod_cast hs.1
  have hleft : i < cr12 R.HD := by
    by_contra h
    have hd : d < cr21 R.HD := by rcases hcases with hc | hc | hc <;> omega
    have hdZ : (d : ℤ) < cr21 R.HD := by exact_mod_cast hd
    have hcapZ : (H0 P.M.base R.e : ℤ) ≤ cr31 R.HD := by exact_mod_cast hcap
    omega
  have hmemd : d ∈ leftDepths P.M.base R.e R.HD :=
    Finset.mem_image.mpr ⟨(d,i,j),Finset.mem_filter.mpr
      ⟨(mem_preSchedule _ _ _ _).mpr ⟨n,hpos,hpre,hdepth,heq,hcases⟩,hleft⟩,rfl⟩
  have hmaxZ : (d : ℤ) ≤ D := by exact_mod_cast hmax d hmemd
  have hf : (cr21 R.HD : ℤ)+cr31 R.HD-D ≤ H0 P.M.base R.e := by omega
  have hsub : (cr31 R.HD-D : ℕ) + D=cr31 R.HD := by omega
  have hsubZ : (cr31 R.HD-D : ℕ)+ (D : ℤ)=cr31 R.HD := by exact_mod_cast hsub
  exact_mod_cast (show (cr21 R.HD : ℤ)+(cr31 R.HD-D : ℕ) ≤ H0 P.M.base R.e by omega)

theorem preSchedule_coordinate_unique (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d i' j' d' : ℕ}
    (hdom : HerzogLShapeDomain HD i j) (hdom' : HerzogLShapeDomain HD i' j')
    (heq : n*routingM B e+d*routingA B e=i*routingB B e+j*routingC B e)
    (heq' : n*routingM B e+d'*routingA B e=i'*routingB B e+j'*routingC B e) :
    i=i' ∧ j=j' ∧ d=d' := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hres : gridResidue B e i j=gridResidue B e i' j' := by
    have h := congrArg (fun x : ℕ => (x : ZMod (routingA B e))) heq
    have h' := congrArg (fun x : ℕ => (x : ZMod (routingA B e))) heq'
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,add_zero] at h h'
    exact h.symm.trans h'
  have hcan := herzogLShapeCanonicality B e HD i j hdom
  have hcan' := herzogLShapeCanonicality B e HD i' j' hdom'
  change (normalizedGrid B e 0 i j : ℤ)=physicalAlpha B e (gridResidue B e i j) at hcan
  change (normalizedGrid B e 0 i' j' : ℤ)=physicalAlpha B e (gridResidue B e i' j') at hcan'
  rw [hres] at hcan
  have hv : monomialDegree B e (0,i,j)=monomialDegree B e (0,i',j') := by exact_mod_cast hcan.trans hcan'.symm
  have hu := canonical_monomial_unique B e HD hdom hdom' hv
  have hi := congrArg (fun z : Monomial => z.2.1) hu
  have hj := congrArg (fun z : Monomial => z.2.2) hu
  simp only [Prod.fst,Prod.snd] at hi hj
  refine ⟨hi,hj,?_⟩
  rw [←hi,←hj] at heq'
  exact Nat.eq_of_mul_eq_mul_right (routingA_pos B e) (by omega : d*routingA B e=d'*routingA B e)

private theorem schedule_extrema_bounds (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
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

private theorem right_generator_lower {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (_hP : FullySupported (principalVector P.M.base R.e R.HD))
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

private theorem opposite_generator_lower {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hP : FullySupported (principalVector P.M.base R.e R.HD))
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
    rw [heq] at hP
    change 0 < delta ∧ 0 < U ∧ 0 < V at hP
    have htP' : V ≤ j → t ≤ delta := by simpa only [heq,Prod.fst,Prod.snd] using htP
    rcases hg with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at *
    · omega
    · have ht := htP' (by omega)
      omega
    · omega

private theorem left_axis_generators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
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

private theorem near_axis_generator (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
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

theorem actual_interior_principal_right_envelope {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=1) :
    ∃ L h : ℕ, 0 < L ∧ 0 < h ∧ h < cr13 R.HD ∧ rightHeight P.M.base R.e h=0 ∧
      (∀ j : ℕ, j < h → rightHeight P.M.base R.e j=
        if (principalVector P.M.base R.e R.HD).2.2 ≤ j then min L (principalVector P.M.base R.e R.HD).1 else L) ∧
      (∀ j : ℕ, j < h → oppositeHeight P.M.base R.e R.HD j=cr21 R.HD+rightHeight P.M.base R.e j) ∧
      (PB_epsilon P.M.base R.e R.HD=1 → 0 < (principalVector P.M.base R.e R.HD).2.2 ∧
        (principalVector P.M.base R.e R.HD).2.2 < h ∧ (principalVector P.M.base R.e R.HD).1 < L) := by
  classical
  have hP : FullySupported (principalVector P.M.base R.e R.HD) := by
    unfold principal_iota at hiota
    split_ifs at hiota with h
    exact h
  have hdelta := hP.1
  have hV := hP.2.2
  have hs := coherent_coefficients P.M.base R.e R.HD
  obtain ⟨D,hD,hDpos,hDlt,hmax,hfloor⟩ := actual_left_depth_max R hm hn hiota
  obtain ⟨h,hhpos,hhlt,hzero,hhmem,hmin⟩ := actual_first_zero_cut R hm hn hiota
  let L := cr31 R.HD-D
  have hLpos : 0 < L := by dsimp [L]; omega
  obtain ⟨⟨i,hi,hrightgen⟩,v,hv,hopgen⟩ := left_axis_generators _ _ R.HD hD
  have hsum : c1 P.M.base R.e-D=cr21 R.HD+L := by dsimp [L]; omega
  have hprincipal := (principalVector_spec P.M.base R.e R.HD).1
  have hUbound := hprincipal.1
  have hprinGen : principalVector P.M.base R.e R.HD ∈ canonicalIdealGenerators P.M.base R.e R.HD :=
    Or.inr (Or.inr ⟨(principalVector P.M.base R.e R.HD).1,(principalVector P.M.base R.e R.HD).2.1,
      (principalVector P.M.base R.e R.HD).2.2,hprincipal,(principalVector_spec _ _ _).2.symm,Or.inl rfl⟩)
  have hPBgen : principalPB P.M.base R.e R.HD ∈ canonicalIdealGenerators P.M.base R.e R.HD :=
    Or.inr (Or.inr ⟨(principalVector P.M.base R.e R.HD).1,(principalVector P.M.base R.e R.HD).2.1,
      (principalVector P.M.base R.e R.HD).2.2,hprincipal,(principalVector_spec _ _ _).2.symm,Or.inr (Or.inl rfl)⟩)
  have hright : ∀ j : ℕ, j < h → rightHeight P.M.base R.e j=
      if (principalVector P.M.base R.e R.HD).2.2 ≤ j then min L (principalVector P.M.base R.e R.HD).1 else L := by
    intro j hj
    have hdom := right_boundary_domain P.M.base R.e R.HD (j:=j) (by omega)
    have hL : rightHeight P.M.base R.e j ≤ L := by
      apply (chart_threshold_iff R hm hn L _ _ hdom).mp
      exact ⟨(L,i,0),Or.inl hrightgen,le_rfl,hi,Nat.zero_le _⟩
    have hPval : (principalVector P.M.base R.e R.HD).2.2 ≤ j → rightHeight P.M.base R.e j ≤ (principalVector P.M.base R.e R.HD).1 := by
      intro hVj
      apply (chart_threshold_iff R hm hn _ _ _ hdom).mp
      exact ⟨_,Or.inl hprinGen,le_rfl,by simp only [Prod.fst,Prod.snd]; omega,hVj⟩
    have hx := (chart_threshold_iff R hm hn (rightHeight P.M.base R.e j) _ _ hdom).mpr le_rfl
    obtain ⟨g,hg,hgr,hgi,hgj⟩ := (chart_on_domain_iff _ _ _ _ hdom).mp hx
    have hlo := right_generator_lower R hP hmax hmin hfloor hhlt hj hg hgj
    dsimp [L] at hL ⊢
    split_ifs with hVj
    · simp only [ite_eq_left hVj] at hlo
      exact Nat.le_antisymm (Nat.le_min.mpr ⟨hL,hPval hVj⟩) (hlo.trans hgr)
    · simp only [ite_eq_right hVj] at hlo
      exact Nat.le_antisymm hL (hlo.trans hgr)
  have hop : ∀ j : ℕ, j < h → oppositeHeight P.M.base R.e R.HD j=cr21 R.HD+rightHeight P.M.base R.e j := by
    intro j hj
    have hdom := opposite_boundary_domain P.M.base R.e R.HD (j:=j) (by omega)
    have hL : oppositeHeight P.M.base R.e R.HD j ≤ cr21 R.HD+L := by
      apply (chart_threshold_iff R hm hn _ _ _ hdom).mp
      refine ⟨(c1 P.M.base R.e-D,0,v),Or.inl hopgen,?_,le_rfl,?_⟩
      · simp only [Prod.fst]; omega
      · simp only [Prod.fst,Prod.snd]; omega
    have hPval : (principalVector P.M.base R.e R.HD).2.2 ≤ j →
        oppositeHeight P.M.base R.e R.HD j ≤ cr21 R.HD+(principalVector P.M.base R.e R.HD).1 := by
      intro hVj
      apply (chart_threshold_iff R hm hn _ _ _ hdom).mp
      exact ⟨_,Or.inl hPBgen,by simp only [principalPB,Prod.fst]; omega,le_rfl,
        by simp only [principalPB,Prod.fst,Prod.snd]; omega⟩
    have hx := (chart_threshold_iff R hm hn (oppositeHeight P.M.base R.e R.HD j) _ _ hdom).mpr le_rfl
    obtain ⟨g,hg,hgr,hgi,hgj⟩ := (chart_on_domain_iff _ _ _ _ hdom).mp hx
    simp only [Prod.fst,Prod.snd] at hgr hgi hgj
    have hg0 : g.2.1=0 := by omega
    have hlo := opposite_generator_lower R hP hmax hmin hfloor hj hg hg0 hgj
    rw [hright j hj]
    dsimp [L] at hL ⊢
    split_ifs with hVj
    · simp only [ite_eq_left hVj] at hlo
      have hPval := hPval hVj
      omega
    · simp only [ite_eq_right hVj] at hlo
      omega
  refine ⟨L,h,hLpos,hhpos,hhlt,hzero,hright,hop,?_⟩
  intro heps
  have hPB : ChartMinimal P.M.base R.e R.HD (principalPB P.M.base R.e R.HD) := by
    unfold PB_epsilon at heps
    split_ifs at heps with h
    exact h
  have hdeltaL : (principalVector P.M.base R.e R.HD).1 < L := by
    by_contra h
    have hdiv := hPB.2 (c1 P.M.base R.e-D,0,v)
      ⟨_,Or.inl hopgen,le_rfl,le_rfl,le_rfl⟩
      (by simp only [principalPB,Prod.fst]; omega) (by simp [principalPB])
      (by simp only [principalPB,Prod.fst,Prod.snd]; omega)
    have hvEq := congrArg (fun z : Monomial => z.2.2) hdiv
    simp only [principalPB,Prod.fst,Prod.snd] at hvEq
    omega
  have hVh : (principalVector P.M.base R.e R.HD).2.2 < h := by
    by_contra hnot
    obtain ⟨r,hr,hgen⟩ := near_axis_generator _ _ R.HD hhmem
    have hdiv := hPB.2 (r,0,h+cr23 R.HD)
      ⟨_,Or.inl hgen,le_rfl,le_rfl,le_rfl⟩
      (by simp only [principalPB,Prod.fst]; omega) (by simp [principalPB])
      (by simp only [principalPB,Prod.fst,Prod.snd]; omega)
    have hrEq := congrArg Prod.fst hdiv
    simp only [principalPB,Prod.fst,Prod.snd] at hrEq
    omega
  exact ⟨hV,hVh,hdeltaL⟩

theorem actual_interior_principal_tight_count {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=1) :
    principal_iota P.M.base R.e R.HD+PB_epsilon P.M.base R.e R.HD ≤
      Nat.card (TightRightIndex P.M.base R.e R.HD) := by
  classical
  letI := tight_right_indices_finite P.M.base R.e R.HD
  obtain ⟨L,h,hL,hh,hhq,hzero,hright,hop,hstrict⟩ := actual_interior_principal_right_envelope R hm hn hiota
  have hP : FullySupported (principalVector P.M.base R.e R.HD) := by
    unfold principal_iota at hiota
    split_ifs at hiota with h
    exact h
  have hdelta := hP.1
  have hlast : h-1+1=h := by omega
  have hlastPos : 0 < rightHeight P.M.base R.e (h-1) := by
    rw [hright (h-1) (by omega)]
    split_ifs <;> omega
  let last : TightRightIndex P.M.base R.e R.HD :=
    ⟨h-1,by rw [hlast]; exact ⟨hhq,hlastPos,by omega,hop _ (by omega)⟩⟩
  rcases PB_epsilon_zero_or_one P.M.base R.e R.HD with heps | heps
  · have hinj : Function.Injective (fun _ : Fin 1 => last) := by intro x y _; exact Subsingleton.elim x y
    have hcard := Nat.card_le_card_of_injective _ hinj
    simp only [Nat.card_fin] at hcard
    omega
  · obtain ⟨hV,hVh,hδL⟩ := hstrict heps
    let V := (principalVector P.M.base R.e R.HD).2.2
    have hvstep : V-1+1=V := by dsimp [V]; omega
    have hleftHeight : rightHeight P.M.base R.e (V-1)=L := by
      rw [hright _ (by dsimp [V]; omega),ite_eq_right (by dsimp [V]; omega)]
    have hnextHeight : rightHeight P.M.base R.e V=(principalVector P.M.base R.e R.HD).1 := by
      rw [hright _ hVh,ite_eq_left le_rfl,Nat.min_eq_right (by omega)]
    let first : TightRightIndex P.M.base R.e R.HD :=
      ⟨V-1,by rw [hvstep]; refine ⟨by omega,by omega,by omega,hop _ (by omega)⟩⟩
    have hne : first ≠ last := by
      intro heq
      have hval := congrArg Subtype.val heq
      change V-1=h-1 at hval
      dsimp [V] at hval
      omega
    let f : Fin 2 → TightRightIndex P.M.base R.e R.HD := fun x => if x.val=0 then first else last
    have hinj : Function.Injective f := by
      intro x y heq
      fin_cases x <;> fin_cases y <;> simp only [f,Fin.val_zero,ite_true,Fin.val_one,Nat.one_ne_zero,ite_false] at heq ⊢
      · exact False.elim (hne heq)
      · exact False.elim (hne heq.symm)
    have hcard := Nat.card_le_card_of_injective f hinj
    simp only [Nat.card_fin] at hcard
    omega

theorem actual_interior_principal_type_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=1) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have hc := actual_correction_count R hm hn
  have ht := actual_interior_principal_tight_count R hm hn hiota
  have hs := L5A2C4OR24.actual_T5_T6_socle_source_bound R hm hn
  omega

theorem actual_no_indicator_type_bound {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=0)
    (heps : PB_epsilon P.M.base R.e R.HD=0) :
    Gamma.asRelativeIdeal.idealType ≤ P.sourceCount := by
  have hc := actual_correction_count R hm hn
  have hs := L5A2C4OR24.actual_T5_T6_socle_source_bound R hm hn
  omega

theorem actual_boundary_principal_cases {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=0)
    (heps : PB_epsilon P.M.base R.e R.HD=1) :
    0 < (principalVector P.M.base R.e R.HD).2.1 ∧
    (principalVector P.M.base R.e R.HD).2.2 < cr13 R.HD ∧
    (((principalVector P.M.base R.e R.HD).1=0 ∧ 0 < (principalVector P.M.base R.e R.HD).2.2) ∨
      ((principalVector P.M.base R.e R.HD).2.2=0 ∧ 0 < (principalVector P.M.base R.e R.HD).1)) := by
  classical
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hspec := principalVector_spec P.M.base R.e R.HD
  have hUbound := hspec.1.1
  have hPB : ChartMinimal P.M.base R.e R.HD (principalPB P.M.base R.e R.HD) := by
    unfold PB_epsilon at heps
    split_ifs at heps with h
    exact h
  have hgen : principalVector P.M.base R.e R.HD ∈ canonicalIdealGenerators P.M.base R.e R.HD :=
    Or.inr (Or.inr ⟨(principalVector P.M.base R.e R.HD).1,(principalVector P.M.base R.e R.HD).2.1,
      (principalVector P.M.base R.e R.HD).2.2,hspec.1,hspec.2.symm,Or.inl rfl⟩)
  have hU : 0 < (principalVector P.M.base R.e R.HD).2.1 := by
    by_contra h
    have hU0 : (principalVector P.M.base R.e R.HD).2.1=0 := by omega
    have heq := hPB.2 _ ⟨_,Or.inl hgen,le_rfl,le_rfl,le_rfl⟩
      (by simp only [principalPB,Prod.fst]; omega) (by simp only [principalPB,Prod.fst,Prod.snd]; omega)
      (by simp only [principalPB,Prod.fst,Prod.snd]; omega)
    have hx := congrArg Prod.fst heq
    simp only [principalPB,Prod.fst,Prod.snd] at hx
    omega
  have hV : (principalVector P.M.base R.e R.HD).2.2 < cr13 R.HD := by
    by_contra h
    have hz : (0,0,c3 P.M.base R.e) ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) :=
      ⟨_,Or.inr (Or.inr (Or.inl rfl)),le_rfl,le_rfl,le_rfl⟩
    have heq := hPB.2 _ hz (by simp [principalPB]) (by simp [principalPB])
      (by simp only [principalPB,Prod.fst,Prod.snd]; omega)
    have hx := congrArg Prod.fst heq
    simp only [principalPB,Prod.fst,Prod.snd] at hx
    omega
  have hnot : ¬FullySupported (principalVector P.M.base R.e R.HD) := by
    unfold principal_iota at hiota
    split_ifs at hiota with h
    exact h
  have hnonzero : (principalVector P.M.base R.e R.HD).1=0 →
      0 < (principalVector P.M.base R.e R.HD).2.2 := by
    intro hδ
    by_contra h
    have hV0 : (principalVector P.M.base R.e R.HD).2.2=0 := by omega
    have hdom := right_boundary_domain P.M.base R.e R.HD (j:=0) hp.2.1
    have hcut : (0,c2 P.M.base R.e-1,0) ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) :=
      ⟨_,Or.inl hgen,by simp only [Prod.fst,Prod.snd]; omega,
        by simp only [Prod.fst,Prod.snd]; omega,by simp only [Prod.fst,Prod.snd]; omega⟩
    have hz := (chart_threshold_iff R hm hn _ _ _ hdom).mp hcut
    have hG2 := (normalized_mixed_notch_G0_G4 R hm hn).2.2.1
    omega
  refine ⟨hU,hV,?_⟩
  by_cases hδ : (principalVector P.M.base R.e R.HD).1=0
  · exact Or.inl ⟨hδ,hnonzero hδ⟩
  · have hδpos : 0 < (principalVector P.M.base R.e R.HD).1 := by omega
    have hV0 : (principalVector P.M.base R.e R.HD).2.2=0 := by
      by_contra h
      exact hnot ⟨hδpos,hU,by omega⟩
    exact Or.inr ⟨hV0,hδpos⟩

end NS25Lean.L5A2C4OR26
