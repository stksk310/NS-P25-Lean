import NS25Lean.P2SectorCT6GlobalLedgerR24

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.L5A2C4OR25
open FourGeneratedBridge L5A2C4A L5A2C4C L5A2C4D L5A2C4H
  L5A2C4OR1 L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 L5A2C4OR23 L5A2C4OR24
variable {Gamma : NumericalSemigroup}

def rightHeight (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (j : ℕ) : ℕ :=
  eta B e (c2 B e-1) j

def oppositeHeight (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (j : ℕ) : ℕ := eta B e 0 (cr23 HD+j)

def rightWitness (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (j : ℕ) : Monomial :=
  (rightHeight B e j-1,c2 B e-1,j)

def TightRightIndex (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) :=
  {j : ℕ // j+1<cr13 HD ∧ 0<rightHeight B e j ∧
    rightHeight B e (j+1)<rightHeight B e j ∧
    oppositeHeight B e HD j=cr21 HD+rightHeight B e j}

theorem right_boundary_domain (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {j : ℕ} (hj : j<cr13 HD) :
    HerzogLShapeDomain HD (c2 B e-1) j := by
  have hp := coherent_coefficients_positive B e HD
  have hs := coherent_coefficients B e HD
  exact ⟨by omega,by omega,Or.inr hj⟩

theorem opposite_boundary_domain (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {j : ℕ} (hj : j<cr13 HD) :
    HerzogLShapeDomain HD 0 (cr23 HD+j) := by
  have hp := coherent_coefficients_positive B e HD
  have hs := coherent_coefficients B e HD
  exact ⟨by omega,by omega,Or.inl hp.1⟩

theorem grid_degree_mem_H (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (z : Monomial) : monomialDegree B e z ∈ routingH B e := by
  change monomialDegree B e z ∈ generatedThree (routingA B e) (routingB B e) (routingC B e)
  apply (mem_generatedThree_iff _ _ _ _).mpr
  exact ⟨z.1,z.2.1,z.2.2,rfl⟩

theorem chart_threshold_iff {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (r i j : ℕ) (hd : HerzogLShapeDomain R.HD i j) :
    (r,i,j) ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) ↔
      eta P.M.base R.e i j ≤ r := by
  exact (actual_chart_staircase_iff R hm hn r i j hd).symm.trans
    ((actual_cyclicCut_iff_routingI P.M.base R.e _).trans
      (normalizedGrid_mem_iff_eta_le P.M.base R.e r i j))

theorem outside_domain_mem_chart (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (r i j : ℕ)
    (hd : ¬HerzogLShapeDomain HD i j) :
    (r,i,j) ∈ monomialClosure (chartGenerators B e HD) := by
  by_cases hi : c2 B e ≤ i
  · exact ⟨(0,c2 B e,0),Or.inr (Or.inl rfl),Nat.zero_le _,hi,Nat.zero_le _⟩
  by_cases hj : c3 B e ≤ j
  · exact ⟨(0,0,c3 B e),Or.inr (Or.inr (Or.inl rfl)),Nat.zero_le _,Nat.zero_le _,hj⟩
  have hc : cr12 HD ≤ i ∧ cr13 HD ≤ j := by
    unfold HerzogLShapeDomain at hd
    omega
  exact ⟨(0,cr12 HD,cr13 HD),Or.inr (Or.inr (Or.inr rfl)),Nat.zero_le _,hc.1,hc.2⟩

theorem tight_right_standard {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (j : ℕ) (hRange : j+1<cr13 R.HD) (hPos : 0<rightHeight P.M.base R.e j) :
    rightWitness P.M.base R.e j ∉ monomialClosure (chartGenerators P.M.base R.e R.HD) := by
  rw [rightWitness,chart_threshold_iff R hm hn _ _ _
    (right_boundary_domain P.M.base R.e R.HD (by omega))]
  unfold rightHeight at hPos
  dsimp [rightHeight]
  omega

theorem tight_right_monomial_socle {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (j : ℕ) (hRange : j+1<cr13 R.HD) (hPos : 0<rightHeight P.M.base R.e j)
    (hDrop : rightHeight P.M.base R.e (j+1)<rightHeight P.M.base R.e j)
    (_hTight : oppositeHeight P.M.base R.e R.HD j=cr21 R.HD+rightHeight P.M.base R.e j) :
    MonomialSocle (chartGenerators P.M.base R.e R.HD) (rightWitness P.M.base R.e j) := by
  refine ⟨tight_right_standard R hm hn j hRange hPos,?_,?_,?_⟩
  · change (rightHeight P.M.base R.e j-1+1,c2 P.M.base R.e-1,j) ∈ _
    rw [chart_threshold_iff R hm hn _ _ _
      (right_boundary_domain P.M.base R.e R.HD (by omega))]
    change rightHeight P.M.base R.e j ≤ rightHeight P.M.base R.e j-1+1
    omega
  · change (rightHeight P.M.base R.e j-1,c2 P.M.base R.e-1+1,j) ∈ _
    have hp := coherent_coefficients_positive P.M.base R.e R.HD
    have hs := coherent_coefficients P.M.base R.e R.HD
    exact ⟨(0,c2 P.M.base R.e,0),Or.inr (Or.inl rfl),Nat.zero_le _,
      by simp only [Prod.fst,Prod.snd]; omega,Nat.zero_le _⟩
  · change (rightHeight P.M.base R.e j-1,c2 P.M.base R.e-1,j+1) ∈ _
    rw [chart_threshold_iff R hm hn _ _ _ (right_boundary_domain P.M.base R.e R.HD hRange)]
    change rightHeight P.M.base R.e (j+1) ≤ rightHeight P.M.base R.e j-1
    omega

theorem right_b_wrap_degree (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (r j : ℕ) :
    monomialDegree B e (r,c2 B e-1,j)+routingB B e =
      normalizedGrid B e (r+cr21 HD) 0 (cr23 HD+j) := by
  have hp := coherent_coefficients_positive B e HD
  have hs := coherent_coefficients B e HD
  have hr := (coherent_normalized_relations B e HD).2.1
  have hi : c2 B e-1+1=c2 B e := by omega
  have hi' := congrArg (fun n => n*routingB B e) hi
  simp only [Nat.add_mul,one_mul] at hi'
  simp only [monomialDegree,normalizedGrid,Prod.fst,Prod.snd,zero_mul,add_zero,Nat.add_mul]
  nlinarith only [hr,hi']

theorem tight_right_y_product_survives {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (_hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (_hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (j : ℕ) (_hRange : j+1<cr13 R.HD) (hPos : 0<rightHeight P.M.base R.e j)
    (hTight : oppositeHeight P.M.base R.e R.HD j=cr21 R.HD+rightHeight P.M.base R.e j) :
    monomialDegree P.M.base R.e (rightWitness P.M.base R.e j)+routingB P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
  rw [rightWitness,right_b_wrap_degree P.M.base R.e R.HD,
    actual_cyclicCut_iff_routingI,normalizedGrid_mem_iff_eta_le]
  change ¬oppositeHeight P.M.base R.e R.HD j ≤ rightHeight P.M.base R.e j-1+cr21 R.HD
  omega

theorem tight_right_degree_standard {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (j : ℕ) (hRange : j+1<cr13 R.HD) (hPos : 0<rightHeight P.M.base R.e j) :
    monomialDegree P.M.base R.e (rightWitness P.M.base R.e j) ∈ routingH P.M.base R.e ∧
      monomialDegree P.M.base R.e (rightWitness P.M.base R.e j) ∉
        cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
  refine ⟨grid_degree_mem_H _ _ _,?_⟩
  intro hcut
  exact tight_right_standard R hm hn j hRange hPos
    ((actual_chart_staircase_iff R hm hn _ _ _
      (right_boundary_domain P.M.base R.e R.HD (by omega))).mp hcut)

theorem tight_right_not_actual_socle {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (j : ℕ) (hRange : j+1<cr13 R.HD) (hPos : 0<rightHeight P.M.base R.e j)
    (hTight : oppositeHeight P.M.base R.e R.HD j=cr21 R.HD+rightHeight P.M.base R.e j) :
    ¬IsIntegralSocle (routingI P.M.base R.e)
      (monomialDegree P.M.base R.e (rightWitness P.M.base R.e j) : ℤ) := by
  intro h
  have hb := h.2.2 (routingB P.M.base R.e) (routingHB P.M.base R.e)
    (Nat.ne_of_gt (routingB_positive P.M.base R.e))
  have hc : monomialDegree P.M.base R.e (rightWitness P.M.base R.e j)+routingB P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) :=
    (actual_cyclicCut_iff_routingI P.M.base R.e _).mpr (by rw [Nat.cast_add]; exact hb)
  exact tight_right_y_product_survives R hm hn j hRange hPos hTight hc

theorem tight_right_degree_injective (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) :
    Function.Injective (fun j : TightRightIndex B e HD => monomialDegree B e (rightWitness B e j.val)) := by
  intro j j' heq
  have hz := canonical_monomial_unique B e HD
    (right_boundary_domain B e HD (j:=j.val) (by have := j.property.1; omega))
    (right_boundary_domain B e HD (j:=j'.val) (by have := j'.property.1; omega)) heq
  exact Subtype.ext (congrArg (fun z : Monomial => z.2.2) hz)

theorem actual_socle_canonical_exists (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (x : {x : ℤ // IsIntegralSocle (routingI B e) x}) :
    ∃ z : Monomial, HerzogLShapeDomain HD z.2.1 z.2.2 ∧ (monomialDegree B e z : ℤ)=x.val := by
  have hx := x.property.1
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hx
  obtain ⟨n,hn,heq⟩ := hx
  obtain ⟨z,hz,_⟩ := canonical_monomial_of_H B e HD hn
  exact ⟨z,hz.1,by rw [hz.2]; exact heq.symm⟩

def actualSocleCanonical (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (x : {x : ℤ // IsIntegralSocle (routingI B e) x}) : Monomial :=
  Classical.choose (actual_socle_canonical_exists B e HD x)

theorem actualSocleCanonical_spec (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (x : {x : ℤ // IsIntegralSocle (routingI B e) x}) :
    HerzogLShapeDomain HD (actualSocleCanonical B e HD x).2.1 (actualSocleCanonical B e HD x).2.2 ∧
      (monomialDegree B e (actualSocleCanonical B e HD x) : ℤ)=x.val :=
  Classical.choose_spec (actual_socle_canonical_exists B e HD x)

theorem actualSocleCanonical_is_chart_socle {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (x : {x : ℤ // IsIntegralSocle (routingI P.M.base R.e) x}) :
    MonomialSocle (chartGenerators P.M.base R.e R.HD) (actualSocleCanonical P.M.base R.e R.HD x) := by
  let z := actualSocleCanonical P.M.base R.e R.HD x
  have hspec := actualSocleCanonical_spec P.M.base R.e R.HD x
  change HerzogLShapeDomain R.HD z.2.1 z.2.2 ∧ (monomialDegree P.M.base R.e z : ℤ)=x.val at hspec
  have haH : routingA P.M.base R.e ∈ routingH P.M.base R.e := by
    change routingA P.M.base R.e ∈ generatedThree (routingA P.M.base R.e) (routingB P.M.base R.e) (routingC P.M.base R.e)
    exact AddSubmonoid.subset_closure (by simp)
  have hA := x.property.2.2 _ haH (Nat.ne_of_gt (routingA_pos P.M.base R.e))
  have hB := x.property.2.2 _ (routingHB P.M.base R.e) (Nat.ne_of_gt (routingB_positive P.M.base R.e))
  have hC := x.property.2.2 _ (routingHC P.M.base R.e) (Nat.ne_of_gt (routingC_positive P.M.base R.e))
  have hkill : ∀ z' : Monomial, HerzogLShapeDomain R.HD z'.2.1 z'.2.2 →
      (monomialDegree P.M.base R.e z' : ℤ) ∈ routingI P.M.base R.e →
      z' ∈ monomialClosure (chartGenerators P.M.base R.e R.HD) := by
    intro z' hd hi
    exact (actual_chart_staircase_iff R hm hn _ _ _ hd).mp
      ((actual_cyclicCut_iff_routingI P.M.base R.e _).mpr hi)
  refine ⟨?_,?_,?_,?_⟩
  · intro hz
    apply x.property.2.1
    rw [←hspec.2]
    exact (actual_cyclicCut_iff_routingI P.M.base R.e _).mp
      ((actual_chart_staircase_iff R hm hn _ _ _ hspec.1).mpr hz)
  · apply hkill (z.1+1,z.2.1,z.2.2) hspec.1
    have heq : (monomialDegree P.M.base R.e (z.1+1,z.2.1,z.2.2) : ℤ)=
        x.val+routingA P.M.base R.e := by
      rw [←hspec.2]
      simp only [monomialDegree,normalizedGrid,Prod.fst,Prod.snd,Nat.add_mul,one_mul]
      push_cast
      ring
    rw [heq]
    exact hA
  · by_cases hd : HerzogLShapeDomain R.HD (z.2.1+1) z.2.2
    · apply hkill (z.1,z.2.1+1,z.2.2) hd
      have heq : (monomialDegree P.M.base R.e (z.1,z.2.1+1,z.2.2) : ℤ)=
          x.val+routingB P.M.base R.e := by
        rw [←hspec.2]
        simp only [monomialDegree,normalizedGrid,Prod.fst,Prod.snd,Nat.add_mul,one_mul]
        push_cast
        ring
      rw [heq]
      exact hB
    · exact outside_domain_mem_chart _ _ _ _ _ _ hd
  · by_cases hd : HerzogLShapeDomain R.HD z.2.1 (z.2.2+1)
    · apply hkill (z.1,z.2.1,z.2.2+1) hd
      have heq : (monomialDegree P.M.base R.e (z.1,z.2.1,z.2.2+1) : ℤ)=
          x.val+routingC P.M.base R.e := by
        rw [←hspec.2]
        simp only [monomialDegree,normalizedGrid,Prod.fst,Prod.snd,Nat.add_mul,one_mul]
        push_cast
        ring
      rw [heq]
      exact hC
    · exact outside_domain_mem_chart _ _ _ _ _ _ hd

def actualSocleToChartSocle {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    {x : ℤ // IsIntegralSocle (routingI P.M.base R.e) x} →
      {z // MonomialSocle (chartGenerators P.M.base R.e R.HD) z} := fun x =>
  ⟨actualSocleCanonical P.M.base R.e R.HD x,actualSocleCanonical_is_chart_socle R hm hn x⟩

theorem actualSocleToChartSocle_degree {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (x : {x : ℤ // IsIntegralSocle (routingI P.M.base R.e) x}) :
    (monomialDegree P.M.base R.e (actualSocleToChartSocle R hm hn x).val : ℤ)=x.val :=
  (actualSocleCanonical_spec P.M.base R.e R.HD x).2

theorem actualSocleToChartSocle_injective {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    Function.Injective (actualSocleToChartSocle R hm hn) := by
  intro x y heq
  apply Subtype.ext
  rw [←actualSocleToChartSocle_degree R hm hn x,←actualSocleToChartSocle_degree R hm hn y,heq]

theorem tight_right_outside_actual_image {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (j : TightRightIndex P.M.base R.e R.HD)
    (x : {x : ℤ // IsIntegralSocle (routingI P.M.base R.e) x}) :
    (actualSocleToChartSocle R hm hn x).val ≠ rightWitness P.M.base R.e j.val := by
  intro heq
  have hx := x.property
  have hdegree := actualSocleToChartSocle_degree R hm hn x
  rw [heq] at hdegree
  rw [←hdegree] at hx
  exact tight_right_not_actual_socle R hm hn j.val j.property.1 j.property.2.1 j.property.2.2.2 hx

theorem actual_chart_socle_finite {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    Finite {z // MonomialSocle (chartGenerators P.M.base R.e R.HD) z} := by
  obtain ⟨a,b,c,_,_,_,ha,hb,hc⟩ := (actualJ0_proper_artinian R hm hn).2
  have hfin := monomialSocle_finite (actualJ0Generators P.M.base R.e R.HD : Set Monomial) a b c ha hb hc
  simp only [actualJ0_socle_iff] at hfin
  exact hfin

theorem actual_integral_socle_finite {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    Finite {x : ℤ // IsIntegralSocle (routingI P.M.base R.e) x} := by
  letI := actual_chart_socle_finite R hm hn
  exact Finite.of_injective _ (actualSocleToChartSocle_injective R hm hn)

theorem tight_right_indices_finite (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Finite (TightRightIndex B e HD) := by
  let F : TightRightIndex B e HD → Fin (cr13 HD) := fun j =>
    ⟨j.val,by have := j.property.1; omega⟩
  exact Finite.of_injective F (by intro j j' heq; exact Subtype.ext (congrArg Fin.val heq))

theorem actual_integral_socle_card_eq_type (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Nat.card {x : ℤ // IsIntegralSocle (routingI B e) x}=Gamma.asRelativeIdeal.idealType := by
  calc
    _ = Nat.card {w // IsSocle Gamma.toAddSubmonoid
        (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e)) B.q.val w} :=
      (normalizedTail_socle_card Gamma B.q.val _ _ _ (chosenBase_minimalFour B e)).symm
    _ = Gamma.asRelativeIdeal.idealType :=
      (fourGenerated_idealType_eq_natCard_socle Gamma B.q.val _ _ _
        (chosenBase_minimalFour B e).m_pos (chosenBase_minimalFour B e).generated).symm

def actualCorrectionInjection {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    ({x : ℤ // IsIntegralSocle (routingI P.M.base R.e) x} ⊕ TightRightIndex P.M.base R.e R.HD) →
      {z // MonomialSocle (chartGenerators P.M.base R.e R.HD) z}
  | Sum.inl x => actualSocleToChartSocle R hm hn x
  | Sum.inr j => ⟨rightWitness P.M.base R.e j.val,
      tight_right_monomial_socle R hm hn j.val j.property.1 j.property.2.1
        j.property.2.2.1 j.property.2.2.2⟩

theorem actualCorrectionInjection_injective {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    Function.Injective (actualCorrectionInjection R hm hn) := by
  intro x y heq
  cases x with
  | inl x =>
    cases y with
    | inl y => exact congrArg Sum.inl (actualSocleToChartSocle_injective R hm hn heq)
    | inr j => exact False.elim (tight_right_outside_actual_image R hm hn j x (congrArg Subtype.val heq))
  | inr j =>
    cases y with
    | inl x => exact False.elim (tight_right_outside_actual_image R hm hn j x (congrArg Subtype.val heq.symm))
    | inr j' =>
      apply congrArg Sum.inr
      apply tight_right_degree_injective P.M.base R.e R.HD
      exact congrArg (fun z => monomialDegree P.M.base R.e z.val) heq

/-- Subtraction-free T7 correction ledger. It does not supply the T9/T10 indicator witnesses. -/
theorem actual_correction_count {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    Gamma.asRelativeIdeal.idealType + Nat.card (TightRightIndex P.M.base R.e R.HD) ≤
      Nat.card {z // MonomialSocle (chartGenerators P.M.base R.e R.HD) z} := by
  letI := actual_chart_socle_finite R hm hn
  letI := actual_integral_socle_finite R hm hn
  letI := tight_right_indices_finite P.M.base R.e R.HD
  have h := Nat.card_le_card_of_injective _ (actualCorrectionInjection_injective R hm hn)
  rw [Nat.card_sum,actual_integral_socle_card_eq_type] at h
  exact h

/-- Literal counts are constructed from a legal frozen rewrite trace, not passed as a packet field. -/
theorem rewrite_counts (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {z z' : Monomial}
    (path : Relation.ReflTransGen (HerzogRewrite B e HD) z z') :
    ∃ A N D : ℕ,
      z'.1=z.1+A*c1 B e+N*cr21 HD+D*cr31 HD ∧
      z'.2.1+A*cr12 HD+N*c2 B e=z.2.1+D*cr32 HD ∧
      z'.2.2+A*cr13 HD+D*c3 B e=z.2.2+N*cr23 HD := by
  induction path with
  | refl => exact ⟨0,0,0,by simp,by simp,by simp⟩
  | @tail v w _ step ih =>
    obtain ⟨A,N,D,ha,hb,hc⟩ := ih
    cases step with
    | central r i j hi hj =>
      have hsi := Nat.sub_add_cancel hi
      have hsj := Nat.sub_add_cancel hj
      refine ⟨A+1,N,D,?_,?_,?_⟩ <;>
        simp only [Prod.fst,Prod.snd,Nat.add_mul,one_mul] at * <;> omega
    | bWrap r i j _ hi =>
      have hsi := Nat.sub_add_cancel hi
      refine ⟨A,N+1,D,?_,?_,?_⟩ <;>
        simp only [Prod.fst,Prod.snd,Nat.add_mul,one_mul] at * <;> omega
    | cWrap r i j _ _ hj =>
      have hsj := Nat.sub_add_cancel hj
      refine ⟨A,N,D+1,?_,?_,?_⟩ <;>
        simp only [Prod.fst,Prod.snd,Nat.add_mul,one_mul] at * <;> omega

private theorem carry_bounds (p q s t k l A N D X Y : ℕ)
    (hk : 0<k) (hl : 0<l) (_hs : 0<s) (_ht : 0<t)
    (hX : 0<X) (hY : 0<Y)
    (hb : A*p+N*(p+s)=X+D*s) (hc : A*q+D*(q+t)=Y+N*t) :
    k+l ≤ A*(k+l)+N*k+D*l ∧
      (p<X → k+l+k ≤ A*(k+l)+N*k+D*l) ∧
      (q<Y → k+l+l ≤ A*(k+l)+N*k+D*l) := by
  have hbase : k+l ≤ A*(k+l)+N*k+D*l := by
    by_cases hA : 1≤A
    · nlinarith
    · have hA0 : A=0 := by omega
      subst A
      have hN : 1≤N := by
        by_contra h
        have : N=0 := by omega
        subst N
        simp at hb
        omega
      have hD : 1≤D := by
        by_contra h
        have : D=0 := by omega
        subst D
        simp at hc
        omega
      nlinarith
  refine ⟨hbase,?_,?_⟩
  · intro hpX
    by_cases hA : 2≤A
    · nlinarith
    by_cases hA1 : A=1
    · subst A
      have hN : 1≤N := by
        by_contra h
        have : N=0 := by omega
        subst N
        simp at hb
        omega
      nlinarith
    · have hA0 : A=0 := by omega
      subst A
      have hD : 1≤D := by
        by_contra h
        have : D=0 := by omega
        subst D
        simp at hc
        omega
      have hN : 2≤N := by
        by_contra h
        have hN0 : N=0 ∨ N=1 := by omega
        rcases hN0 with rfl | rfl
        · simp at hb; omega
        · simp at hb; nlinarith
      nlinarith
  · intro hqY
    by_cases hA : 2≤A
    · nlinarith
    by_cases hA1 : A=1
    · subst A
      have hD : 1≤D := by
        by_contra h
        have : D=0 := by omega
        subst D
        simp at hc
        omega
      nlinarith
    · have hA0 : A=0 := by omega
      subst A
      have hN : 1≤N := by
        by_contra h
        have : N=0 := by omega
        subst N
        simp at hb
        omega
      have hD : 2≤D := by
        by_contra h
        have hD0 : D=0 ∨ D=1 := by omega
        rcases hD0 with rfl | rfl
        · simp at hc; omega
        · simp at hc; nlinarith
      nlinarith

theorem inverse_apery_coordinate (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (n : ℕ) :
    ∃ u v : ℕ, HerzogLShapeDomain HD u v ∧
      physicalAlpha B e (-(n*routingM B e : ℕ)) = (normalizedGrid B e 0 u v : ℤ) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  let s : ZMod (routingA B e) := -(n*routingM B e : ℕ)
  have hx : physicalAlpha B e s ∈ (routingH B e).asRelativeIdeal :=
    (routingH B e).asRelativeIdeal.aperyRepresentative_mem (routingA B e) s
  rw [NumericalSemigroup.mem_asRelativeIdeal_iff] at hx
  obtain ⟨x,hx,hax⟩ := hx
  obtain ⟨z,hz,_⟩ := canonical_monomial_of_H B e HD hx
  have hmod : gridResidue B e z.2.1 z.2.2=s := by
    rw [←normalizedGrid_mod B e z.1 z.2.1 z.2.2]
    change (monomialDegree B e z : ZMod (routingA B e))=s
    rw [hz.2]
    have haMod := (routingH B e).asRelativeIdeal.aperyRepresentative_mod (routingA B e) s
    change (physicalAlpha B e s : ZMod (routingA B e))=s at haMod
    rw [hax] at haMod
    exact_mod_cast haMod
  refine ⟨z.2.1,z.2.2,hz.1,?_⟩
  have hc := herzogLShapeCanonicality B e HD _ _ hz.1
  change (normalizedGrid B e 0 z.2.1 z.2.2 : ℤ)=physicalAlpha B e (gridResidue B e z.2.1 z.2.2) at hc
  rw [hmod] at hc
  exact hc.symm

theorem physicalAlpha_zero (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    physicalAlpha B e 0=0 := by
  have h := L5A2C4OR5.H0_isCanonicalTailGridPoint B e
  simpa [IsCanonicalTailGridPoint,normalizedGrid,gridResidue] using h.symm

theorem origin_candidate_sum (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (n i j d u v : ℕ)
    (hpre : n*routingM B e+d*routingA B e=i*routingB B e+j*routingC B e)
    (hinv : physicalAlpha B e (-(n*routingM B e : ℕ))=(normalizedGrid B e 0 u v : ℤ)) :
    (normalizedGrid B e 0 (i+u) (j+v) : ℤ)=
      (routingA B e : ℤ)*(rawCandidate B e n 0+(d : ℤ)) := by
  have hs := rawCandidate_spec B e n 0
  change (n : ℤ)*routingM B e+physicalAlpha B e (0-(n*routingM B e : ℕ))-
    physicalAlpha B e 0 = (routingA B e : ℤ)*rawCandidate B e n 0 at hs
  simp only [zero_sub,physicalAlpha_zero,sub_zero,hinv] at hs
  have heq : (n : ℤ)*routingM B e+(d : ℤ)*routingA B e=
      (i : ℤ)*routingB B e+(j : ℤ)*routingC B e := by exact_mod_cast hpre
  simp only [normalizedGrid,zero_mul,zero_add,Nat.add_mul] at hs ⊢
  push_cast at hs heq ⊢
  nlinarith only [hs,heq]

/-- A residue-zero canonical bottom is the origin. This uses actual Apéry canonicality. -/
theorem canonical_zero_residue (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {i j : ℕ}
    (hd : HerzogLShapeDomain HD i j) (hr : gridResidue B e i j=0) : i=0 ∧ j=0 := by
  have h := herzogLShapeCanonicality B e HD i j hd
  change (normalizedGrid B e 0 i j : ℤ)=physicalAlpha B e (gridResidue B e i j) at h
  rw [hr,physicalAlpha_zero] at h
  have hb := routingB_positive B e
  have hc := routingC_positive B e
  have hz : normalizedGrid B e 0 i j=0 := by exact_mod_cast h
  simp only [normalizedGrid,zero_mul,zero_add] at hz
  constructor
  · nlinarith
  · nlinarith

theorem preprincipal_origin_carry_bounds (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (n i j d : ℕ)
    (hi : 0 < i) (hj : 0 < j)
    (heq : n*routingM B e+d*routingA B e=i*routingB B e+j*routingC B e) :
    (c1 B e : ℤ)-(d : ℤ) ≤ rawCandidate B e n 0 ∧
      (cr12 HD < i → (c1 B e : ℤ)+cr21 HD-(d : ℤ) ≤ rawCandidate B e n 0) ∧
      (cr13 HD < j → (c1 B e : ℤ)+cr31 HD-(d : ℤ) ≤ rawCandidate B e n 0) := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  obtain ⟨u,v,_huv,hinv⟩ := inverse_apery_coordinate B e HD n
  have hsum := origin_candidate_sum B e n i j d u v heq hinv
  obtain ⟨z,path,hdom,hdeg⟩ := rewrite_normalizes B e HD (0,i+u,j+v)
  have hzsum : (monomialDegree B e z : ℤ)=(routingA B e : ℤ)*(rawCandidate B e n 0+(d : ℤ)) := by
    rw [←hdeg]
    exact hsum
  have hzres : gridResidue B e z.2.1 z.2.2=0 := by
    rw [←normalizedGrid_mod B e z.1 z.2.1 z.2.2]
    have hmod := congrArg (fun t : ℤ => (t : ZMod (routingA B e))) hzsum
    simp only [Int.cast_mul,Int.cast_add,Int.cast_natCast,ZMod.natCast_self,zero_mul] at hmod
    exact hmod
  obtain ⟨hzi,hzj⟩ := canonical_zero_residue B e HD hdom hzres
  obtain ⟨A,N,D,hr,hb,hc⟩ := rewrite_counts B e HD path
  simp only [Prod.fst,Prod.snd,zero_add,hzi,hzj] at hr hb hc
  have hp := coherent_coefficients_positive B e HD
  have hcoef := coherent_coefficients B e HD
  rw [hcoef.2.1] at hb
  rw [hcoef.2.2] at hc
  have hbounds := carry_bounds (cr12 HD) (cr13 HD) (cr32 HD) (cr23 HD)
    (cr21 HD) (cr31 HD) A N D (i+u) (j+v) hp.2.2.1 hp.2.2.2.2.1 hp.2.2.2.2.2 hp.2.2.2.1
    (by omega) (by omega) hb hc
  have hcarry : (z.1 : ℤ)=rawCandidate B e n 0+(d : ℤ) := by
    simp only [monomialDegree,normalizedGrid,hzi,hzj,zero_mul,add_zero] at hzsum
    rw [Nat.cast_mul] at hzsum
    have ha : (0 : ℤ)<routingA B e := by exact_mod_cast routingA_pos B e
    nlinarith only [hzsum,ha]
  rw [←hcoef.1] at hbounds
  have h0 : c1 B e ≤ z.1 := by rw [hr]; exact hbounds.1
  have hB : cr12 HD < i → c1 B e+cr21 HD ≤ z.1 := by
    intro h
    rw [hr]
    exact hbounds.2.1 (by omega)
  have hC : cr13 HD < j → c1 B e+cr31 HD ≤ z.1 := by
    intro h
    rw [hr]
    exact hbounds.2.2 (by omega)
  refine ⟨?_,?_,?_⟩
  · have h : (c1 B e : ℤ) ≤ z.1 := by exact_mod_cast h0
    omega
  · intro hi'
    have h : (c1 B e : ℤ)+cr21 HD ≤ z.1 := by exact_mod_cast hB hi'
    omega
  · intro hj'
    have h : (c1 B e : ℤ)+cr31 HD ≤ z.1 := by exact_mod_cast hC hj'
    omega

/-- T8 at the actual preprincipal return, with G2/G3 recovered from this same role packet. -/
theorem actual_origin_carry_bounds {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    {n : ℕ} (hnpos : 0 < n)
    (hpre : n < firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e) (routingM_pos P.M.base R.e)) :
    ∃ i j d : ℕ, HerzogLShapeDomain R.HD i j ∧ 0 < d ∧
      n*routingM P.M.base R.e+d*routingA P.M.base R.e=i*routingB P.M.base R.e+j*routingC P.M.base R.e ∧
      (c1 P.M.base R.e : ℤ)-(d : ℤ) ≤ rawCandidate P.M.base R.e n 0 ∧
      (cr12 R.HD < i → (c1 P.M.base R.e : ℤ)+cr21 R.HD-(d : ℤ) ≤ rawCandidate P.M.base R.e n 0) ∧
      (cr13 R.HD < j → (c1 P.M.base R.e : ℤ)+cr31 R.HD-(d : ℤ) ≤ rawCandidate P.M.base R.e n 0) := by
  obtain ⟨i,j,d,hdom,hd,heq⟩ := preprincipal_canonical_negative_height P.M.base R.e R.HD hnpos hpre
  have hgate := normalized_mixed_notch_G0_G4 R hm hn
  have hpos := preprincipal_positive_depth_bounds P.M.base R.e R.HD hnpos hdom hd heq
    hgate.2.2.1 hgate.2.2.2.1
  exact ⟨i,j,d,hdom,hd,heq,preprincipal_origin_carry_bounds P.M.base R.e R.HD n i j d hpos.1 hpos.2.1 heq⟩

private theorem low_axis_generator_is_pureX (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (hP : FullySupported (principalVector B e HD))
    {g : Monomial} (hg : g ∈ canonicalIdealGenerators B e HD)
    (hi : g.2.1 ≤ cr32 HD) (hj : g.2.2=0) (hr : g.1 ≤ cr31 HD) : g.2.1=0 := by
  have hp := coherent_coefficients_positive B e HD
  have hs := coherent_coefficients B e HD
  rcases hg with rfl | hcolon | hprincipal
  · rfl
  · obtain ⟨n,i,j,d,_,_,_,_,hcases,hg⟩ := hcolon
    rcases hcases with hc | hc | hc
    · simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_left hc.2.2.2.1,Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
    · simp only [colonMonomials,ite_eq_left hc.2.1,ite_eq_right (by omega : ¬j<cr13 HD),Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
    · simp only [colonMonomials,ite_eq_right (by omega : ¬i<cr12 HD),Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega
  · obtain ⟨delta,U,V,hdom,hdegree,hg⟩ := hprincipal
    have hspec := principalVector_spec B e HD
    have heq : principalVector B e HD=(delta,U,V) :=
      canonical_monomial_unique B e HD hspec.1 hdom (hspec.2.trans hdegree)
    rw [heq] at hP
    change 0<delta ∧ 0<U ∧ 0<V at hP
    rcases hg with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega

private theorem low_axis_cut_origin_cap {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hP : FullySupported (principalVector P.M.base R.e R.HD))
    (r i : ℕ) (hi : i ≤ cr32 R.HD) (hr : r ≤ cr31 R.HD)
    (hx : (r,i,0) ∈ monomialClosure (chartGenerators P.M.base R.e R.HD)) : H0 P.M.base R.e ≤ r := by
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  obtain ⟨g,hg,hgr,hgi,hgj⟩ := hx
  simp only [Prod.fst,Prod.snd] at hgr hgi hgj
  have gj : g.2.2=0 := by omega
  rcases hg with hg | hg
  · have gi := low_axis_generator_is_pureX P.M.base R.e R.HD hP hg (hgi.trans hi) gj (hgr.trans hr)
    have heq : g=(g.1,0,0) := Prod.ext rfl (Prod.ext gi gj)
    have hcut := canonicalIdealGenerators_degree_mem_cut P.M.base R.e R.HD hg
    rw [heq] at hcut
    have hI := (actual_cyclicCut_iff_routingI P.M.base R.e _).mp hcut
    have heta := (normalizedGrid_mem_iff_eta_le P.M.base R.e g.1 0 0).mp hI
    change H0 P.M.base R.e ≤ g.1 at heta
    exact heta.trans hgr
  · rcases hg with rfl | rfl | rfl <;> simp only [Prod.fst,Prod.snd] at * <;> omega

/-- The first T9 step is derived from the actual G4 cuts and the complete T3/P/PB/PC list. -/
theorem actual_interior_principal_origin_cap {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    (hiota : principal_iota P.M.base R.e R.HD=1) : H0 P.M.base R.e ≤ cr31 R.HD := by
  classical
  have hP : FullySupported (principalVector P.M.base R.e R.HD) := by
    unfold principal_iota at hiota
    split_ifs at hiota with h
    · exact h
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hgate := normalized_mixed_notch_G0_G4 R hm hn
  rcases hgate.2.2.2.2 with h | h
  · have hd : HerzogLShapeDomain R.HD (cr32 R.HD) 0 := ⟨by omega,by omega,Or.inr hp.2.1⟩
    have hx := (chart_threshold_iff R hm hn (eta P.M.base R.e (cr32 R.HD) 0) _ _ hd).mpr le_rfl
    exact (low_axis_cut_origin_cap R hP _ _ le_rfl (by omega) hx).trans (by omega)
  · have hd : HerzogLShapeDomain R.HD (cr32 R.HD-1) 0 := ⟨by omega,by omega,Or.inr hp.2.1⟩
    have hx := (chart_threshold_iff R hm hn (eta P.M.base R.e (cr32 R.HD-1) 0) _ _ hd).mpr le_rfl
    exact (low_axis_cut_origin_cap R hP _ _ (by omega) h hx).trans h

end NS25Lean.L5A2C4OR25
