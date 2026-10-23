import NS25Lean.P2SectorCM6InitialSocleR34

set_option linter.style.header false
set_option linter.style.whitespace false
noncomputable section
namespace NS25Lean.L5A2C4OR35
open L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20
  L5A2C4OR21 L5A2C4OR22 L5A2C4OR23 L5A2C4OR29 L5A2C4OR32 L5A2C4OR33
  FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

def borderExceptional (R : ActualRolePacket P) : Set Monomial :=
  {z | MonomialSocle (initialGenerators R) z ∧
    z.2.1+1=c2 P.M.base R.e ∧
    sourceWrap R z ∉ monomialClosure (M4Generators R)}

def StandardStrip (R : ActualRolePacket P) (z : Monomial) : Prop :=
  z.2.1<c2 P.M.base R.e ∧ z ∉ monomialClosure (M4Generators R)

theorem initial_mem_iff (R : ActualRolePacket P) (z : Monomial) :
    z ∈ monomialClosure (initialGenerators R) ↔
      c2 P.M.base R.e≤z.2.1 ∨ z ∈ monomialClosure (M4Generators R) := by
  constructor
  · rintro ⟨g,hg,hr,hi,hj⟩
    rcases hg with rfl | hg
    · exact Or.inl hi
    · exact Or.inr ⟨g,hg,hr,hi,hj⟩
  · rintro (hy | hz)
    · exact ⟨(0,c2 P.M.base R.e,0),Or.inl rfl,Nat.zero_le _,hy,Nat.zero_le _⟩
    · obtain ⟨g,hg,hr,hi,hj⟩ := hz
      exact ⟨g,Or.inr hg,hr,hi,hj⟩

theorem standardStrip_iff (R : ActualRolePacket P) (z : Monomial) :
    StandardStrip R z ↔ z ∉ monomialClosure (initialGenerators R) := by
  rw [initial_mem_iff]
  exact ⟨fun h => not_or.mpr ⟨Nat.not_le_of_lt h.1,h.2⟩,
    fun h => ⟨by have := (not_or.mp h).1; omega,(not_or.mp h).2⟩⟩

theorem role_monomial_mem_iff_cut (k : Type*) [Field k] (R : ActualRolePacket P)
    (z : Monomial) :
    roleMonomial k R.e z ∈ P.M.base.J k ↔
      monomialDegree P.M.base R.e z ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
  rw [roleMonomial,ChosenBase.Data.J_eq_comap_tail]
  change ToricPresentation.toricMap k P.M.base.H P.M.base.tailDegrees
      (MvPolynomial.monomial (roleExponent R.e z) 1) ∈
      ToricPresentation.tailMonomialIdeal k Gamma.toAddSubmonoid P.M.base.H P.M.base.q.val ↔ _
  rw [ChosenBase.Data.tailMap_monomial,
    ToricPresentation.single_mem_tailMonomialIdeal_iff k _ _ _ P.M.base.H_le,
    ←L2B.weight_eq_degree,roleExponent_weight]
  exact (actual_scaled_cut_iff P.M.base R.e _).symm

theorem normal_mem_iff_cut (R : ActualRolePacket P) (z : Monomial) :
    f2Normal P.M.base R.e R.HD z ∈ monomialClosure (M4Generators R) ↔
      monomialDegree P.M.base R.e z ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
  rw [←source_initial_normal_strip R ℚ _ (f2Normal_y_lt _ _ _ _),
    role_monomial_mem_iff_cut,f2Normal_degree]

theorem strip_mem_iff_cut (R : ActualRolePacket P) (z : Monomial)
    (hy : z.2.1<c2 P.M.base R.e) :
    z ∈ monomialClosure (M4Generators R) ↔
      monomialDegree P.M.base R.e z ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
  simpa only [normal_strip_fixed R z hy] using normal_mem_iff_cut R z

/-- Arbitrary polynomial, arbitrary field: no extra linear strip relation. -/
theorem standard_polynomial_no_relation (k : Type*) [Field k] (R : ActualRolePacket P)
    (f : ToricPresentation.Poly k 3)
    (hs : ∀ d ∈ f.support, StandardStrip R (roleCoordinates R.e d))
    (hf : f ∈ P.M.base.J k) : f=0 := by
  have hn := actual_normalForm_supported k R hf
  rw [linearNormalForm_fixed_of_strip_support k R f (fun d hd => (hs d hd).1)] at hn
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_zero]
  by_contra hc
  have hd := MvPolynomial.mem_support_iff.mpr hc
  exact (hs d hd).2 (hn hd)

theorem standard_degree_injective (R : ActualRolePacket P) {z w : Monomial}
    (hz : StandardStrip R z) (hw : StandardStrip R w)
    (he : monomialDegree P.M.base R.e z=monomialDegree P.M.base R.e w) : z=w := by
  classical
  by_contra hzw
  have heq := equal_degree_quotient_relation ℚ R he
  have hj : roleMonomial ℚ R.e z-roleMonomial ℚ R.e w ∈ P.M.base.J ℚ := by
    rw [←actual_source_quotient_eq ℚ R]
    exact Ideal.Quotient.eq.mp heq
  have hexp : roleExponent R.e z≠roleExponent R.e w := by
    intro h
    apply hzw
    simpa only [roleCoordinates_exponent] using congrArg (roleCoordinates R.e) h
  have hf : roleMonomial ℚ R.e z-roleMonomial ℚ R.e w=0 :=
    standard_polynomial_no_relation ℚ R _ (by
      intro d hd
      have hc := MvPolynomial.mem_support_iff.mp hd
      by_cases hdZ : roleExponent R.e z=d
      · subst d; simpa only [roleCoordinates_exponent] using hz
      · have hdW : roleExponent R.e w=d := by
          by_contra h
          simp [roleMonomial,MvPolynomial.coeff_sub,hdZ,h] at hc
        subst d; simpa only [roleCoordinates_exponent] using hw) hj
  have hc := congrArg (MvPolynomial.coeff (roleExponent R.e z)) hf
  simp [roleMonomial,MvPolynomial.coeff_sub,Ne.symm hexp] at hc

theorem standard_degree_surjective (R : ActualRolePacket P) {x : ℕ}
    (hx : x ∈ routingH P.M.base R.e)
    (hk : x ∉ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) :
    ∃ z, StandardStrip R z ∧ monomialDegree P.M.base R.e z=x := by
  obtain ⟨r,i,j,he⟩ := L5A2C4OR6.routingH_factorization P.M.base R.e hx
  refine ⟨f2Normal P.M.base R.e R.HD (r,i,j),⟨f2Normal_y_lt _ _ _ _,?_⟩,?_⟩
  · intro hm
    apply hk
    simpa only [monomialDegree,normalizedGrid,←he] using (normal_mem_iff_cut R (r,i,j)).mp hm
  · rw [f2Normal_degree]
    exact he.symm

theorem strip_initial_mem_iff (R : ActualRolePacket P) (z : Monomial)
    (hy : z.2.1<c2 P.M.base R.e) :
    z ∈ monomialClosure (initialGenerators R) ↔ z ∈ monomialClosure (M4Generators R) := by
  rw [initial_mem_iff]
  simp only [Nat.not_le.mpr hy,false_or]

theorem top_y_normal (R : ActualRolePacket P) (z : Monomial)
    (hy : z.2.1+1=c2 P.M.base R.e) :
    f2Normal P.M.base R.e R.HD (z.1,z.2.1+1,z.2.2)=sourceWrap R z := by
  have hC : 0<c2 P.M.base R.e := herzogC_positive P.M.base R.e 1
  simp [f2Normal,sourceWrap,hy,Nat.div_self hC]

def TrueStripSocle (R : ActualRolePacket P) (z : Monomial) : Prop :=
  StandardStrip R z ∧
    f2Normal P.M.base R.e R.HD (z.1+1,z.2.1,z.2.2) ∈ monomialClosure (M4Generators R) ∧
    f2Normal P.M.base R.e R.HD (z.1,z.2.1+1,z.2.2) ∈ monomialClosure (M4Generators R) ∧
    f2Normal P.M.base R.e R.HD (z.1,z.2.1,z.2.2+1) ∈ monomialClosure (M4Generators R)

theorem trueStripSocle_iff_border_complement (R : ActualRolePacket P) (z : Monomial) :
    TrueStripSocle R z ↔
      MonomialSocle (initialGenerators R) z ∧ z ∉ borderExceptional R := by
  constructor
  · rintro ⟨hs,hx,hy,hz⟩
    rw [normal_strip_fixed R (z.1+1,z.2.1,z.2.2) hs.1] at hx
    rw [normal_strip_fixed R (z.1,z.2.1,z.2.2+1) hs.1] at hz
    have hx' := (strip_initial_mem_iff R (z.1+1,z.2.1,z.2.2) hs.1).mpr hx
    have hz' := (strip_initial_mem_iff R (z.1,z.2.1,z.2.2+1) hs.1).mpr hz
    have hy' : (z.1,z.2.1+1,z.2.2) ∈ monomialClosure (initialGenerators R) := by
      by_cases ht : z.2.1+1<c2 P.M.base R.e
      · rw [normal_strip_fixed R _ ht] at hy
        exact (strip_initial_mem_iff R _ ht).mpr hy
      · exact (initial_mem_iff R _).mpr (Or.inl (by simpa using (show c2 P.M.base R.e≤z.2.1+1 by omega)))
    refine ⟨⟨(standardStrip_iff R z).mp hs,hx',hy',hz'⟩,?_⟩
    rintro ⟨_,ht,hn⟩
    rw [top_y_normal R z ht] at hy
    exact hn hy
  · rintro ⟨⟨hn,hx,hy,hz⟩,he⟩
    have hs := (standardStrip_iff R z).mpr hn
    refine ⟨hs,?_,?_,?_⟩
    · rw [normal_strip_fixed R (z.1+1,z.2.1,z.2.2) hs.1]
      exact (strip_initial_mem_iff R (z.1+1,z.2.1,z.2.2) hs.1).mp hx
    · by_cases ht : z.2.1+1<c2 P.M.base R.e
      · rw [normal_strip_fixed R _ ht]
        exact (strip_initial_mem_iff R _ ht).mp hy
      · have htop : z.2.1+1=c2 P.M.base R.e := by have := hs.1; omega
        rw [top_y_normal R z htop]
        by_contra hw
        exact he ⟨⟨hn,hx,hy,hz⟩,htop,hw⟩
    · rw [normal_strip_fixed R (z.1,z.2.1,z.2.2+1) hs.1]
      exact (strip_initial_mem_iff R (z.1,z.2.1,z.2.2+1) hs.1).mp hz

theorem normalized_grid_mem (R : ActualRolePacket P) (z : Monomial) :
    monomialDegree P.M.base R.e z ∈ routingH P.M.base R.e :=
  (mem_generatedThree_iff _ _ _ _).mpr ⟨z.1,z.2.1,z.2.2,rfl⟩

theorem cut_add_tail {H : NumericalSemigroup} {m x h : ℕ}
    (hx : x ∈ cyclicCut H m) (hh : h ∈ H) : x+h ∈ cyclicCut H m := by
  obtain ⟨hxH,n,hn,t,ht,he⟩ := hx
  exact ⟨H.toAddSubmonoid.add_mem hxH hh,n,hn,t+h,
    H.toAddSubmonoid.add_mem ht hh,by omega⟩

/-- Three actual variable tests suffice for the full H-order socle. -/
theorem modelTop_iff_three_steps (R : ActualRolePacket P) (x : ℕ) :
    ModelTop P.M.base R.e x ↔
      x ∈ routingH P.M.base R.e ∧
      x ∉ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) ∧
      x+routingA P.M.base R.e ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) ∧
      x+routingB P.M.base R.e ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) ∧
      x+routingC P.M.base R.e ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
  have ha : routingA P.M.base R.e ∈ routingH P.M.base R.e := by
    simpa [monomialDegree,normalizedGrid] using normalized_grid_mem R (1,0,0)
  have hb : routingB P.M.base R.e ∈ routingH P.M.base R.e := by
    simpa [monomialDegree,normalizedGrid] using normalized_grid_mem R (0,1,0)
  have hc : routingC P.M.base R.e ∈ routingH P.M.base R.e := by
    simpa [monomialDegree,normalizedGrid] using normalized_grid_mem R (0,0,1)
  constructor
  · rintro ⟨hx,hn,hh⟩
    exact ⟨hx,hn,hh _ ha (routingA_pos _ _).ne',
      hh _ hb (routingB_positive _ _).ne',hh _ hc (routingC_positive _ _).ne'⟩
  · rintro ⟨hx,hn,hA,hB,hC⟩
    refine ⟨hx,hn,?_⟩
    intro h hh h0
    obtain ⟨r,i,j,he⟩ := L5A2C4OR6.routingH_factorization P.M.base R.e hh
    cases r with
    | succ r =>
      have ht := cut_add_tail hA (normalized_grid_mem R (r,i,j))
      convert ht using 1 <;> simp [monomialDegree,normalizedGrid,he,Nat.succ_mul] <;> ring
    | zero =>
      cases i with
      | succ i =>
        have ht := cut_add_tail hB (normalized_grid_mem R (0,i,j))
        convert ht using 1 <;> simp [monomialDegree,normalizedGrid,he,Nat.succ_mul] <;> ring
      | zero =>
        cases j with
        | zero => exact (h0 (by simpa using he)).elim
        | succ j =>
          have ht := cut_add_tail hC (normalized_grid_mem R (0,0,j))
          convert ht using 1 <;> simp [monomialDegree,normalizedGrid,he,Nat.succ_mul] <;> ring

theorem trueStripSocle_iff_modelTop (R : ActualRolePacket P) (z : Monomial)
    (hs : StandardStrip R z) :
    TrueStripSocle R z ↔ ModelTop P.M.base R.e (monomialDegree P.M.base R.e z) := by
  have hn : monomialDegree P.M.base R.e z ∉ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) :=
    fun h => hs.2 ((strip_mem_iff_cut R z hs.1).mpr h)
  rw [TrueStripSocle,modelTop_iff_three_steps,normal_mem_iff_cut,normal_mem_iff_cut,normal_mem_iff_cut]
  have hx : monomialDegree P.M.base R.e (z.1+1,z.2.1,z.2.2)=monomialDegree P.M.base R.e z+routingA P.M.base R.e := by
    simp [monomialDegree,normalizedGrid]; ring
  have hy : monomialDegree P.M.base R.e (z.1,z.2.1+1,z.2.2)=monomialDegree P.M.base R.e z+routingB P.M.base R.e := by
    simp [monomialDegree,normalizedGrid]; ring
  have hz : monomialDegree P.M.base R.e (z.1,z.2.1,z.2.2+1)=monomialDegree P.M.base R.e z+routingC P.M.base R.e := by
    simp [monomialDegree,normalizedGrid]; ring
  rw [hx,hy,hz]
  simp only [hs,hn,normalized_grid_mem,true_and,not_false_eq_true]

def trueSocleEquivModelTops (R : ActualRolePacket P) :
    {z // TrueStripSocle R z} ≃ ModelTops P.M.base R.e := by
  let f : {z // TrueStripSocle R z} → ModelTops P.M.base R.e :=
    fun z => ⟨monomialDegree P.M.base R.e z.val,
      (trueStripSocle_iff_modelTop R z.val z.property.1).mp z.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro z w he
    apply Subtype.ext
    exact standard_degree_injective R z.property.1 w.property.1 (congrArg Subtype.val he)
  · intro x
    obtain ⟨z,hs,he⟩ := standard_degree_surjective R x.property.1 x.property.2.1
    refine ⟨⟨z,(trueStripSocle_iff_modelTop R z hs).mpr (he.symm ▸ x.property)⟩,?_⟩
    exact Subtype.ext he

theorem actual_one_binomial_type_correction :
    ∀ {Gamma : NumericalSemigroup} {P : P2Data Gamma} (R : ActualRolePacket P),
      Gamma.asRelativeIdeal.idealType+Nat.card {z // z ∈ borderExceptional R}=
        Nat.card {z // MonomialSocle (initialGenerators R) z} := by
  intro Gamma P R
  have hsub : borderExceptional R ⊆ {z | MonomialSocle (initialGenerators R) z} := fun _ h => h.1
  obtain ⟨a,b,c,_,_,_,ha,hb,hc⟩ := initial_axes R
  have hfinite := monomialSocle_finite (initialGenerators R) a b c ha hb hc
  have he : {z // TrueStripSocle R z} ≃
      {z // z ∈ {z | MonomialSocle (initialGenerators R) z} \ borderExceptional R} :=
    L5A2C4OR34.predicateSubtypeEquiv (trueStripSocle_iff_border_complement R)
  have hcount := Nat.card_congr (trueSocleEquivModelTops R)
  rw [actual_model_top_count R] at hcount
  rw [←hcount,Nat.card_congr he]
  exact Set.ncard_sdiff_add_ncard_of_subset hsub hfinite

abbrev StandardSeats (R : ActualRolePacket P) := {z // StandardStrip R z}

def standardQuotientMonomial (k : Type*) [Field k] (R : ActualRolePacket P)
    (z : StandardSeats R) : ToricPresentation.Poly k 3 ⧸ P.M.base.J k :=
  Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z.val)

theorem roleExponent_injective (e : Fin 3 ≃ Fin 3) : Function.Injective (roleExponent e) := by
  intro z w h
  simpa only [roleCoordinates_exponent] using congrArg (roleCoordinates e) h

theorem standardQuotientMonomial_linearIndependent (k : Type*) [Field k]
    (R : ActualRolePacket P) : LinearIndependent k (standardQuotientMonomial k R) := by
  classical
  rw [linearIndependent_iff']
  intro s c he i hi
  let f : ToricPresentation.Poly k 3 := ∑ z ∈ s, c z • roleMonomial k R.e z.val
  have hf : f ∈ P.M.base.J k := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mkₐ k (P.M.base.J k) f=0
    simpa only [f,map_sum,map_smul,standardQuotientMonomial] using he
  have hs : ∀ d ∈ f.support, StandardStrip R (roleCoordinates R.e d) := by
    intro d hd
    by_contra hn
    have hzero : MvPolynomial.coeff d f=0 := by
      simp only [f,MvPolynomial.coeff_sum,MvPolynomial.coeff_smul]
      apply Finset.sum_eq_zero
      intro z hz
      have hne : roleExponent R.e z.val≠d := by
        intro h
        subst d
        exact hn (by simpa only [roleCoordinates_exponent] using z.property)
      simp [roleMonomial,hne]
    exact MvPolynomial.mem_support_iff.mp hd hzero
  have hzero := standard_polynomial_no_relation k R f hs hf
  have hcoeff : MvPolynomial.coeff (roleExponent R.e i.val) f=c i := by
    simp only [f,MvPolynomial.coeff_sum,MvPolynomial.coeff_smul]
    rw [Finset.sum_eq_single i]
    · simp [roleMonomial]
    · intro z hz hzi
      have hne : roleExponent R.e z.val≠roleExponent R.e i.val :=
        fun h => hzi (Subtype.ext (roleExponent_injective R.e h))
      simp [roleMonomial,hne]
    · exact fun h => (h hi).elim
  rw [hzero,MvPolynomial.coeff_zero] at hcoeff
  exact hcoeff.symm

theorem monicF2Ideal_le_actual (k : Type*) [Field k] (R : ActualRolePacket P) :
    monicF2Ideal k R ≤ P.M.base.J k := by
  rw [←actual_source_quotient_eq k R]
  apply Ideal.span_le.mpr
  rintro f rfl
  exact Ideal.subset_span (Or.inl (Or.inl rfl))

theorem quotient_role_normal (k : Type*) [Field k] (R : ActualRolePacket P) (z : Monomial) :
    Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z)=
      Ideal.Quotient.mkₐ k (P.M.base.J k)
        (roleMonomial k R.e (f2Normal P.M.base R.e R.HD z)) :=
  Ideal.Quotient.eq.mpr (monicF2Ideal_le_actual k R (monomial_normalForm_congr k R z))

theorem standardQuotientMonomial_spans (k : Type*) [Field k] (R : ActualRolePacket P) :
    Submodule.span k (Set.range (standardQuotientMonomial k R))=⊤ := by
  classical
  let W := Submodule.span k (Set.range (standardQuotientMonomial k R))
  have hm (z : Monomial) : Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z) ∈ W := by
    rw [quotient_role_normal]
    by_cases hn : f2Normal P.M.base R.e R.HD z ∈ monomialClosure (M4Generators R)
    · have hzero : Ideal.Quotient.mkₐ k (P.M.base.J k)
          (roleMonomial k R.e (f2Normal P.M.base R.e R.HD z))=0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (monomialClosure_mem_actual k R hn)
      rw [hzero]
      exact W.zero_mem
    · exact Submodule.subset_span ⟨⟨f2Normal P.M.base R.e R.HD z,
        f2Normal_y_lt _ _ _ _,hn⟩,rfl⟩
  apply top_unique
  intro q hq
  clear hq
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective q
  change Ideal.Quotient.mkₐ k (P.M.base.J k) f ∈ W
  induction f using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [scalar_role_monomial k R.e d c,map_smul]
    exact W.smul_mem c (hm _)
  | add f g hf hg =>
    rw [map_add]
    exact W.add_mem hf hg

/-- Literal standard-monomial basis of the ORIGINAL actual quotient, any field. -/
def actual_normalStripBasis (k : Type*) [Field k] (R : ActualRolePacket P) :
    Module.Basis (StandardSeats R) k (ToricPresentation.Poly k 3 ⧸ P.M.base.J k) :=
  Module.Basis.mk (standardQuotientMonomial_linearIndependent k R)
    (by rw [standardQuotientMonomial_spans])

@[simp] theorem actual_normalStripBasis_apply (k : Type*) [Field k] (R : ActualRolePacket P)
    (z : StandardSeats R) : actual_normalStripBasis k R z=standardQuotientMonomial k R z :=
  Module.Basis.mk_apply _ _ _

theorem normal_successor_injective (R : ActualRolePacket P) (t : Monomial)
    {z w : Monomial} (hz : StandardStrip R z) (hw : StandardStrip R w)
    (he : f2Normal P.M.base R.e R.HD (z+t)=f2Normal P.M.base R.e R.HD (w+t)) : z=w := by
  apply standard_degree_injective R hz hw
  have h := congrArg (monomialDegree P.M.base R.e) he
  rw [f2Normal_degree,f2Normal_degree,monomialDegree_add,monomialDegree_add] at h
  exact Nat.add_right_cancel h

theorem quotient_role_zero_iff_normal_mem (k : Type*) [Field k] (R : ActualRolePacket P)
    (z : Monomial) : Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z)=0 ↔
      f2Normal P.M.base R.e R.HD z ∈ monomialClosure (M4Generators R) := by
  change Ideal.Quotient.mk (P.M.base.J k) (roleMonomial k R.e z)=0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,role_monomial_mem_iff_cut,normal_mem_iff_cut]

theorem actual_M6_M7_bound (R : ActualRolePacket P) :
    Gamma.asRelativeIdeal.idealType+Nat.card {z // z ∈ borderExceptional R}+2 ≤
      P.sourceCount+2+survivingWrapCount R+
      Nat.card {s : ModelSources P.M.base R.e // FullySupported (sourceNormal R s)} := by
  rw [actual_one_binomial_type_correction]
  exact L5A2C4OR34.actual_initial_socle_source_bound R

theorem actual_product_normal (k : Type*) [Field k] (R : ActualRolePacket P)
    (z t : Monomial) :
    Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z)*
        Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e t)=
      Ideal.Quotient.mkₐ k (P.M.base.J k)
        (roleMonomial k R.e (f2Normal P.M.base R.e R.HD (z+t))) := by
  rw [←map_mul,←roleMonomial_add,quotient_role_normal]

theorem actual_product_zero_iff (k : Type*) [Field k] (R : ActualRolePacket P)
    (z t : Monomial) :
    Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z)*
        Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e t)=0 ↔
      f2Normal P.M.base R.e R.HD (z+t) ∈ monomialClosure (M4Generators R) := by
  rw [←map_mul,←roleMonomial_add,quotient_role_zero_iff_normal_mem]

/-- Individual basis socle tests in the original quotient, not initial y^C=0. -/
theorem trueStripSocle_iff_actual_annihilation (k : Type*) [Field k]
    (R : ActualRolePacket P) (z : Monomial) (hs : StandardStrip R z) :
    TrueStripSocle R z ↔
      (Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z)*
        Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e (1,0,0))=0) ∧
      (Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z)*
        Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e (0,1,0))=0) ∧
      (Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z)*
        Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e (0,0,1))=0) := by
  rw [actual_product_zero_iff,actual_product_zero_iff,actual_product_zero_iff]
  rcases z with ⟨x,y,z⟩
  simpa only [TrueStripSocle,hs,true_and,Prod.mk_add_mk,
    Prod.fst,Prod.snd,Nat.add_zero]

theorem action_coeff (k : Type*) [Field k] (R : ActualRolePacket P)
    (z i : StandardSeats R) (t : Monomial) :
    (actual_normalStripBasis k R).repr
      (standardQuotientMonomial k R z *
        Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e t)) i =
      if f2Normal P.M.base R.e R.HD (z.val+t)=i.val then 1 else 0 := by
  classical
  change (actual_normalStripBasis k R).repr
    (Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e z.val) * _) i = _
  rw [actual_product_normal]
  by_cases hn : f2Normal P.M.base R.e R.HD (z.val+t) ∈ monomialClosure (M4Generators R)
  · have he : Ideal.Quotient.mkₐ k (P.M.base.J k)
        (roleMonomial k R.e (f2Normal P.M.base R.e R.HD (z.val+t)))=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (monomialClosure_mem_actual k R hn)
    rw [he]
    have hne : f2Normal P.M.base R.e R.HD (z.val+t)≠i.val := by
      intro h; rw [h] at hn; exact i.property.2 hn
    simp [hne]
  · let n : StandardSeats R := ⟨_,f2Normal_y_lt _ _ _ _,hn⟩
    change (actual_normalStripBasis k R).repr (standardQuotientMonomial k R n) i = _
    rw [←actual_normalStripBasis_apply,Module.Basis.repr_self]
    simp only [Finsupp.single_apply]
    congr 1
    exact propext ⟨fun h => congrArg Subtype.val h,
      fun h => Subtype.ext h⟩

theorem actual_mul_zero_iff (k : Type*) [Field k] (R : ActualRolePacket P)
    (q : ToricPresentation.Poly k 3 ⧸ P.M.base.J k) (t : Monomial) :
    q * Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e t)=0 ↔
      ∀ z : StandardSeats R, (actual_normalStripBasis k R).repr q z≠0 →
        f2Normal P.M.base R.e R.HD (z.val+t) ∈ monomialClosure (M4Generators R) := by
  classical
  let b := actual_normalStripBasis k R
  let c := b.repr q
  have hsum : (∑ z ∈ c.support, c z • standardQuotientMonomial k R z)=q := by
    simpa only [b,c,Finsupp.linearCombination_apply,Finsupp.sum,actual_normalStripBasis_apply]
      using b.linearCombination_repr q
  constructor
  · intro h z hz
    by_contra hn
    let i : StandardSeats R := ⟨_,f2Normal_y_lt _ _ _ _,hn⟩
    have hc : b.repr (q * Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e t)) i=c z := by
      rw [←hsum,Finset.sum_mul]
      simp only [smul_mul_assoc,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
      change (∑ j ∈ c.support, c j *
        ((actual_normalStripBasis k R).repr
          (standardQuotientMonomial k R j * _) i))=c z
      simp_rw [action_coeff]
      rw [Finset.sum_eq_single z]
      · simp [i]
      · intro j hj hne
        have hh : f2Normal P.M.base R.e R.HD (j.val+t)≠i.val := by
          intro he
          exact hne (Subtype.ext (normal_successor_injective R t j.property z.property he))
        simp [hh]
      · intro hnot
        exact (hnot (Finsupp.mem_support_iff.mpr hz)).elim
    rw [h] at hc
    exact hz (by simpa using hc.symm)
  · intro h
    rw [←hsum,Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro z hz
    rw [smul_mul_assoc]
    have he : standardQuotientMonomial k R z *
        Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e t)=0 :=
      (actual_product_zero_iff k R z.val t).mpr (h z (Finsupp.mem_support_iff.mp hz))
    rw [he,smul_zero]

def ActualQuotientSocle (k : Type*) [Field k] (R : ActualRolePacket P) :
    Submodule k (ToricPresentation.Poly k 3 ⧸ P.M.base.J k) where
  carrier := {q | ∀ t ∈ ({(1,0,0),(0,1,0),(0,0,1)} : Set Monomial),
    q * Ideal.Quotient.mkₐ k (P.M.base.J k) (roleMonomial k R.e t)=0}
  zero_mem' := by simp
  add_mem' := by intro q q' h h' t ht; rw [add_mul,h t ht,h' t ht,add_zero]
  smul_mem' := by intro a q h t ht; rw [smul_mul_assoc,h t ht,smul_zero]

theorem actual_socle_iff_supported (k : Type*) [Field k] (R : ActualRolePacket P)
    (q : ToricPresentation.Poly k 3 ⧸ P.M.base.J k) :
    q ∈ ActualQuotientSocle k R ↔
      ∀ z : StandardSeats R, (actual_normalStripBasis k R).repr q z≠0 →
        TrueStripSocle R z.val := by
  constructor
  · intro h z hz
    rcases z with ⟨⟨x,y,z'⟩,hs⟩
    have hx := (actual_mul_zero_iff k R q (1,0,0)).mp (h _ (by simp)) ⟨(x,y,z'),hs⟩ hz
    have hy := (actual_mul_zero_iff k R q (0,1,0)).mp (h _ (by simp)) ⟨(x,y,z'),hs⟩ hz
    have hz' := (actual_mul_zero_iff k R q (0,0,1)).mp (h _ (by simp)) ⟨(x,y,z'),hs⟩ hz
    exact ⟨hs,by simpa using hx,by simpa using hy,by simpa using hz'⟩
  · intro h t ht
    apply (actual_mul_zero_iff k R q t).mpr
    intro z hz
    rcases z with ⟨⟨x,y,z'⟩,hs⟩
    have hh := h ⟨⟨x,y,z'⟩,hs⟩ hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl | rfl
    · simpa using hh.2.1
    · simpa using hh.2.2.1
    · simpa using hh.2.2.2

def trueSocleMonomial (k : Type*) [Field k] (R : ActualRolePacket P)
    (z : {z // TrueStripSocle R z}) : ToricPresentation.Poly k 3 ⧸ P.M.base.J k :=
  standardQuotientMonomial k R ⟨z.val,z.property.1⟩

theorem actual_socle_eq_span (k : Type*) [Field k] (R : ActualRolePacket P) :
    ActualQuotientSocle k R = Submodule.span k (Set.range (trueSocleMonomial k R)) := by
  classical
  apply le_antisymm
  · intro q hq
    have h := (actual_socle_iff_supported k R q).mp hq
    let b := actual_normalStripBasis k R
    rw [←b.linearCombination_repr q,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Submodule.sum_mem
    intro z hz
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨z.val,h z (Finsupp.mem_support_iff.mp hz)⟩,
      by simp [trueSocleMonomial,b]⟩
  · apply Submodule.span_le.mpr
    rintro q ⟨z,rfl⟩
    apply (actual_socle_iff_supported k R _).mpr
    intro w hw
    change (actual_normalStripBasis k R).repr
      (standardQuotientMonomial k R ⟨z.val,z.property.1⟩) w≠0 at hw
    rw [←actual_normalStripBasis_apply,Module.Basis.repr_self] at hw
    have he : (⟨z.val,z.property.1⟩ : StandardSeats R)=w := by
      by_contra hn; exact hw (by simp [Finsupp.single_apply,hn])
    rw [←he]
    exact z.property

theorem trueSocleMonomial_linearIndependent (k : Type*) [Field k]
    (R : ActualRolePacket P) : LinearIndependent k (trueSocleMonomial k R) := by
  apply (standardQuotientMonomial_linearIndependent k R).comp
    (fun z : {z // TrueStripSocle R z} => (⟨z.val,z.property.1⟩ : StandardSeats R))
  intro z w h
  exact Subtype.ext (congrArg (fun s : StandardSeats R => s.val) h)

def actual_socleBasis (k : Type*) [Field k] (R : ActualRolePacket P) :
    Module.Basis {z // TrueStripSocle R z} k (ActualQuotientSocle k R) := by
  rw [actual_socle_eq_span]
  exact Module.Basis.span (trueSocleMonomial_linearIndependent k R)

theorem actual_quotient_socle_dimension (k : Type*) [Field k] (R : ActualRolePacket P) :
    Module.finrank k (ActualQuotientSocle k R)=Gamma.asRelativeIdeal.idealType := by
  obtain ⟨a,b,c,_,_,_,ha,hb,hc⟩ := NS25Lean.L5A2C4OR33.initial_axes R
  haveI : Finite {z // MonomialSocle (initialGenerators R) z} :=
    (monomialSocle_finite (initialGenerators R) a b c ha hb hc).to_subtype
  haveI : Finite {z // TrueStripSocle R z} := by
    apply Finite.of_injective (fun z : {z // TrueStripSocle R z} =>
      (⟨z.val,(trueStripSocle_iff_border_complement R z.val).mp z.property |>.1⟩ :
        {z // MonomialSocle (initialGenerators R) z}))
    intro z w h
    exact Subtype.ext (congrArg (fun s : {z // MonomialSocle (initialGenerators R) z} => s.val) h)
  rw [Module.finrank_eq_nat_card_basis (actual_socleBasis k R)]
  rw [Nat.card_congr (trueSocleEquivModelTops R),actual_model_top_count R]

end NS25Lean.L5A2C4OR35
