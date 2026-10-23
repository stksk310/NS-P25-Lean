import NS25Lean.P2SectorCPureInternalFirstSourcePlaneR43

set_option linter.style.header false
set_option linter.style.whitespace false
set_option autoImplicit false
noncomputable section
namespace NS25Lean.L5A2C4OR44
open ChosenBase L2B L5A1 L5A2C3G L5A2B4AR4R1 L5A2B4AR4R2A L5A2B4AR5A
  L5A2C4C L5A2C4H L5A2C4OR1 L5A2C4OR19 L5A2C4OR20 L5A2C4OR22
  L5A2C4OR23 L5A2C4OR29 L5A2C4OR33 L5A2C4OR35 L5A2C4OR39 L5A2C4OR40
  L5A2C4OR41 L5A2C4OR42 L5A2C4OR43 FourGeneratedBridge
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

theorem pure_beta_pos (A : SectorBCriticalRoleBranchA P) : 0 < beta A := by
  have h := (branchA_symmetricTailData A).n1_pos
  rw [(branchA_symmetricTailData A).n1_eq] at h
  exact Nat.pos_of_ne_zero (fun hz => by simp [hz] at h)

theorem pureAlive_degree (A : SectorBCriticalRoleBranchA P) :
    monomialDegree P.M.base A.reindex (pureAlive A) = d A*routingC P.M.base A.reindex := by
  rw [pureAlive,pureNormal_degree]
  unfold pureAliveRaw
  split_ifs
  · simpa [monomialDegree,normalizedGrid,routingA_eq_n0,routingB_eq_n1,routingC_eq_n2]
      using (branchA_symmetricTailData A).mixed_relation.symm
  · simp [monomialDegree,normalizedGrid]

/-- A strict exponent deficit supplies the corresponding actual cut predecessor. -/
theorem cut_divisor_predecessors (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    {w g : Monomial} (h : Divides w g)
    (hw : monomialDegree B e w ∈ cyclicCut (routingH B e) (routingM B e)) :
    (w.1<g.1 → monomialDegree B e g-routingA B e ∈ cyclicCut (routingH B e) (routingM B e)) ∧
    (w.2.1<g.2.1 → monomialDegree B e g-routingB B e ∈ cyclicCut (routingH B e) (routingM B e)) ∧
    (w.2.2<g.2.2 → monomialDegree B e g-routingC B e ∈ cyclicCut (routingH B e) (routingM B e)) := by
  let t : Monomial := (g.1-w.1,g.2.1-w.2.1,g.2.2-w.2.2)
  have hd : monomialDegree B e g=monomialDegree B e w+monomialDegree B e t :=
    degree_divisor_reconstruct B e h
  have hp := monomial_positive_predecessors B e t
  refine ⟨?_,?_,?_⟩
  · intro hx
    obtain ⟨y,hy,he⟩ := hp.1 (by simp only [t]; omega)
    have hk := cut_add_tail hw hy
    convert hk using 1; omega
  · intro hx
    obtain ⟨y,hy,he⟩ := hp.2.1 (by simp only [t]; omega)
    have hk := cut_add_tail hw hy
    convert hk using 1; omega
  · intro hx
    obtain ⟨y,hy,he⟩ := hp.2.2 (by simp only [t]; omega)
    have hk := cut_add_tail hw hy
    convert hk using 1; omega

/-- Proper cut divisors would kill the selected alive component, even at canonical y=0. -/
theorem pureAlive_divisor_eq_of_cut (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) {w : Monomial}
    (h : Divides w (pureAlive A))
    (hw : monomialDegree P.M.base A.reindex w ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    w=pureAlive A := by
  classical
  have hp := cut_divisor_predecessors P.M.base A.reindex h hw
  rw [pureAlive_degree] at hp
  by_cases hpk : BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent
  · have hl : ¬BoundaryKilled P.M A.mixedDegree A.mixed.mixedComponent :=
      fun hm => boundary_not_both_killed A hk ⟨hpk,hm⟩
    have hab :
        d A*routingC P.M.base A.reindex-routingA P.M.base A.reindex ∉
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) ∧
        d A*routingC P.M.base A.reindex-routingB P.M.base A.reindex ∉
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
      constructor
      · intro hc
        apply hl
        exact (normalized_component_killed_iff _ P.M rfl _ (mixed_boundary_degree_scale A) _).mpr
          ⟨0,(mixed_support_first_two A).1,by simpa [roleWeight] using hc⟩
      · intro hc
        apply hl
        exact (normalized_component_killed_iff _ P.M rfl _ (mixed_boundary_degree_scale A) _).mpr
          ⟨1,(mixed_support_first_two A).2,by simpa [roleWeight] using hc⟩
    have hz : (pureAlive A).2.2=0 := by simp [pureAlive,pureAliveRaw,hpk,pureNormal]
    have hx : w.1=(pureAlive A).1 := by
      by_contra hn
      exact hab.1 (hp.1 (by have := h.1; omega))
    have hy : w.2.1=(pureAlive A).2.1 := by
      by_contra hn
      exact hab.2 (hp.2.1 (by have := h.2.1; omega))
    exact Prod.ext hx (Prod.ext hy (by have := h.2.2; omega))
  · have hg : pureAlive A=(0,0,d A) := by
      simp [pureAlive,pureAliveRaw,hpk,pureNormal]
    have hc : d A*routingC P.M.base A.reindex-routingC P.M.base A.reindex ∉
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
      intro hc
      apply hpk
      exact (normalized_component_killed_iff _ P.M rfl _ (mixed_boundary_degree_scale A) _).mpr
        ⟨2,by rw [A.mixed.pureSupport,←A.reindex_two]; simp,by simpa [roleWeight] using hc⟩
    rw [hg] at h ⊢
    have hz : w.2.2=d A := by
      by_contra hn
      apply hc
      apply hp.2.2
      rw [hg]
      have := h.2.2
      dsimp at this ⊢
      omega
    exact Prod.ext (by have := h.1; simpa using this) (Prod.ext
      (by have := h.2.1; simpa using this) hz)

theorem pureSource_divisor_eq (A : SectorBCriticalRoleBranchA P)
    (v : ModelSources P.M.base A.reindex) {w : Monomial}
    (h : Divides w (pureSourceNormal A v))
    (hw : monomialDegree P.M.base A.reindex w ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)) :
    w=pureSourceNormal A v := by
  have hr := degree_divisor_reconstruct P.M.base A.reindex h
  have hm := ((minimalTail_iff_literal _ _ _).mp v.property).2 _ _ hw
    (grid_mem_H _ _ _) ((pureSourceNormal_spec A v).1.symm.trans hr)
  apply degree_divisor_eq P.M.base A.reindex h
  omega

theorem pureStrip_cut (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) {w : Monomial}
    (hw : w∈pureStripGenerators A) :
    monomialDegree P.M.base A.reindex w ∈
      cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
  apply (pure_role_mem_iff_cut A ℚ w).mp
  exact pureStrip_mem_J A hk ℚ ⟨w,hw,le_rfl,le_rfl,le_rfl⟩

def pureRaw (A : SectorBCriticalRoleBranchA P) : Set Monomial :=
  {(0,alpha A,0)} ∪ pureOriginals A

theorem pureStrip_y_lt (A : SectorBCriticalRoleBranchA P) {g : Monomial}
    (hg : g∈pureStripGenerators A) : g.2.1<alpha A := by
  rcases hg with hg | ⟨w,hw,hy,rfl⟩
  · exact pureOriginals_y_lt A hg
  · simpa [pureWrap] using pure_alpha_pos A

theorem pure_initial_divisor_of_raw_eq (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) {w g : Monomial}
    (hg : g∈pureRaw A) (hw : w∈pureInitialGenerators A) (h : Divides w g) : w=g := by
  have hk : killedCount P.M A.mixedDegree=1 := by rw [hb]; exact G.boundarySignature.2
  rcases hg with rfl | (⟨v,rfl⟩ | rfl)
  · rcases hw with rfl | hw
    · rfl
    · have hwy := pureStrip_y_lt A hw
      have hx : w.1=0 := by have := h.1; simpa using this
      have hz : w.2.2=0 := by have := h.2.2; simpa using this
      have hc := pureStrip_cut A hk hw
      have hyK : w.2.1*routingB P.M.base A.reindex ∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
        simpa [monomialDegree,normalizedGrid,hx,hz] using hc
      have := (internal_axis_cut_bounds G A ha).2 w.2.1 hyK
      omega
  · rcases hw with rfl | hw
    · have hy := (pureSourceNormal_spec A v).2.1
      have hh := h.2.1
      dsimp at hh
      omega
    · exact pureSource_divisor_eq A v h (pureStrip_cut A hk hw)
  · rcases hw with rfl | hw
    · have hy := pureNormal_y_lt A (pureAliveRaw A)
      have hh := h.2.1
      change alpha A≤(pureAlive A).2.1 at hh
      change (pureAlive A).2.1<alpha A at hy
      omega
    · exact pureAlive_divisor_eq_of_cut A hk h (pureStrip_cut A hk hw)

/-- All raw S+2 elements survive in the WHOLE initial ideal, including every wrap. -/
theorem pure_raw_minimal (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) {g : Monomial} (hg : g∈pureRaw A) :
    PolynomialMinimal (pureInitialGenerators A) g := by
  have hi : g∈pureInitialGenerators A := by
    rcases hg with hg | hg
    · exact Or.inl hg
    · exact Or.inr (Or.inl hg)
  refine ⟨⟨g,hi,le_rfl,le_rfl,le_rfl⟩,?_⟩
  rintro z ⟨w,hw,hw1,hw2,hw3⟩ hz1 hz2 hz3
  have he := pure_initial_divisor_of_raw_eq G A ha hb hg hw
    ⟨hw1.trans hz1,hw2.trans hz2,hw3.trans hz3⟩
  subst w
  exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))

theorem pureAlive_not_source (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (hb : A.mixedDegree=G.boundaryDegree)
    (v : ModelSources P.M.base A.reindex) : pureAlive A≠pureSourceNormal A v := by
  intro he
  have hd : v.val=d A*routingC P.M.base A.reindex :=
    (pureSourceNormal_spec A v).1.symm.trans (he ▸ pureAlive_degree A)
  apply pure_source_boundary_divisor_impossible P G A.reindex v
    ((mixed_boundary_degree_scale A).trans hb) (routingH _ _).zero_mem
  simpa using hd

theorem pureWrap_degree_increment (A : SectorBCriticalRoleBranchA P) {g : Monomial}
    (hy : g.2.1<alpha A) :
    monomialDegree P.M.base A.reindex (pureWrap A g)=
      monomialDegree P.M.base A.reindex g+(alpha A-g.2.1)*routingB P.M.base A.reindex := by
  have hr := (branchA_symmetricTailData A).pure_relation
  rw [←routingA_eq_n0,←routingB_eq_n1] at hr
  have hm := congrArg (fun n => n*routingB P.M.base A.reindex)
    (Nat.sub_add_cancel (Nat.le_of_lt hy))
  simp only [pureWrap,monomialDegree,normalizedGrid,Nat.add_mul,zero_mul,add_zero] at hm ⊢
  nlinarith only [hr,hm]

/-- In particular source-wrap = alive is impossible: inverse F gives h-b in K.
The raw mixed component contains b even when its canonical y exponent is zero. -/
theorem source_wrap_not_divides_alive (A : SectorBCriticalRoleBranchA P)
    (hk : killedCount P.M A.mixedDegree=1) (v : ModelSources P.M.base A.reindex)
    (hy : 0<(pureSourceNormal A v).2.1)
    (h : Divides (pureWrap A (pureSourceNormal A v)) (pureAlive A)) : False := by
  classical
  have he := pureAlive_divisor_eq_of_cut A hk h
    (pureStrip_cut A hk (Or.inr ⟨pureSourceNormal A v,Or.inl ⟨v,rfl⟩,hy,rfl⟩))
  by_cases hpk : BoundaryKilled P.M A.mixedDegree A.mixed.pureComponent
  · have hl : ¬BoundaryKilled P.M A.mixedDegree A.mixed.mixedComponent :=
      fun hm => boundary_not_both_killed A hk ⟨hpk,hm⟩
    have hgy := (pureSourceNormal_spec A v).2.1
    have hd := pureWrap_degree_increment A hgy
    rw [he,pureAlive_degree,(pureSourceNormal_spec A v).1] at hd
    have hc := cut_add_tail v.property.1
      (grid_mem_H P.M.base A.reindex (0,alpha A-(pureSourceNormal A v).2.1-1,0))
    have hs := congrArg (fun n => n*routingB P.M.base A.reindex)
      (Nat.sub_add_cancel (by omega : 1≤alpha A-(pureSourceNormal A v).2.1))
    simp only [Nat.add_mul,one_mul] at hs
    have hpred : d A*routingC P.M.base A.reindex-routingB P.M.base A.reindex ∈
        cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
      convert hc using 1
      simp only [monomialDegree,normalizedGrid,zero_mul,zero_add,add_zero]
      omega
    apply hl
    exact (normalized_component_killed_iff _ P.M rfl _ (mixed_boundary_degree_scale A) _).mpr
      ⟨1,(mixed_support_first_two A).2,by simpa [roleWeight] using hpred⟩
  · have hx := congrArg (fun z : Monomial => z.1) he
    have hb := pure_beta_pos A
    have hg : pureAlive A=(0,0,d A) := by simp [pureAlive,pureAliveRaw,hpk,pureNormal]
    rw [hg] at hx
    change (pureSourceNormal A v).1+beta A=0 at hx
    omega

theorem pure_model_sources_finite (A : SectorBCriticalRoleBranchA P) :
    Finite (ModelSources P.M.base A.reindex) :=
  (Nat.card_pos_iff.mp (show 0<Nat.card (ModelSources P.M.base A.reindex) by
    rw [pure_model_source_count P A.reindex]
    exact chosenBase_sourceCount_pos P.M.base)).2

theorem pure_raw_finite (A : SectorBCriticalRoleBranchA P) : (pureRaw A).Finite := by
  let := pure_model_sources_finite A
  exact (Set.finite_singleton _).union ((Set.finite_range _).union (Set.finite_singleton _))

theorem pure_initial_finite (A : SectorBCriticalRoleBranchA P) : (pureInitialGenerators A).Finite := by
  let := pure_model_sources_finite A
  have ho : (pureOriginals A).Finite := (Set.finite_range _).union (Set.finite_singleton _)
  have hw : {w | ∃ g∈pureOriginals A, 0<g.2.1 ∧ w=pureWrap A g} ⊆
      pureWrap A '' pureOriginals A := by
    rintro w ⟨g,hg,_,rfl⟩
    exact ⟨g,hg,rfl⟩
  exact (Set.finite_singleton _).union (ho.union ((ho.image _).subset hw))

theorem pure_raw_card (G : SectorCActualFibers P) (A : SectorBCriticalRoleBranchA P)
    (hb : A.mixedDegree=G.boundaryDegree) : Nat.card (pureRaw A)=P.sourceCount+2 := by
  let := pure_model_sources_finite A
  have hsf : (Set.range (pureSourceNormal A)).Finite := Set.finite_range _
  have hy : (0,alpha A,0)∉Set.range (pureSourceNormal A) := by
    rintro ⟨v,hv⟩
    have hh := (pureSourceNormal_spec A v).2.1
    rw [hv] at hh
    dsimp at hh
    omega
  have hbns : pureAlive A∉Set.range (pureSourceNormal A) := by
    rintro ⟨v,hv⟩
    exact pureAlive_not_source G A hb v hv.symm
  have hbny : pureAlive A≠(0,alpha A,0) := by
    intro he
    have hh := pureNormal_y_lt A (pureAliveRaw A)
    change (pureAlive A).2.1<alpha A at hh
    rw [he] at hh
    dsimp at hh
    omega
  have he : pureRaw A=insert (0,alpha A,0) (insert (pureAlive A) (Set.range (pureSourceNormal A))) := by
    ext g
    simp only [pureRaw,pureOriginals,Set.mem_union,Set.mem_singleton_iff,Set.mem_insert_iff]
    tauto
  have hnot : (0,alpha A,0)∉insert (pureAlive A) (Set.range (pureSourceNormal A)) := by
    exact fun h => (Set.mem_insert_iff.mp h).elim (fun h => hbny h.symm) hy
  change (pureRaw A).ncard=P.sourceCount+2
  rw [he,Set.ncard_insert_of_notMem hnot (hsf.insert _),
    Set.ncard_insert_of_notMem hbns hsf,Set.ncard_range_of_injective (pureSourceNormal_injective A),
    pure_model_source_count]

theorem pure_trueMinima_partition (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) :
    {g | PolynomialMinimal (pureInitialGenerators A) g}=pureRaw A ∪ PureSurvivingWraps A := by
  ext g
  constructor
  · intro hg
    by_cases hr : g∈pureRaw A
    · exact Or.inl hr
    · exact Or.inr ⟨hg,hr⟩
  · rintro (hg | hg)
    · exact pure_raw_minimal G A ha hb hg
    · exact hg.1

theorem pure_polynomialMinimal_card_exact (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) :
    Nat.card {g // PolynomialMinimal (pureInitialGenerators A) g}=
      P.sourceCount+2+pureSurvivingWrapCount A := by
  have hd : Disjoint (pureRaw A) (PureSurvivingWraps A) :=
    Set.disjoint_left.mpr (fun _ hr hs => hs.2 hr)
  have hf : (PureSurvivingWraps A).Finite := (pure_initial_finite A).subset
    (fun _ hg => polynomialMinimal_mem_generator _ _ hg.1)
  change {g | PolynomialMinimal (pureInitialGenerators A) g}.ncard=
    P.sourceCount+2+(PureSurvivingWraps A).ncard
  rw [pure_trueMinima_partition G A ha hb,Set.ncard_union_eq hd (pure_raw_finite A) hf]
  have hc : (pureRaw A).ncard=P.sourceCount+2 := pure_raw_card G A hb
  rw [hc]

/-- Original arbitrary Gamma/P/G binder, with the same actual A throughout. -/
theorem internal_initial_minimal_budget (P : P2Data Gamma) (G : SectorCActualFibers P)
    (bp bm : boundaryComponents G) (hne : bp≠bm)
    (hp : IsPureBoundaryComponent G bp) (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,(componentSupport P.M.base G.internalDegree C).card=1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.internalDegree ∧ A.mixedDegree=G.boundaryDegree ∧
      Nat.card {g // PolynomialMinimal (pureInitialGenerators A) g}=
        P.sourceCount+2+pureSurvivingWrapCount A := by
  obtain ⟨A,ha,hb,_⟩ := internal_all_pure_geometry P G bp bm hne hp hm hi
  exact ⟨A,ha,hb,pure_polynomialMinimal_card_exact G A ha hb⟩

/-- Plane status is derived from actual originals; wraps retain y=0. -/
theorem pure_full_minima_empty (A : SectorBCriticalRoleBranchA P)
    (hs : ∀ v : ModelSources P.M.base A.reindex,
      (pureSourceNormal A v).1=0 ∨ (pureSourceNormal A v).2.1=0 ∨
        (pureSourceNormal A v).2.2=0) :
    Nat.card {g // PolynomialMinimal (pureInitialGenerators A) g ∧ FullySupported g}=0 := by
  let : IsEmpty {g // PolynomialMinimal (pureInitialGenerators A) g ∧ FullySupported g} := ⟨by
    rintro ⟨g,hmin,hfull⟩
    have hg := polynomialMinimal_mem_generator _ _ hmin
    rcases hg with rfl | (⟨v,rfl⟩ | rfl) | ⟨w,hw,hy,rfl⟩
    · simp [FullySupported] at hfull
    · rcases hs v with h | h | h <;> simp [FullySupported,h] at hfull
    · rcases pureAlive_z_or_y_zero A with h | h <;> simp [FullySupported,h] at hfull
    · simp [FullySupported,pureWrap] at hfull⟩
  exact Nat.card_of_isEmpty

theorem pure_initial_proper (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree) : (0,0,0)∉monomialClosure (pureInitialGenerators A) := by
  intro hz
  have he := (pure_raw_minimal G A ha hb (g := (0,alpha A,0)) (Or.inl rfl)).2
    (0,0,0) hz (by simp) (by simp) (by simp)
  have hh := congrArg (fun g : Monomial => g.2.1) he
  have hp := pure_alpha_pos A
  dsimp at hh
  omega

/-- B3 and generic T6, without using any C-M-specific counting theorem. -/
theorem pure_socle_source_budget (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree)
    (hs : ∀ v : ModelSources P.M.base A.reindex,
      (pureSourceNormal A v).1=0 ∨ (pureSourceNormal A v).2.1=0 ∨
        (pureSourceNormal A v).2.2=0) :
    Nat.card {z // MonomialSocle (pureInitialGenerators A) z}+2 ≤
      P.sourceCount+2+pureSurvivingWrapCount A := by
  have hk : killedCount P.M A.mixedDegree=1 := by rw [hb]; exact G.boundarySignature.2
  let F : Finset Monomial := (pure_initial_finite A).toFinset
  have hF : (F : Set Monomial)=pureInitialGenerators A := (pure_initial_finite A).coe_toFinset
  have hp : (0,0,0)∉monomialClosure (F : Set Monomial) := by
    rw [hF]; exact pure_initial_proper G A ha hb
  have haxes := pure_initial_axes A hk
  rw [←hF] at haxes
  have ht := L5A2C4OR24.abstract_monomial_socle_bound_general F hp haxes
  rw [hF,pure_polynomialMinimal_card_exact G A ha hb,pure_full_minima_empty A hs,add_zero] at ht
  exact ht

/-- Same actual A combines B2/B3/B4, generic socle budget and frozen actual correction.
B5 (E >= B), and hence the type bound, is NOT assumed or asserted. -/
theorem internal_minimal_and_corrected_socle_budget (P : P2Data Gamma)
    (G : SectorCActualFibers P) (bp bm : boundaryComponents G) (hne : bp≠bm)
    (hp : IsPureBoundaryComponent G bp) (hm : IsMixedBoundaryComponent G bm)
    (hi : ∀ C : internalComponents G,(componentSupport P.M.base G.internalDegree C).card=1) :
    ∃ A : SectorBCriticalRoleBranchA P,
      A.pairDegree=G.internalDegree ∧ A.mixedDegree=G.boundaryDegree ∧
      Nat.card {g // PolynomialMinimal (pureInitialGenerators A) g}=
        P.sourceCount+2+pureSurvivingWrapCount A ∧
      pureSurvivingWrapCount A≤1 ∧
      Gamma.asRelativeIdeal.idealType+Nat.card {z // z∈pureBorderExceptional A}≤
        P.sourceCount+pureSurvivingWrapCount A := by
  obtain ⟨A,ha,hb,hs⟩ := internal_first_source_shape P G bp bm hne hp hm hi
  have hk : killedCount P.M A.mixedDegree=1 := by rw [hb]; exact G.boundarySignature.2
  have hsoc := pure_socle_source_budget G A ha hb (all_source_plane_of_first_shape A hs)
  have hcorr := pure_one_binomial_type_correction A hk
  refine ⟨A,ha,hb,pure_polynomialMinimal_card_exact G A ha hb,
    pure_surviving_wrap_count_le_one A hk hs,?_⟩
  omega

/-- B5 entry: a genuine surviving wrap supplies its positive, least-x xy producer.
This does not yet assert existence of the exceptional socle corner. -/
theorem surviving_wrap_minimal_producer (G : SectorCActualFibers P)
    (A : SectorBCriticalRoleBranchA P) (ha : A.pairDegree=G.internalDegree)
    (hb : A.mixedDegree=G.boundaryDegree)
    (hs : ∀ v : ModelSources P.M.base A.reindex,
      v.val=firstPrincipal (routingH P.M.base A.reindex) (routingM P.M.base A.reindex)
        (routingM_pos _ _)*routingM P.M.base A.reindex →
      ((pureSourceNormal A v).1=0 ∧ (pureSourceNormal A v).2.1=0) ∨
        (pureSourceNormal A v).2.2=0)
    {w : Monomial} (hw : w∈PureSurvivingWraps A) :
    ∃ g∈pureOriginals A, 0<g.1 ∧ 0<g.2.1 ∧ g.2.2=0 ∧ w=pureWrap A g ∧
      ∀ t∈pureOriginals A, 0<t.2.1 → t.2.2=0 → g.1≤t.1 := by
  have hk : killedCount P.M A.mixedDegree=1 := by rw [hb]; exact G.boundarySignature.2
  have haxes := surviving_wrap_axes A hk hs hw
  have hgen := polynomialMinimal_mem_generator _ _ hw.1
  rcases hgen with hlead | horig | ⟨g,hg,hgy,rfl⟩
  · exact (hw.2 (Or.inl hlead)).elim
  · exact (hw.2 (Or.inr horig)).elim
  · have hgz : g.2.2=0 := haxes.2
    have hgx : 0<g.1 := by
      by_contra hn
      have hx0 : g.1=0 := by omega
      have hc := pureStrip_cut A hk (Or.inl hg)
      have hyK : g.2.1*routingB P.M.base A.reindex∈
          cyclicCut (routingH P.M.base A.reindex) (routingM P.M.base A.reindex) := by
        simpa [monomialDegree,normalizedGrid,hx0,hgz] using hc
      have hbound := (internal_axis_cut_bounds G A ha).2 g.2.1 hyK
      have hlt := pureOriginals_y_lt A hg
      omega
    refine ⟨g,hg,hgx,hgy,hgz,rfl,?_⟩
    intro t ht hty htz
    by_contra hn
    have htwrap : pureWrap A t∈monomialClosure (pureInitialGenerators A) :=
      ⟨pureWrap A t,Or.inr (Or.inr ⟨t,ht,hty,rfl⟩),le_rfl,le_rfl,le_rfl⟩
    have he := hw.1.2 (pureWrap A t) htwrap (by simp [pureWrap]; omega)
      (by simp [pureWrap]) (by simp [pureWrap,hgz,htz])
    have hx := congrArg (fun z : Monomial => z.1) he
    simp only [pureWrap] at hx
    omega

end NS25Lean.L5A2C4OR44
