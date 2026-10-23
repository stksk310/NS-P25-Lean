import NS25Lean.P2SectorCT5SourceDictionaryR22

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.L5A2C4OR22
open FourGeneratedBridge L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1
  L5A2C4OR3 L5A2C4OR5 L5A2C4OR6 L5A2C4OR19 L5A2C4OR20 L5A2C4OR21
variable {Gamma : NumericalSemigroup}

abbrev ChartMinimalVectors (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) := {z : Monomial // ChartMinimal B e HD z}

abbrev ActualHSources (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  {x : ℕ // IsMinimalTailGenerator (routingH B e).toAddSubmonoid
    (cyclicCut (routingH B e) (routingM B e)) x}

def principalVector (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Monomial :=
  Classical.choose (canonical_monomial_of_H B e HD
    (firstPrincipal_spec (routingH B e) (routingM B e) (routingM_pos B e)).2)

theorem principalVector_spec (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) :
    HerzogLShapeDomain HD (principalVector B e HD).2.1 (principalVector B e HD).2.2 ∧
    monomialDegree B e (principalVector B e HD)=
      firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e)*routingM B e :=
  (Classical.choose_spec (canonical_monomial_of_H B e HD
    (firstPrincipal_spec (routingH B e) (routingM B e) (routingM_pos B e)).2)).1

def principalPB (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Monomial :=
  ((principalVector B e HD).1+cr21 HD,0,(principalVector B e HD).2.2+cr23 HD)

abbrev CanonicalSourceVectors (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) :=
  {z : Monomial // HerzogLShapeDomain HD z.2.1 z.2.2 ∧
    ChartMinimal B e HD z ∧ z ≠ principalPB B e HD}

theorem principalPB_exception_iff (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) :
    z ≠ principalPB B e HD ↔
      ∀ delta U V, HerzogLShapeDomain HD U V →
        firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e)*routingM B e =
          normalizedGrid B e delta U V → z ≠ (delta+cr21 HD,0,V+cr23 HD) := by
  have hs := principalVector_spec B e HD
  constructor
  · intro hne delta U V hd hf
    have hsame : (delta,U,V)=principalVector B e HD :=
      canonical_monomial_unique B e HD hd hs.1 (hf.symm.trans hs.2.symm)
    have hr := congrArg Prod.fst hsame
    have hj := congrArg (fun z : Monomial => z.2.2) hsame
    simp only [Prod.fst,Prod.snd] at hr hj
    simpa only [principalPB,hr,hj] using hne
  · intro h
    exact h _ _ _ hs.1 hs.2.symm

/-- Degree is a genuine bijection between canonical non-PB chart minima
and actual H-minimal sources. This is NOT a polynomial-count surrogate. -/
def canonicalSourceEquiv {P : L5A1.P2Data Gamma} (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    CanonicalSourceVectors P.M.base R.e R.HD ≃ ActualHSources P.M.base R.e := by
  let f : CanonicalSourceVectors P.M.base R.e R.HD → ActualHSources P.M.base R.e :=
    fun z => ⟨monomialDegree P.M.base R.e z.val,
      (actual_canonical_chart_source_iff R hm hn _ _ _ z.property.1).mpr
        ⟨z.property.2.1,(principalPB_exception_iff _ _ _ _).mp z.property.2.2⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro z z' heq
    apply Subtype.ext
    exact canonical_monomial_unique P.M.base R.e R.HD z.property.1 z'.property.1
      (congrArg Subtype.val heq)
  · intro x
    obtain ⟨z,hz,_⟩ := canonical_monomial_of_H P.M.base R.e R.HD x.property.1.1
    have hsrc : IsMinimalTailGenerator (routingH P.M.base R.e).toAddSubmonoid
        (cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
        (monomialDegree P.M.base R.e z) := hz.2.symm ▸ x.property
    have hdic := (actual_canonical_chart_source_iff R hm hn _ _ _ hz.1).mp hsrc
    refine ⟨⟨z,hz.1,hdic.1,(principalPB_exception_iff _ _ _ _).mpr hdic.2⟩,?_⟩
    exact Subtype.ext hz.2

/-- G2/G3 pure minima and G1 central removal force every other chart
minimum into the actual whole Herzog domain, including boundary points. -/
theorem actual_chart_minimal_domain_or_pure {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) {z : Monomial}
    (hz : ChartMinimal P.M.base R.e R.HD z) :
    HerzogLShapeDomain R.HD z.2.1 z.2.2 ∨
      z=(0,c2 P.M.base R.e,0) ∨ z=(0,0,c3 P.M.base R.e) := by
  by_cases hi : c2 P.M.base R.e ≤ z.2.1
  · exact Or.inr (Or.inl (hz.2 _ (actual_pureB_chart_minimal R hm hn).1
      (Nat.zero_le _) hi (Nat.zero_le _)).symm)
  · by_cases hj : c3 P.M.base R.e ≤ z.2.2
    · exact Or.inr (Or.inr (hz.2 _ (actual_pureC_chart_minimal R hm hn).1
        (Nat.zero_le _) (Nat.zero_le _) hj).symm)
    · left
      refine ⟨by omega,by omega,?_⟩
      by_contra hcorner
      have hboth : cr12 R.HD ≤ z.2.1 ∧ cr13 R.HD ≤ z.2.2 := by omega
      have hc : (0,cr12 R.HD,cr13 R.HD) ∈
          monomialClosure (chartGenerators P.M.base R.e R.HD) :=
        ⟨_,Or.inr (Or.inr (Or.inr rfl)),le_refl _,le_refl _,le_refl _⟩
      have heq := hz.2 _ hc (Nat.zero_le _) hboth.1 hboth.2
      exact actual_central_chart_not_minimal R hm hn (heq.symm ▸ hz)

/-- Finiteness is proved by literal pure divisors; no finite replay or
bounded numerical enumeration enters any theorem. -/
theorem chartMinimal_bounds (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {z : Monomial} (hz : ChartMinimal B e HD z) :
    z.1 ≤ H0 B e ∧ z.2.1 ≤ c2 B e ∧ z.2.2 ≤ c3 B e := by
  have hx : (H0 B e,0,0) ∈ monomialClosure (chartGenerators B e HD) :=
    ⟨_,Or.inl (Or.inl rfl),le_refl _,le_refl _,le_refl _⟩
  have hy : (0,c2 B e,0) ∈ monomialClosure (chartGenerators B e HD) :=
    ⟨_,Or.inr (Or.inl rfl),le_refl _,le_refl _,le_refl _⟩
  have hz' : (0,0,c3 B e) ∈ monomialClosure (chartGenerators B e HD) :=
    ⟨_,Or.inr (Or.inr (Or.inl rfl)),le_refl _,le_refl _,le_refl _⟩
  constructor
  · by_cases h : H0 B e ≤ z.1
    · have heq := hz.2 _ hx h (Nat.zero_le _) (Nat.zero_le _)
      have ht := congrArg Prod.fst heq
      simp only [Prod.fst] at ht
      omega
    · omega
  · constructor
    · by_cases h : c2 B e ≤ z.2.1
      · have heq := hz.2 _ hy (Nat.zero_le _) h (Nat.zero_le _)
        have ht := congrArg (fun z : Monomial => z.2.1) heq
        simp only [Prod.fst,Prod.snd] at ht
        omega
      · omega
    · by_cases h : c3 B e ≤ z.2.2
      · have heq := hz.2 _ hz' (Nat.zero_le _) (Nat.zero_le _) h
        have ht := congrArg (fun z : Monomial => z.2.2) heq
        simp only [Prod.fst,Prod.snd] at ht
        omega
      · omega

instance chartMinimalVectors_finite (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Finite (ChartMinimalVectors B e HD) := by
  let f : ChartMinimalVectors B e HD →
      Fin (H0 B e+1) × Fin (c2 B e+1) × Fin (c3 B e+1) := fun z =>
    ⟨⟨z.val.1,by have h := (chartMinimal_bounds B e HD z.property).1; omega⟩,
     ⟨z.val.2.1,by have h := (chartMinimal_bounds B e HD z.property).2.1; omega⟩,
     ⟨z.val.2.2,by have h := (chartMinimal_bounds B e HD z.property).2.2; omega⟩⟩
  apply Finite.of_injective f
  intro z z' heq
  apply Subtype.ext
  have hr := congrArg (fun t => t.1.val) heq
  have hi := congrArg (fun t => t.2.1.val) heq
  have hj := congrArg (fun t => t.2.2.val) heq
  exact Prod.ext hr (Prod.ext hi hj)

theorem routingI_member_nonnegative (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    {x : ℤ} (hx : x ∈ routingI B e) : 0 ≤ x := by
  obtain ⟨_,_,⟨n,_,heq⟩,_⟩ := (mem_routingI_iff_positive_return B e x).mp hx
  rw [heq]
  positivity

theorem actual_cut_source_cast_iff (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (x : ℕ) :
    IsMinimalTailGenerator (routingH B e).toAddSubmonoid
      (cyclicCut (routingH B e) (routingM B e)) x ↔
      (routingI B e).IsMinimalGenerator (x : ℤ) := by
  rw [minimalTail_iff_literal]
  constructor
  · rintro ⟨hx,hmin⟩
    refine ⟨(actual_cyclicCut_iff_routingI B e x).mp hx,?_⟩
    intro h hh h0 hbad
    have hnon := routingI_member_nonnegative B e hbad
    have hle : h ≤ x := by omega
    have hnat : ((x-h : ℕ) : ℤ)= (x : ℤ)-h := Nat.cast_sub hle
    have hy := (actual_cyclicCut_iff_routingI B e (x-h)).mpr (hnat.symm ▸ hbad)
    exact h0 (hmin (x-h) h hy hh (by omega))
  · rintro ⟨hx,hmin⟩
    refine ⟨(actual_cyclicCut_iff_routingI B e x).mpr hx,?_⟩
    intro y h hy hh heq
    by_contra h0
    apply hmin h hh h0
    have hyI := (actual_cyclicCut_iff_routingI B e y).mp hy
    convert hyI using 1
    have hcast : (x : ℤ)=(y : ℤ)+(h : ℤ) := by exact_mod_cast heq
    omega

def actualHSourceEquivIdealGenerators (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    ActualHSources B e ≃ {x : ℤ // (routingI B e).IsMinimalGenerator x} where
  toFun x := ⟨x.val,(actual_cut_source_cast_iff B e x.val).mp x.property⟩
  invFun x := ⟨x.val.toNat,(actual_cut_source_cast_iff B e _).mpr
    (by simpa only [Int.toNat_of_nonneg (routingI_member_nonnegative B e x.property.1)]
      using x.property)⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by
    apply Subtype.ext
    exact Int.toNat_of_nonneg (routingI_member_nonnegative B e x.property.1)

/-- Aligns the actual H-source type with P.sourceCount through the
frozen normalization theorem, not through polynomial generators. -/
theorem actual_H_source_count (P : L5A1.P2Data Gamma) (e : Fin 3 ≃ Fin 3) :
    Nat.card (ActualHSources P.M.base e)=P.sourceCount := by
  calc
    Nat.card (ActualHSources P.M.base e) = (routingI P.M.base e).generatorCount :=
      Nat.card_congr (actualHSourceEquivIdealGenerators P.M.base e)
    _ = tailGeneratorCount
      (generatedThree (routingN1 P.M.base e) (routingN2 P.M.base e) (routingN3 P.M.base e))
      (aperyTail Gamma.toAddSubmonoid
        (generatedThree (routingN1 P.M.base e) (routingN2 P.M.base e) (routingN3 P.M.base e))
          P.M.base.q.val) :=
      normalizedTail_generatorCount Gamma P.M.base.q.val _ _ _ (chosenBase_minimalFour P.M.base e)
    _ = P.sourceCount := by
      rw [L5A1.P2Data.sourceCount,L2B.sourceCount,ChosenBase.Data.K,
        chosenBase_tail_eq_generatedThree P.M.base e]

private theorem finite_predicate_partition {α : Type*} (p q : α → Prop)
    [Finite {x : α // p x}] :
    Nat.card {x : α // p x} = Nat.card {x : α // p x ∧ q x} +
      Nat.card {x : α // p x ∧ ¬q x} := by
  classical
  have h := (Nat.card_congr (Equiv.sumCompl (fun x : {x : α // p x} => q x.val))).symm
  rw [Nat.card_sum] at h
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p q),
    Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p (fun x => ¬q x))] at h
  exact h

private theorem finite_point_card {α : Type*} (p : α → Prop) [DecidablePred p] (a : α) :
    Nat.card {x : α // p x ∧ x=a} = if p a then 1 else 0 := by
  classical
  by_cases h : p a
  · letI : Nonempty {x : α // p x ∧ x=a} := ⟨⟨a,h,rfl⟩⟩
    letI : Subsingleton {x : α // p x ∧ x=a} := ⟨by
      intro x y; apply Subtype.ext; exact x.property.2.trans y.property.2.symm⟩
    simpa only [h,ite_true] using (Nat.card_unique (α := {x : α // p x ∧ x=a}))
  · letI : IsEmpty {x : α // p x ∧ x=a} := ⟨fun x => h (x.property.2 ▸ x.property.1)⟩
    simpa only [h,ite_false] using
      ((Nat.card_eq_zero).mpr (Or.inl (inferInstance : IsEmpty {x : α // p x ∧ x=a})))

def chartGeneratorCount (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : ℕ := Nat.card (ChartMinimalVectors B e HD)

/-- PB minimality is not assumed. The correction is the actual 0/1
truth indicator of polynomial minimality at its unique principal form. -/
def PB_epsilon (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : ℕ := by
  classical
  exact if ChartMinimal B e HD (principalPB B e HD) then 1 else 0

theorem PB_epsilon_zero_or_one (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : PB_epsilon B e HD=0 ∨ PB_epsilon B e HD=1 := by
  unfold PB_epsilon
  split_ifs <;> simp

/-- Exact T5 count: actual H-sources, two noncanonical pure chart minima,
and the optional polynomial-minimal PB. Partitions are of literal vectors,
and the source bijection is proved in both directions. -/
theorem actual_chart_generator_count {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    chartGeneratorCount P.M.base R.e R.HD = P.sourceCount+2+PB_epsilon P.M.base R.e R.HD := by
  classical
  let p : Monomial → Prop := ChartMinimal P.M.base R.e R.HD
  let y : Monomial := (0,c2 P.M.base R.e,0)
  let z : Monomial := (0,0,c3 P.M.base R.e)
  let v := principalPB P.M.base R.e R.HD
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hs := coherent_coefficients P.M.base R.e R.HD
  have hy : p y := actual_pureB_chart_minimal R hm hn
  have hz : p z := actual_pureC_chart_minimal R hm hn
  have hzy : z ≠ y := by intro heq; have h := congrArg (fun w : Monomial => w.2.1) heq; dsimp [y,z] at h; omega
  have hvy : v ≠ y := by intro heq; have h := congrArg Prod.fst heq; dsimp [v,principalPB,y] at h; omega
  have hvz : v ≠ z := by intro heq; have h := congrArg Prod.fst heq; dsimp [v,principalPB,z] at h; omega
  let p1 : Monomial → Prop := fun w => p w ∧ w≠y
  letI : Finite {w : Monomial // p1 w} := Finite.of_injective
    (fun w => (⟨w.val,w.property.1⟩ : ChartMinimalVectors P.M.base R.e R.HD))
    (by intro a b heq; apply Subtype.ext
        simpa using congrArg (fun w : ChartMinimalVectors P.M.base R.e R.HD => w.val) heq)
  let p2 : Monomial → Prop := fun w => p1 w ∧ w≠z
  letI : Finite {w : Monomial // p2 w} := Finite.of_injective
    (fun w => (⟨w.val,w.property.1⟩ : {w : Monomial // p1 w}))
    (by intro a b heq; apply Subtype.ext
        simpa using congrArg (fun w : {w : Monomial // p1 w} => w.val) heq)
  have h1 := finite_predicate_partition p (fun w => w=y)
  have h2 := finite_predicate_partition p1 (fun w => w=z)
  have h3 := finite_predicate_partition p2 (fun w => w=v)
  have hyc : Nat.card {w : Monomial // p w ∧ w=y}=1 := by
    simpa only [hy,ite_true] using finite_point_card p y
  have hzc : Nat.card {w : Monomial // p1 w ∧ w=z}=1 := by
    have hz1 : p1 z := ⟨hz,hzy⟩
    simpa only [hz1,ite_true] using finite_point_card p1 z
  have hvc : Nat.card {w : Monomial // p2 w ∧ w=v}=PB_epsilon P.M.base R.e R.HD := by
    rw [finite_point_card]
    have heq : p2 v ↔ p v := ⟨fun h => h.1.1,fun h => ⟨⟨h,hvy⟩,hvz⟩⟩
    simp only [heq,PB_epsilon,p,v]
  let E : {w : Monomial // p2 w ∧ ¬w=v} ≃ CanonicalSourceVectors P.M.base R.e R.HD := {
    toFun := fun w => ⟨w.val,by
      rcases actual_chart_minimal_domain_or_pure R hm hn w.property.1.1.1 with hd | he | he
      · exact hd
      · exact False.elim (w.property.1.1.2 he)
      · exact False.elim (w.property.1.2 he),w.property.1.1.1,w.property.2⟩
    invFun := fun w => ⟨w.val,⟨⟨⟨w.property.2.1,by
      intro he; have h := w.property.1; rw [he] at h; exact (pure_chart_vectors_not_canonical _ _ _).1 h⟩,by
      intro he; have h := w.property.1; rw [he] at h; exact (pure_chart_vectors_not_canonical _ _ _).2 h⟩,w.property.2.2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hrest : Nat.card {w : Monomial // p2 w ∧ ¬w=v}=P.sourceCount :=
    (Nat.card_congr (E.trans (canonicalSourceEquiv R hm hn))).trans (actual_H_source_count P R.e)
  change chartGeneratorCount P.M.base R.e R.HD = _
  change Nat.card {w : Monomial // p w} = _
  rw [h1,hyc]
  change 1 + Nat.card {w : Monomial // p1 w} = _
  rw [h2,hzc]
  change 1 + (1 + Nat.card {w : Monomial // p2 w}) = _
  rw [h3,hvc,hrest]
  omega

def FullySupported (z : Monomial) : Prop := 0<z.1 ∧ 0<z.2.1 ∧ 0<z.2.2

def principal_iota (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : ℕ := by
  classical
  exact if FullySupported (principalVector B e HD) then 1 else 0

theorem principal_iota_zero_or_one (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : principal_iota B e HD=0 ∨ principal_iota B e HD=1 := by
  unfold principal_iota
  split_ifs <;> simp

theorem actual_principal_chart_minimal {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    ChartMinimal P.M.base R.e R.HD (principalVector P.M.base R.e R.HD) := by
  have hs := principalVector_spec P.M.base R.e R.HD
  apply actual_H_source_canonical_chart_minimal R hm hn _ _ _ hs.1
  change IsMinimalTailGenerator _ _ (monomialDegree P.M.base R.e (principalVector P.M.base R.e R.HD))
  rw [hs.2]
  exact firstPrincipal_minimal_cut_source _ _ (routingM_pos P.M.base R.e)

/-- Only the principal P can be a fully-supported minimal generator.
All frozen T3 families, PB, PC, and chart relations have a zero exponent. -/
theorem actual_fullySupported_minimal_eq_principal {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) {z : Monomial}
    (hz : ChartMinimal P.M.base R.e R.HD z) (hfull : FullySupported z) :
    z=principalVector P.M.base R.e R.HD := by
  have hd : HerzogLShapeDomain R.HD z.2.1 z.2.2 := by
    rcases actual_chart_minimal_domain_or_pure R hm hn hz with hd | he | he
    · exact hd
    · subst z; simp [FullySupported] at hfull
    · subst z; simp [FullySupported] at hfull
  have hg := chartMinimal_on_domain_mem_generators P.M.base R.e R.HD hd hz
  rcases hg with he | hcol | hpr
  · subst z; simp [FullySupported] at hfull
  · obtain ⟨n,i,j,d,_,_,_,_,_,hzm⟩ := hcol
    by_cases hi : i<cr12 R.HD
    · by_cases hj : j<cr13 R.HD
      · simp only [colonMonomials,hi,hj,ite_true,Set.mem_ofPred_eq] at hzm
        rcases hzm with rfl | rfl | rfl | rfl <;> simp [FullySupported] at hfull
      · simp only [colonMonomials,hi,hj,ite_true,ite_false,Set.mem_ofPred_eq] at hzm
        rcases hzm with rfl | rfl | rfl <;> simp [FullySupported] at hfull
    · simp only [colonMonomials,hi,ite_false,Set.mem_ofPred_eq] at hzm
      rcases hzm with rfl | rfl | rfl <;> simp [FullySupported] at hfull
  · obtain ⟨delta,U,V,hdom,hform,he⟩ := hpr
    rcases he with he | he | he
    · have hs := principalVector_spec P.M.base R.e R.HD
      exact he.trans (canonical_monomial_unique P.M.base R.e R.HD hdom hs.1
        (hform.symm.trans hs.2.symm))
    · subst z; simp [FullySupported] at hfull
    · subst z; simp [FullySupported] at hfull

def fullySupportedGeneratorCount (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : ℕ :=
  Nat.card {z : Monomial // ChartMinimal B e HD z ∧ FullySupported z}

instance canonicalSourceVectors_finite (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) : Finite (CanonicalSourceVectors B e HD) := by
  apply Finite.of_injective
    (fun z => (⟨z.val,z.property.2.1⟩ : ChartMinimalVectors B e HD))
  intro z z' heq
  apply Subtype.ext
  exact congrArg (fun w : ChartMinimalVectors B e HD => w.val) heq

theorem actual_H_sources_finite {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    Finite (ActualHSources P.M.base R.e) :=
  Finite.of_equiv (CanonicalSourceVectors P.M.base R.e R.HD) (canonicalSourceEquiv R hm hn)

instance fullySupportedMinimal_finite (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) :
    Finite {z : Monomial // ChartMinimal B e HD z ∧ FullySupported z} := by
  apply Finite.of_injective
    (fun z => (⟨z.val,z.property.1⟩ : ChartMinimalVectors B e HD))
  intro z z' heq
  apply Subtype.ext
  exact congrArg (fun w : ChartMinimalVectors B e HD => w.val) heq

/-- Exactly iota fully-supported polynomial generators, with no
assumption that the principal has all three exponents positive. -/
theorem actual_fullySupported_generator_count {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hm : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hn : L5A2C4G.SurvivingNotch P.M.base R.e R.HD) :
    fullySupportedGeneratorCount P.M.base R.e R.HD=principal_iota P.M.base R.e R.HD := by
  classical
  have hP := actual_principal_chart_minimal R hm hn
  let E : {z : Monomial // ChartMinimal P.M.base R.e R.HD z ∧ FullySupported z} ≃
      {z : Monomial // FullySupported z ∧ z=principalVector P.M.base R.e R.HD} := {
    toFun := fun z => ⟨z.val,z.property.2,
      actual_fullySupported_minimal_eq_principal R hm hn z.property.1 z.property.2⟩
    invFun := fun z => ⟨z.val,z.property.2.symm ▸ hP,z.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  exact (Nat.card_congr E).trans (finite_point_card FullySupported (principalVector P.M.base R.e R.HD))

end NS25Lean.L5A2C4OR22
