import NS25Lean.P2SectorCDirectPFModelAdapterR29

set_option linter.style.header false
set_option linter.style.whitespace false
noncomputable section
namespace NS25Lean.L5A2C4OR29
open L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR5
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

/-- Exact degree-fiber connectivity by the three literal coherent Herzog
relations. Both paths are constructed by terminating reduction; neither
normality nor toric generation is supplied as a premise. -/
theorem equal_degree_has_common_herzog_reduct
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e)
    {z z' : Monomial} (heq : monomialDegree B e z = monomialDegree B e z') :
    ∃ w, Relation.ReflTransGen (HerzogRewrite B e HD) z w ∧
      Relation.ReflTransGen (HerzogRewrite B e HD) z' w := by
  obtain ⟨w, hp, hd, hw⟩ := rewrite_normalizes B e HD z
  obtain ⟨w', hp', hd', hw'⟩ := rewrite_normalizes B e HD z'
  have hww' : w = w' := canonical_monomial_unique B e HD hd hd'
    (hw.symm.trans (heq.trans hw'))
  exact ⟨w, hp, hww'.symm ▸ hp'⟩

theorem degree_eq_of_herzog_path
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e)
    {z w : Monomial} (hp : Relation.ReflTransGen (HerzogRewrite B e HD) z w) :
    monomialDegree B e z = monomialDegree B e w := by
  induction hp with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (rewrite_arithmetic B e HD hs).1

theorem equal_degree_iff_common_herzog_reduct
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e)
    (z z' : Monomial) :
    monomialDegree B e z = monomialDegree B e z' ↔
      ∃ w, Relation.ReflTransGen (HerzogRewrite B e HD) z w ∧
        Relation.ReflTransGen (HerzogRewrite B e HD) z' w := by
  constructor
  · exact equal_degree_has_common_herzog_reduct B e HD
  · rintro ⟨w, hp, hp'⟩
    exact (degree_eq_of_herzog_path B e HD hp).trans
      (degree_eq_of_herzog_path B e HD hp').symm

/-- M1 support separation in its intrinsic common-H-summand form.
It applies to every positive return, not just to a chosen small return. -/
theorem model_source_return_no_common_summand
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (s : ModelSources B e)
    {n y z h : ℕ} (hn : 0 < n) (hy : y ∈ routingH B e)
    (hz : z ∈ routingH B e) (hh : h ∈ routingH B e)
    (hs : s.val = z+h) (hreturn : s.val = n*routingM B e+(y+h)) : h = 0 := by
  have hcut : z ∈ cyclicCut (routingH B e) (routingM B e) :=
    ⟨hz, n, hn, y, hy, by omega⟩
  exact ((minimalTail_iff_literal _ _ _).mp s.property).2 z h hcut hh hs

/-- M1 small-return firewall: existence of a small return for each nonfirst
source, without asserting anything false about arbitrary large returns. -/
theorem model_nonfirst_source_small_return
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (s : ModelSources B e)
    (hfirst : s.val ≠ firstPrincipal (routingH B e) (routingM B e)
      (routingM_pos B e)*routingM B e) :
    ∃ n y : ℕ, 0 < n ∧ n < firstPrincipal (routingH B e) (routingM B e)
      (routingM_pos B e) ∧ y ∈ routingH B e ∧ 0 < y ∧
      s.val = n*routingM B e+y := by
  obtain ⟨_, n, hn, hnle, y, hy, heq⟩ :=
    (cyclicCut_finite_principal_reduction _ _ (routingM_pos B e) s.val).mp s.property.1
  have hnlt : n < firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) := by
    by_contra hnot
    have hnq : n = firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) := by omega
    have hy0 := ((minimalTail_iff_literal _ _ _).mp s.property).2 _ y
      (firstPrincipal_minimal_cut_source _ _ (routingM_pos B e)).1 hy
      (by simpa [hnq] using heq)
    exact hfirst (by simpa [hnq, hy0] using heq)
  have hypos : 0 < y := by
    by_contra hnot
    have hy0 : y = 0 := by omega
    have hnH : n*routingM B e ∈ routingH B e := by
      simpa [heq, hy0] using s.property.1.1
    have hmin := firstPrincipal_le _ _ (routingM_pos B e) hn hnH
    omega
  exact ⟨n, y, hn, hnlt, hy, hypos, heq⟩

/-- Full union support expressed as literal H-predecessors at all three
generators. It does not require one fully supported factorization. -/
def ModelFullSupport (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (x : ℕ) : Prop :=
  (∃ y ∈ routingH B e, x = y+routingA B e) ∧
  (∃ y ∈ routingH B e, x = y+routingB B e) ∧
  (∃ y ∈ routingH B e, x = y+routingC B e)

private theorem monomial_mem_H (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r i j : ℕ) : normalizedGrid B e r i j ∈ routingH B e :=
  (mem_generatedThree_iff _ _ _ _).mpr ⟨r,i,j,rfl⟩

private theorem monomial_pred_a (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r i j : ℕ) (hr : 0 < r) :
    ∃ y ∈ routingH B e, monomialDegree B e (r,i,j)=y+routingA B e := by
  refine ⟨normalizedGrid B e (r-1) i j,monomial_mem_H B e _ _ _,?_⟩
  simp only [monomialDegree,normalizedGrid]
  have h := congrArg (fun n => n*routingA B e) (show r-1+1=r by omega)
  simp only [Nat.add_mul,one_mul] at h
  omega

private theorem monomial_pred_b (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r i j : ℕ) (hi : 0 < i) :
    ∃ y ∈ routingH B e, monomialDegree B e (r,i,j)=y+routingB B e := by
  refine ⟨normalizedGrid B e r (i-1) j,monomial_mem_H B e _ _ _,?_⟩
  simp only [monomialDegree,normalizedGrid]
  have h := congrArg (fun n => n*routingB B e) (show i-1+1=i by omega)
  simp only [Nat.add_mul,one_mul] at h
  omega

private theorem monomial_pred_c (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r i j : ℕ) (hj : 0 < j) :
    ∃ y ∈ routingH B e, monomialDegree B e (r,i,j)=y+routingC B e := by
  refine ⟨normalizedGrid B e r i (j-1),monomial_mem_H B e _ _ _,?_⟩
  simp only [monomialDegree,normalizedGrid]
  have h := congrArg (fun n => n*routingC B e) (show j-1+1=j by omega)
  simp only [Nat.add_mul,one_mul] at h
  omega

/-- M1: full union support forces first-principality; ties and different
factorizations at the same degree are not discarded. -/
theorem model_full_support_source_is_first
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (s : ModelSources B e)
    (hfull : ModelFullSupport B e s.val) :
    s.val = firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e)*routingM B e := by
  by_contra hnot
  obtain ⟨n,y,hn,_,hy,hypos,heq⟩ := model_nonfirst_source_small_return B e s hnot
  obtain ⟨r,i,j,hyfac⟩ := L5A2C4OR6.routingH_factorization B e hy
  have hdeg : monomialDegree B e (r,i,j)=y := hyfac.symm
  have common {t : ℕ} (ht : 0<t) (htH : t ∈ routingH B e)
      (hsy : ∃ z ∈ routingH B e, s.val=z+t)
      (hyy : ∃ z ∈ routingH B e, y=z+t) : False := by
    obtain ⟨z,hz,hs⟩ := hsy
    obtain ⟨v,hv,hy⟩ := hyy
    have h0 := model_source_return_no_common_summand B e s hn hv hz htH hs
      (by omega)
    omega
  by_cases hr : 0<r
  · exact common (routingA_pos B e) (by simpa [normalizedGrid] using monomial_mem_H B e 1 0 0)
      hfull.1 (hdeg ▸ monomial_pred_a B e r i j hr)
  by_cases hi : 0 < i
  · have hb : 0 < routingB B e := quotient_pos_of_dvd
      (chosenBase_minimalFour B e).n₂_pos (tailGcd_dvd _ _ _).2.1
    exact common hb (routingHB B e) hfull.2.1 (hdeg ▸ monomial_pred_b B e r i j hi)
  have hj : 0 < j := by
    by_contra hnj
    have : r=0 ∧ i=0 ∧ j=0 := by omega
    simp [this.1,this.2.1,this.2.2] at hyfac
    omega
  have hc : 0 < routingC B e := quotient_pos_of_dvd
    (chosenBase_minimalFour B e).n₃_pos (tailGcd_dvd _ _ _).2.2
  exact common hc (routingHC B e) hfull.2.2 (hdeg ▸ monomial_pred_c B e r i j hj)

theorem rewrite_degree_has_full_support
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e)
    {z z' : Monomial} (h : HerzogRewrite B e HD z z') :
    ModelFullSupport B e (monomialDegree B e z) := by
  have hp := coherent_coefficients_positive B e HD
  have hc1 : 0 < c1 B e := herzogC_positive B e 0
  have hc2 : 0 < c2 B e := herzogC_positive B e 1
  have hc3 : 0 < c3 B e := herzogC_positive B e 2
  have heq := (rewrite_arithmetic B e HD h).1
  cases h with
  | central r i j hi hj =>
    exact ⟨heq ▸ monomial_pred_a B e _ _ _ (by omega),
      monomial_pred_b B e _ _ _ (by omega),monomial_pred_c B e _ _ _ (by omega)⟩
  | bWrap r i j _ hi =>
    exact ⟨heq ▸ monomial_pred_a B e _ _ _ (by omega),
      monomial_pred_b B e _ _ _ (by omega),heq ▸ monomial_pred_c B e _ _ _ (by omega)⟩
  | cWrap r i j _ _ hj =>
    exact ⟨heq ▸ monomial_pred_a B e _ _ _ (by omega),
      heq ▸ monomial_pred_b B e _ _ _ (by omega),monomial_pred_c B e _ _ _ (by omega)⟩

theorem model_nonfirst_source_no_rewrite
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e)
    (s : ModelSources B e)
    (hfirst : s.val ≠ firstPrincipal (routingH B e) (routingM B e)
      (routingM_pos B e)*routingM B e)
    {z z' : Monomial} (hz : monomialDegree B e z=s.val) : ¬HerzogRewrite B e HD z z' := by
  intro hs
  exact hfirst (model_full_support_source_is_first B e s
    (hz ▸ rewrite_degree_has_full_support B e HD hs))

private theorem path_eq_of_no_step {α : Type*} {r : α → α → Prop} {x y : α}
    (h : Relation.ReflTransGen r x y) (hn : ∀ z, ¬r x z) : x=y := by
  induction h with
  | refl => rfl
  | tail hp hs ih =>
    have heq := ih
    exact (hn _ (heq.symm ▸ hs)).elim

/-- M2: nonfirst source degrees have a unique literal exponent vector. -/
theorem model_nonfirst_source_unique_factorization
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e)
    (s : ModelSources B e)
    (hfirst : s.val ≠ firstPrincipal (routingH B e) (routingM B e)
      (routingM_pos B e)*routingM B e)
    {z z' : Monomial} (hz : monomialDegree B e z=s.val)
    (hz' : monomialDegree B e z'=s.val) : z=z' := by
  obtain ⟨w,hp,hp'⟩ := equal_degree_has_common_herzog_reduct B e HD (hz.trans hz'.symm)
  exact (path_eq_of_no_step hp (fun _ => model_nonfirst_source_no_rewrite B e HD s hfirst hz)).trans
    (path_eq_of_no_step hp' (fun _ => model_nonfirst_source_no_rewrite B e HD s hfirst hz')).symm

theorem model_nonfirst_source_proper_support
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (s : ModelSources B e)
    (hfirst : s.val ≠ firstPrincipal (routingH B e) (routingM B e)
      (routingM_pos B e)*routingM B e) : ¬ModelFullSupport B e s.val :=
  fun h => hfirst (model_full_support_source_is_first B e s h)

end NS25Lean.L5A2C4OR29
