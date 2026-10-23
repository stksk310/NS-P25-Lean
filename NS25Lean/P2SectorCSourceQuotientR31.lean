import NS25Lean.P2SectorCF2SourceFiberR30

set_option linter.style.header false
set_option linter.style.whitespace false
noncomputable section
namespace NS25Lean.L5A2C4OR29
open L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR5
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

theorem roleExponent_add (e : Fin 3 ≃ Fin 3) (z w : Monomial) :
    roleExponent e (z+w)=roleExponent e z+roleExponent e w := by
  simp only [roleExponent,Prod.fst_add,Prod.snd_add,Finsupp.single_add]
  abel

theorem roleMonomial_add (k : Type*) [Field k] (e : Fin 3 ≃ Fin 3)
    (z w : Monomial) : roleMonomial k e (z+w)=roleMonomial k e z*roleMonomial k e w := by
  simp only [roleMonomial,roleExponent_add,MvPolynomial.monomial_mul,one_mul]

def sourceQuotientMonomial (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z : Monomial) :
    ToricPresentation.Poly k 3 ⧸ sourceQuotientIdeal k R :=
  Ideal.Quotient.mk _ (roleMonomial k R.e z)

theorem sourceQuotientMonomial_add (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z w : Monomial) :
    sourceQuotientMonomial k R (z+w)=
      sourceQuotientMonomial k R z*sourceQuotientMonomial k R w := by
  simp only [sourceQuotientMonomial,roleMonomial_add,map_mul]

theorem sourceQuotientMonomial_eq_zero_iff (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z : Monomial) :
    sourceQuotientMonomial k R z=0 ↔ roleMonomial k R.e z ∈ sourceQuotientIdeal k R :=
  Ideal.Quotient.eq_zero_iff_mem

theorem f2_quotient_relation (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) :
    sourceQuotientMonomial k R (0,c2 P.M.base R.e,0)=
      sourceQuotientMonomial k R (cr21 R.HD,0,cr23 R.HD) := by
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span (Or.inl (Or.inl rfl))

theorem source_normal_quotient_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (s : ModelSources P.M.base R.e) :
    sourceQuotientMonomial k R (sourceNormal R s)=0 := by
  apply (sourceQuotientMonomial_eq_zero_iff k R _).mpr
  exact Ideal.subset_span (Or.inl (Or.inr ⟨s,rfl⟩))

theorem boundary_alive_quotient_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) : sourceQuotientMonomial k R (boundaryAliveMonomial R)=0 := by
  apply (sourceQuotientMonomial_eq_zero_iff k R _).mpr
  exact Ideal.subset_span (Or.inr rfl)

theorem f2_context_quotient_relation (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (r i j : ℕ) (hi : c2 P.M.base R.e ≤ i) :
    sourceQuotientMonomial k R (r,i,j)=
      sourceQuotientMonomial k R (r+cr21 R.HD,i-c2 P.M.base R.e,j+cr23 R.HD) := by
  have ha : (r,i,j)=(r,i-c2 P.M.base R.e,j)+(0,c2 P.M.base R.e,0) := by
    ext <;> simp <;> omega
  have hb : (r+cr21 R.HD,i-c2 P.M.base R.e,j+cr23 R.HD)=
      (r,i-c2 P.M.base R.e,j)+(cr21 R.HD,0,cr23 R.HD) := by ext <;> simp
  rw [ha,hb,sourceQuotientMonomial_add,sourceQuotientMonomial_add,f2_quotient_relation]

theorem source_path_quotient_relation (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (s : ModelSources P.M.base R.e) {z w : Monomial}
    (hz : monomialDegree P.M.base R.e z=s.val)
    (hp : Relation.ReflTransGen (HerzogRewrite P.M.base R.e R.HD) z w) :
    sourceQuotientMonomial k R z=sourceQuotientMonomial k R w := by
  induction hp with
  | refl => rfl
  | tail hp hs ih =>
    obtain ⟨r,i,j,hi,hz',hw⟩ := minimal_source_rewrite_is_bWrap R s
      ((degree_eq_of_herzog_path _ _ _ hp).symm.trans hz) hs
    exact ih.trans (by rw [hz',hw]; exact f2_context_quotient_relation k R r i j hi)

theorem source_fiber_quotient_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (s : ModelSources P.M.base R.e) (z : Monomial)
    (hz : monomialDegree P.M.base R.e z=s.val) : sourceQuotientMonomial k R z=0 := by
  obtain ⟨w,hp,hp'⟩ := equal_degree_has_common_herzog_reduct _ _ R.HD
    (hz.trans (sourceNormal_spec R s).1.symm)
  exact (source_path_quotient_relation k R s hz hp).trans
    ((source_path_quotient_relation k R s (sourceNormal_spec R s).1 hp').symm.trans
      (source_normal_quotient_zero k R s))

theorem monomialDegree_add (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (z w : Monomial) : monomialDegree B e (z+w)=monomialDegree B e z+monomialDegree B e w := by
  simp only [monomialDegree,normalizedGrid,Prod.fst_add,Prod.snd_add,Nat.add_mul]
  omega

private theorem zero_from_a_predecessor (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (n : ℕ)
    (ih : ∀ d<n, ∀ z, monomialDegree P.M.base R.e z=d →
      d ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      sourceQuotientMonomial k R z=0)
    (r i j : ℕ) (hr : 0<r)
    (hc : monomialDegree P.M.base R.e (r,i,j)-routingA P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hle : monomialDegree P.M.base R.e (r,i,j) ≤ n) :
    sourceQuotientMonomial k R (r,i,j)=0 := by
  have hz : (r,i,j)=(r-1,i,j)+(1,0,0) := by ext <;> simp <;> omega
  have hd : monomialDegree P.M.base R.e (r-1,i,j)+routingA P.M.base R.e=
      monomialDegree P.M.base R.e (r,i,j) := by
    rw [hz,monomialDegree_add]; simp [monomialDegree,normalizedGrid]
  have ha := routingA_pos P.M.base R.e
  have hzero := ih (monomialDegree P.M.base R.e (r-1,i,j)) (by omega) _ rfl
    (by convert hc using 1; omega)
  rw [hz,sourceQuotientMonomial_add,hzero,zero_mul]

private theorem zero_from_b_predecessor (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (n : ℕ)
    (ih : ∀ d<n, ∀ z, monomialDegree P.M.base R.e z=d →
      d ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      sourceQuotientMonomial k R z=0)
    (r i j : ℕ) (hi : 0 < i)
    (hc : monomialDegree P.M.base R.e (r,i,j)-routingB P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hle : monomialDegree P.M.base R.e (r,i,j) ≤ n) :
    sourceQuotientMonomial k R (r,i,j)=0 := by
  have hz : (r,i,j)=(r,i-1,j)+(0,1,0) := by ext <;> simp <;> omega
  have hd : monomialDegree P.M.base R.e (r,i-1,j)+routingB P.M.base R.e=
      monomialDegree P.M.base R.e (r,i,j) := by
    rw [hz,monomialDegree_add]; simp [monomialDegree,normalizedGrid]
  have hb := routingB_positive P.M.base R.e
  have hzero := ih (monomialDegree P.M.base R.e (r,i-1,j)) (by omega) _ rfl
    (by convert hc using 1; omega)
  rw [hz,sourceQuotientMonomial_add,hzero,zero_mul]

private theorem zero_from_c_predecessor (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (n : ℕ)
    (ih : ∀ d<n, ∀ z, monomialDegree P.M.base R.e z=d →
      d ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      sourceQuotientMonomial k R z=0)
    (r i j : ℕ) (hj : 0<j)
    (hc : monomialDegree P.M.base R.e (r,i,j)-routingC P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e))
    (hle : monomialDegree P.M.base R.e (r,i,j) ≤ n) :
    sourceQuotientMonomial k R (r,i,j)=0 := by
  have hz : (r,i,j)=(r,i,j-1)+(0,0,1) := by ext <;> simp <;> omega
  have hd : monomialDegree P.M.base R.e (r,i,j-1)+routingC P.M.base R.e=
      monomialDegree P.M.base R.e (r,i,j) := by
    rw [hz,monomialDegree_add]; simp [monomialDegree,normalizedGrid]
  have hb := routingC_positive P.M.base R.e
  have hzero := ih (monomialDegree P.M.base R.e (r,i,j-1)) (by omega) _ rfl
    (by convert hc using 1; omega)
  rw [hz,sourceQuotientMonomial_add,hzero,zero_mul]

theorem inactive_endpoints_quotient_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (n : ℕ)
    (ih : ∀ d<n, ∀ z, monomialDegree P.M.base R.e z=d →
      d ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      sourceQuotientMonomial k R z=0)
    (hle : c1 P.M.base R.e*routingA P.M.base R.e ≤ n) :
    sourceQuotientMonomial k R (c1 P.M.base R.e,0,0)=0 ∧
      sourceQuotientMonomial k R (0,cr12 R.HD,cr13 R.HD)=0 := by
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hc1 := herzogC_positive P.M.base R.e 0
  have hr := (coherent_normalized_relations P.M.base R.e R.HD).1
  have hm : monomialDegree P.M.base R.e (0,cr12 R.HD,cr13 R.HD)=
      c1 P.M.base R.e*routingA P.M.base R.e := by
    simpa [monomialDegree,normalizedGrid] using hr.symm
  have hk := actual_normalized_inactive_killed R
  constructor
  · apply zero_from_a_predecessor k R n ih _ _ _ hc1
    · simpa [monomialDegree,normalizedGrid] using hk.1
    · simpa [monomialDegree,normalizedGrid] using hle
  · rcases hk.2 with hb | hc
    · apply zero_from_b_predecessor k R n ih _ _ _ (by omega)
      · rwa [hm]
      · rwa [hm]
    · apply zero_from_c_predecessor k R n ih _ _ _ (by omega)
      · rwa [hm]
      · rwa [hm]

theorem boundary_endpoints_quotient_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (n : ℕ)
    (ih : ∀ d<n, ∀ z, monomialDegree P.M.base R.e z=d →
      d ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      sourceQuotientMonomial k R z=0)
    (hle : c3 P.M.base R.e*routingC P.M.base R.e ≤ n) :
    sourceQuotientMonomial k R (0,0,c3 P.M.base R.e)=0 ∧
      sourceQuotientMonomial k R (cr31 R.HD,cr32 R.HD,0)=0 := by
  classical
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hc3 := herzogC_positive P.M.base R.e 2
  have hr := (coherent_normalized_relations P.M.base R.e R.HD).2.2
  have hm : monomialDegree P.M.base R.e (cr31 R.HD,cr32 R.HD,0)=
      c3 P.M.base R.e*routingC P.M.base R.e := by
    simpa [monomialDegree,normalizedGrid] using hr.symm
  have hz := boundary_alive_quotient_zero k R
  rcases actual_normalized_boundary_dichotomy R with h | h
  · refine ⟨?_,?_⟩
    · apply zero_from_c_predecessor k R n ih _ _ _ hc3
      · simpa [monomialDegree,normalizedGrid] using h.1
      · simpa [monomialDegree,normalizedGrid] using hle
    · simpa only [boundaryAliveMonomial,if_neg (not_not.mpr h.1)] using hz
  · refine ⟨?_,?_⟩
    · simpa only [boundaryAliveMonomial,if_pos h.1] using hz
    · rcases h.2 with ha | hb
      · apply zero_from_a_predecessor k R n ih _ _ _ (by omega)
        · rwa [hm]
        · rwa [hm]
      · apply zero_from_b_predecessor k R n ih _ _ _ (by omega)
        · rwa [hm]
        · rwa [hm]

theorem rewrite_quotient_relation_of_lower_cut (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (n : ℕ)
    (ih : ∀ d<n, ∀ z, monomialDegree P.M.base R.e z=d →
      d ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      sourceQuotientMonomial k R z=0)
    {z z' : Monomial} (hz : monomialDegree P.M.base R.e z=n)
    (hs : HerzogRewrite P.M.base R.e R.HD z z') :
    sourceQuotientMonomial k R z=sourceQuotientMonomial k R z' := by
  have hr := coherent_normalized_relations P.M.base R.e R.HD
  cases hs with
  | central r i j hi hj =>
    let t : Monomial := (r,i-cr12 R.HD,j-cr13 R.HD)
    have he : (r,i,j)=t+(0,cr12 R.HD,cr13 R.HD) := by
      ext <;> simp [t] <;> omega
    have he' : (r+c1 P.M.base R.e,i-cr12 R.HD,j-cr13 R.HD)=
        t+(c1 P.M.base R.e,0,0) := by ext <;> simp [t]
    have hm : monomialDegree P.M.base R.e (0,cr12 R.HD,cr13 R.HD)=
        c1 P.M.base R.e*routingA P.M.base R.e := by
      simpa [monomialDegree,normalizedGrid] using hr.1.symm
    have hd := monomialDegree_add P.M.base R.e t (0,cr12 R.HD,cr13 R.HD)
    rw [←he,hz,hm] at hd
    obtain ⟨ha,hb⟩ := inactive_endpoints_quotient_zero k R n ih (by omega)
    rw [he,he',sourceQuotientMonomial_add,sourceQuotientMonomial_add,ha,hb]
  | bWrap r i j _ hi => exact f2_context_quotient_relation k R r i j hi
  | cWrap r i j _ _ hj =>
    let t : Monomial := (r,i,j-c3 P.M.base R.e)
    have he : (r,i,j)=t+(0,0,c3 P.M.base R.e) := by
      ext <;> simp [t] <;> omega
    have he' : (r+cr31 R.HD,i+cr32 R.HD,j-c3 P.M.base R.e)=
        t+(cr31 R.HD,cr32 R.HD,0) := by ext <;> simp [t]
    have hd := monomialDegree_add P.M.base R.e t (0,0,c3 P.M.base R.e)
    rw [←he,hz] at hd
    simp only [monomialDegree,normalizedGrid,zero_mul,zero_add] at hd
    obtain ⟨ha,hb⟩ := boundary_endpoints_quotient_zero k R n ih (by omega)
    rw [he,he',sourceQuotientMonomial_add,sourceQuotientMonomial_add,ha,hb]

theorem path_quotient_relation_of_lower_cut (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (n : ℕ)
    (ih : ∀ d<n, ∀ z, monomialDegree P.M.base R.e z=d →
      d ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      sourceQuotientMonomial k R z=0)
    {z w : Monomial} (hz : monomialDegree P.M.base R.e z=n)
    (hp : Relation.ReflTransGen (HerzogRewrite P.M.base R.e R.HD) z w) :
    sourceQuotientMonomial k R z=sourceQuotientMonomial k R w := by
  induction hp with
  | refl => rfl
  | tail hp hs hi =>
    exact hi.trans (rewrite_quotient_relation_of_lower_cut k R n ih
      ((degree_eq_of_herzog_path _ _ _ hp).symm.trans hz) hs)

/-- Strong induction on the actual normalized degree. Only smaller cut
fibers are assumed inside the induction; no presentation premise is used. -/
theorem all_cut_monomials_quotient_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (n : ℕ) :
    ∀ z, monomialDegree P.M.base R.e z=n →
      n ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      sourceQuotientMonomial k R z=0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro z hz hc
    by_cases hs : IsMinimalTailGenerator (routingH P.M.base R.e).toAddSubmonoid
        (cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)) n
    · exact source_fiber_quotient_zero k R ⟨n,hs⟩ z hz
    have hn : ¬∀ y h : ℕ,
        y ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
        h ∈ routingH P.M.base R.e → n=y+h → h=0 := by
      intro hm
      exact hs ((minimalTail_iff_literal _ _ _).mpr ⟨hc,hm⟩)
    push_neg at hn
    obtain ⟨y,h,hy,hh,heq,hne⟩ := hn
    obtain ⟨r,i,j,hyfac⟩ := L5A2C4OR6.routingH_factorization P.M.base R.e hy.1
    obtain ⟨r',i',j',hhfac⟩ := L5A2C4OR6.routingH_factorization P.M.base R.e hh
    let v : Monomial := (r,i,j)
    let t : Monomial := (r',i',j')
    have hv : monomialDegree P.M.base R.e v=y := hyfac.symm
    have ht : monomialDegree P.M.base R.e t=h := hhfac.symm
    have hvz := ih y (by omega) v hv hy
    have hvt : monomialDegree P.M.base R.e (v+t)=n := by
      rw [monomialDegree_add,hv,ht,←heq]
    have hvzero : sourceQuotientMonomial k R (v+t)=0 := by
      rw [sourceQuotientMonomial_add,hvz,zero_mul]
    obtain ⟨w,hp,hp'⟩ := equal_degree_has_common_herzog_reduct _ _ R.HD (hz.trans hvt.symm)
    exact (path_quotient_relation_of_lower_cut k R n ih hz hp).trans
      ((path_quotient_relation_of_lower_cut k R n ih hvt hp').symm.trans hvzero)

theorem equal_degree_quotient_relation (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) {z z' : Monomial}
    (hz : monomialDegree P.M.base R.e z=monomialDegree P.M.base R.e z') :
    sourceQuotientMonomial k R z=sourceQuotientMonomial k R z' := by
  let n := monomialDegree P.M.base R.e z
  have ih : ∀ d<n, ∀ w, monomialDegree P.M.base R.e w=d →
      d ∈ cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) →
      sourceQuotientMonomial k R w=0 := fun d _ => all_cut_monomials_quotient_zero k R d
  obtain ⟨w,hp,hp'⟩ := equal_degree_has_common_herzog_reduct _ _ R.HD hz
  exact (path_quotient_relation_of_lower_cut k R n ih rfl hp).trans
    (path_quotient_relation_of_lower_cut k R n ih hz.symm hp').symm

theorem roleExponent_coordinates (e : Fin 3 ≃ Fin 3) (u : Fin 3 →₀ ℕ) :
    roleExponent e (u (e 0),u (e 1),u (e 2))=u := by
  ext j
  obtain ⟨t,rfl⟩ := e.surjective j
  fin_cases t <;> simp [roleExponent]

theorem actual_cut_monomial_mem_sourceQuotient (k : Type*) [Field k]
    {P : P2Data Gamma} (R : ActualRolePacket P) (u : Fin 3 →₀ ℕ)
    (hu : L2B.weight P.M.base u ∈ P.M.base.K) :
    MvPolynomial.monomial u (1 : k) ∈ sourceQuotientIdeal k R := by
  let z : Monomial := (u (R.e 0),u (R.e 1),u (R.e 2))
  have he : roleExponent R.e z=u := roleExponent_coordinates R.e u
  have hc : monomialDegree P.M.base R.e z ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
    apply (actual_scaled_cut_iff _ _ _).mpr
    rwa [←roleExponent_weight,he]
  have hz := (sourceQuotientMonomial_eq_zero_iff k R z).mp
    (all_cut_monomials_quotient_zero k R _ z rfl hc)
  simpa only [roleMonomial,he] using hz

theorem actual_equal_weight_binomial_mem_sourceQuotient (k : Type*) [Field k]
    {P : P2Data Gamma} (R : ActualRolePacket P) (u v : Fin 3 →₀ ℕ)
    (huv : L2B.weight P.M.base u=L2B.weight P.M.base v) :
    MvPolynomial.monomial u (1 : k)-MvPolynomial.monomial v 1 ∈
      sourceQuotientIdeal k R := by
  let z : Monomial := (u (R.e 0),u (R.e 1),u (R.e 2))
  let z' : Monomial := (v (R.e 0),v (R.e 1),v (R.e 2))
  have he : roleExponent R.e z=u := roleExponent_coordinates R.e u
  have he' : roleExponent R.e z'=v := roleExponent_coordinates R.e v
  have hd : 0<routingD P.M.base R.e :=
    tailGcd_pos (L2B.weights_positive P.M.base (R.e 0))
  have hdeg : monomialDegree P.M.base R.e z=monomialDegree P.M.base R.e z' := by
    have h := (roleExponent_weight P.M.base R.e z).symm.trans
      ((congrArg (L2B.weight P.M.base) he).trans
        (huv.trans ((congrArg (L2B.weight P.M.base) he').symm.trans
          (roleExponent_weight P.M.base R.e z'))))
    exact Nat.eq_of_mul_eq_mul_left hd h
  have h := Ideal.Quotient.eq.mp (equal_degree_quotient_relation k R hdeg)
  simpa only [sourceQuotientMonomial,roleMonomial,he,he'] using h

/-- M3 reverse inclusion, exact arbitrary role packet and arbitrary field. -/
theorem actual_source_quotient_reverse :
    ∀ {Gamma : NumericalSemigroup} {P : P2Data Gamma}
      (R : ActualRolePacket P) (k : Type*) [Field k],
      P.M.base.J k ≤ sourceQuotientIdeal k R := by
  intro Gamma P R k inst
  have hle : (P.M.base.J k).restrictScalars k ≤
      (sourceQuotientIdeal k R).restrictScalars k := by
    rw [L2B2A2.J_eq_span_moves]
    apply Submodule.span_le.mpr
    intro f hf
    rcases hf with ⟨u,v,huv,rfl⟩ | ⟨u,hu,rfl⟩
    · exact actual_equal_weight_binomial_mem_sourceQuotient k R u v huv
    · exact actual_cut_monomial_mem_sourceQuotient k R u hu
  exact hle

theorem actual_source_quotient_eq (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) : sourceQuotientIdeal k R=P.M.base.J k :=
  le_antisymm (sourceQuotientIdeal_le_actual k R) (actual_source_quotient_reverse R k)

theorem actual_toricIdeal_le_sourceQuotient (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) : P.M.base.IH k ≤ sourceQuotientIdeal k R := by
  have hle : (P.M.base.IH k).restrictScalars k ≤
      (sourceQuotientIdeal k R).restrictScalars k := by
    rw [L2B2A.IH_eq_span_toricMoves]
    apply Submodule.span_le.mpr
    rintro f ⟨u,v,h,rfl⟩
    exact actual_equal_weight_binomial_mem_sourceQuotient k R u v h
  exact hle

theorem actual_cutIdeal_le_sourceQuotient (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) : P.M.base.MK k ≤ sourceQuotientIdeal k R := by
  have hle : (P.M.base.MK k).restrictScalars k ≤
      (sourceQuotientIdeal k R).restrictScalars k := by
    rw [L2B2A2.MK_eq_span_boundaryMonomials]
    apply Submodule.span_le.mpr
    rintro f ⟨u,hu,rfl⟩
    exact actual_cut_monomial_mem_sourceQuotient k R u hu
  exact hle

theorem actual_F1_F3_endpoints_quotient_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) :
    (sourceQuotientMonomial k R (c1 P.M.base R.e,0,0)=0 ∧
      sourceQuotientMonomial k R (0,cr12 R.HD,cr13 R.HD)=0) ∧
    (sourceQuotientMonomial k R (0,0,c3 P.M.base R.e)=0 ∧
      sourceQuotientMonomial k R (cr31 R.HD,cr32 R.HD,0)=0) := by
  constructor
  · exact inactive_endpoints_quotient_zero k R _
      (fun d _ => all_cut_monomials_quotient_zero k R d) le_rfl
  · exact boundary_endpoints_quotient_zero k R _
      (fun d _ => all_cut_monomials_quotient_zero k R d) le_rfl

/-- M4 preparation: the literal one-binomial wrap, not a guessed initial
ideal or a source counted twice. -/
def sourceWrap {P : P2Data Gamma} (R : ActualRolePacket P) (z : Monomial) : Monomial :=
  (z.1+cr21 R.HD,0,z.2.2+cr23 R.HD)

theorem quotient_zero_wrap (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (z : Monomial)
    (hz : sourceQuotientMonomial k R z=0)
    (hy : 0 < z.2.1) (hC : z.2.1<c2 P.M.base R.e) :
    sourceQuotientMonomial k R (sourceWrap R z)=0 := by
  obtain ⟨r,i,j⟩ := z
  have he : (r,c2 P.M.base R.e,j)=(r,i,j)+(0,c2 P.M.base R.e-i,0) := by
    ext <;> simp at * <;> omega
  have hzero : sourceQuotientMonomial k R (r,c2 P.M.base R.e,j)=0 := by
    rw [he,sourceQuotientMonomial_add,hz,zero_mul]
  have hw := f2_context_quotient_relation k R r (c2 P.M.base R.e) j le_rfl
  simpa only [Nat.sub_self,sourceWrap] using hw.symm.trans hzero

theorem source_wrap_quotient_zero (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) (s : ModelSources P.M.base R.e)
    (hy : 0 < (sourceNormal R s).2.1) :
    sourceQuotientMonomial k R (sourceWrap R (sourceNormal R s))=0 :=
  quotient_zero_wrap k R _ (source_normal_quotient_zero k R s) hy (sourceNormal_spec R s).2.1

end NS25Lean.L5A2C4OR29
