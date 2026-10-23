import NS25Lean.P2SectorCDirectPFSourceModelR29

set_option linter.style.header false
set_option linter.style.whitespace false
noncomputable section
namespace NS25Lean.L5A2C4OR29
open L5A1 L5A2C4A L5A2C4C L5A2C4D L5A2C4H L5A2C4OR1 L5A2C4OR5
  L5A2C4OR19 L5A2C4OR20 L5A2C4OR21 L5A2C4OR22 FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

/-- Literal formula promoted unchanged from the R29 verification benchmark. -/
def f2Normal (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) : Monomial :=
  (z.1 + cr21 HD * (z.2.1 / c2 B e), z.2.1 % c2 B e,
    z.2.2 + cr23 HD * (z.2.1 / c2 B e))

private theorem grid_mem_H (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r i j : ℕ) : normalizedGrid B e r i j ∈ routingH B e :=
  (mem_generatedThree_iff _ _ _ _).mpr ⟨r,i,j,rfl⟩

private theorem cut_add_H {H : NumericalSemigroup} {m x h : ℕ}
    (hx : x ∈ cyclicCut H m) (hh : h ∈ H) : x+h ∈ cyclicCut H m := by
  obtain ⟨hxH,n,hn,t,ht,heq⟩ := hx
  exact ⟨H.toAddSubmonoid.add_mem hxH hh,n,hn,t+h,
    H.toAddSubmonoid.add_mem ht hh,by omega⟩

/-- A genuine proper critical predecessor, multiplied by an actual H
monomial, contradicts source minimality. Reconstruction guards Nat.sub. -/
theorem source_forbids_critical_divisor (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (s : ModelSources B e) {h g k : ℕ}
    (hpred : h-g ∈ cyclicCut (routingH B e) (routingM B e))
    (hgle : g ≤ h) (hg : g ∈ routingH B e) (hgpos : 0 < g)
    (hk : k ∈ routingH B e) (heq : s.val=h+k) : False := by
  have hrec := Nat.sub_add_cancel hgle
  have hzero := ((minimalTail_iff_literal _ _ _).mp s.property).2
    (h-g+k) g (cut_add_H hpred hk) hg (by omega)
  omega

theorem source_no_central_rewrite {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (r i j : ℕ)
    (hi : cr12 R.HD ≤ i) (hj : cr13 R.HD ≤ j)
    (hz : monomialDegree P.M.base R.e (r,i,j)=s.val) : False := by
  have hr := (coherent_normalized_relations P.M.base R.e R.HD).1
  have hb := congrArg (fun n => n*routingB P.M.base R.e) (Nat.sub_add_cancel hi)
  have hc := congrArg (fun n => n*routingC P.M.base R.e) (Nat.sub_add_cancel hj)
  have hp : 0<c1 P.M.base R.e := herzogC_positive _ _ 0
  apply source_forbids_critical_divisor P.M.base R.e s
    (actual_normalized_inactive_killed R).1
    (by simpa using Nat.mul_le_mul_right (routingA P.M.base R.e) (show 1 ≤ c1 P.M.base R.e by omega))
    (by simpa [normalizedGrid] using grid_mem_H P.M.base R.e 1 0 0)
    (routingA_pos _ _) (grid_mem_H P.M.base R.e r (i-cr12 R.HD) (j-cr13 R.HD))
  simp only [monomialDegree,normalizedGrid,Nat.add_mul] at hz hb hc ⊢
  nlinarith only [hr,hb,hc,hz]

theorem source_no_cWrap_rewrite {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) (r i j : ℕ) (hj : c3 P.M.base R.e ≤ j)
    (hz : monomialDegree P.M.base R.e (r,i,j)=s.val) : False := by
  have hr := (coherent_normalized_relations P.M.base R.e R.HD).2.2
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hc3 : 0<c3 P.M.base R.e := herzogC_positive _ _ 2
  have hmul := congrArg (fun n => n*routingC P.M.base R.e) (Nat.sub_add_cancel hj)
  have heq : s.val=c3 P.M.base R.e*routingC P.M.base R.e+
      normalizedGrid P.M.base R.e r i (j-c3 P.M.base R.e) := by
    simp only [monomialDegree,normalizedGrid,Nat.add_mul] at hz hmul ⊢
    omega
  rcases actual_normalized_boundary_dichotomy R with h | h
  · exact source_forbids_critical_divisor _ _ s h.1
      (by simpa using Nat.mul_le_mul_right (routingC P.M.base R.e) (show 1 ≤ c3 P.M.base R.e by omega))
      (routingHC _ _) (routingC_positive _ _) (grid_mem_H _ _ _ _ _) heq
  · rcases h.2 with ha | hb
    · have hle := Nat.mul_le_mul_right (routingA P.M.base R.e)
        (show 1 ≤ cr31 R.HD by omega)
      have hbnd : routingA P.M.base R.e ≤ c3 P.M.base R.e*routingC P.M.base R.e := by
        rw [hr]
        exact le_trans (by simpa using hle) (Nat.le_add_right _ _)
      exact source_forbids_critical_divisor _ _ s ha hbnd
        (by simpa [normalizedGrid] using grid_mem_H P.M.base R.e 1 0 0)
        (routingA_pos _ _) (grid_mem_H _ _ _ _ _) heq
    · have hle := Nat.mul_le_mul_right (routingB P.M.base R.e)
        (show 1 ≤ cr32 R.HD by omega)
      have hbnd : routingB P.M.base R.e ≤ c3 P.M.base R.e*routingC P.M.base R.e := by
        rw [hr]
        exact le_trans (by simpa using hle) (Nat.le_add_left _ _)
      exact source_forbids_critical_divisor _ _ s hb hbnd
        (routingHB _ _) (routingB_positive _ _) (grid_mem_H _ _ _ _ _) heq

/-- Every directed step at a minimal-source degree is literally F2.
No nonfirst-source or DirectPF premise is needed. -/
theorem minimal_source_rewrite_is_bWrap {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) {z z' : Monomial}
    (hz : monomialDegree P.M.base R.e z=s.val)
    (hs : HerzogRewrite P.M.base R.e R.HD z z') :
    ∃ r i j : ℕ, c2 P.M.base R.e ≤ i ∧
      z=(r,i,j) ∧ z'=(r+cr21 R.HD,i-c2 P.M.base R.e,j+cr23 R.HD) := by
  cases hs with
  | central r i j hi hj => exact (source_no_central_rewrite R s r i j hi hj hz).elim
  | bWrap r i j _ hi => exact ⟨r,i,j,hi,rfl,rfl⟩
  | cWrap r i j _ _ hj => exact (source_no_cWrap_rewrite R s r i j hj hz).elim

theorem f2Normal_y_lt (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) :
    (f2Normal B e HD z).2.1 < c2 B e := Nat.mod_lt _ (herzogC_positive B e 1)

theorem f2Normal_degree (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) :
    monomialDegree B e (f2Normal B e HD z)=monomialDegree B e z := by
  have hr := congrArg (fun n => n*(z.2.1/c2 B e))
    (coherent_normalized_relations B e HD).2.1
  have hi := congrArg (fun n => n*routingB B e) (Nat.div_add_mod z.2.1 (c2 B e))
  simp only [f2Normal,monomialDegree,normalizedGrid,Nat.add_mul] at *
  nlinarith only [hr,hi]

theorem f2Normal_idempotent (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (z : Monomial) :
    f2Normal B e HD (f2Normal B e HD z)=f2Normal B e HD z := by
  have h := f2Normal_y_lt B e HD z
  simp only [f2Normal] at h ⊢
  simp [Nat.div_eq_of_lt h,Nat.mod_eq_of_lt h]

theorem f2Normal_bWrap (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (r i j : ℕ) (hi : c2 B e ≤ i) :
    f2Normal B e HD (r,i,j)=f2Normal B e HD (r+cr21 HD,i-c2 B e,j+cr23 HD) := by
  have hd : i/c2 B e=(i-c2 B e)/c2 B e+1 := by
    simpa only [Nat.sub_add_cancel hi] using
      Nat.add_div_right (i-c2 B e) (herzogC_positive B e 1)
  have hm : i%c2 B e=(i-c2 B e)%c2 B e := by
    simpa only [Nat.sub_add_cancel hi] using Nat.add_mod_right (i-c2 B e) (c2 B e)
  apply Prod.ext
  · change r+cr21 HD*(i/c2 B e)=(r+cr21 HD)+cr21 HD*((i-c2 B e)/c2 B e)
    rw [hd,Nat.mul_add,Nat.mul_one]
    omega
  · apply Prod.ext
    · exact hm
    · change j+cr23 HD*(i/c2 B e)=(j+cr23 HD)+cr23 HD*((i-c2 B e)/c2 B e)
      rw [hd,Nat.mul_add,Nat.mul_one]
      omega

theorem f2Normal_source_rewrite {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) {z z' : Monomial}
    (hz : monomialDegree P.M.base R.e z=s.val)
    (hs : HerzogRewrite P.M.base R.e R.HD z z') :
    f2Normal P.M.base R.e R.HD z=f2Normal P.M.base R.e R.HD z' := by
  obtain ⟨r,i,j,hi,rfl,rfl⟩ := minimal_source_rewrite_is_bWrap R s hz hs
  exact f2Normal_bWrap _ _ _ r i j hi

theorem f2Normal_source_path {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) {z w : Monomial}
    (hz : monomialDegree P.M.base R.e z=s.val)
    (hp : Relation.ReflTransGen (HerzogRewrite P.M.base R.e R.HD) z w) :
    f2Normal P.M.base R.e R.HD z=f2Normal P.M.base R.e R.HD w := by
  induction hp with
  | refl => rfl
  | tail hp hs ih =>
    exact ih.trans (f2Normal_source_rewrite R s
      ((degree_eq_of_herzog_path _ _ _ hp).symm.trans hz) hs)

/-- The original R29 executable target, now a proof on its full binder.
The first principal source is deliberately included. -/
theorem source_fiber_F2_normal_form_target :
    ∀ {Gamma : NumericalSemigroup} {P : P2Data Gamma}
      (R : ActualRolePacket P) (s : ModelSources P.M.base R.e),
    ∃ g : Monomial,
      monomialDegree P.M.base R.e g=s.val ∧ g.2.1<c2 P.M.base R.e ∧
      ∀ z : Monomial, monomialDegree P.M.base R.e z=s.val →
        f2Normal P.M.base R.e R.HD z=g := by
  intro Gamma P R s
  obtain ⟨r,i,j,hfac⟩ := L5A2C4OR6.routingH_factorization P.M.base R.e s.property.1.1
  have hz0 : monomialDegree P.M.base R.e (r,i,j)=s.val := hfac.symm
  refine ⟨f2Normal _ _ R.HD (r,i,j),(f2Normal_degree _ _ R.HD _).trans hz0,
    f2Normal_y_lt _ _ R.HD _,?_⟩
  intro z hz
  obtain ⟨w,hp,hp0⟩ := equal_degree_has_common_herzog_reduct _ _ R.HD (hz.trans hz0.symm)
  exact (f2Normal_source_path R s hz hp).trans (f2Normal_source_path R s hz0 hp0).symm

/-- A chosen source representative, justified by the proved full-binder
normal form theorem, rather than by a packet field. -/
def sourceNormal {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) : Monomial :=
  Classical.choose (source_fiber_F2_normal_form_target R s)

theorem sourceNormal_spec {P : P2Data Gamma} (R : ActualRolePacket P)
    (s : ModelSources P.M.base R.e) :
    monomialDegree P.M.base R.e (sourceNormal R s)=s.val ∧
      (sourceNormal R s).2.1<c2 P.M.base R.e ∧
      ∀ z, monomialDegree P.M.base R.e z=s.val →
        f2Normal P.M.base R.e R.HD z=sourceNormal R s :=
  Classical.choose_spec (source_fiber_F2_normal_form_target R s)

theorem sourceNormal_injective {P : P2Data Gamma} (R : ActualRolePacket P) :
    Function.Injective (sourceNormal R) := by
  intro s t h
  apply Subtype.ext
  exact (sourceNormal_spec R s).1.symm.trans
    ((congrArg (monomialDegree P.M.base R.e) h).trans (sourceNormal_spec R t).1)

theorem sourceNormalRepresentatives_card {P : P2Data Gamma} (R : ActualRolePacket P) :
    Nat.card (Set.range (sourceNormal R))=P.sourceCount :=
  (Nat.card_congr (Equiv.ofInjective _ (sourceNormal_injective R))).symm.trans
    (actual_model_source_count R)

/-- The polynomial exponent lives in the ORIGINAL variable indexing. -/
def roleExponent (e : Fin 3 ≃ Fin 3) (z : Monomial) : Fin 3 →₀ ℕ :=
  Finsupp.single (e 0) z.1 + Finsupp.single (e 1) z.2.1 + Finsupp.single (e 2) z.2.2

theorem roleExponent_weight (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (z : Monomial) : L2B.weight B (roleExponent e z)=routingD B e*monomialDegree B e z := by
  simp only [roleExponent,map_add,L2B.weight_single,monomialDegree]
  exact (normalizedGrid_scale B e z.1 z.2.1 z.2.2).symm

def roleMonomial (k : Type*) [Field k] (e : Fin 3 ≃ Fin 3) (z : Monomial) :
    ToricPresentation.Poly k 3 := MvPolynomial.monomial (roleExponent e z) 1

/-- The alive boundary endpoint is selected using actual predecessor
membership, never a guessed orientation. -/
def boundaryAliveMonomial {P : P2Data Gamma} (R : ActualRolePacket P) : Monomial := by
  classical
  exact if c3 P.M.base R.e*routingC P.M.base R.e-routingC P.M.base R.e ∉
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e)
    then (0,0,c3 P.M.base R.e) else (cr31 R.HD,cr32 R.HD,0)

theorem boundaryAliveMonomial_degree {P : P2Data Gamma} (R : ActualRolePacket P) :
    monomialDegree P.M.base R.e (boundaryAliveMonomial R)=
      c3 P.M.base R.e*routingC P.M.base R.e := by
  classical
  unfold boundaryAliveMonomial
  split_ifs <;> simp only [monomialDegree,normalizedGrid,zero_mul,zero_add,add_zero]
  exact (coherent_normalized_relations P.M.base R.e R.HD).2.2.symm

theorem actual_boundary_degree_in_cut {P : P2Data Gamma} (R : ActualRolePacket P) :
    c3 P.M.base R.e*routingC P.M.base R.e ∈
      cyclicCut (routingH P.M.base R.e) (routingM P.M.base R.e) := by
  have hp := coherent_coefficients_positive P.M.base R.e R.HD
  have hr := (coherent_normalized_relations P.M.base R.e R.HD).2.2
  have hc3 : 1 ≤ c3 P.M.base R.e := Nat.succ_le_of_lt (herzogC_positive _ _ 2)
  rcases actual_normalized_boundary_dichotomy R with h | h
  · have hle : routingC P.M.base R.e ≤ c3 P.M.base R.e*routingC P.M.base R.e := by
      simpa using Nat.mul_le_mul_right (routingC P.M.base R.e) hc3
    simpa only [Nat.sub_add_cancel hle] using cut_add_H h.1 (routingHC _ _)
  · rcases h.2 with ha | hb
    · have hl := Nat.mul_le_mul_right (routingA P.M.base R.e) (show 1 ≤ cr31 R.HD by omega)
      have hle : routingA P.M.base R.e ≤ c3 P.M.base R.e*routingC P.M.base R.e := by
        rw [hr]; exact le_trans (by simpa using hl) (Nat.le_add_right _ _)
      have haH : routingA P.M.base R.e ∈ routingH P.M.base R.e := by
        simpa [normalizedGrid] using grid_mem_H P.M.base R.e 1 0 0
      simpa only [Nat.sub_add_cancel hle] using cut_add_H ha haH
    · have hl := Nat.mul_le_mul_right (routingB P.M.base R.e) (show 1 ≤ cr32 R.HD by omega)
      have hle : routingB P.M.base R.e ≤ c3 P.M.base R.e*routingC P.M.base R.e := by
        rw [hr]; exact le_trans (by simpa using hl) (Nat.le_add_left _ _)
      simpa only [Nat.sub_add_cancel hle] using cut_add_H hb (routingHB _ _)

def sourceQuotientGenerators (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) : Set (ToricPresentation.Poly k 3) :=
  {roleMonomial k R.e (0,c2 P.M.base R.e,0)-
    roleMonomial k R.e (cr21 R.HD,0,cr23 R.HD)} ∪
    Set.range (fun s : ModelSources P.M.base R.e => roleMonomial k R.e (sourceNormal R s)) ∪
    {roleMonomial k R.e (boundaryAliveMonomial R)}

def sourceQuotientIdeal (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) : Ideal (ToricPresentation.Poly k 3) :=
  Ideal.span (sourceQuotientGenerators k R)

/-- Soundness of the literal F2/source/alive-boundary polynomial ideal.
This is only the easy inclusion of C.3, not presentation exactness. -/
theorem sourceQuotientIdeal_le_actual (k : Type*) [Field k] {P : P2Data Gamma}
    (R : ActualRolePacket P) : sourceQuotientIdeal k R ≤ P.M.base.J k := by
  apply Ideal.span_le.mpr
  intro f hf
  rcases hf with (hf | hf) | hf
  · rw [Set.mem_singleton_iff] at hf
    subst f
    have hle : P.M.base.IH k ≤ P.M.base.J k := by
      rw [ChosenBase.Data.J_eq_IH_sup_MK]; exact le_sup_left
    apply hle
    apply L2B.binomial_mem_IH
    rw [roleExponent_weight,roleExponent_weight]
    congr 1
    simpa [monomialDegree,normalizedGrid] using
      (coherent_normalized_relations P.M.base R.e R.HD).2.1
  · obtain ⟨s,rfl⟩ := hf
    apply L2B2A2.boundary_monomial_mem_J
    rw [roleExponent_weight,(sourceNormal_spec R s).1]
    exact (actual_scaled_cut_iff _ _ _).mp s.property.1
  · rw [Set.mem_singleton_iff] at hf
    subst f
    apply L2B2A2.boundary_monomial_mem_J
    rw [roleExponent_weight,boundaryAliveMonomial_degree]
    exact (actual_scaled_cut_iff _ _ _).mp (actual_boundary_degree_in_cut R)

end NS25Lean.L5A2C4OR29
