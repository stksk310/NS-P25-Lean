import NS25Lean.PrincipalSourceFibers
import NS25Lean.AppendixASourceOrder

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.OriginalSourceFibers
open ChosenBase L2B L2B2A L2B2A2 L3B L3C
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]

theorem scale_pos (B : Data Gamma) : 0<transferScale B :=
  lt_trans B.q_positive (transferScale_gt B)

theorem transfer_weight (B : Data Gamma) (v : Fin 3→₀ℕ) :
    weight (transferBase B).base v=transferScale B*weight B v :=
  dilatedData_weight B (transferScale B) (transferScale_gt B) (transferScale_coprime B) v

def transfer_source (B : Data Gamma) (s : Source B) : Source (transferBase B).base :=
  ⟨transferScale B*s.val,
    (dilation_source_iff B (transferScale B) (transferScale_gt B) (transferScale_coprime B) s.val).mpr s.property⟩

/-- Pull the actual tie itself back to the original weights and original
Apéry degree. This is an exact vector identity, not merely an invariant bound. -/
def originalNormal (B : Data Gamma) {h : ℕ}
    (N : TieNormalForm (transferBase B).base h) : TieNormalForm B (weight B N.alpha.val) where
  perm:=N.perm
  a:=N.a
  b:=N.b
  c:=N.c
  a_ge_two:=N.a_ge_two
  b_positive:=N.b_positive
  nontrivial_yz:=N.nontrivial_yz
  alpha:=⟨N.alpha.val,rfl⟩
  beta:=⟨N.beta.val,by
    apply Nat.eq_of_mul_eq_mul_left (scale_pos B)
    rw [←transfer_weight,←transfer_weight]
    exact N.beta.property.trans N.alpha.property.symm⟩
  distinct:=by
    intro he
    have hv : N.alpha.val=N.beta.val:=
      congrArg (fun u : FactorizationFiber B (weight B N.alpha.val)=>u.val) he
    exact N.distinct (Subtype.ext hv)
  exactly_two:=by
    intro u
    let v : FactorizationFiber (transferBase B).base h:=⟨u.val,by
      rw [transfer_weight,u.property,←transfer_weight]
      exact N.alpha.property⟩
    rcases N.exactly_two v with he | he
    · have hv : u.val=N.alpha.val:=
        congrArg (fun u : FactorizationFiber (transferBase B).base h=>u.val) he
      exact Or.inl (Subtype.ext hv)
    · have hv : u.val=N.beta.val:=
        congrArg (fun u : FactorizationFiber (transferBase B).base h=>u.val) he
      exact Or.inr (Subtype.ext hv)
  alpha_eq:=N.alpha_eq
  beta_eq:=N.beta_eq
  apery:=by
    rw [B.apery_eq_compl]
    refine ⟨weight_mem_H B N.alpha.val,?_⟩
    intro hk
    have hA:=N.apery
    rw [(transferBase B).base.apery_eq_compl] at hA
    apply hA.2
    have hcut:transferScale B*weight B N.alpha.val∈(transferBase B).base.K:=
      (dilatedData_K B (transferScale B) (transferScale_gt B) (transferScale_coprime B) _).mpr hk
    rwa [←transfer_weight,N.alpha.property] at hcut

/-- C.3 on the whole fiber of each ORIGINAL minimal source, with no common
coordinate premise. The internal proof retains the exact dilation adapter. -/
theorem source_paths (B : Data Gamma) {h : ℕ}
    (F : InternalFrontend k (transferBase B) h) (s : Source B)
    (u v : FactorizationFiber B s.val) :
    TiePath (originalNormal B F.normal) u.val v.val := by
  change TiePath F.normal u.val v.val
  apply source_presentation_paths F (transfer_source B s)
    (⟨u.val,by rw [transfer_weight,u.property];rfl⟩ : FactorizationFiber (transferBase B).base _)
    (⟨v.val,by rw [transfer_weight,v.property];rfl⟩ : FactorizationFiber (transferBase B).base _)

theorem source_difference (B : Data Gamma) {h : ℕ}
    (F : InternalFrontend k (transferBase B) h) (s : Source B)
    (u v : FactorizationFiber B s.val) :
    ∃ j : ℤ, ∀i, (v.val i:ℤ)=(u.val i:ℤ)+j*tieDelta (originalNormal B F.normal) i :=
  tiePath_integer_difference _ (source_paths B F s u v)

theorem transfer_apery (B : Data Gamma) (w : ℕ) (hw : w∈B.apery) :
    transferScale B*w∈(transferBase B).base.apery := by
  rw [B.apery_eq_compl] at hw
  rw [(transferBase B).base.apery_eq_compl]
  constructor
  · exact (dilatedData_mem_H B (transferScale B) (transferScale_gt B)
      (transferScale_coprime B) _).mpr ⟨w,hw.1,rfl⟩
  · intro hk
    exact hw.2 ((dilatedData_K B (transferScale B) (transferScale_gt B)
      (transferScale_coprime B) w).mp hk)

theorem apery_paths (B : Data Gamma) {h : ℕ}
    (F : InternalFrontend k (transferBase B) h) (w : ℕ) (hw : w∈B.apery)
    (u v : FactorizationFiber B w) :
    TiePath (originalNormal B F.normal) u.val v.val := by
  change TiePath F.normal u.val v.val
  exact apery_presentation_paths F _ (transfer_apery B w hw)
    (⟨u.val,by rw [transfer_weight,u.property]⟩ : FactorizationFiber (transferBase B).base _)
    (⟨v.val,by rw [transfer_weight,v.property]⟩ : FactorizationFiber (transferBase B).base _)

theorem source_chain (B : Data Gamma) {h : ℕ}
    (F : InternalFrontend k (transferBase B) h) (s : Source B) :
    ∃ u₀ : FactorizationFiber B s.val, ∃ l r : ℤ, l≤r ∧
      (∀ v : FactorizationFiber B s.val, ∃ j : ℤ, l≤j ∧ j≤r ∧
        ∀ i, (v.val i:ℤ)=(u₀.val i:ℤ)+j*tieDelta (originalNormal B F.normal) i) ∧
      (∀ j : ℤ, l≤j → j≤r → ∃ v : FactorizationFiber B s.val,
        ∀ i, (v.val i:ℤ)=(u₀.val i:ℤ)+j*tieDelta (originalNormal B F.normal) i) :=
  fiber_chain_of_difference (originalNormal B F.normal) s.val s.property.1.1
    (source_difference B F s)

theorem source_unique_normal (B : Data Gamma) {h : ℕ}
    (F : InternalFrontend k (transferBase B) h) (s : Source B) :
    ∃! u : FactorizationFiber B s.val,
      u.val ((originalNormal B F.normal).perm 0)<(originalNormal B F.normal).a := by
  obtain ⟨u,hu,_⟩:=normalized_fiber_chain_of_difference k (originalNormal B F.normal)
    s.val s.property.1.1 (source_difference B F s)
  refine ⟨u,hu,fun v hv=>?_⟩
  exact slab_unique_of_integer_difference (originalNormal B F.normal) v u
    (source_difference B F s v u) hv hu

/-- No additional toric-presentation premise: defect one itself constructs
the actual original-pivot one-tie source law in the nonmonomial branch. -/
theorem original_one_defect_source_law (B : Data Gamma) (hp : chosenDefect B=1) :
    IsMonomialIdeal k (B.J k) ∨
      ∃ d : ℕ, ∃ N : TieNormalForm B d,
        (∀ s : Source B, ∀ u v : FactorizationFiber B s.val, TiePath N u.val v.val) ∧
        (∀ s : Source B, ∃! u : FactorizationFiber B s.val, u.val (N.perm 0)<N.a) := by
  obtain ⟨h,_,_,hm|hi,hmono,hinternal⟩:=chosen_one_defect_frontend k B hp
  · left
    have hJ: (transferBase B).base.J k=B.J k:=
      dilatedData_J k B (transferScale B) (transferScale_gt B) (transferScale_coprime B)
    simpa only [hJ] using (hmono hm).1
  · obtain ⟨F⟩:=hinternal hi
    exact Or.inr ⟨_,originalNormal B F.normal,source_paths B F,source_unique_normal B F⟩

theorem nonmonomial_original_source_law (B : Data Gamma) (hp : chosenDefect B=1)
    (hn : ¬IsMonomialIdeal k (B.J k)) :
    ∃ d : ℕ, ∃ N : TieNormalForm B d,
      (∀ s : Source B, ∀ u v : FactorizationFiber B s.val, TiePath N u.val v.val) ∧
      (∀ s : Source B, ∃! u : FactorizationFiber B s.val, u.val (N.perm 0)<N.a) :=
  (original_one_defect_source_law B hp).resolve_left hn
/-- Complete C.3 interval on every original minimal source, with a genuine
original-pivot tie constructed from defect one. No auxiliary frontend or
presentation is supplied by the caller. -/
theorem nonmonomial_original_source_chains (B : Data Gamma) (hp : chosenDefect B=1)
    (hn : ¬IsMonomialIdeal k (B.J k)) :
    ∃ d : ℕ, ∃ N : TieNormalForm B d, ∀ s : Source B,
      ∃ u₀ : FactorizationFiber B s.val, u₀.val (N.perm 0)<N.a ∧
        ∃ r : ℤ, 0≤r ∧
          (∀ v : FactorizationFiber B s.val, ∃! j : ℤ, 0≤j ∧ j≤r ∧
            ∀ i, (v.val i:ℤ)=(u₀.val i:ℤ)+j*tieDelta N i) ∧
          (∀ j : ℤ, 0≤j → j≤r → ∃ v : FactorizationFiber B s.val,
            ∀ i, (v.val i:ℤ)=(u₀.val i:ℤ)+j*tieDelta N i) := by
  obtain ⟨d,N,hpaths,_⟩ := nonmonomial_original_source_law B hp hn
  refine ⟨d,N,?_⟩
  intro s
  exact normalized_fiber_chain_of_difference k N s.val s.property.1.1
    (fun u v=>tiePath_integer_difference N (hpaths s u v))

theorem nonmonomial_original_source_binomials (B : Data Gamma) (hp : chosenDefect B=1)
    (hn : ¬IsMonomialIdeal k (B.J k)) :
    ∃ d : ℕ, ∃ N : TieNormalForm B d, ∀ s : Source B,
      ∀ u v : FactorizationFiber B s.val,
        MvPolynomial.monomial u.val (1:k)-MvPolynomial.monomial v.val 1∈principalTieIdeal N := by
  obtain ⟨d,N,hpaths,_⟩ := nonmonomial_original_source_law B hp hn
  exact ⟨d,N,fun s u v=>tiePath_binomial_mem_principal N (hpaths s u v)⟩

/-- Both Apéry and minimal-source fibers are covered at the original B.
The caller supplies only defect one and actual nonmonomiality. -/
theorem nonmonomial_original_fiber_law (B : Data Gamma) (hp : chosenDefect B=1)
    (hn : ¬IsMonomialIdeal k (B.J k)) :
    ∃ d : ℕ, ∃ N : TieNormalForm B d, ∀ w : ℕ,
      w∈B.apery ∨ FourGeneratedBridge.IsMinimalTailGenerator B.H B.K w →
      ∀ u v : FactorizationFiber B w, TiePath N u.val v.val := by
  obtain ⟨h,_,_,hm|hi,hmono,hinternal⟩:=chosen_one_defect_frontend k B hp
  · have hJ: (transferBase B).base.J k=B.J k:=
      dilatedData_J k B (transferScale B) (transferScale_gt B) (transferScale_coprime B)
    have hm' : IsMonomialIdeal k (B.J k):=by simpa only [hJ] using (hmono hm).1
    exact (hn hm').elim
  · obtain ⟨F⟩:=hinternal hi
    refine ⟨_,originalNormal B F.normal,?_⟩
    intro w hw u v
    rcases hw with hw | hw
    · exact apery_paths B F w hw u v
    · exact source_paths B F ⟨w,hw⟩ u v

theorem nonmonomial_original_fiber_intervals (B : Data Gamma) (hp : chosenDefect B=1)
    (hn : ¬IsMonomialIdeal k (B.J k)) :
    ∃ d : ℕ, ∃ N : TieNormalForm B d, ∀ w : ℕ,
      w∈B.apery ∨ FourGeneratedBridge.IsMinimalTailGenerator B.H B.K w →
      ∃ u₀ : FactorizationFiber B w, u₀.val (N.perm 0)<N.a ∧
        ∃ r : ℤ, 0≤r ∧
          (∀ v : FactorizationFiber B w, ∃! j : ℤ, 0≤j ∧ j≤r ∧
            ∀ i, (v.val i:ℤ)=(u₀.val i:ℤ)+j*tieDelta N i) ∧
          (∀ j : ℤ, 0≤j → j≤r → ∃ v : FactorizationFiber B w,
            ∀ i, (v.val i:ℤ)=(u₀.val i:ℤ)+j*tieDelta N i) := by
  obtain ⟨d,N,hpaths⟩:=nonmonomial_original_fiber_law B hp hn
  refine ⟨d,N,?_⟩
  intro w hw
  have hH : w∈B.H := by
    rcases hw with hw | hw
    · exact (B.apery_eq_compl ▸ hw).1
    · exact hw.1.1
  exact normalized_fiber_chain_of_difference k N w hH
    (fun u v=>tiePath_integer_difference N (hpaths w hw u v))

end NS25Lean.OriginalSourceFibers

#print axioms NS25Lean.OriginalSourceFibers.original_one_defect_source_law
#print axioms NS25Lean.OriginalSourceFibers.nonmonomial_original_source_law
#print axioms NS25Lean.OriginalSourceFibers.nonmonomial_original_source_chains
#print axioms NS25Lean.OriginalSourceFibers.nonmonomial_original_source_binomials
#print axioms NS25Lean.OriginalSourceFibers.nonmonomial_original_fiber_law
#print axioms NS25Lean.OriginalSourceFibers.nonmonomial_original_fiber_intervals
