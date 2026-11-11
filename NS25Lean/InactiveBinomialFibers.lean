import NS25Lean.PrincipalSourceFibers
import NS25Lean.PresentationCongruence

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A2 L3B FourGeneratedBridge
variable {Gamma : NumericalSemigroup}
abbrev FiberRelation := (Fin 3 →₀ ℕ) × (Fin 3 →₀ ℕ)

def ContextStep (R : Set FiberRelation) (u v : Fin 3 →₀ ℕ) : Prop :=
  ∃ p ∈ R, ∃ t : Fin 3 →₀ ℕ,
    (u = t+p.1 ∧ v = t+p.2) ∨ (u = t+p.2 ∧ v = t+p.1)
abbrev ContextPath (R : Set FiberRelation) := Relation.ReflTransGen (ContextStep R)

theorem contextStep_add (R : Set FiberRelation) {u v : Fin 3 →₀ ℕ}
    (huv : ContextStep R u v) (w : Fin 3 →₀ ℕ) : ContextStep R (w+u) (w+v) := by
  obtain ⟨p,hp,t,he⟩:=huv
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨p,hp,w+t,Or.inl ⟨by simp [add_assoc],by simp [add_assoc]⟩⟩
  · exact ⟨p,hp,w+t,Or.inr ⟨by simp [add_assoc],by simp [add_assoc]⟩⟩

theorem contextStep_symm (R : Set FiberRelation) {u v : Fin 3 →₀ ℕ}
    (huv : ContextStep R u v) : ContextStep R v u := by
  obtain ⟨p,hp,t,he⟩:=huv
  exact ⟨p,hp,t,he.elim (fun h=>Or.inr ⟨h.2,h.1⟩) (fun h=>Or.inl ⟨h.2,h.1⟩)⟩

theorem contextPath_add (R : Set FiberRelation) {u v : Fin 3 →₀ ℕ}
    (huv : ContextPath R u v) (w : Fin 3 →₀ ℕ) : ContextPath R (w+u) (w+v) :=
  huv.lift (fun t=>w+t) (fun _ _ h=>contextStep_add R h w)

theorem contextPath_symm (R : Set FiberRelation) {u v : Fin 3 →₀ ℕ}
    (huv : ContextPath R u v) : ContextPath R v u := by
  induction huv with
  | refl => exact .refl
  | @tail v w _ hvw ih => exact (Relation.ReflTransGen.single (contextStep_symm R hvw)).trans ih

theorem generated_contextPath (R : Set FiberRelation) (u v : Fin 3 →₀ ℕ)
    (h : Presentation.generatedCongruence R u v) : ContextPath R u v := by
  induction h with
  | of x y h => exact .single ⟨(x,y),h,0,Or.inl ⟨by simp,by simp⟩⟩
  | refl x => exact .refl
  | symm h ih => exact contextPath_symm R ih
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | @add w x y z h₁ h₂ ih₁ ih₂ =>
      have ha : ContextPath R (w+y) (x+y) := by
        simpa only [add_comm] using contextPath_add R ih₁ y
      exact ha.trans (contextPath_add R ih₂ x)

theorem contextStep_weight (B : Data Gamma) (R : Set FiberRelation)
    (hhom : ∀p∈R, weight B p.1=weight B p.2) {u v : Fin 3 →₀ ℕ}
    (huv : ContextStep R u v) : weight B u=weight B v := by
  obtain ⟨p,hp,t,he⟩:=huv
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rw [map_add,map_add,hhom p hp]

theorem contextPath_weight (B : Data Gamma) (R : Set FiberRelation)
    (hhom : ∀p∈R, weight B p.1=weight B p.2) {u v : Fin 3 →₀ ℕ}
    (huv : ContextPath R u v) : weight B u=weight B v := by
  induction huv with
  | refl => rfl
  | @tail v w _ hvw ih => exact ih.trans (contextStep_weight B R hhom hvw)

/-- An inactive boundary degree cannot H-divide an Apéry or minimal-source degree. -/
theorem inactive_not_divisor (B : Data Gamma) (w d : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w)
    (hd : d∈B.K) (hnot : ¬IsMinimalTailGenerator B.H B.K d)
    (t : Fin 3 →₀ ℕ) (he : w=d+weight B t) : False := by
  have htH : weight B t∈B.H := by
    rw [weight_eq_degree]
    exact (Presentation.factorizationMap B.tailDegrees t).property
  rcases hw with ha | hs
  · rw [B.apery_eq_compl] at ha
    apply ha.2
    rcases hd with ⟨hdH,hdq,hdG⟩
    change w∈B.H ∧ B.q.val ≤ w ∧ w-B.q.val∈Gamma.toAddSubmonoid
    refine ⟨?_,by omega,?_⟩
    · rw [he];exact B.H.add_mem hdH htH
    · have hh:=Gamma.toAddSubmonoid.add_mem hdG (B.H_le htH)
      convert hh using 1 <;> omega
  · by_cases hz : weight B t=0
    · have hwd : w=d := by omega
      exact hnot (hwd ▸ hs)
    · rcases hs.2 (weight B t) htH hz with hlt | hno
      · omega
      · apply hno
        convert hd using 1 <;> omega

/-- The only active relation at the degree is the displayed principal tie.
All other generators are genuinely inactive K-degrees, not assumed source paths. -/
def InactivePresentation {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (R : Set FiberRelation) : Prop :=
  ∀p∈R, p=(N.alpha.val,N.beta.val) ∨ p=(N.beta.val,N.alpha.val) ∨
    (weight B p.1=weight B p.2 ∧ weight B p.1∈B.K ∧
      ¬IsMinimalTailGenerator B.H B.K (weight B p.1))

theorem inactive_presentation_homogeneous {B : Data Gamma} {h : ℕ}
    (N : TieNormalForm B h) (R : Set FiberRelation) (hr : InactivePresentation N R) :
    ∀p∈R, weight B p.1=weight B p.2 := by
  intro p hp
  rcases hr p hp with rfl | rfl | hi
  · exact N.alpha.property.trans N.beta.property.symm
  · exact N.beta.property.trans N.alpha.property.symm
  · exact hi.1

theorem inactive_contextStep {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (R : Set FiberRelation) (hr : InactivePresentation N R) (w : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w)
    {u v : Fin 3 →₀ ℕ} (hu : weight B u=w) (hs : ContextStep R u v) : TieStep N u v := by
  obtain ⟨p,hp,t,he⟩:=hs
  rcases hr p hp with rfl | rfl | hi
  · exact ⟨t,he⟩
  · exact ⟨t,he.elim (fun hc=>Or.inr hc) (fun hc=>Or.inl hc)⟩
  · have hd : w=weight B p.1+weight B t := by
      rcases he with ⟨heu,_⟩ | ⟨heu,_⟩
      · rw [heu,map_add] at hu;omega
      · rw [heu,map_add] at hu;omega
    exact (inactive_not_divisor B w _ hw hi.2.1 hi.2.2 t hd).elim

theorem inactive_contextPath {B : Data Gamma} {h : ℕ} (N : TieNormalForm B h)
    (R : Set FiberRelation) (hr : InactivePresentation N R) (w : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w)
    {u v : Fin 3 →₀ ℕ} (hu : weight B u=w) (hs : ContextPath R u v) : TiePath N u v := by
  induction hs with
  | refl => exact .refl
  | @tail v z huv hvz ih =>
      have hv : weight B v=w := (contextPath_weight B R (inactive_presentation_homogeneous N R hr) huv).symm.trans hu
      exact ih.trans (.single (inactive_contextStep N R hr w hw hv hvz))

/-- The inactive-relation corollary before any boundary presentation of J:
only the actual toric ideal IH and its homogeneous binomial generators occur. -/
theorem inactive_presentation_paths {k : Type*} [Field k] {B : Data Gamma} {h : ℕ}
    (N : TieNormalForm B h) (R : Set FiberRelation) (hr : InactivePresentation N R)
    (hgen : Presentation.relationIdeal k R=B.IH k) (w : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w)
    (u v : FactorizationFiber B w) : TiePath N u.val v.val := by
  have hb:=binomial_mem_IH k B u.val v.val (u.property.trans v.property.symm)
  change Presentation.relationBinomial k (u.val,v.val)∈B.IH k at hb
  rw [←hgen] at hb
  exact inactive_contextPath N R hr w hw u.property
    (generated_contextPath R u.val v.val (Presentation.generated_of_relationBinomial_mem k R _ _ hb))

theorem inactive_factorization_difference {k : Type*} [Field k] {B : Data Gamma} {h : ℕ}
    (N : TieNormalForm B h) (R : Set FiberRelation) (hr : InactivePresentation N R)
    (hgen : Presentation.relationIdeal k R=B.IH k) (w : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w)
    (u v : FactorizationFiber B w) :
    ∃ j : ℤ, ∀i, (v.val i:ℤ)=(u.val i:ℤ)+j*tieDelta N i :=
  tiePath_integer_difference N (inactive_presentation_paths N R hr hgen w hw u v)

theorem inactive_binomial_mem_principal {k : Type*} [Field k] {B : Data Gamma} {h : ℕ}
    (N : TieNormalForm B h) (R : Set FiberRelation) (hr : InactivePresentation N R)
    (hgen : Presentation.relationIdeal k R=B.IH k) (w : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w)
    (u v : FactorizationFiber B w) :
    MvPolynomial.monomial u.val (1:k)-MvPolynomial.monomial v.val 1∈principalTieIdeal N :=
  tiePath_binomial_mem_principal N (inactive_presentation_paths N R hr hgen w hw u v)

theorem good_degree_mem_H (B : Data Gamma) (w : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w) : w∈B.H := by
  rcases hw with ha | hs
  · exact (B.apery_eq_compl ▸ ha).1
  · exact hs.1.1

theorem inactive_factorization_chain {k : Type*} [Field k] {B : Data Gamma} {h : ℕ}
    (N : TieNormalForm B h) (R : Set FiberRelation) (hr : InactivePresentation N R)
    (hgen : Presentation.relationIdeal k R=B.IH k) (w : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w) :
    ∃ u₀ : FactorizationFiber B w, ∃ l r : ℤ, l ≤ r ∧
      (∀ v : FactorizationFiber B w, ∃ j : ℤ, l ≤ j ∧ j ≤ r ∧
        ∀ i, (v.val i : ℤ)=(u₀.val i : ℤ)+j*tieDelta N i) ∧
      (∀ j : ℤ, l ≤ j → j ≤ r → ∃ v : FactorizationFiber B w,
        ∀ i, (v.val i : ℤ)=(u₀.val i : ℤ)+j*tieDelta N i) :=
  fiber_chain_of_difference N w (good_degree_mem_H B w hw)
    (fun u v=>inactive_factorization_difference N R hr hgen w hw u v)

theorem inactive_normalized_factorization_chain {k : Type*} [Field k] {B : Data Gamma} {h : ℕ}
    (N : TieNormalForm B h) (R : Set FiberRelation) (hr : InactivePresentation N R)
    (hgen : Presentation.relationIdeal k R=B.IH k) (w : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w) :
    ∃ u₀ : FactorizationFiber B w, u₀.val (N.perm 0)<N.a ∧
      ∃ r : ℤ, 0 ≤ r ∧
        (∀ v : FactorizationFiber B w, ∃! j : ℤ, 0 ≤ j ∧ j ≤ r ∧
          ∀ i, (v.val i : ℤ)=(u₀.val i : ℤ)+j*tieDelta N i) ∧
        (∀ j : ℤ, 0 ≤ j → j ≤ r → ∃ v : FactorizationFiber B w,
          ∀ i, (v.val i : ℤ)=(u₀.val i : ℤ)+j*tieDelta N i) :=
  normalized_fiber_chain_of_difference k N w (good_degree_mem_H B w hw)
    (fun u v=>inactive_factorization_difference N R hr hgen w hw u v)

theorem inactive_unique_normal_form {k : Type*} [Field k] {B : Data Gamma} {h : ℕ}
    (N : TieNormalForm B h) (R : Set FiberRelation) (hr : InactivePresentation N R)
    (hgen : Presentation.relationIdeal k R=B.IH k) (w : ℕ)
    (hw : w∈B.apery ∨ IsMinimalTailGenerator B.H B.K w) :
    ∃! u : FactorizationFiber B w, u.val (N.perm 0)<N.a := by
  obtain ⟨u,hu,_⟩:=inactive_normalized_factorization_chain N R hr hgen w hw
  refine ⟨u,hu,fun v hv=>?_⟩
  exact slab_unique_of_integer_difference N v u
    (inactive_factorization_difference N R hr hgen w hw v u) hv hu

end NS25Lean.L3C
