import NS25Lean.P2SectorCFirstPrincipalR19
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option linter.style.header false
noncomputable section

namespace NS25Lean.ReturnExchange
open FourGeneratedBridge L5A2C4OR19
open Classical

/-- A union of actual positive-return intersections, allowing any index subset. -/
def returnCut (H : NumericalSemigroup) (m : ℕ) (E : Set ℕ) : Set ℕ :=
  {s | s ∈ H ∧ ∃ n ∈ E, 0<n ∧ ∃ r ∈ H, s=n*m+r}

abbrev Sources (H : NumericalSemigroup) (m : ℕ) (E : Set ℕ) :=
  {s : ℕ // IsMinimalTailGenerator H.toAddSubmonoid (returnCut H m E) s}

theorem returnCut_univ (H : NumericalSemigroup) (m : ℕ) :
    returnCut H m Set.univ=cyclicCut H m := by
  ext s
  simp only [returnCut,cyclicCut,Set.mem_setOf_eq,Set.mem_univ,true_and]

theorem returnCut_add (H : NumericalSemigroup) {m s d : ℕ} {E : Set ℕ}
    (hs : s∈returnCut H m E) (hd : d∈H) : s+d∈returnCut H m E := by
  obtain ⟨hs,n,hn,hp,r,hr,he⟩ := hs
  exact ⟨H.add_mem hs hd,n,hn,hp,r+d,H.add_mem hr hd,by omega⟩

theorem minimal_iff_literal (H : NumericalSemigroup) (I : Set ℕ) (s : ℕ) :
    IsMinimalTailGenerator H.toAddSubmonoid I s ↔
      s∈I ∧ ∀ t d : ℕ, t∈I → d∈H → s=t+d → d=0 := by
  constructor
  · rintro ⟨hs,hm⟩
    refine ⟨hs,?_⟩
    intro t d ht hd he
    by_contra hn
    rcases hm d hd hn with hlt | hnot
    · omega
    · apply hnot
      simpa [he] using ht
  · rintro ⟨hs,hm⟩
    refine ⟨hs,?_⟩
    intro d hd hn
    by_cases hlt : s<d
    · exact Or.inl hlt
    · exact Or.inr (fun ht => hn (hm (s-d) d ht hd (by omega)))

/-- Separation is valid for every return, and for every common H-summand. -/
theorem source_return_separation (H : NumericalSemigroup) (m : ℕ) (E : Set ℕ)
    (s : Sources H m E) {n y z g : ℕ}
    (hn : n∈E) (hp : 0<n) (hy : y∈H) (hz : z∈H) (hg : g∈H)
    (hs : s.val=z+g) (hr : s.val=n*m+(y+g)) : g=0 := by
  have hcut : z∈returnCut H m E := ⟨hz,n,hn,hp,y,hy,by omega⟩
  exact ((minimal_iff_literal H _ _).mp s.property).2 z g hcut hg hs

/-- The explicit p∈H premise is the actual-predecessor guard. -/
theorem guarded_live_reflection (H : NumericalSemigroup) (m n s r h g d e p : ℕ)
    (hn : 0<n) (hret : s=n*m+r) (hd : d∈H) (he : e∈H) (hp : p∈H)
    (hdiv : h=s+d) (hrg : r=g+e) (hhg : h=g+p) : p∈cyclicCut H m := by
  exact ⟨hp,n,hn,d+e,H.add_mem hd he,by omega⟩

theorem live_reflection_excludes (H : NumericalSemigroup) (m n s r h g d e p : ℕ)
    (hn : 0<n) (hret : s=n*m+r) (hd : d∈H) (he : e∈H) (hp : p∈H)
    (hdiv : h=s+d) (hrg : r=g+e) (hhg : h=g+p)
    (hlive : p∉cyclicCut H m) : False :=
  hlive (guarded_live_reflection H m n s r h g d e p hn hret hd he hp hdiv hrg hhg)

/-- Erasure gives a complementary positive return of the original remainder. -/
theorem cyclic_erasure_reflection (H : NumericalSemigroup) (m Q s n r d : ℕ)
    (hnQ : n<Q) (hr : r∈H) (hd : d∈H)
    (hret : s=n*m+r) (herased : s=Q*m+d) : r∈cyclicCut H m := by
  refine ⟨hr,Q-n,by omega,d,hd,?_⟩
  have hm := congrArg (fun t => t*m) (Nat.sub_add_cancel hnQ.le)
  simp only [Nat.add_mul] at hm
  omega

theorem small_return_positive (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    {s n r : ℕ} (hs : s∈H) (hn : 0<n)
    (hnQ : n<firstPrincipal H m hm) (he : s=n*m+r) : 0<r := by
  by_contra h
  have hz : r=0 := by omega
  have hmem : n*m∈H := by simpa [he,hz] using hs
  have := firstPrincipal_le H m hm hn hmem
  omega

/-- Includes Q=1: there is never another positive return of Qm. -/
theorem first_principal_only_return (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    {n r : ℕ} (hn : 0<n) (hr : r∈H)
    (he : firstPrincipal H m hm*m=n*m+r) :
    n=firstPrincipal H m hm ∧ r=0 := by
  let Q := firstPrincipal H m hm
  change Q*m=n*m+r at he
  have hnQ : n≤Q := by nlinarith
  by_cases hlt : n<Q
  · have hmem : (Q-n)*m∈H := by
      have hm' := congrArg (fun t => t*m) (Nat.sub_add_cancel hnQ)
      simp only [Nat.add_mul] at hm'
      have : (Q-n)*m=r := by omega
      simpa [this] using hr
    have hmin := firstPrincipal_le H m hm (by omega : 0<Q-n) hmem
    change Q≤Q-n at hmin
    omega
  · have hnEq : n=Q := by omega
    rw [←hnEq] at he
    exact ⟨hnEq,by omega⟩

/-- Existence, rather than an assertion about all returns of a nonfirst source. -/
theorem nonfirst_source_small_return (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    (s : {s : ℕ // IsMinimalTailGenerator H.toAddSubmonoid (cyclicCut H m) s})
    (hnf : s.val≠firstPrincipal H m hm*m) :
    ∃ n r : ℕ, 0<n ∧ n<firstPrincipal H m hm ∧ r∈H ∧ 0<r ∧ s.val=n*m+r := by
  obtain ⟨hsH,n,hn,hnQ,r,hr,he⟩ :=
    (cyclicCut_finite_principal_reduction H m hm s.val).mp s.property.1
  have hnlt : n<firstPrincipal H m hm := by
    by_contra h
    have hnq : n=firstPrincipal H m hm := by omega
    have hr0 := ((minimal_iff_literal H _ _).mp s.property).2 _ r
      (firstPrincipal_minimal_cut_source H m hm).1 hr (by simpa [hnq] using he)
    exact hnf (by simpa [hnq,hr0] using he)
  exact ⟨n,r,hn,hnlt,hr,small_return_positive H m hm hsH hn hnlt he,he⟩

/-- Well-founded descent works for every natural subset, without a cofinite premise. -/
theorem minimal_source_cover (H : NumericalSemigroup) (I : Set ℕ) (n : ℕ)
    (hn : n∈I) :
    ∃ s : {s : ℕ // IsMinimalTailGenerator H.toAddSubmonoid I s},
      ∃ d∈H, n=s.val+d := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : IsMinimalTailGenerator H.toAddSubmonoid I n
    · exact ⟨⟨n,hs⟩,0,H.zero_mem,by simp⟩
    have hnot : ¬∀ y d : ℕ, y∈I → d∈H → n=y+d → d=0 := by
      intro h
      exact hs ((minimal_iff_literal H I n).mpr ⟨hn,h⟩)
    push Not at hnot
    obtain ⟨y,d,hy,hd,he,hnz⟩ := hnot
    obtain ⟨s,u,hu,hsu⟩ := ih y (by omega) hy
    exact ⟨s,u+d,H.add_mem hu hd,by omega⟩

/-- Full degree-fiber uniqueness forces literal source divisibility. -/
theorem unique_cut_literal_source_divisor {ι : Type*} [DecidableEq ι]
    (H : NumericalSemigroup) (I : Set ℕ) (hIH : ∀ h∈I, h∈H)
    (W : (ι→₀ℕ)→+ℕ) (hfac : ∀ h∈H, ∃ u, W u=h)
    (M : ι→₀ℕ) (hcut : W M∈I)
    (hUF : ∀ z, W z=W M → z=M) :
    ∃ s : {s : ℕ // IsMinimalTailGenerator H.toAddSubmonoid I s},
      ∃ u : ι→₀ℕ, W u=s.val ∧ u≤M ∧
        (∀ w, W w=s.val → w=u) := by
  obtain ⟨s,d,hd,he⟩ := minimal_source_cover H I (W M) hcut
  obtain ⟨u,hu⟩ := hfac s.val (hIH s.val s.property.1)
  obtain ⟨v,hv⟩ := hfac d hd
  have huv : u+v=M := hUF _ (by rw [map_add,hu,hv]; omega)
  refine ⟨s,u,hu,?_,?_⟩
  · intro i
    have hi := congrArg (fun w : ι→₀ℕ => w i) huv
    simp only [Finsupp.add_apply] at hi
    omega
  · intro w hw
    have hwv : w+v=M := hUF _ (by rw [map_add,hw,hv]; omega)
    exact add_right_cancel (hwv.trans huv.symm)

theorem extracted_coordinate_attained {ι : Type*} [DecidableEq ι]
    (H : NumericalSemigroup) (I : Set ℕ) (hIH : ∀ h∈I, h∈H)
    (W : (ι→₀ℕ)→+ℕ) (hfac : ∀ h∈H, ∃ u, W u=h)
    (M : ι→₀ℕ) (hcut : W M∈I) (hUF : ∀ z, W z=W M → z=M)
    (i : ι)
    (hlower : ∀ s : {s : ℕ // IsMinimalTailGenerator H.toAddSubmonoid I s},
      ∀ u : ι→₀ℕ, W u=s.val → u≤M → M i≤u i) :
    ∃ s : {s : ℕ // IsMinimalTailGenerator H.toAddSubmonoid I s},
      ∃ u : ι→₀ℕ, W u=s.val ∧ u≤M ∧ u i=M i := by
  obtain ⟨s,u,hu,hle,_⟩ := unique_cut_literal_source_divisor H I hIH W hfac M hcut hUF
  exact ⟨s,u,hu,hle,Nat.le_antisymm (hle i) (hlower s u hu hle)⟩

abbrev IdealSources (H : NumericalSemigroup) (I : Set ℕ) :=
  {s : ℕ // IsMinimalTailGenerator H.toAddSubmonoid I s}

def principalAdjoin (H : NumericalSemigroup) (I : Set ℕ) (f : ℕ) : Set ℕ :=
  I∪{s | ∃ d∈H, s=f+d}

def PrincipalErased (H : NumericalSemigroup) (f : ℕ) {I : Set ℕ}
    (s : IdealSources H I) : Prop := ∃ d∈H, s.val=f+d

/-- Every principal insertion has precisely one new source and erases exactly
the old sources divisible by f. No socle correction is inferred here. -/
theorem minimal_principal_adjoin_iff (H : NumericalSemigroup) (I : Set ℕ)
    (hadd : ∀ x∈I, ∀ d∈H, x+d∈I) (f : ℕ) (hf : f∉I) (x : ℕ) :
    IsMinimalTailGenerator H.toAddSubmonoid (principalAdjoin H I f) x ↔
      x=f ∨ (IsMinimalTailGenerator H.toAddSubmonoid I x ∧ ¬∃ d∈H, x=f+d) := by
  have hfm : f∈principalAdjoin H I f := Or.inr ⟨0,H.zero_mem,by simp⟩
  rw [minimal_iff_literal]
  constructor
  · rintro ⟨hx,hm⟩
    rcases hx with hx | ⟨d,hd,he⟩
    · right
      refine ⟨(minimal_iff_literal H I x).mpr ⟨hx,?_⟩,?_⟩
      · intro y d hy hd he
        exact hm y d (Or.inl hy) hd he
      · rintro ⟨d,hd,he⟩
        have hz := hm f d hfm hd he
        have hxf : x=f := by omega
        exact hf (hxf ▸ hx)
    · left
      have hz := hm f d hfm hd he
      omega
  · rintro (rfl | ⟨hx,hn⟩)
    · refine ⟨hfm,?_⟩
      intro y d hy hd he
      rcases hy with hy | ⟨t,ht,he'⟩
      · exact (hf (he ▸ hadd y hy d hd)).elim
      · omega
    · refine ⟨Or.inl hx.1,?_⟩
      intro y d hy hd he
      rcases hy with hy | ⟨t,ht,he'⟩
      · exact ((minimal_iff_literal H I x).mp hx).2 y d hy hd he
      · exact (hn ⟨t+d,H.add_mem ht hd,by omega⟩).elim

def principal_adjoin_source_equiv (H : NumericalSemigroup) (I : Set ℕ)
    (hadd : ∀ x∈I, ∀ d∈H, x+d∈I) (f : ℕ) (hf : f∉I) :
    IdealSources H (principalAdjoin H I f) ≃
      {s : IdealSources H I // ¬PrincipalErased H f s} ⊕ Unit where
  toFun s := if he : s.val=f then Sum.inr () else
    Sum.inl ⟨⟨s.val,(((minimal_principal_adjoin_iff H I hadd f hf _).mp s.property).resolve_left he).1⟩,
      (((minimal_principal_adjoin_iff H I hadd f hf _).mp s.property).resolve_left he).2⟩
  invFun s := match s with
    | Sum.inl s => ⟨s.val.val,(minimal_principal_adjoin_iff H I hadd f hf _).mpr
        (Or.inr ⟨s.val.property,s.property⟩)⟩
    | Sum.inr _ => ⟨f,(minimal_principal_adjoin_iff H I hadd f hf _).mpr (Or.inl rfl)⟩
  left_inv s := by
    dsimp only
    by_cases he : s.val=f
    · simp only [dif_pos he]
      exact Subtype.ext he.symm
    · simp only [dif_neg he]
  right_inv s := by
    cases s with
    | inl s =>
      have hn : s.val.val≠f := by intro h; exact hf (h ▸ s.val.property.1)
      simp only [dif_neg hn]
    | inr s => cases s; simp

theorem principal_adjoin_source_count (H : NumericalSemigroup) (I : Set ℕ)
    (hadd : ∀ x∈I, ∀ d∈H, x+d∈I) (f : ℕ) (hf : f∉I)
    [Finite (IdealSources H I)] :
    Nat.card (IdealSources H (principalAdjoin H I f))+
      Nat.card {s : IdealSources H I // PrincipalErased H f s}=
        Nat.card (IdealSources H I)+1 := by
  letI : Finite {s : IdealSources H I // ¬PrincipalErased H f s} := Subtype.finite
  letI : Finite {s : IdealSources H I // PrincipalErased H f s} := Subtype.finite
  have hs := Nat.card_congr (principal_adjoin_source_equiv H I hadd f hf)
  have hp := Nat.card_congr (Equiv.sumCompl (PrincipalErased H f (I:=I)))
  rw [Nat.card_sum] at hs hp
  simp only [Nat.card_eq_fintype_card,Fintype.card_unit] at hs
  omega

theorem ideal_sources_finite_of_tail (H : NumericalSemigroup) (I : Set ℕ)
    (N : ℕ) (hI : ∀ n : ℕ, N≤n → n∈I) : Finite (IdealSources H I) := by
  obtain ⟨c,hc⟩ := H.exists_conductor
  let a := c+1
  have ha : a∈H := hc a (by dsimp [a]; omega)
  have hapos : 0<a := by dsimp [a]; omega
  have bound (s : IdealSources H I) : s.val<N+a := by
    by_contra hb
    have hy := hI (s.val-a) (by omega)
    have hzero := ((minimal_iff_literal H I _).mp s.property).2
      (s.val-a) a hy ha (by omega)
    omega
  let f : IdealSources H I→Fin (N+a) := fun s => ⟨s.val,bound s⟩
  exact Finite.of_injective f (fun s t h => Subtype.ext (congrArg Fin.val h))

/-- Any nonempty positive-return union is cofinite; the empty union has no
sources. Thus arbitrary index subsets still have finitely many sources. -/
theorem return_sources_finite (H : NumericalSemigroup) (m : ℕ) (E : Set ℕ) :
    Finite (Sources H m E) := by
  classical
  by_cases hex : ∃ n∈E, 0<n
  · obtain ⟨n,hn,hp⟩ := hex
    obtain ⟨c,hc⟩ := H.exists_conductor
    let a := c+1
    have ha : a∈H := hc a (by dsimp [a]; omega)
    have hapos : 0<a := by dsimp [a]; omega
    have bound (s : Sources H m E) : s.val<n*m+c+a := by
      by_contra hb
      have hy : s.val-a∈returnCut H m E := by
        refine ⟨hc _ (by omega),n,hn,hp,s.val-a-n*m,hc _ (by omega),by omega⟩
      have hzero := ((minimal_iff_literal H _ _).mp s.property).2
        (s.val-a) a hy ha (by omega)
      omega
    let f : Sources H m E→Fin (n*m+c+a) := fun s => ⟨s.val,bound s⟩
    exact Finite.of_injective f (fun s t h => Subtype.ext (congrArg Fin.val h))
  · letI : IsEmpty (Sources H m E) := ⟨fun s => by
      obtain ⟨_,n,hn,hp,_⟩ := s.property.1
      exact hex ⟨n,hn,hp⟩⟩
    infer_instance

theorem first_principal_not_in_gap_cut (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    (E : Set ℕ) (hE : ∀ n∈E, n<firstPrincipal H m hm) :
    firstPrincipal H m hm*m∉returnCut H m E := by
  rintro ⟨_,n,hn,hp,r,hr,he⟩
  have heq := (first_principal_only_return H m hm hp hr he).1
  have hlt := hE n hn
  omega

/-- The exact +1-e correction for every gap-index subset, including E=∅. -/
theorem gap_return_source_count (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    (E : Set ℕ) (hE : ∀ n∈E, n<firstPrincipal H m hm) :
    Nat.card (IdealSources H (principalAdjoin H (returnCut H m E)
      (firstPrincipal H m hm*m)))+
      Nat.card {s : Sources H m E // PrincipalErased H (firstPrincipal H m hm*m) s}=
        Nat.card (Sources H m E)+1 := by
  letI := return_sources_finite H m E
  exact principal_adjoin_source_count H (returnCut H m E)
    (fun _ hx _ hd => returnCut_add H hx hd) _
    (first_principal_not_in_gap_cut H m hm E hE)

theorem critical_transport
    (a b c C u v n m : ℤ) (xi zeta xi' zeta' : Fin 3→ℤ) (t : ℤ)
    (hrel : C*b=u*a+v*c)
    (hret : xi 0*a+xi 1*b+xi 2*c=n*m+(zeta 0*a+zeta 1*b+zeta 2*c))
    (h0 : xi' 0-zeta' 0=xi 0-zeta 0-t*u)
    (h1 : xi' 1-zeta' 1=xi 1-zeta 1+t*C)
    (h2 : xi' 2-zeta' 2=xi 2-zeta 2-t*v) :
    xi' 0*a+xi' 1*b+xi' 2*c=n*m+(zeta' 0*a+zeta' 1*b+zeta' 2*c) := by
  linear_combination hret+t*hrel+h0*a+h1*b+h2*c

def H35 (z : ℤ) : Prop := ∃ x y : ℕ, z=3*(x:ℤ)+5*(y:ℤ)

/-- A return expression does not supply the actual predecessor membership. -/
theorem missing_predecessor_guard_counterexample :
    H35 5 ∧ H35 3 ∧ (5:ℤ)=1*2+3 ∧ ¬H35 2 := by
  refine ⟨⟨0,1,by norm_num⟩,⟨1,0,by norm_num⟩,by norm_num,?_⟩
  rintro ⟨x,y,he⟩
  omega

end NS25Lean.ReturnExchange
