import NS25Lean.GenericReturnStrictGeometry

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturn
open SharedTail ErasedSourceScreen L5A2C4OR19
open scoped Classical
variable {H : NumericalSemigroup}

/-- Adding opposite strict returns gives an actual full-support factorization;
all three coefficients are at least two. -/
theorem opposite_factorization (D : Positive H) (m r q i j d i' j' d' : ℕ)
    (hr : RB D i j d) (hq : LT D i' j' d')
    (her : i*D.b+j*D.c=r*m+d*D.a)
    (heq : i'*D.b+j'*D.c=q*m+d'*D.a) :
    2 ≤ D.A-d-d' ∧ 2 ≤ i-D.p+i' ∧ 2 ≤ j+j'-D.q ∧
      (r+q)*m=(D.A-d-d')*D.a+(i-D.p+i')*D.b+(j+j'-D.q)*D.c := by
  have sums := D.coefficient_sums
  obtain ⟨hpi,hiB,hj0,hjq,hd0,hdu⟩ := hr
  obtain ⟨hi0',hip',hqj',hjC',hd0',hdw'⟩ := hq
  have ha : 2≤D.A-d-d' := by omega
  have hb : 2 ≤ i-D.p+i' := by omega
  have hc : 2≤j+j'-D.q := by omega
  refine ⟨ha,hb,hc,?_⟩
  have h1 := Nat.sub_add_cancel (by omega : d+d'≤D.A)
  have h2 := Nat.sub_add_cancel hpi.le
  have h3 := Nat.sub_add_cancel (by omega : D.q≤j+j')
  have heA : D.A-d-d'=D.A-(d+d') := by omega
  rw [heA]
  nlinarith only [her,heq,D.center,h1,h2,h3]

theorem opposite_levels_ge_principal (D : Positive H) (m : ℕ) (hm : 0<m)
    (r q i j d i' j' d' : ℕ) (hrpos : 0<r) (hqpos : 0<q)
    (hr : RB D i j d) (hq : LT D i' j' d')
    (her : i*D.b+j*D.c=r*m+d*D.a)
    (heq : i'*D.b+j'*D.c=q*m+d'*D.a) :
    firstPrincipal H m hm≤r+q := by
  have he := (opposite_factorization D m r q i j d i' j' d' hr hq her heq).2.2.2
  apply firstPrincipal_le H m hm (by omega)
  rw [he]
  exact combination_mem D _ _ _

def PrefixIndex (H : NumericalSemigroup) (m : ℕ) (hm : 0<m) :=
  {q : ℕ // 0<q ∧ q<firstPrincipal H m hm}

/-- This package states only the preceding strict canonical forms, as required
by the opposite-arm proposition. It contains no common-arm/anchor conclusion. -/
structure StrictFamily (D : Positive H) (m : ℕ) (hm : 0<m) where
  point : PrefixIndex H m hm→ℕ×ℕ×ℕ
  strict : ∀ q, RB D (point q).1 (point q).2.1 (point q).2.2 ∨
    LT D (point q).1 (point q).2.1 (point q).2.2
  equation : ∀ q, (point q).1*D.b+(point q).2.1*D.c=
    q.val*m+(point q).2.2*D.a

def StrictFamily.fromLocalCut (D : Positive H) (K : LocalCut D) (m : ℕ) (hm : 0<m)
    (hreturns : ∀ q : PrefixIndex H m hm, ∀ x, InReturn H (q.val*m) x → x∈K.carrier) :
    StrictFamily D m hm where
  point q := Classical.choose (strict_canonical_return D K (q.val*m)
    (Nat.mul_pos q.property.1 hm)
    (fun h => by have := firstPrincipal_le H m hm q.property.1 h; have := q.property.2; omega)
    (hreturns q))
  strict q := (Classical.choose_spec (strict_canonical_return D K (q.val*m)
    (Nat.mul_pos q.property.1 hm)
    (fun h => by have := firstPrincipal_le H m hm q.property.1 h; have := q.property.2; omega)
    (hreturns q))).1.1
  equation q := (Classical.choose_spec (strict_canonical_return D K (q.val*m)
    (Nat.mul_pos q.property.1 hm)
    (fun h => by have := firstPrincipal_le H m hm q.property.1 h; have := q.property.2; omega)
    (hreturns q))).1.2

def StrictFamily.OnRB {D : Positive H} {m : ℕ} {hm : 0<m}
    (F : StrictFamily D m hm) (q : PrefixIndex H m hm) : Prop :=
  RB D (F.point q).1 (F.point q).2.1 (F.point q).2.2

def StrictFamily.OnLT {D : Positive H} {m : ℕ} {hm : 0<m}
    (F : StrictFamily D m hm) (q : PrefixIndex H m hm) : Prop :=
  LT D (F.point q).1 (F.point q).2.1 (F.point q).2.2

theorem StrictFamily.opposite_levels {D : Positive H} {m : ℕ} {hm : 0<m}
    (F : StrictFamily D m hm) {r q : PrefixIndex H m hm}
    (hr : F.OnRB r) (hq : F.OnLT q) : firstPrincipal H m hm≤r.val+q.val :=
  opposite_levels_ge_principal D m hm r.val q.val _ _ _ _ _ _ r.property.1 q.property.1
    hr hq (F.equation r) (F.equation q)

/-- If both arms occur, one is opposite level one, hence is exactly Q-1. -/
theorem StrictFamily.level_one_anchor {D : Positive H} {m : ℕ} {hm : 0<m}
    (F : StrictFamily D m hm) (hboth : (∃ q, F.OnRB q) ∧ (∃ q, F.OnLT q)) :
    ∃ q : PrefixIndex H m hm, q.val=firstPrincipal H m hm-1 ∧
      ∃ x y z : ℕ, 2≤x ∧ 2≤y ∧ 2≤z ∧
        firstPrincipal H m hm*m=x*D.a+y*D.b+z*D.c := by
  obtain ⟨r,hr⟩ := hboth.1
  obtain ⟨q,hq⟩ := hboth.2
  have hQ : 1<firstPrincipal H m hm := by have := r.property; omega
  let one : PrefixIndex H m hm := ⟨1,by omega,hQ⟩
  rcases F.strict one with h1 | h1
  · have hge := F.opposite_levels h1 hq
    have heq : q.val=firstPrincipal H m hm-1 := by dsimp [one] at hge; have := q.property; omega
    have hf := opposite_factorization D m 1 q.val _ _ _ _ _ _ h1 hq (F.equation one) (F.equation q)
    refine ⟨q,heq,_,_,_,hf.1,hf.2.1,hf.2.2.1,?_⟩
    have hn : 1+q.val=firstPrincipal H m hm := by omega
    simpa only [hn] using hf.2.2.2
  · have hge := F.opposite_levels hr h1
    have heq : r.val=firstPrincipal H m hm-1 := by dsimp [one] at hge; have := r.property; omega
    have hf := opposite_factorization D m r.val 1 _ _ _ _ _ _ hr h1 (F.equation r) (F.equation one)
    refine ⟨r,heq,_,_,_,hf.1,hf.2.1,hf.2.2.1,?_⟩
    have hn : r.val+1=firstPrincipal H m hm := by omega
    simpa only [hn] using hf.2.2.2

theorem StrictFamily.common_arm_of_no_full_support {D : Positive H} {m : ℕ} {hm : 0<m}
    (F : StrictFamily D m hm)
    (hno : ¬∃ x y z : ℕ, 0<x ∧ 0<y ∧ 0<z ∧
      firstPrincipal H m hm*m=x*D.a+y*D.b+z*D.c) :
    (∀ q, F.OnRB q) ∨ (∀ q, F.OnLT q) := by
  by_cases hall : ∀ q, F.OnRB q
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨q,hq⟩ := hall
    have hlt := (F.strict q).resolve_left hq
    intro r
    rcases F.strict r with hr | hr
    · obtain ⟨s,hs,x,y,z,hx,hy,hz,he⟩ := F.level_one_anchor ⟨⟨r,hr⟩,⟨q,hlt⟩⟩
      exact (hno ⟨x,y,z,by omega,by omega,by omega,he⟩).elim
    · exact hr

theorem prefix_empty_at_one (H : NumericalSemigroup) (m : ℕ) (hm : 0<m)
    (hQ : firstPrincipal H m hm=1) : IsEmpty (PrefixIndex H m hm) := by
  refine ⟨fun q => ?_⟩
  have := q.property
  omega

theorem StrictFamily.no_two_arms_at_two {D : Positive H} {m : ℕ} {hm : 0<m}
    (F : StrictFamily D m hm) (hQ : firstPrincipal H m hm=2) :
    ¬((∃ q, F.OnRB q) ∧ (∃ q, F.OnLT q)) := by
  rintro ⟨⟨r,hr⟩,⟨q,hq⟩⟩
  have hreq : r.val=1 := by have := r.property; omega
  have hqeq : q.val=1 := by have := q.property; omega
  have he : r=q := Subtype.ext (by omega)
  subst q
  exact strict_arms_disjoint D _ _ _ ⟨hr,hq⟩

end NS25Lean.GenericReturn
