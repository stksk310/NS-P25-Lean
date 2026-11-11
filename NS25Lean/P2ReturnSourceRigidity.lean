import NS25Lean.P2ErasedSourceScreen

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.ReturnSourceRigidity
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen

def FullSupport {H : NumericalSemigroup} (T : Triple H) (h : ℕ) : Prop :=
  ∀ i : Fin 3, T.D h i

theorem full_support_source_is_first {H : NumericalSemigroup} (T : Triple H)
    (m : ℕ) (hm : 0<m) (s : IdealSources H (cyclicCut H m))
    (hfull : FullSupport T s.val) : s.val=firstPrincipal H m hm*m := by
  by_contra hnf
  obtain ⟨n,r,hn,_,hr,hp,he⟩ := nonfirst_source_small_return H m hm s hnf
  obtain ⟨i,hi⟩ := T.D_nonempty hr hp
  let se : Sources H m Set.univ :=
    ⟨s.val,by simpa only [returnCut_univ] using s.property⟩
  exact source_remainder_support_disjoint T m Set.univ se (Set.mem_univ n) hn he (hfull i) hi

/-- A relation with a proper K-predecessor cannot divide any actual source
degree, including the first source. -/
theorem source_forbids_inactive_divisor {H : NumericalSemigroup}
    (m : ℕ) (s : IdealSources H (cyclicCut H m))
    (h g d p : ℕ) (hp : p∈cyclicCut H m) (hg : g∈H) (hgpos : 0<g)
    (hd : d∈H) (hh : h=p+g) (hs : s.val=h+d) : False := by
  have hpd := ErasedSourceScreen.cut_add H hp hd
  have hzero := ((minimal_iff_literal H _ _).mp s.property).2 (p+d) g hpd hg (by omega)
  omega

def Move (S : Set (Exponent×Exponent)) (e f : Exponent) : Prop :=
  ∃ l r, (l,r)∈S ∧ ∃ d, e=l+d ∧ f=r+d

theorem move_weight {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent))
    (hrel : ∀ lr∈S, T.weight lr.1=T.weight lr.2)
    {e f : Exponent} (h : Move S e f) : T.weight e=T.weight f := by
  obtain ⟨l,r,hlr,d,rfl,rfl⟩ := h
  simp only [map_add,hrel (l,r) hlr]

theorem relation_union_support {H : NumericalSemigroup} (T : Triple H)
    (l r d : Exponent) (he : T.weight l=T.weight r)
    (hsupp : ∀ i : Fin 3, 0<l i ∨ 0<r i) :
    FullSupport T (T.weight (l+d)) := by
  intro i
  rcases hsupp i with hi | hi
  · exact T.D_of_coordinate (l+d) i (by simpa only [Finsupp.add_apply] using Nat.add_pos_left hi (d i))
  · have hm : T.weight (l+d)=T.weight (r+d) := by simp only [map_add,he]
    rw [hm]
    exact T.D_of_coordinate (r+d) i (by simpa only [Finsupp.add_apply] using Nat.add_pos_left hi (d i))

theorem nonfirst_source_no_full_move {H : NumericalSemigroup} (T : Triple H)
    (m : ℕ) (hm : 0<m) (S : Set (Exponent×Exponent))
    (hrel : ∀ lr∈S, T.weight lr.1=T.weight lr.2)
    (hsupp : ∀ lr∈S, ∀ i : Fin 3, 0<lr.1 i ∨ 0<lr.2 i)
    (s : IdealSources H (cyclicCut H m))
    (hnf : s.val≠firstPrincipal H m hm*m) {e f : Exponent}
    (he : T.weight e=s.val) : ¬Move S e f := by
  rintro ⟨l,r,hlr,d,rfl,_⟩
  have hfull := relation_union_support T l r d (hrel (l,r) hlr) (hsupp (l,r) hlr)
  exact hnf (full_support_source_is_first T m hm s (he ▸ hfull))

theorem path_eq_of_no_move {α : Type*} {r : α→α→Prop} {x y : α}
    (hpath : Relation.ReflTransGen r x y) (hn : ∀ z, ¬r x z) : x=y := by
  induction hpath with
  | refl => rfl
  | tail hp hs ih => exact (hn _ (ih.symm ▸ hs)).elim

/-- Exact full-fiber connectivity and a short monomial admitting no relation
move give full uniqueness, independently of chart-normal representatives. -/
theorem fiber_unique_of_no_move {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent))
    (hconnect : ∀ e f : Exponent, T.weight e=T.weight f →
      Relation.ReflTransGen (Move S) e f)
    (M : Exponent) (hn : ∀ z, ¬Move S M z) :
    ∀ z, T.weight z=T.weight M → z=M := by
  intro z hz
  exact (path_eq_of_no_move (hconnect M z hz.symm) hn).symm

theorem nonfirst_source_unique {H : NumericalSemigroup} (T : Triple H)
    (m : ℕ) (hm : 0<m) (S : Set (Exponent×Exponent))
    (hrel : ∀ lr∈S, T.weight lr.1=T.weight lr.2)
    (hsupp : ∀ lr∈S, ∀ i : Fin 3, 0<lr.1 i ∨ 0<lr.2 i)
    (hconnect : ∀ e f : Exponent, T.weight e=T.weight f →
      Relation.ReflTransGen (Move S) e f)
    (s : IdealSources H (cyclicCut H m))
    (hnf : s.val≠firstPrincipal H m hm*m)
    {e f : Exponent} (he : T.weight e=s.val) (hf : T.weight f=s.val) : e=f := by
  exact path_eq_of_no_move (hconnect e f (he.trans hf.symm))
    (fun z => nonfirst_source_no_full_move T m hm S hrel hsupp s hnf he)

theorem path_weight {H : NumericalSemigroup} (T : Triple H)
    (S : Set (Exponent×Exponent))
    (hrel : ∀ lr∈S, T.weight lr.1=T.weight lr.2)
    {e f : Exponent} (hp : Relation.ReflTransGen (Move S) e f) :
    T.weight e=T.weight f := by
  induction hp with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (move_weight T S hrel hs)

/-- Critical moves are either the full-union-support active relation or have
a genuinely killed proper predecessor. This is a local degree hypothesis,
not source rigidity, unique factorization, or cap attainment stored as data. -/
theorem nonfirst_no_active_or_inactive_move {H : NumericalSemigroup} (T : Triple H)
    (m : ℕ) (hm : 0<m) (S : Set (Exponent×Exponent))
    (hrel : ∀ lr∈S, T.weight lr.1=T.weight lr.2)
    (hclass : ∀ lr∈S,
      (∀ i : Fin 3, 0<lr.1 i ∨ 0<lr.2 i) ∨
      (∃ p∈cyclicCut H m, ∃ g∈H, 0<g ∧ T.weight lr.1=p+g))
    (s : IdealSources H (cyclicCut H m))
    (hnf : s.val≠firstPrincipal H m hm*m) {e f : Exponent}
    (he : T.weight e=s.val) : ¬Move S e f := by
  rintro ⟨l,r,hlr,d,rfl,_⟩
  rcases hclass (l,r) hlr with hfull | ⟨p,hp,g,hg,hgp,hdegree⟩
  · have hfull' := relation_union_support T l r d (hrel (l,r) hlr) hfull
    exact hnf (full_support_source_is_first T m hm s (he ▸ hfull'))
  · apply source_forbids_inactive_divisor m s (T.weight l) g (T.weight d) p hp hg hgp
      (T.member d) hdegree
    simpa only [map_add] using he.symm

theorem nonfirst_unique_active_or_inactive {H : NumericalSemigroup} (T : Triple H)
    (m : ℕ) (hm : 0<m) (S : Set (Exponent×Exponent))
    (hrel : ∀ lr∈S, T.weight lr.1=T.weight lr.2)
    (hclass : ∀ lr∈S,
      (∀ i : Fin 3, 0<lr.1 i ∨ 0<lr.2 i) ∨
      (∃ p∈cyclicCut H m, ∃ g∈H, 0<g ∧ T.weight lr.1=p+g))
    (hconnect : ∀ e f : Exponent, T.weight e=T.weight f →
      Relation.ReflTransGen (Move S) e f)
    (s : IdealSources H (cyclicCut H m))
    (hnf : s.val≠firstPrincipal H m hm*m)
    {e f : Exponent} (he : T.weight e=s.val) (hf : T.weight f=s.val) : e=f := by
  exact path_eq_of_no_move (hconnect e f (he.trans hf.symm))
    (fun z => nonfirst_no_active_or_inactive_move T m hm S hrel hclass s hnf he)

/-- At any source degree, an exact presentation path uses only the active
relations; every inactive step is discharged by proper cut divisibility. -/
theorem source_path_uses_active {H : NumericalSemigroup} (T : Triple H)
    (m : ℕ) (S : Set (Exponent×Exponent)) (active : Exponent×Exponent→Prop)
    (hrel : ∀ lr∈S, T.weight lr.1=T.weight lr.2)
    (hinactive : ∀ lr∈S, ¬active lr →
      ∃ p∈cyclicCut H m, ∃ g∈H, 0<g ∧ T.weight lr.1=p+g)
    (s : IdealSources H (cyclicCut H m)) {e f : Exponent}
    (he : T.weight e=s.val) (hp : Relation.ReflTransGen (Move S) e f) :
    Relation.ReflTransGen (Move {lr | lr∈S ∧ active lr}) e f := by
  classical
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | @tail z y hp hs ih =>
    obtain ⟨l,r,hlr,d,heq,hyeq⟩ := hs
    by_cases ha : active (l,r)
    · exact Relation.ReflTransGen.tail ih ⟨l,r,⟨hlr,ha⟩,d,heq,hyeq⟩
    · obtain ⟨p,hpK,g,hg,hgp,hdegree⟩ := hinactive (l,r) hlr ha
      have hz : T.weight z=s.val := (path_weight T S hrel hp).symm.trans he
      have hsz : s.val=T.weight l+T.weight d := by rw [heq,map_add] at hz; exact hz.symm
      exact (source_forbids_inactive_divisor m s (T.weight l) g (T.weight d) p
        hpK hg hgp (T.member d) hdegree hsz).elim

end NS25Lean.ReturnSourceRigidity
