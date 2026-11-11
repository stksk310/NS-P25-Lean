import NS25Lean.SharedTailPurePair

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse

def TailFiber {H : NumericalSemigroup} (T : Triple H) (h : ℕ) :=
  {e : Exponent // T.weight e=h}
def tailGraph {H : NumericalSemigroup} (T : Triple H) (h : ℕ) : SimpleGraph (TailFiber T h) where
  Adj e f := e≠f ∧ ∃ i : Fin 3, 0<e.val i ∧ 0<f.val i
  symm := ⟨by rintro e f ⟨hne,i,he,hf⟩; exact ⟨hne.symm,i,hf,he⟩⟩
  loopless := ⟨by rintro e ⟨hne,_⟩; exact hne rfl⟩
abbrev TailComponent {H : NumericalSemigroup} (T : Triple H) (h : ℕ) :=
  (tailGraph T h).ConnectedComponent
def tailComponentSupport {H : NumericalSemigroup} (T : Triple H) (h : ℕ)
    (C : TailComponent T h) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun i => ∃ e : TailFiber T h,
    (tailGraph T h).connectedComponentMk e=C ∧ 0<e.val i)

theorem mem_tailComponentSupport {H : NumericalSemigroup} (T : Triple H) (h : ℕ)
    (C : TailComponent T h) (i : Fin 3) : i∈tailComponentSupport T h C ↔
      ∃ e : TailFiber T h, (tailGraph T h).connectedComponentMk e=C ∧ 0<e.val i := by
  classical
  simp only [tailComponentSupport,Finset.mem_filter,Finset.mem_univ,true_and]

theorem tail_same_component_shared {H : NumericalSemigroup} (T : Triple H) (h : ℕ)
    (e f : TailFiber T h) (i : Fin 3) (he : 0<e.val i) (hf : 0<f.val i) :
    (tailGraph T h).connectedComponentMk e=(tailGraph T h).connectedComponentMk f := by
  by_cases hef : e=f
  · rw [hef]
  · exact SimpleGraph.ConnectedComponent.sound (show (tailGraph T h).Adj e f from ⟨hef,i,he,hf⟩).reachable

/-- A singleton-support component of a disconnected fiber is at the true
least outside exponent. This supplies the paper's graph-to-critical bridge. -/
theorem singleton_component_is_critical {H : NumericalSemigroup} (T : Triple H)
    (C : Critical T) (h : ℕ) (hh : 0<h) (i : Fin 3)
    (E F : TailComponent T h) (hne : E≠F) (hs : tailComponentSupport T h E={i}) :
    h=C.exponent i*T.g i := by
  classical
  obtain ⟨u,hu⟩ := E.exists_rep
  obtain ⟨v,hv⟩ := F.exists_rep
  have hupure : u.val=Finsupp.single i (u.val i) := by
    ext j
    by_cases hji : j=i
    · subst j; simp
    · have hz : u.val j=0 := by
        by_contra hn
        have hm := (mem_tailComponentSupport T h E j).mpr ⟨u,hu,Nat.pos_of_ne_zero hn⟩
        simpa [hs,hji] using hm
      simp [hji,hz]
  have hui : 0<u.val i := by
    have hw := u.property
    rw [hupure,T.weight_single] at hw
    nlinarith
  have hvi : v.val i=0 := by
    by_contra hn
    exact hne (hu.symm.trans ((tail_same_component_shared T h u v i hui (Nat.pos_of_ne_zero hn)).trans hv))
  have hdeg : h=u.val i*T.g i := by
    have hw := u.property
    rw [hupure,T.weight_single] at hw
    exact hw.symm
  have hle := C.least i (u.val i) v.val hui hvi (hdeg.symm.trans v.property.symm)
  have hge : u.val i≤C.exponent i := by
    by_contra hn
    obtain ⟨w,hwi,hww⟩ := C.outside i
    let e := Finsupp.single i (u.val i-C.exponent i)+w
    have hew : T.weight e=h := by
      have hsub := Nat.sub_add_cancel hle
      dsimp [e]
      rw [map_add,T.weight_single,hww]
      nlinarith
    let e' : TailFiber T h := ⟨e,hew⟩
    have hei : 0<e i := by simp [e,hwi]; omega
    have heE : (tailGraph T h).connectedComponentMk e'=E :=
      (tail_same_component_shared T h e' u i hei hui).trans hu
    obtain ⟨j,hwj⟩ : ∃ j : Fin 3, 0<w j := by
      by_contra hn
      push Not at hn
      have hw0 : w=0 := by ext j; exact Nat.eq_zero_of_le_zero (hn j)
      have hp := C.positive i
      have hgp := T.positive i
      change 0<T.g i at hgp
      rw [hw0,map_zero] at hww
      nlinarith
    have hji : j≠i := by intro he; subst j; omega
    have hej : 0<e'.val j := by simp only [e',e,Finsupp.add_apply]; omega
    have hm := (mem_tailComponentSupport T h E j).mpr ⟨e',heE,hej⟩
    simpa [hs,hji] using hm
  rw [hdeg,Nat.le_antisymm hge hle]

/-- The paper's two actual singleton-support components produce the full
primitive pure-pair hypothesis package; no normalized exponent is assumed. -/
def purePair_of_singleton_components {H : NumericalSemigroup} (T : Triple H)
    (C : Critical T) (h : ℕ) (hh : 0<h) (E F : TailComponent T h)
    (hne : E≠F) (hE : tailComponentSupport T h E={0})
    (hF : tailComponentSupport T h F={1})
    (hprimitive : Nat.gcd (T.g 0) (Nat.gcd (T.g 1) (T.g 2))=1)
    (hminimal : ∀ i, 2≤C.exponent i) : PurePair H where
  triple := T
  critical := C
  pair := (singleton_component_is_critical T C h hh 0 E F hne hE).symm.trans
    (singleton_component_is_critical T C h hh 1 F E hne.symm hF)
  primitive := hprimitive
  minimal := hminimal

theorem critical_ge_two_of_irredundant {H : NumericalSemigroup} (T : Triple H)
    (C : Critical T)
    (hirr : ∀ (i : Fin 3) (e : Exponent), e i=0 → T.weight e≠T.g i) :
    ∀ i, 2≤C.exponent i := by
  intro i
  have hp := C.positive i
  by_contra hn
  have he : C.exponent i=1 := by omega
  obtain ⟨e,hei,hew⟩ := C.outside i
  exact hirr i e hei (by simpa [he] using hew)

/-- The graph hypothesis together with the literal minimal-three hypothesis
derives the true critical pure-pair package used by all subsequent theorems. -/
def purePair_of_irredundant_singleton_components {H : NumericalSemigroup} (T : Triple H)
    (C : Critical T) (h : ℕ) (hh : 0<h) (E F : TailComponent T h)
    (hne : E≠F) (hE : tailComponentSupport T h E={0})
    (hF : tailComponentSupport T h F={1})
    (hprimitive : Nat.gcd (T.g 0) (Nat.gcd (T.g 1) (T.g 2))=1)
    (hirr : ∀ (i : Fin 3) (e : Exponent), e i=0 → T.weight e≠T.g i) : PurePair H :=
  purePair_of_singleton_components T C h hh E F hne hE hF hprimitive
    (critical_ge_two_of_irredundant T C hirr)

end NS25Lean.SharedTail
