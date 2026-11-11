import NS25Lean.P3R3AntichainR67
import NS25Lean.P3R2ZeroRectangleR63

set_option autoImplicit false
set_option linter.style.header false
set_option maxHeartbeats 1000000
noncomputable section
namespace NS25Lean.GenericFloorStaircase
open CombinatorialCore L5A2C4I P3R67
variable {H : NumericalSemigroup}

/-- A genuine canonical rectangle in an arbitrary numerical H and final
H-ideal. No multiplicity datum, defect, merge or endpoint conclusion is an
input. Canonical representative equations express the structural zero carries. -/
theorem floor_staircase_family (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hb : b ∈ H) (hc : c ∈ H)
    (hsub : ∀ z : ℤ, z ∈ I → z ∈ H.asRelativeIdeal)
    (Imax Jmax : ℕ) (S : Finset (ℕ × ℕ)) (hS : S.Nonempty)
    (hcan : ∀ i j : ℕ, i < Imax → j < Jmax →
      H.asRelativeIdeal.aperyRepresentative a
        ((((i:ℤ)*b+j*c):ℤ):ZMod a)=(i:ℤ)*b+j*c)
    (hinjective : ∀ i j i' j' : ℕ, i < Imax → j < Jmax → i' < Imax → j' < Jmax →
      ((((i:ℤ)*b+j*c):ℤ):ZMod a)=((((i':ℤ)*b+j'*c):ℤ):ZMod a) → i=i' ∧ j=j')
    (hbounds : ∀ p ∈ S, p.1 < Imax ∧ p.2 < Jmax)
    (hfloor : ∀ i j : ℕ, i < Imax → j < Jmax →
      ((i : ℤ) * b + j * c ∈ I ↔ ∃ p ∈ S, p.1 ≤ i ∧ p.2 ≤ j)) :
    ∃ base : Fin ((coordinateMinima S).card-1) → ZMod a,
      Function.Injective base ∧
      (∀ k, ResidueData.ExactUnusedMergeReverseBase (P3R60.idealData I a b c hb hc) (base k)) ∧
      (∀ k, ∃ p ∈ S, ∃ q ∈ S, p.1 < q.1 ∧ q.2 < p.2 ∧
        base k=((((q.1-1:ℕ):ℤ)*b+((p.2-1:ℕ):ℤ)*c:ℤ):ZMod a)) := by
  classical
  let n := (coordinateMinima S).card
  have hn : 0<n := Finset.card_pos.mpr (coordinate_minima_nonempty S hS)
  obtain ⟨f,hf,hmono,hanti⟩ := coordinate_minima_enumeration S
  have fmem : ∀ k : Fin n, f k ∈ coordinateMinima S := by
    intro k
    change f k ∈ (coordinateMinima S : Set (ℕ × ℕ))
    rw [← hf]
    exact ⟨k,rfl⟩
  have fbounds : ∀ k : Fin n, (f k).1<Imax ∧ (f k).2<Jmax := by
    intro k
    exact hbounds _ ((mem_coordinateMinima S _).mp (fmem k)).1
  let prev : Fin (n-1) → Fin n := fun k => ⟨k.val,by omega⟩
  let next : Fin (n-1) → Fin n := fun k => ⟨k.val+1,by omega⟩
  let px : Fin (n-1) → ℕ := fun k => (f (next k)).1-1
  let py : Fin (n-1) → ℕ := fun k => (f (prev k)).2-1
  let base : Fin (n-1) → ZMod a := fun k => (((px k : ℤ)*b+py k*c : ℤ) : ZMod a)
  have hxy : ∀ k, px k+1<Imax ∧ py k+1<Jmax := by
    intro k
    have h1 := fbounds (next k)
    have h2 := fbounds (prev k)
    have hnextpos : (f (prev k)).1 < (f (next k)).1 := hmono (show prev k < next k from Nat.lt_succ_self k.val)
    have hprevpos : (f (next k)).2 < (f (prev k)).2 := hanti (show prev k < next k from Nat.lt_succ_self k.val)
    dsimp only [px,py]
    omega
  have hbase : ∀ k, ResidueData.ExactUnusedMergeReverseBase (P3R60.idealData I a b c hb hc) (base k) := by
    intro k
    have hxyk := hxy k
    have hstep : prev k < next k := Nat.lt_succ_self k.val
    have hmx : (f (prev k)).1 < (f (next k)).1 := hmono hstep
    have hmy : (f (next k)).2 < (f (prev k)).2 := hanti hstep
    have hnext := fbounds (next k)
    have hprev := fbounds (prev k)
    have c0 := hcan (px k) (py k) (by omega) (by omega)
    have c1 := hcan (px k+1) (py k) (by omega) (by omega)
    have c2 := hcan (px k) (py k+1) (by omega) (by omega)
    have c3 := hcan (px k+1) (py k+1) (by omega) (by omega)
    have hnmem : (px k : ℤ)*b+py k*c ∉ I := by
      intro hm
      obtain ⟨p,hpS,hpx,hpy⟩ := (hfloor (px k) (py k) (by omega) (by omega)).mp hm
      obtain ⟨q,hq,hqx,hqy⟩ := coordinate_minima_cover S p hpS
      obtain ⟨l,hl⟩ := (show q ∈ Set.range f by rw [hf]; exact hq)
      have hd := adjacent_corner_not_dominates n f hmono hanti k l
      apply hd
      rw [hl]
      exact ⟨le_trans hqx hpx,le_trans hqy hpy⟩
    have east : ((px k+1 : ℕ) : ℤ)*b+py k*c ∈ I := by
      apply (hfloor _ _ (by omega) (by omega)).mpr
      refine ⟨f (next k),((mem_coordinateMinima S _).mp (fmem (next k))).1,?_,?_⟩ <;>
        dsimp only [px,py] <;> omega
    have north : (px k : ℤ)*b+((py k+1 : ℕ) : ℤ)*c ∈ I := by
      apply (hfloor _ _ (by omega) (by omega)).mpr
      refine ⟨f (prev k),((mem_coordinateMinima S _).mp (fmem (prev k))).1,?_,?_⟩ <;>
        dsimp only [px,py] <;> omega
    have ne : ((px k+1 : ℕ) : ℤ)*b+((py k+1 : ℕ) : ℤ)*c ∈ I := by
      apply (hfloor _ _ (by omega) (by omega)).mpr
      refine ⟨f (next k),((mem_coordinateMinima S _).mp (fmem (next k))).1,?_,?_⟩ <;>
        dsimp only [px,py] <;> omega
    have e1 : ((px k+1 : ℕ) : ℤ)*b+py k*c = (px k : ℤ)*b+py k*c+b := by push_cast; ring
    have e2 : (px k : ℤ)*b+((py k+1 : ℕ) : ℤ)*c = (px k : ℤ)*b+py k*c+c := by push_cast; ring
    have e3 : ((px k+1 : ℕ) : ℤ)*b+((py k+1 : ℕ) : ℤ)*c = (px k : ℤ)*b+py k*c+b+c := by push_cast; ring
    rw [e1] at east c1
    rw [e2] at north c2
    rw [e3] at ne c3
    exact unused_merge_of_final_square I a b c hb hc hsub _ c0 c1 c2 c3 hnmem east north ne
  have hinj : Function.Injective base := by
    intro k l he
    have heq := hinjective (px k) (py k) (px l) (py l)
      (by have := hxy k; omega) (by have := hxy k; omega)
      (by have := hxy l; omega) (by have := hxy l; omega) he
    have h1 := fbounds (next k)
    have h2 := fbounds (next l)
    have hkp : (f (prev k)).1 < (f (next k)).1 := hmono (show prev k < next k from Nat.lt_succ_self k.val)
    have hlp : (f (prev l)).1 < (f (next l)).1 := hmono (show prev l < next l from Nat.lt_succ_self l.val)
    have hfst : (f (next k)).1=(f (next l)).1 := by dsimp only [px] at heq; omega
    have hi := hmono.injective hfst
    apply Fin.ext
    have := congrArg Fin.val hi
    dsimp only [next] at this
    omega
  refine ⟨base,hinj,hbase,?_⟩
  intro k
  have hstep : prev k < next k := Nat.lt_succ_self k.val
  exact ⟨f (prev k),((mem_coordinateMinima S _).mp (fmem (prev k))).1,
    f (next k),((mem_coordinateMinima S _).mp (fmem (next k))).1,
    hmono hstep,hanti hstep,rfl⟩

end NS25Lean.GenericFloorStaircase
