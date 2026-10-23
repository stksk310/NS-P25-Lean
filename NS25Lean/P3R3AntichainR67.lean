import NS25Lean.P3R3StaircaseR67

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R67

/-- Distinct coordinatewise minimal floor points, never a multiset of returns. -/
def coordinateMinima (S : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  S.filter (fun x => ∀ y ∈ S, y.1 ≤ x.1 → y.2 ≤ x.2 → x = y)

theorem mem_coordinateMinima (S : Finset (ℕ × ℕ)) (x : ℕ × ℕ) :
    x ∈ coordinateMinima S ↔ x ∈ S ∧ ∀ y ∈ S, y.1 ≤ x.1 → y.2 ≤ x.2 → x=y := by
  simp only [coordinateMinima,Finset.mem_filter]

/-- Every finite floor point is dominated by a genuinely minimal point. -/
theorem coordinate_minima_cover (S : Finset (ℕ × ℕ)) (x : ℕ × ℕ) (hx : x ∈ S) :
    ∃ y ∈ coordinateMinima S, y.1 ≤ x.1 ∧ y.2 ≤ x.2 := by
  classical
  let T := S.filter (fun y => y.1 ≤ x.1 ∧ y.2 ≤ x.2)
  have hT : T.Nonempty := ⟨x,Finset.mem_filter.mpr ⟨hx,le_rfl,le_rfl⟩⟩
  obtain ⟨y,hy,hmin⟩ := T.exists_min_image (fun y => y.1+y.2) hT
  have hy' := Finset.mem_filter.mp hy
  refine ⟨y,(mem_coordinateMinima S y).mpr ⟨hy'.1,?_⟩,hy'.2⟩
  intro z hz hz1 hz2
  have hzT : z ∈ T := Finset.mem_filter.mpr ⟨hz,le_trans hz1 hy'.2.1,le_trans hz2 hy'.2.2⟩
  have hsum := hmin z hzT
  exact Prod.ext (by omega) (by omega)

theorem coordinate_minima_nonempty (S : Finset (ℕ × ℕ)) (hS : S.Nonempty) :
    (coordinateMinima S).Nonempty := by
  obtain ⟨x,hx⟩ := hS
  obtain ⟨y,hy,_⟩ := coordinate_minima_cover S x hx
  exact ⟨y,hy⟩

theorem coordinate_minima_fst_injective (S : Finset (ℕ × ℕ)) :
    Set.InjOn Prod.fst (coordinateMinima S : Set (ℕ × ℕ)) := by
  intro x hx y hy he
  have hxm := (mem_coordinateMinima S x).mp hx
  have hym := (mem_coordinateMinima S y).mp hy
  by_cases hj : x.2 ≤ y.2
  · exact (hym.2 x hxm.1 (by omega) hj).symm
  · exact hxm.2 y hym.1 (by omega) (by omega)

/-- A coordinate antichain admits an actual increasing/decreasing enumeration. -/
theorem coordinate_minima_enumeration (S : Finset (ℕ × ℕ)) :
    ∃ f : Fin (coordinateMinima S).card → ℕ × ℕ,
      Set.range f = (coordinateMinima S : Set (ℕ × ℕ)) ∧
      StrictMono (fun i => (f i).1) ∧ StrictAnti (fun i => (f i).2) := by
  classical
  let E := coordinateMinima S
  let X := E.image Prod.fst
  have hcard : X.card = E.card := Finset.card_image_of_injOn (coordinate_minima_fst_injective S)
  let emb := X.orderEmbOfFin hcard
  have hex : ∀ i : Fin E.card, ∃ x ∈ E, x.1 = emb i := by
    intro i
    exact Finset.mem_image.mp (X.orderEmbOfFin_mem hcard i)
  choose f hf he using hex
  have hmono : StrictMono (fun i => (f i).1) := by
    intro i j hij
    change (f i).1 < (f j).1
    rw [he i,he j]
    exact emb.strictMono hij
  have hrange : Set.range f = (E : Set (ℕ × ℕ)) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩; exact hf i
    · intro hx
      have hxm : x.1 ∈ X := Finset.mem_image_of_mem Prod.fst hx
      have hxr : x.1 ∈ Set.range emb := by
        change x.1 ∈ Set.range (X.orderEmbOfFin hcard)
        rw [Finset.range_orderEmbOfFin]
        exact hxm
      obtain ⟨i,hi⟩ := hxr
      exact ⟨i,coordinate_minima_fst_injective S (hf i) hx ((he i).trans hi)⟩
  refine ⟨f,hrange,hmono,?_⟩
  intro i j hij
  have hm := hmono hij
  change (f i).1 < (f j).1 at hm
  have hmin := ((mem_coordinateMinima S (f j)).mp (hf j)).2
  by_contra hn
  change ¬ (f j).2 < (f i).2 at hn
  have heq := hmin (f i) ((mem_coordinateMinima S (f i)).mp (hf i)).1 (by omega) (by omega)
  have := congrArg Prod.fst heq
  omega

/-- An adjacent staircase southwest corner dominates no antichain point. -/
theorem adjacent_corner_not_dominates (n : ℕ) (f : Fin n → ℕ × ℕ)
    (hi : StrictMono (fun i => (f i).1)) (hj : StrictAnti (fun i => (f i).2))
    (k : Fin (n-1)) (l : Fin n) :
    ¬ ((f l).1 ≤ (f ⟨k.val+1,by omega⟩).1-1 ∧
       (f l).2 ≤ (f ⟨k.val,by omega⟩).2-1) := by
  rintro ⟨hx,hy⟩
  have hstep : (⟨k.val,by omega⟩ : Fin n) < ⟨k.val+1,by omega⟩ := by
    exact Nat.lt_succ_self k.val
  have hxstep : (f ⟨k.val,by omega⟩).1 < (f ⟨k.val+1,by omega⟩).1 := hi hstep
  have hystep : (f ⟨k.val+1,by omega⟩).2 < (f ⟨k.val,by omega⟩).2 := hj hstep
  by_cases hle : l.val ≤ k.val
  · have hh : (⟨k.val,by omega⟩ : Fin n) ≥ l := hle
    have hcomp : (f ⟨k.val,by omega⟩).2 ≤ (f l).2 := hj.antitone hh
    omega
  · have hh : (⟨k.val+1,by omega⟩ : Fin n) ≤ l := by exact Nat.succ_le_iff.mpr (by omega)
    have hcomp : (f ⟨k.val+1,by omega⟩).1 ≤ (f l).1 := hi.monotone hh
    omega

end NS25Lean.P3R67
