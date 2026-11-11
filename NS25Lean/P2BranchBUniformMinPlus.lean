import NS25Lean.P2BranchBPrefixOrigin

set_option linter.style.header false
noncomputable section
namespace NS25Lean.BranchBUniformMinPlus
open scoped Classical

/-- Generator-level data for an arbitrary admitted family of L-chart returns.
No prefix ideal, minimum, seam closure or target count is assumed. -/
structure Data where
  Index : Type
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  p : ℕ
  q : ℕ
  u : ℕ
  v : ℕ
  w : ℕ
  z : ℕ
  coefficients : 0<p ∧ 0<q ∧ 0<u ∧ 0<v ∧ 0<w ∧ 0<z ∧
    c1=u+w ∧ c2=p+z ∧ c3=q+v
  tuple : Index → ℕ × ℕ × ℕ
  tuple_spec : ∀ ell, let t := tuple ell
    (t.1<c2 ∧ t.2.1<c3 ∧ (t.1<p ∨ t.2.1<q)) ∧
    0<t.1 ∧ 0<t.2.1 ∧ 0<t.2.2 ∧
    (t.1<p → t.2.2<w) ∧ (t.2.1<q → t.2.2<u)
  origin : ∃ ell, (tuple ell).1≤p ∧ (tuple ell).2.1≤q

def Candidate (D : Data) (x y h : ℕ) : Prop :=
  ∃ ell : D.Index,
    let t := D.tuple ell
    (t.1≤x ∧ t.2.1≤y ∧ h=0) ∨
    (t.1<D.p ∧ t.2.1<D.q ∧ h=D.c1-t.2.2) ∨
    (D.p≤t.1 ∧ t.1-D.p≤x ∧ h=D.c1-t.2.2) ∨
    (D.q≤t.2.1 ∧ t.2.1-D.q≤y ∧ h=D.c1-t.2.2) ∨
    (t.1<D.p ∧ t.1+D.z≤x ∧ h=D.w-t.2.2) ∨
    (t.2.1<D.q ∧ t.2.1+D.v≤y ∧ h=D.u-t.2.2)

theorem depth_lt (D : Data) (ell : D.Index) : (D.tuple ell).2.2<D.c1 := by
  have S := D.tuple_spec ell
  have hp := D.coefficients
  rcases S.1.2.2 with h | h
  · have := S.2.2.2.2.1 h; omega
  · have := S.2.2.2.2.2 h; omega

theorem candidate_nonempty (D : Data) (x y : ℕ) :
    Nonempty {h : ℕ // Candidate D x y h} := by
  obtain ⟨ell,hi,hj⟩ := D.origin
  refine ⟨⟨D.c1-(D.tuple ell).2.2,ell,?_⟩⟩
  by_cases hip : (D.tuple ell).1 < D.p
  · by_cases hjq : (D.tuple ell).2.1 < D.q
    · exact Or.inr (Or.inl ⟨hip,hjq,rfl⟩)
    · right; right; right; left
      exact ⟨by omega,by omega,rfl⟩
  · right; right; left
    exact ⟨by omega,by omega,rfl⟩

theorem candidate_exists (D : Data) (x y : ℕ) : ∃ h, Candidate D x y h := by
  obtain ⟨h⟩ := candidate_nonempty D x y
  exact ⟨h.val,h.property⟩

def height (D : Data) (x y : ℕ) : ℕ := Nat.find (candidate_exists D x y)

theorem height_attained (D : Data) (x y : ℕ) : Candidate D x y (height D x y) :=
  Nat.find_spec (candidate_exists D x y)

theorem le_candidate (D : Data) {x y h : ℕ} (hc : Candidate D x y h) :
    height D x y ≤ h := Nat.find_min' (candidate_exists D x y) hc

theorem candidate_lt_c1 (D : Data) {x y h : ℕ} (hc : Candidate D x y h) : h<D.c1 := by
  obtain ⟨ell,hc⟩ := hc
  have S := D.tuple_spec ell
  have hd := depth_lt D ell
  have hp := D.coefficients
  rcases hc with ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ <;> omega

theorem height_lt_c1 (D : Data) (x y : ℕ) : height D x y<D.c1 :=
  candidate_lt_c1 D (height_attained D x y)

theorem candidate_zero_iff (D : Data) (x y : ℕ) :
    Candidate D x y 0 ↔ ∃ ell, (D.tuple ell).1≤x ∧ (D.tuple ell).2.1≤y := by
  constructor
  · rintro ⟨ell,hc⟩
    have S := D.tuple_spec ell
    have hd := depth_lt D ell
    rcases hc with ⟨hi,hj,_⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨_,_,he⟩ | ⟨hi,_,he⟩ | ⟨hj,_,he⟩
    · exact ⟨ell,hi,hj⟩
    · omega
    · omega
    · omega
    · have := S.2.2.2.2.1 hi; omega
    · have := S.2.2.2.2.2 hj; omega
  · rintro ⟨ell,hi,hj⟩
    exact ⟨ell,Or.inl ⟨hi,hj,rfl⟩⟩

theorem height_zero_iff (D : Data) (x y : ℕ) :
    height D x y=0 ↔ ∃ ell, (D.tuple ell).1≤x ∧ (D.tuple ell).2.1≤y := by
  constructor
  · intro he
    have hm := height_attained D x y
    rw [he] at hm
    exact (candidate_zero_iff D x y).mp hm
  · intro hm
    have hl := le_candidate D ((candidate_zero_iff D x y).mpr hm)
    omega

theorem candidate_mono (D : Data) {x y x' y' h : ℕ}
    (hc : Candidate D x y h) (hx : x≤x') (hy : y≤y') : Candidate D x' y' h := by
  obtain ⟨ell,hc⟩ := hc
  refine ⟨ell,?_⟩
  rcases hc with ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ |
    ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩
  · exact Or.inl ⟨by omega,by omega,he⟩
  · exact Or.inr (Or.inl ⟨hi,hj,he⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hi,by omega,he⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,by omega,he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,by omega,he⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hi,by omega,he⟩))))

theorem antitone (D : Data) {x y x' y' : ℕ} (hx : x≤x') (hy : y≤y') :
    height D x' y'≤height D x y :=
  le_candidate D (candidate_mono D (height_attained D x y) hx hy)

theorem outer_b (D : Data) {y : ℕ} (hy : y<D.q) :
    height D 0 (y+D.v) ≤ height D (D.c2-1) y+D.u := by
  obtain ⟨ell,hc⟩ := height_attained D (D.c2-1) y
  have S := D.tuple_spec ell
  have hp := D.coefficients
  have hd := depth_lt D ell
  have upper := height_lt_c1 D 0 (y+D.v)
  have dom := S.1
  change (D.tuple ell).1 < D.c2 ∧ (D.tuple ell).2.1 < D.c3 ∧ ((D.tuple ell).1 < D.p ∨ (D.tuple ell).2.1 < D.q) at dom
  have bound {h : ℕ} (hc : Candidate D 0 (y+D.v) h) :=
    le_candidate D hc
  rcases hc with ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hx,he⟩ |
    ⟨hj,hy',he⟩ | ⟨hi,hx,he⟩ | ⟨hj,hy',he⟩
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨by omega,by omega,rfl⟩))))⟩
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
    omega
  · have hj : (D.tuple ell).2.1 < D.q := by
      rcases S.1.2.2 with h | h <;> omega
    have hb := S.2.2.2.2.2 hj
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inl ⟨hj,by omega,rfl⟩)))⟩
    omega
  · have hb := S.2.2.2.2.1 hi
    by_cases hj : (D.tuple ell).2.1 < D.q
    · have hl := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
      omega
    · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega,by omega,rfl⟩)))⟩
      omega
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hj,by omega,rfl⟩))))⟩
    omega

theorem outer_c (D : Data) {x : ℕ} (hx : x<D.p) :
    height D (x+D.z) 0 ≤ height D x (D.c3-1)+D.w := by
  obtain ⟨ell,hc⟩ := height_attained D x (D.c3-1)
  have S := D.tuple_spec ell
  have hp := D.coefficients
  have hd := depth_lt D ell
  have upper := height_lt_c1 D (x+D.z) 0
  have dom := S.1
  change (D.tuple ell).1 < D.c2 ∧ (D.tuple ell).2.1 < D.c3 ∧ ((D.tuple ell).1 < D.p ∨ (D.tuple ell).2.1 < D.q) at dom
  have bound {h : ℕ} (hc : Candidate D (x+D.z) 0 h) :=
    le_candidate D hc
  rcases hc with ⟨hi,hj,he⟩ | ⟨hi,hj,he⟩ | ⟨hi,hx',he⟩ |
    ⟨hj,hy,he⟩ | ⟨hi,hx',he⟩ | ⟨hj,hy,he⟩
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega,by omega,rfl⟩))))⟩
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inl ⟨hi,by omega,rfl⟩))⟩
    omega
  · have hi : (D.tuple ell).1 < D.p := by
      rcases S.1.2.2 with h | h <;> omega
    have hb := S.2.2.2.2.1 hi
    omega
  · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,by omega,rfl⟩))))⟩
    omega
  · have hb := S.2.2.2.2.2 hj
    by_cases hi : (D.tuple ell).1 < D.p
    · have hl := bound ⟨ell,Or.inr (Or.inl ⟨hi,hj,rfl⟩)⟩
      omega
    · have hl := bound ⟨ell,Or.inr (Or.inr (Or.inl ⟨by omega,by omega,rfl⟩))⟩
      omega

theorem inner_b (D : Data) (x y : ℕ) :
    height D 0 (y-D.q)≤height D x y+D.c1 := by
  have := height_lt_c1 D 0 (y-D.q)
  omega

theorem inner_c (D : Data) (x y : ℕ) :
    height D (x-D.p) 0≤height D x y+D.c1 := by
  have := height_lt_c1 D (x-D.p) 0
  omega

/-- Every ordinary step and all four seams preserve the same min-plus ideal. -/
theorem generator_closure (D : Data) :
    (∀ x y x' y', x≤x' → y≤y' → height D x' y'≤height D x y) ∧
    (∀ x y, height D 0 (y-D.q)≤height D x y+D.c1) ∧
    (∀ x y, height D (x-D.p) 0≤height D x y+D.c1) ∧
    (∀ y, y<D.q → height D 0 (y+D.v)≤height D (D.c2-1) y+D.u) ∧
    (∀ x, x<D.p → height D (x+D.z) 0≤height D x (D.c3-1)+D.w) :=
  ⟨fun _ _ _ _ hx hy => antitone D hx hy,inner_b D,inner_c D,
    fun _ hy => outer_b D hy,fun _ hx => outer_c D hx⟩

end NS25Lean.BranchBUniformMinPlus

namespace NS25Lean.L5A2BFinalRepair
open ChosenBase FourGeneratedBridge L2B L5A1 L5A2B4AR1 L5A2B4AR4R1
open L5A2B4AR5B L5A2C4H L5A2C4C L5A2C4OR3
variable {Gamma : NumericalSemigroup} {P : P2Data Gamma}

/-- The universal input is derived from the actual semigroup return witnesses,
including the inclusive origin. BAL and Q≥3 are absent. -/
def nonsymmetricUniformMinPlusData (R : SectorBCriticalRoleBranchB P)
    (hB : SectorB P.M) (hQ : 1<actualPrincipalIndex P.M.base) :
    BranchBUniformMinPlus.Data where
  Index := NonsymmetricReturnIndex R
  c1 := nsC1 R
  c2 := nsC2 R
  c3 := nsC3 R
  p := nsP R
  q := nsQ R
  u := nsU R
  v := nsV R
  w := nsW R
  z := nsZ R
  coefficients := nonsymmetric_coefficients R
  tuple := nonsymmetricReturnTuple R hB
  tuple_spec := by
    intro ell
    have S := nonsymmetricReturnTuple_spec R hB ell
    exact ⟨S.1,S.2.1,S.2.2.1,S.2.2.2.1,S.2.2.2.2.1,S.2.2.2.2.2.1⟩
  origin := nonsymmetric_inclusive_origin_return R hB hQ

end NS25Lean.L5A2BFinalRepair
