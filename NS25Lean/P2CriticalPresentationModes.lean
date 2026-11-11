import NS25Lean.P2CriticalCapGeometry

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalPresentationModes
open FourGeneratedBridge L5A2C4OR19 ReturnExchange ErasedSourceScreen ReturnSourceRigidity
  ReturnPresentationAdapter PureInternalTransverse CriticalNormalForm CriticalShortFibers CriticalCapGeometry

/-- Exactly the two genuine critical presentations in the common theorem.
Every exponent is tied to the same Base critical minima and physical cut. -/
inductive Mode {H : NumericalSemigroup} (B : Base H) where
  | positive (p q w z : ℕ) (hp : 0<p) (hq : 0<q) (hw : 0<w) (hz : 0<z)
      (hR : B.R=B.u+w) (hC : B.C=p+z) (hL : B.L=q+B.v)
      (center : B.R*B.triple.g 0=p*B.triple.g 1+q*B.triple.g 2)
      (boundary : B.L*B.triple.g 2=w*B.triple.g 0+z*B.triple.g 1) : Mode B
  | purePair (pair : B.R*B.triple.g 0=B.L*B.triple.g 2) : Mode B

def Mode.relations {H : NumericalSemigroup} {B : Base H} : Mode B→Set (Exponent×Exponent)
  | .positive p q w z _ _ _ _ _ _ _ _ _ =>
      {(vector B.R 0 0,vector 0 p q),(vector 0 B.C 0,vector B.u 0 B.v),
        (vector 0 0 B.L,vector w z 0)}
  | .purePair _ => {(vector B.R 0 0,vector 0 0 B.L),(vector 0 B.C 0,vector B.u 0 B.v)}

def Mode.xyCorner {H : NumericalSemigroup} {B : Base H} : Mode B→ℕ→ℕ→Prop
  | .positive _ _ w z _ _ _ _ _ _ _ _ _,x,y => x<w ∨ y<z
  | .purePair _,_,_ => True

def Mode.yzCorner {H : NumericalSemigroup} {B : Base H} : Mode B→ℕ→ℕ→Prop
  | .positive p q _ _ _ _ _ _ _ _ _ _ _,y,z => y<p ∨ z<q
  | .purePair _,_,_ => True

def Mode.Genuine {H : NumericalSemigroup} {B : Base H} (D : Mode B) : Prop :=
  Presentation.relationIdeal ℚ D.relations=
    Presentation.relationIdeal ℚ {lr : Exponent×Exponent | B.triple.weight lr.1=B.triple.weight lr.2}

theorem Mode.relation_weight {H : NumericalSemigroup} {B : Base H} (D : Mode B)
    (lr : Exponent×Exponent) (hlr : lr∈D.relations) :
    B.triple.weight lr.1=B.triple.weight lr.2 := by
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
    rcases hlr with rfl | rfl | rfl <;>
      simp only [vector_weight,Triple.grid,zero_mul,zero_add,add_zero] <;>
      first | assumption | exact B.tie
  | purePair hpair =>
    rcases hlr with rfl | rfl <;>
      simp only [vector_weight,Triple.grid,zero_mul,zero_add,add_zero] <;>
      first | assumption | exact B.tie

theorem Mode.short_xz {H : NumericalSemigroup} {B : Base H} (D : Mode B)
    (hgen : D.Genuine) (x z : ℕ) (hx : x<B.R) (hz : z<B.L)
    (hneck : x<B.u ∨ z<B.v) :
    ∀ e : Exponent, B.triple.weight e=B.triple.weight (vector x 0 z) → e=vector x 0 z := by
  apply unique_of_no_toric_side B.triple D.relations hgen (vector x 0 z)
  intro lr hlr
  cases D with
  | positive p q w t hp hq hw ht hR hC hL hcenter hboundary =>
    have hCp : 0<B.C := B.critical.positive 1
    rcases hlr with rfl | rfl | rfl
    · constructor
      · intro h; have hi := h 0; simp at hi; omega
      · intro h; have hi := h 1; simp at hi; omega
    · constructor
      · intro h; have hi := h 1; simp at hi; omega
      · intro h
        rcases hneck with hneck | hneck
        · have hi := h 0; simp at hi; omega
        · have hi := h 2; simp at hi; omega
    · constructor
      · intro h; have hi := h 2; simp at hi; omega
      · intro h; have hi := h 1; simp at hi; omega
  | purePair hpair =>
    have hCp : 0<B.C := B.critical.positive 1
    rcases hlr with rfl | rfl
    · constructor
      · intro h; have hi := h 0; simp at hi; omega
      · intro h; have hi := h 2; simp at hi; omega
    · constructor
      · intro h; have hi := h 1; simp at hi; omega
      · intro h
        rcases hneck with hneck | hneck
        · have hi := h 0; simp at hi; omega
        · have hi := h 2; simp at hi; omega

theorem Mode.short_xy {H : NumericalSemigroup} {B : Base H} (D : Mode B)
    (hgen : D.Genuine) (x y : ℕ) (hx : x<B.R) (hy : y<B.C)
    (hcorner : D.xyCorner x y) :
    ∀ e : Exponent, B.triple.weight e=B.triple.weight (vector x y 0) → e=vector x y 0 := by
  apply unique_of_no_toric_side B.triple D.relations hgen (vector x y 0)
  intro lr hlr
  have hv := B.v_pos
  have hLp : 0<B.L := B.critical.positive 2
  cases D with
  | positive p q w z hp hq hw hz hR hC hL hcenter hboundary =>
    rcases hlr with rfl | rfl | rfl
    · constructor
      · intro h; have hi := h 0; simp at hi; omega
      · intro h; have hi := h 2; simp at hi; omega
    · constructor
      · intro h; have hi := h 1; simp at hi; omega
      · intro h; have hi := h 2; simp at hi; omega
    · constructor
      · intro h; have hi := h 2; simp at hi; omega
      · intro h
        rcases hcorner with hcorner | hcorner
        · have hi := h 0; simp at hi; omega
        · have hi := h 1; simp at hi; omega
  | purePair hpair =>
    rcases hlr with rfl | rfl
    · constructor
      · intro h; have hi := h 0; simp at hi; omega
      · intro h; have hi := h 2; simp at hi; omega
    · constructor
      · intro h; have hi := h 1; simp at hi; omega
      · intro h; have hi := h 2; simp at hi; omega

theorem Mode.short_yz {H : NumericalSemigroup} {B : Base H} (D : Mode B)
    (hgen : D.Genuine) (y z : ℕ) (hy : y<B.C) (hz : z<B.L)
    (hcorner : D.yzCorner y z) :
    ∀ e : Exponent, B.triple.weight e=B.triple.weight (vector 0 y z) → e=vector 0 y z := by
  apply unique_of_no_toric_side B.triple D.relations hgen (vector 0 y z)
  intro lr hlr
  have hu := B.u_pos
  have hRp : 0<B.R := B.critical.positive 0
  cases D with
  | positive p q w t hp hq hw ht hR hC hL hcenter hboundary =>
    rcases hlr with rfl | rfl | rfl
    · constructor
      · intro h; have hi := h 0; simp at hi; omega
      · intro h
        rcases hcorner with hcorner | hcorner
        · have hi := h 1; simp at hi; omega
        · have hi := h 2; simp at hi; omega
    · constructor
      · intro h; have hi := h 1; simp at hi; omega
      · intro h; have hi := h 0; simp at hi; omega
    · constructor
      · intro h; have hi := h 2; simp at hi; omega
      · intro h; have hi := h 0; simp at hi; omega
  | purePair hpair =>
    rcases hlr with rfl | rfl
    · constructor
      · intro h; have hi := h 0; simp at hi; omega
      · intro h; have hi := h 2; simp at hi; omega
    · constructor
      · intro h; have hi := h 1; simp at hi; omega
      · intro h; have hi := h 0; simp at hi; omega

end NS25Lean.CriticalPresentationModes
