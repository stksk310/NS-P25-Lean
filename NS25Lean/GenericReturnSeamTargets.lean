import NS25Lean.GenericReturnCanonicalRepresentatives
import NS25Lean.GenericReturnMixedRectangle
import NS25Lean.P3IdealHeightsR61

set_option autoImplicit false
set_option linter.style.header false
set_option maxHeartbeats 600000
noncomputable section
namespace NS25Lean.GenericReturn
open SharedTail ErasedSourceScreen PureInternalTransverse
open L5A2B4AR1 L5A2C4I
open scoped Classical
variable {H : NumericalSemigroup}

local instance (D : Positive H) : NeZero D.a := ⟨(D.triple.positive 0).ne'⟩

structure Return (D : Positive H) where
  nu : ℕ
  i : ℕ
  j : ℕ
  depth : ℕ
  strict : RB D i j depth ∨ LT D i j depth
  equation : (i : ℤ)*D.b+j*D.c=(nu : ℤ)+depth*D.a

def Return.transpose {D : Positive H} (R : Return D) : Return D.swapBC where
  nu := R.nu
  i := R.j
  j := R.i
  depth := R.depth
  strict := by
    rcases R.strict with hr | hl
    · exact Or.inr ((transpose_rb D _ _ _).mp hr)
    · exact Or.inl ((transpose_lt D _ _ _).mp hl)
  equation := by
    simpa only [Positive.swapBC_a,Positive.swapBC_b,Positive.swapBC_c,add_comm] using R.equation

def LocalZeroFloor {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D) (x y : ℕ) : Prop :=
  P3R61.idealHeight I D.a hsub ((x*D.b+y*D.c : ℕ) : ZMod D.a)=0 →
    ∃ r, (F r).i≤x ∧ (F r).j≤y

theorem local_floor_of_global_floor {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D)
    (hglobal : ∀ x y, D.ChartA x y →
      (P3R61.idealHeight I D.a hsub ((x*D.b+y*D.c : ℕ) : ZMod D.a)=0 ↔
        ∃ r, (F r).i≤x ∧ (F r).j≤y))
    (x y : ℕ) (hc : D.ChartA x y) : LocalZeroFloor D I hsub F x y :=
  (hglobal x y hc).mp

theorem canonical_int_grid (D : Positive H) (x y : ℤ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x<D.B) (hy : y<D.C)
    (hc : x<D.p ∨ y<D.q) :
    H.asRelativeIdeal.aperyRepresentative D.a ((x*D.b+y*D.c : ℤ) : ZMod D.a)=
      x*D.b+y*D.c := by
  have hxn : (x.toNat : ℤ)=x := Int.toNat_of_nonneg hx0
  have hyn : (y.toNat : ℤ)=y := Int.toNat_of_nonneg hy0
  have hxm : (x.toNat : ZMod D.a)=(x : ZMod D.a) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod D.a)) hxn
    simpa only [Int.cast_natCast] using hh
  have hym : (y.toNat : ZMod D.a)=(y : ZMod D.a) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod D.a)) hyn
    simpa only [Int.cast_natCast] using hh
  have hchart : D.ChartA x.toNat y.toNat := ⟨by omega,by omega,by omega⟩
  have hh := chartA_representative D x.toNat y.toNat hchart
  simpa only [Nat.cast_add,Nat.cast_mul,hxn,hyn,hxm,hym,Int.cast_add,Int.cast_mul,
    Int.cast_natCast] using hh

theorem return_F_mem (D : Positive H) (R : Return D) :
    (R.i : ℤ)*D.b+R.j*D.c∈returnIdeal H R.nu := by
  refine ⟨?_,?_⟩
  · simpa only [zero_mul,zero_add] using combination_int D 0 R.i R.j (by omega) (by omega) (by omega)
  · change (R.i : ℤ)*D.b+R.j*D.c-R.nu∈H.asRelativeIdeal
    rw [R.equation]
    convert combination_int D R.depth 0 0 (by omega) (by omega) (by omega) using 1 <;> ring

theorem rb_X_no_double_zero {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D)
    (hcontain : ∀ r z, z∈returnIdeal H (F r).nu → z∈I)
    (q : ι) (hr : RB D (F q).i (F q).j (F q).depth)
    (hfloor : LocalZeroFloor D I hsub F ((F q).i-1) (D.q-1))
    (hu : I.aperyStepQuotient D.a D.b (D.triple.member (Finsupp.single 1 1))
      ((((F q).i-1)*D.b+(D.q-1)*D.c : ℕ) : ZMod D.a)=0)
    (hv : I.aperyStepQuotient D.a D.c (D.triple.member (Finsupp.single 2 1))
      ((((F q).i-1)*D.b+(D.q-1)*D.c : ℕ) : ZMod D.a)=0) : False := by
  let i := (F q).i
  let j := (F q).j
  let x : ℤ := ((i-1 : ℕ) : ℤ)*D.b+((D.q-1 : ℕ) : ℤ)*D.c
  let y : ℤ := ((i : ℤ)-D.p-1)*D.b
  obtain ⟨hpi,hiB,hj0,hjq,hd0,hdu⟩ := hr
  have sums := D.coefficient_sums
  have hq := D.q_pos
  have hi1 : ((i-1 : ℕ) : ℤ)=(i : ℤ)-1 := by dsimp [i]; have := D.p_pos; omega
  have hq1 : ((D.q-1 : ℕ) : ℤ)=(D.q : ℤ)-1 := by omega
  have hxb : x+D.b=(i : ℤ)*D.b+((D.q-1 : ℕ) : ℤ)*D.c := by dsimp [x]; rw [hi1]; ring
  have hcanB := canonical_int_grid D i (D.q-1 : ℕ) (by omega) (by omega)
    (by dsimp [i]; exact_mod_cast hiB) (by omega) (Or.inr (by omega))
  rw [←hxb] at hcanB
  have hmemB : x+D.b∈I := by
    have hh := ideal_add_int I (hcontain q _ (return_F_mem D (F q)))
      (combination_int D 0 0 ((D.q-1 : ℕ)-(F q).j : ℤ) (by omega) (by omega) (by omega))
    convert hh using 1
    rw [hxb]
    dsimp [i]
    push_cast
    ring
  have hu' : I.aperyStepQuotient D.a D.b (D.triple.member (Finsupp.single 1 1)) (x : ZMod D.a)=0 := by
    simpa only [x,i,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hu
  have hv' : I.aperyStepQuotient D.a D.c (D.triple.member (Finsupp.single 2 1)) (x : ZMod D.a)=0 := by
    simpa only [x,i,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hv
  have hseed := P3R61.zero_b_seed_mem I D.a D.b hsub
    (D.triple.member (Finsupp.single 1 1)) x hcanB hmemB hu'
  have hcanSeed := canonical_int_grid D (i-1 : ℕ) (D.q-1 : ℕ) (by omega) (by omega)
    (by dsimp [i]; omega) (by omega) (Or.inr (by omega))
  have hzero := P3R61.canonical_height_zero I D.a hsub x hcanSeed hseed
  obtain ⟨r,hir,hjr⟩ := hfloor (by
    simpa only [x,i,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hzero)
  have hrr : RB D (F r).i (F r).j (F r).depth := by
    rcases (F r).strict with hrr | hrr
    · exact hrr
    · have := hrr.2.2.1; omega
  obtain ⟨hrpi,hriB,hrj0,hrjq,hrd0,hrdu⟩ := hrr
  have hdA : (F r).depth≤D.A := by omega
  have haxis := (rb_axes_mem D (F r).nu (F r).i (F r).j (F r).depth
    (by have := D.p_pos; omega) hrj0 hrd0 hrpi hrjq hriB (by omega) hrdu (F r).equation).1
  have hcand : y+(D.a : ℤ)*(D.A-(F r).depth : ℕ)∈I := by
    have hh := ideal_add_int I (hcontain r _ haxis)
      (combination_int D 0 ((i : ℤ)-1-(F r).i) 0 (by omega) (by dsimp [i]; omega) (by omega))
    convert hh using 1
    dsimp [y,rbAxisA]
    rw [Nat.cast_sub hdA]
    ring
  have hopp : x+D.c=y+(D.a : ℤ)*D.A := by
    dsimp [x,y]
    rw [hi1,hq1]
    nlinarith only [(relations_int D).1]
  exact P3R61.stencil_zero_b_contradiction I D.a D.b D.c hsub
    (D.triple.member (Finsupp.single 1 1)) (D.triple.member (Finsupp.single 2 1))
    x y D.A (D.A-(F r).depth) hcanB hmemB hopp hu' hv' hcand (by omega)

theorem rb_Y_no_double_zero {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D)
    (hcontain : ∀ r z, z∈returnIdeal H (F r).nu → z∈I)
    (q : ι) (hr : RB D (F q).i (F q).j (F q).depth)
    (hfloor : LocalZeroFloor D I hsub F (D.B-1) ((F q).j-1))
    (hu : I.aperyStepQuotient D.a D.b (D.triple.member (Finsupp.single 1 1))
      (((D.B-1)*D.b+((F q).j-1)*D.c : ℕ) : ZMod D.a)=0)
    (hv : I.aperyStepQuotient D.a D.c (D.triple.member (Finsupp.single 2 1))
      (((D.B-1)*D.b+((F q).j-1)*D.c : ℕ) : ZMod D.a)=0) : False := by
  let j := (F q).j
  let x : ℤ := ((D.B-1 : ℕ) : ℤ)*D.b+((j-1 : ℕ) : ℤ)*D.c
  let y : ℤ := ((j : ℤ)+D.v-1)*D.c
  obtain ⟨hpi,hiB,hj0,hjq,hd0,hdu⟩ := hr
  have sums := D.coefficient_sums
  have hp := D.p_pos
  have hz := D.z_pos
  have hB1 : ((D.B-1 : ℕ) : ℤ)=(D.B : ℤ)-1 := by omega
  have hj1 : ((j-1 : ℕ) : ℤ)=(j : ℤ)-1 := by dsimp [j]; omega
  have hxc : x+D.c=((D.B-1 : ℕ) : ℤ)*D.b+(j : ℤ)*D.c := by dsimp [x]; rw [hj1]; ring
  have hcanC := canonical_int_grid D (D.B-1 : ℕ) j (by omega) (by omega)
    (by omega) (by dsimp [j]; omega) (Or.inr (by dsimp [j]; exact_mod_cast hjq))
  rw [←hxc] at hcanC
  have hmemC : x+D.c∈I := by
    have hh := ideal_add_int I (hcontain q _ (return_F_mem D (F q)))
      (combination_int D 0 ((D.B-1 : ℕ)-(F q).i : ℤ) 0 (by omega) (by omega) (by omega))
    convert hh using 1
    rw [hxc]
    dsimp [j]
    push_cast
    ring
  have hu' : I.aperyStepQuotient D.a D.b (D.triple.member (Finsupp.single 1 1)) (x : ZMod D.a)=0 := by
    simpa only [x,j,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hu
  have hv' : I.aperyStepQuotient D.a D.c (D.triple.member (Finsupp.single 2 1)) (x : ZMod D.a)=0 := by
    simpa only [x,j,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hv
  have hseed := P3R61.zero_c_seed_mem I D.a D.c hsub
    (D.triple.member (Finsupp.single 2 1)) x hcanC hmemC hv'
  have hcanSeed := canonical_int_grid D (D.B-1 : ℕ) (j-1 : ℕ) (by omega) (by omega)
    (by omega) (by dsimp [j]; omega) (Or.inr (by dsimp [j]; omega))
  have hzero := P3R61.canonical_height_zero I D.a hsub x hcanSeed hseed
  obtain ⟨r,hir,hjr⟩ := hfloor (by
    simpa only [x,j,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hzero)
  have hrr : RB D (F r).i (F r).j (F r).depth := by
    rcases (F r).strict with hrr | hrr
    · exact hrr
    · have := hrr.2.2.1; omega
  obtain ⟨hrpi,hriB,hrj0,hrjq,hrd0,hrdu⟩ := hrr
  have haxis := (rb_axes_mem D (F r).nu (F r).i (F r).j (F r).depth
    (by have := D.p_pos; omega) hrj0 hrd0 hrpi hrjq hriB (by omega) hrdu (F r).equation).2
  have hcand : y+(D.a : ℤ)*(D.u-(F r).depth : ℕ)∈I := by
    have hh := ideal_add_int I (hcontain r _ haxis)
      (combination_int D 0 0 ((j : ℤ)-1-(F r).j) (by omega) (by omega) (by dsimp [j]; omega))
    convert hh using 1
    dsimp [y,rbAxisB]
    rw [Nat.cast_sub hrdu.le]
    ring
  have hopp : x+D.b=y+(D.a : ℤ)*D.u := by
    dsimp [x,y]
    rw [hB1,hj1]
    nlinarith only [(relations_int D).2.1]
  exact P3R61.stencil_zero_c_contradiction I D.a D.b D.c hsub
    (D.triple.member (Finsupp.single 1 1)) (D.triple.member (Finsupp.single 2 1))
    x y D.u (D.u-(F r).depth) hcanC hmemC hopp hu' hv' hcand (by omega)

theorem lt_X_no_double_zero {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D)
    (hcontain : ∀ r z, z∈returnIdeal H (F r).nu → z∈I)
    (q : ι) (hr : LT D (F q).i (F q).j (F q).depth)
    (hfloor : LocalZeroFloor D I hsub F ((F q).i-1) (D.C-1))
    (hu : I.aperyStepQuotient D.a D.b (D.triple.member (Finsupp.single 1 1))
      ((((F q).i-1)*D.b+(D.C-1)*D.c : ℕ) : ZMod D.a)=0)
    (hv : I.aperyStepQuotient D.a D.c (D.triple.member (Finsupp.single 2 1))
      ((((F q).i-1)*D.b+(D.C-1)*D.c : ℕ) : ZMod D.a)=0) : False := by
  let i := (F q).i
  let x : ℤ := ((i-1 : ℕ) : ℤ)*D.b+((D.C-1 : ℕ) : ℤ)*D.c
  let y : ℤ := ((i : ℤ)+D.z-1)*D.b
  obtain ⟨hi0,hip,hqj,hjC,hd0,hdw⟩ := hr
  have sums := D.coefficient_sums
  have hp := D.p_pos
  have hq := D.q_pos
  have hi1 : ((i-1 : ℕ) : ℤ)=(i : ℤ)-1 := by dsimp [i]; omega
  have hC1 : ((D.C-1 : ℕ) : ℤ)=(D.C : ℤ)-1 := by omega
  have hxb : x+D.b=(i : ℤ)*D.b+((D.C-1 : ℕ) : ℤ)*D.c := by dsimp [x]; rw [hi1]; ring
  have hcanB := canonical_int_grid D i (D.C-1 : ℕ) (by omega) (by omega)
    (by dsimp [i]; omega) (by omega) (Or.inl (by dsimp [i]; exact_mod_cast hip))
  rw [←hxb] at hcanB
  have hmemB : x+D.b∈I := by
    have hh := ideal_add_int I (hcontain q _ (return_F_mem D (F q)))
      (combination_int D 0 0 ((D.C-1 : ℕ)-(F q).j : ℤ) (by omega) (by omega) (by omega))
    convert hh using 1
    rw [hxb]
    dsimp [i]
    push_cast
    ring
  have hu' : I.aperyStepQuotient D.a D.b (D.triple.member (Finsupp.single 1 1)) (x : ZMod D.a)=0 := by
    simpa only [x,i,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hu
  have hv' : I.aperyStepQuotient D.a D.c (D.triple.member (Finsupp.single 2 1)) (x : ZMod D.a)=0 := by
    simpa only [x,i,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hv
  have hseed := P3R61.zero_b_seed_mem I D.a D.b hsub
    (D.triple.member (Finsupp.single 1 1)) x hcanB hmemB hu'
  have hcanSeed := canonical_int_grid D (i-1 : ℕ) (D.C-1 : ℕ) (by omega) (by omega)
    (by dsimp [i]; omega) (by omega) (Or.inl (by dsimp [i]; omega))
  have hzero := P3R61.canonical_height_zero I D.a hsub x hcanSeed hseed
  obtain ⟨r,hir,hjr⟩ := hfloor (by
    simpa only [x,i,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hzero)
  have hrr : LT D (F r).i (F r).j (F r).depth := by
    rcases (F r).strict with hrr | hrr
    · have := hrr.1; dsimp [i] at *; omega
    · exact hrr
  obtain ⟨hri0,hrip,hrqj,hrjC,hrd0,hrdw⟩ := hrr
  have haxis := (lt_axes_mem D (F r).nu (F r).i (F r).j (F r).depth
    hri0 (by omega) hrd0 hrip hrqj (by omega) hrjC hrdw (F r).equation).1
  have hcand : y+(D.a : ℤ)*(D.w-(F r).depth : ℕ)∈I := by
    have hh := ideal_add_int I (hcontain r _ haxis)
      (combination_int D 0 ((i : ℤ)-1-(F r).i) 0 (by omega) (by dsimp [i]; omega) (by omega))
    convert hh using 1
    dsimp [y,ltAxisA]
    rw [Nat.cast_sub hrdw.le]
    ring
  have hopp : x+D.c=y+(D.a : ℤ)*D.w := by
    dsimp [x,y]
    rw [hi1,hC1]
    nlinarith only [(relations_int D).2.2]
  exact P3R61.stencil_zero_b_contradiction I D.a D.b D.c hsub
    (D.triple.member (Finsupp.single 1 1)) (D.triple.member (Finsupp.single 2 1))
    x y D.w (D.w-(F r).depth) hcanB hmemB hopp hu' hv' hcand (by omega)

theorem lt_Y_no_double_zero {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D)
    (hcontain : ∀ r z, z∈returnIdeal H (F r).nu → z∈I)
    (q : ι) (hr : LT D (F q).i (F q).j (F q).depth)
    (hfloor : LocalZeroFloor D I hsub F (D.p-1) ((F q).j-1))
    (hu : I.aperyStepQuotient D.a D.b (D.triple.member (Finsupp.single 1 1))
      (((D.p-1)*D.b+((F q).j-1)*D.c : ℕ) : ZMod D.a)=0)
    (hv : I.aperyStepQuotient D.a D.c (D.triple.member (Finsupp.single 2 1))
      (((D.p-1)*D.b+((F q).j-1)*D.c : ℕ) : ZMod D.a)=0) : False := by
  let j := (F q).j
  let x : ℤ := ((D.p-1 : ℕ) : ℤ)*D.b+((j-1 : ℕ) : ℤ)*D.c
  let y : ℤ := ((j : ℤ)-D.q-1)*D.c
  obtain ⟨hi0,hip,hqj,hjC,hd0,hdw⟩ := hr
  have sums := D.coefficient_sums
  have hp := D.p_pos
  have hq := D.q_pos
  have hp1 : ((D.p-1 : ℕ) : ℤ)=(D.p : ℤ)-1 := by omega
  have hj1 : ((j-1 : ℕ) : ℤ)=(j : ℤ)-1 := by dsimp [j]; omega
  have hxc : x+D.c=((D.p-1 : ℕ) : ℤ)*D.b+(j : ℤ)*D.c := by dsimp [x]; rw [hj1]; ring
  have hcanC := canonical_int_grid D (D.p-1 : ℕ) j (by omega) (by omega)
    (by omega) (by dsimp [j]; exact_mod_cast hjC) (Or.inl (by omega))
  rw [←hxc] at hcanC
  have hmemC : x+D.c∈I := by
    have hh := ideal_add_int I (hcontain q _ (return_F_mem D (F q)))
      (combination_int D 0 ((D.p-1 : ℕ)-(F q).i : ℤ) 0 (by omega) (by omega) (by omega))
    convert hh using 1
    rw [hxc]
    dsimp [j]
    push_cast
    ring
  have hu' : I.aperyStepQuotient D.a D.b (D.triple.member (Finsupp.single 1 1)) (x : ZMod D.a)=0 := by
    simpa only [x,j,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hu
  have hv' : I.aperyStepQuotient D.a D.c (D.triple.member (Finsupp.single 2 1)) (x : ZMod D.a)=0 := by
    simpa only [x,j,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hv
  have hseed := P3R61.zero_c_seed_mem I D.a D.c hsub
    (D.triple.member (Finsupp.single 2 1)) x hcanC hmemC hv'
  have hcanSeed := canonical_int_grid D (D.p-1 : ℕ) (j-1 : ℕ) (by omega) (by omega)
    (by omega) (by dsimp [j]; omega) (Or.inl (by omega))
  have hzero := P3R61.canonical_height_zero I D.a hsub x hcanSeed hseed
  obtain ⟨r,hir,hjr⟩ := hfloor (by
    simpa only [x,j,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hzero)
  have hrr : LT D (F r).i (F r).j (F r).depth := by
    rcases (F r).strict with hrr | hrr
    · have := hrr.1; omega
    · exact hrr
  obtain ⟨hri0,hrip,hrqj,hrjC,hrd0,hrdw⟩ := hrr
  have hdA : (F r).depth≤D.A := by omega
  have haxis := (lt_axes_mem D (F r).nu (F r).i (F r).j (F r).depth
    hri0 (by omega) hrd0 hrip hrqj (by omega) hrjC hrdw (F r).equation).2
  have hcand : y+(D.a : ℤ)*(D.A-(F r).depth : ℕ)∈I := by
    have hh := ideal_add_int I (hcontain r _ haxis)
      (combination_int D 0 0 ((j : ℤ)-1-(F r).j) (by omega) (by omega) (by dsimp [j]; omega))
    convert hh using 1
    dsimp [y,ltAxisB]
    rw [Nat.cast_sub hdA]
    ring
  have hopp : x+D.b=y+(D.a : ℤ)*D.A := by
    dsimp [x,y]
    rw [hp1,hj1]
    nlinarith only [(relations_int D).1]
  exact P3R61.stencil_zero_c_contradiction I D.a D.b D.c hsub
    (D.triple.member (Finsupp.single 1 1)) (D.triple.member (Finsupp.single 2 1))
    x y D.A (D.A-(F r).depth) hcanC hmemC hopp hu' hv' hcand (by omega)

def routing (D : Positive H) (I : RelativeIdeal H) :=
  (I.toAperyStepData D.a D.b D.c (D.triple.member (Finsupp.single 1 1))
    (D.triple.member (Finsupp.single 2 1))).toResidueData
      (I.toAperyStepData_isValid D.a D.b D.c (D.triple.member (Finsupp.single 1 1))
        (D.triple.member (Finsupp.single 2 1)))

theorem target_seed_zero_edges (D : Positive H) (I : RelativeIdeal H)
    (s : ZMod D.a) (hs : ResidueData.SourceTargetBranch (routing D I) s)
    (x k : ℤ) (hw : I.aperyRepresentative D.a ((routing D I).branchTarget s)=
      x+D.b+D.c+k*D.a) :
    I.aperyStepQuotient D.a D.b (D.triple.member (Finsupp.single 1 1)) (x : ZMod D.a)=0 ∧
    I.aperyStepQuotient D.a D.c (D.triple.member (Finsupp.single 2 1)) (x : ZMod D.a)=0 := by
  have he := I.aperyRepresentative_mod D.a ((routing D I).branchTarget s)
  rw [hw] at he
  change ((x+D.b+D.c+k*D.a : ℤ) : ZMod D.a)=s+D.b+D.c at he
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,mul_zero,add_zero] at he
  have hse : s=(x : ZMod D.a) := by linear_combination -he
  exact ⟨hse ▸ hs.1.1,hse ▸ hs.1.2⟩

theorem rb_X_not_ST_target {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D)
    (hcontain : ∀ r z, z∈returnIdeal H (F r).nu → z∈I)
    (q : ι) (hr : RB D (F q).i (F q).j (F q).depth)
    (hfloor : LocalZeroFloor D I hsub F ((F q).i-1) (D.q-1))
    (s : ZMod D.a) (hs : ResidueData.SourceTargetBranch (routing D I) s)
    (hw : I.aperyRepresentative D.a ((routing D I).branchTarget s)=
      rbAxisA D (F q).i (F q).j (F q).depth) : False := by
  have hp := D.p_pos
  have hq := D.q_pos
  have hi := hr.1
  let x : ℤ := (((F q).i-1 : ℕ) : ℤ)*D.b+((D.q-1 : ℕ) : ℤ)*D.c
  have hweight : rbAxisA D (F q).i (F q).j (F q).depth=
      x+D.b+D.c+(-(F q).depth : ℤ)*D.a := by
    have hi1 : (((F q).i-1 : ℕ) : ℤ)=((F q).i : ℤ)-1 := by omega
    have hq1 : ((D.q-1 : ℕ) : ℤ)=(D.q : ℤ)-1 := by omega
    dsimp [x,rbAxisA]
    rw [hi1,hq1]
    nlinarith only [(relations_int D).1]
  have hz := target_seed_zero_edges D I s hs x (-(F q).depth) (hw.trans hweight)
  apply rb_X_no_double_zero D I hsub F hcontain q hr hfloor
  · simpa only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hz.1
  · simpa only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hz.2

theorem rb_Y_not_ST_target {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D)
    (hcontain : ∀ r z, z∈returnIdeal H (F r).nu → z∈I)
    (q : ι) (hr : RB D (F q).i (F q).j (F q).depth)
    (hfloor : LocalZeroFloor D I hsub F (D.B-1) ((F q).j-1))
    (s : ZMod D.a) (hs : ResidueData.SourceTargetBranch (routing D I) s)
    (hw : I.aperyRepresentative D.a ((routing D I).branchTarget s)=
      rbAxisB D (F q).i (F q).j (F q).depth) : False := by
  have hp := D.p_pos
  have hz := D.z_pos
  have hj := hr.2.2.1
  have sums := D.coefficient_sums
  let x : ℤ := ((D.B-1 : ℕ) : ℤ)*D.b+(((F q).j-1 : ℕ) : ℤ)*D.c
  have hweight : rbAxisB D (F q).i (F q).j (F q).depth=
      x+D.b+D.c+(-(F q).depth : ℤ)*D.a := by
    have hB1 : ((D.B-1 : ℕ) : ℤ)=(D.B : ℤ)-1 := by omega
    have hj1 : (((F q).j-1 : ℕ) : ℤ)=((F q).j : ℤ)-1 := by omega
    dsimp [x,rbAxisB]
    rw [hB1,hj1]
    nlinarith only [(relations_int D).2.1]
  have hz := target_seed_zero_edges D I s hs x (-(F q).depth) (hw.trans hweight)
  apply rb_Y_no_double_zero D I hsub F hcontain q hr hfloor
  · simpa only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hz.1
  · simpa only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hz.2

theorem lt_X_not_ST_target {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D)
    (hcontain : ∀ r z, z∈returnIdeal H (F r).nu → z∈I)
    (q : ι) (hr : LT D (F q).i (F q).j (F q).depth)
    (hfloor : LocalZeroFloor D I hsub F ((F q).i-1) (D.C-1))
    (s : ZMod D.a) (hs : ResidueData.SourceTargetBranch (routing D I) s)
    (hw : I.aperyRepresentative D.a ((routing D I).branchTarget s)=
      ltAxisA D (F q).i (F q).j (F q).depth) : False := by
  have hi := hr.1
  have hj := hr.2.2.2.1
  have hC : 0<D.C := by omega
  let x : ℤ := (((F q).i-1 : ℕ) : ℤ)*D.b+((D.C-1 : ℕ) : ℤ)*D.c
  have hweight : ltAxisA D (F q).i (F q).j (F q).depth=
      x+D.b+D.c+(-(F q).depth : ℤ)*D.a := by
    have hi1 : (((F q).i-1 : ℕ) : ℤ)=((F q).i : ℤ)-1 := by omega
    have hC1 : ((D.C-1 : ℕ) : ℤ)=(D.C : ℤ)-1 := by omega
    dsimp [x,ltAxisA]
    rw [hi1,hC1]
    nlinarith only [(relations_int D).2.2]
  have hz := target_seed_zero_edges D I s hs x (-(F q).depth) (hw.trans hweight)
  apply lt_X_no_double_zero D I hsub F hcontain q hr hfloor
  · simpa only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hz.1
  · simpa only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hz.2

theorem lt_Y_not_ST_target {ι : Type*} (D : Positive H) (I : RelativeIdeal H)
    (hsub : ∀ z∈I, z∈H.asRelativeIdeal) (F : ι→Return D)
    (hcontain : ∀ r z, z∈returnIdeal H (F r).nu → z∈I)
    (q : ι) (hr : LT D (F q).i (F q).j (F q).depth)
    (hfloor : LocalZeroFloor D I hsub F (D.p-1) ((F q).j-1))
    (s : ZMod D.a) (hs : ResidueData.SourceTargetBranch (routing D I) s)
    (hw : I.aperyRepresentative D.a ((routing D I).branchTarget s)=
      ltAxisB D (F q).i (F q).j (F q).depth) : False := by
  have hp := D.p_pos
  have hq := D.q_pos
  have hj := hr.2.2.1
  let x : ℤ := ((D.p-1 : ℕ) : ℤ)*D.b+(((F q).j-1 : ℕ) : ℤ)*D.c
  have hweight : ltAxisB D (F q).i (F q).j (F q).depth=
      x+D.b+D.c+(-(F q).depth : ℤ)*D.a := by
    have hp1 : ((D.p-1 : ℕ) : ℤ)=(D.p : ℤ)-1 := by omega
    have hj1 : (((F q).j-1 : ℕ) : ℤ)=((F q).j : ℤ)-1 := by omega
    dsimp [x,ltAxisB]
    rw [hp1,hj1]
    nlinarith only [(relations_int D).1]
  have hz := target_seed_zero_edges D I s hs x (-(F q).depth) (hw.trans hweight)
  apply lt_Y_no_double_zero D I hsub F hcontain q hr hfloor
  · simpa only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hz.1
  · simpa only [x,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_add,Nat.cast_mul] using hz.2

end NS25Lean.GenericReturn
