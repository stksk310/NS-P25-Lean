import NS25Lean.GenericReturnTriples

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturn
open SharedTail ErasedSourceScreen PureInternalTransverse
open scoped Classical
variable {H : NumericalSemigroup}

/-- A unique full factorization omitting an axis is its actual least residue
representative. The competing vector is unrestricted. -/
theorem omitted_axis_representative (T : Triple H) (axis : Fin 3) (e : ErasedSourceScreen.Exponent)
    (hei : e axis=0) (hu : ∀ f, T.weight f=T.weight e → f=e) :
    letI : NeZero (T.g axis) := ⟨(T.positive axis).ne'⟩
    H.asRelativeIdeal.aperyRepresentative (T.g axis) (T.weight e : ZMod (T.g axis))=
      (T.weight e : ℤ) := by
  letI : NeZero (T.g axis) := ⟨(T.positive axis).ne'⟩
  let alpha := H.asRelativeIdeal.aperyRepresentative (T.g axis) (T.weight e : ZMod (T.g axis))
  have ha : alpha∈H.asRelativeIdeal := H.asRelativeIdeal.aperyRepresentative_mem _ _
  obtain ⟨n,hn,han⟩ := ha
  have hal : alpha≤T.weight e := H.asRelativeIdeal.aperyRepresentative_le _ _
    ⟨T.weight e,T.member e,rfl⟩ (by simp)
  have ham := H.asRelativeIdeal.aperyRepresentative_mod (T.g axis) (T.weight e : ZMod (T.g axis))
  obtain ⟨k,hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq (T.g axis) hal
    (by simpa only [Int.cast_natCast] using ham.symm)
  obtain ⟨f,hfw⟩ := T.factor n hn
  have hnat : T.weight e=n+T.g axis*k := by rw [han] at hk; exact_mod_cast hk
  have hweight : T.weight (Finsupp.single axis k+f)=T.weight e := by
    rw [map_add,T.weight_single,hfw]
    nlinarith only [hnat]
  have heq := hu _ hweight
  have hx := congrArg (fun v : ErasedSourceScreen.Exponent => v axis) heq
  simp only [Finsupp.add_apply,Finsupp.single_eq_same,hei] at hx
  have hk0 : k=0 := by omega
  simp only [hk0,Nat.cast_zero,mul_zero,add_zero] at hk
  exact hk.symm

theorem chartA_representative (D : Positive H) (i j : ℕ) (hc : D.ChartA i j) :
    letI : NeZero D.a := ⟨(D.triple.positive 0).ne'⟩
    H.asRelativeIdeal.aperyRepresentative D.a ((i*D.b+j*D.c : ℕ) : ZMod D.a)=
      (i*D.b+j*D.c : ℕ) := by
  have h := omitted_axis_representative D.triple 0 (vector 0 i j) (by simp) (by
    intro f hf
    apply D.chartA_factorization_unique i j hc f
    simpa only [vector_weight,Triple.grid,zero_mul,zero_add] using hf)
  simpa only [vector_weight,Triple.grid,zero_mul,zero_add] using h

theorem rb_remainders (D : Positive H) (nu i j d : ℕ) (hr : RB D i j d)
    (he : (i : ℤ)*D.b+j*D.c=(nu : ℤ)+d*D.a) :
    rbAxisA D i j d-nu=((D.q-j : ℕ) : ℤ)*D.c ∧
    rbAxisB D i j d-nu=((D.B-i : ℕ) : ℤ)*D.b ∧
    (i : ℤ)*D.b+j*D.c-nu=(d : ℤ)*D.a := by
  have hqj := Nat.sub_add_cancel hr.2.2.2.1.le
  have hBi := Nat.sub_add_cancel hr.2.1.le
  have hqjZ : (D.q-j : ℕ)+j=D.q := hqj
  have hBiZ : (D.B-i : ℕ)+i=D.B := hBi
  have hqcast : ((D.q-j : ℕ) : ℤ)+j=D.q := by exact_mod_cast hqjZ
  have hBcast : ((D.B-i : ℕ) : ℤ)+i=D.B := by exact_mod_cast hBiZ
  have rel := relations_int D
  unfold rbAxisA rbAxisB
  constructor
  · nlinarith only [he,rel.1,hqcast]
  constructor
  · nlinarith only [he,rel.2.1,hBcast]
  · linarith

theorem lt_remainders (D : Positive H) (nu i j d : ℕ) (hr : LT D i j d)
    (he : (i : ℤ)*D.b+j*D.c=(nu : ℤ)+d*D.a) :
    ltAxisA D i j d-nu=((D.C-j : ℕ) : ℤ)*D.c ∧
    ltAxisB D i j d-nu=((D.p-i : ℕ) : ℤ)*D.b ∧
    (i : ℤ)*D.b+j*D.c-nu=(d : ℤ)*D.a := by
  have hCj : ((D.C-j : ℕ) : ℤ)+j=D.C := by exact_mod_cast Nat.sub_add_cancel hr.2.2.2.1.le
  have hpi : ((D.p-i : ℕ) : ℤ)+i=D.p := by exact_mod_cast Nat.sub_add_cancel hr.2.1.le
  have rel := relations_int D
  unfold ltAxisA ltAxisB
  constructor
  · nlinarith only [he,rel.2.2,hCj]
  constructor
  · nlinarith only [he,rel.1,hpi]
  · linarith

theorem rb_axis_canonical (D : Positive H) (nu i j d : ℕ) (hr : RB D i j d)
    (he : (i : ℤ)*D.b+j*D.c=(nu : ℤ)+d*D.a) :
    letI : NeZero D.c := ⟨(D.triple.positive 2).ne'⟩
    letI : NeZero D.b := ⟨(D.triple.positive 1).ne'⟩
    H.asRelativeIdeal.aperyRepresentative D.c (nu : ZMod D.c)=rbAxisA D i j d ∧
    H.asRelativeIdeal.aperyRepresentative D.b (nu : ZMod D.b)=rbAxisB D i j d := by
  letI : NeZero D.c := ⟨(D.triple.positive 2).ne'⟩
  letI : NeZero D.b := ⟨(D.triple.positive 1).ne'⟩
  obtain ⟨hpi,hiB,hj0,hjq,hd0,hdu⟩ := hr
  have sums := D.coefficient_sums
  have hduA : d≤D.A := by omega
  have hXchart : D.ChartC (D.A-d) (i-D.p) := by
    refine ⟨by omega,by omega,Or.inr ?_⟩
    omega
  have hYchart : D.ChartB (D.u-d) (j+D.v) := by
    exact ⟨by omega,by omega,Or.inl (by omega)⟩
  have hX := omitted_axis_representative D.triple 2 (vector (D.A-d) (i-D.p) 0)
    (by simp) (by intro f hf; apply D.chartC_factorization_unique _ _ hXchart f; simpa [vector_weight,Triple.grid] using hf)
  have hY := omitted_axis_representative D.triple 1 (vector (D.u-d) 0 (j+D.v))
    (by simp) (by intro f hf; apply D.chartB_factorization_unique _ _ hYchart f; simpa [vector_weight,Triple.grid] using hf)
  have hXval : (D.triple.weight (vector (D.A-d) (i-D.p) 0) : ℤ)=rbAxisA D i j d := by
    simp only [vector_weight,Triple.grid,zero_mul,add_zero,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub hduA,Nat.cast_sub hpi.le,rbAxisA] <;> ring
  have hYval : (D.triple.weight (vector (D.u-d) 0 (j+D.v)) : ℤ)=rbAxisB D i j d := by
    simp only [vector_weight,Triple.grid,zero_mul,add_zero,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub hdu.le,rbAxisB] <;> ring
  have remainders := rb_remainders D nu i j d ⟨hpi,hiB,hj0,hjq,hd0,hdu⟩ he
  have hXmod : (D.triple.weight (vector (D.A-d) (i-D.p) 0) : ZMod D.c)=(nu : ZMod D.c) := by
    have hh : (D.triple.weight (vector (D.A-d) (i-D.p) 0) : ℤ)=
        nu+((D.q-j : ℕ) : ℤ)*D.c := by omega
    exact_mod_cast (show ((D.triple.weight (vector (D.A-d) (i-D.p) 0) : ℤ) : ZMod D.c)=nu by rw [hh]; simp)
  have hYmod : (D.triple.weight (vector (D.u-d) 0 (j+D.v)) : ZMod D.b)=(nu : ZMod D.b) := by
    have hh : (D.triple.weight (vector (D.u-d) 0 (j+D.v)) : ℤ)=
        nu+((D.B-i : ℕ) : ℤ)*D.b := by omega
    exact_mod_cast (show ((D.triple.weight (vector (D.u-d) 0 (j+D.v)) : ℤ) : ZMod D.b)=nu by rw [hh]; simp)
  rw [hXmod,hXval] at hX
  rw [hYmod,hYval] at hY
  exact ⟨hX,hY⟩

theorem lt_axis_canonical (D : Positive H) (nu i j d : ℕ) (hr : LT D i j d)
    (he : (i : ℤ)*D.b+j*D.c=(nu : ℤ)+d*D.a) :
    letI : NeZero D.c := ⟨(D.triple.positive 2).ne'⟩
    letI : NeZero D.b := ⟨(D.triple.positive 1).ne'⟩
    H.asRelativeIdeal.aperyRepresentative D.c (nu : ZMod D.c)=ltAxisA D i j d ∧
    H.asRelativeIdeal.aperyRepresentative D.b (nu : ZMod D.b)=ltAxisB D i j d := by
  letI : NeZero D.c := ⟨(D.triple.positive 2).ne'⟩
  letI : NeZero D.b := ⟨(D.triple.positive 1).ne'⟩
  obtain ⟨hi0,hip,hqj,hjC,hd0,hdw⟩ := hr
  have sums := D.coefficient_sums
  have hdA : d≤D.A := by omega
  have hXchart : D.ChartC (D.w-d) (i+D.z) :=
    ⟨by omega,by omega,Or.inl (by omega)⟩
  have hYchart : D.ChartB (D.A-d) (j-D.q) :=
    ⟨by omega,by omega,Or.inr (by omega)⟩
  have hX := omitted_axis_representative D.triple 2 (vector (D.w-d) (i+D.z) 0)
    (by simp) (by intro f hf; apply D.chartC_factorization_unique _ _ hXchart f; simpa [vector_weight,Triple.grid] using hf)
  have hY := omitted_axis_representative D.triple 1 (vector (D.A-d) 0 (j-D.q))
    (by simp) (by intro f hf; apply D.chartB_factorization_unique _ _ hYchart f; simpa [vector_weight,Triple.grid] using hf)
  have hXval : (D.triple.weight (vector (D.w-d) (i+D.z) 0) : ℤ)=ltAxisA D i j d := by
    simp only [vector_weight,Triple.grid,zero_mul,add_zero,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub hdw.le,ltAxisA] <;> ring
  have hYval : (D.triple.weight (vector (D.A-d) 0 (j-D.q)) : ℤ)=ltAxisB D i j d := by
    simp only [vector_weight,Triple.grid,zero_mul,add_zero,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub hdA,Nat.cast_sub hqj.le,ltAxisB] <;> ring
  have remainders := lt_remainders D nu i j d ⟨hi0,hip,hqj,hjC,hd0,hdw⟩ he
  have hXmod : (D.triple.weight (vector (D.w-d) (i+D.z) 0) : ZMod D.c)=(nu : ZMod D.c) := by
    have hh : (D.triple.weight (vector (D.w-d) (i+D.z) 0) : ℤ)=
        nu+((D.C-j : ℕ) : ℤ)*D.c := by omega
    exact_mod_cast (show ((D.triple.weight (vector (D.w-d) (i+D.z) 0) : ℤ) : ZMod D.c)=nu by rw [hh]; simp)
  have hYmod : (D.triple.weight (vector (D.A-d) 0 (j-D.q)) : ZMod D.b)=(nu : ZMod D.b) := by
    have hh : (D.triple.weight (vector (D.A-d) 0 (j-D.q)) : ℤ)=
        nu+((D.p-i : ℕ) : ℤ)*D.b := by omega
    exact_mod_cast (show ((D.triple.weight (vector (D.A-d) 0 (j-D.q)) : ℤ) : ZMod D.b)=nu by rw [hh]; simp)
  rw [hXmod,hXval] at hX
  rw [hYmod,hYval] at hY
  exact ⟨hX,hY⟩

end NS25Lean.GenericReturn
