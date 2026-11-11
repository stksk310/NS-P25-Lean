import NS25Lean.GenericReturnGateHeights
import NS25Lean.GenericReturnSeamTargets
import NS25Lean.GenericReturnOppositeArms

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturn
open SharedTail ErasedSourceScreen
open scoped Classical
variable {H : NumericalSemigroup}

def Return.F {D : Positive H} (R : Return D) : ℤ := (R.i : ℤ)*D.b+R.j*D.c

def Return.X {D : Positive H} (R : Return D) : ℤ :=
  if RB D R.i R.j R.depth then rbAxisA D R.i R.j R.depth else ltAxisA D R.i R.j R.depth

def Return.Y {D : Positive H} (R : Return D) : ℤ :=
  if RB D R.i R.j R.depth then rbAxisB D R.i R.j R.depth else ltAxisB D R.i R.j R.depth

theorem Return.exact_generators {D : Positive H} (R : Return D) (x : ℤ) :
    x∈L5A2B4AR1.returnIdeal H R.nu ↔
      x-R.F∈H.asRelativeIdeal ∨ x-R.X∈H.asRelativeIdeal ∨ x-R.Y∈H.asRelativeIdeal := by
  have sums := D.coefficient_sums
  rcases R.strict with hr | hr
  · obtain ⟨hpi,hiB,hj0,hjq,hd0,hdu⟩ := hr
    have hrr : RB D R.i R.j R.depth := ⟨hpi,hiB,hj0,hjq,hd0,hdu⟩
    simp only [Return.F,Return.X,Return.Y,if_pos hrr]
    exact rb_return_three_generators D R.nu R.i R.j R.depth
      (by have := D.p_pos; omega) hj0 hd0 hpi hjq hiB (by omega) hdu R.equation x
  · obtain ⟨hi0,hip,hqj,hjC,hd0,hdw⟩ := hr
    have hnot : ¬RB D R.i R.j R.depth := by intro h; have := h.1; omega
    simp only [Return.F,Return.X,Return.Y,if_neg hnot]
    exact lt_return_three_generators D R.nu R.i R.j R.depth
      hi0 (by have := D.q_pos; omega) hd0 hip hqj (by omega) hjC hdw R.equation x

/-- For the seam theorem, containing the three exact generators supplies the
whole-return containment premise; redundancy is allowed. -/
theorem Return.subset_of_generators_mem {D : Positive H} (R : Return D)
    (I : RelativeIdeal H) (hF : R.F∈I) (hX : R.X∈I) (hY : R.Y∈I) :
    ∀ x, x∈L5A2B4AR1.returnIdeal H R.nu → x∈I := by
  intro x hx
  rcases (R.exact_generators x).mp hx with hf | hx | hy
  · have hh := ideal_add_int I hF hf
    convert hh using 1 <;> ring
  · have hh := ideal_add_int I hX hx
    convert hh using 1 <;> ring
  · have hh := ideal_add_int I hY hy
    convert hh using 1 <;> ring

theorem canonical_F_representative (D : Positive H) (nu i j d : ℕ)
    (hc : D.ChartA i j) (he : i*D.b+j*D.c=nu+d*D.a) :
    letI : NeZero D.a := ⟨(D.triple.positive 0).ne'⟩
    H.asRelativeIdeal.aperyRepresentative D.a (nu : ZMod D.a)=(i*D.b+j*D.c : ℕ) := by
  letI : NeZero D.a := ⟨(D.triple.positive 0).ne'⟩
  have hh := chartA_representative D i j hc
  have hmod : ((i*D.b+j*D.c : ℕ) : ZMod D.a)=(nu : ZMod D.a) := by
    rw [he]
    simp
  rw [hmod] at hh
  exact hh

/-- All six represented predecessors of the two live critical fibers are
excluded by the same actual return, with both mixed literal transposes. -/
theorem all_live_critical_predecessors_absent (D : Positive H) (K : LocalCut D)
    (nu : ℕ) (hnu : 0<nu) (hnon : nu∉H)
    (hRK : ∀ x, InReturn H nu x → x∈K.carrier) :
    ¬InReturn H nu ((D.B-1)*D.b) ∧
    ¬InReturn H nu ((D.u-1)*D.a+D.v*D.c) ∧
    ¬InReturn H nu (D.u*D.a+(D.v-1)*D.c) ∧
    ¬InReturn H nu ((D.C-1)*D.c) ∧
    ¬InReturn H nu ((D.w-1)*D.a+D.z*D.b) ∧
    ¬InReturn H nu (D.w*D.a+(D.z-1)*D.b) := by
  obtain ⟨t,ht,hu⟩ := strict_canonical_return D K nu hnu hnon hRK
  have mixed := mixed_predecessors_absent D nu t.1 t.2.1 t.2.2 ht.1 ht.2
  have hB := D.critical.positive 1
  have hC := D.critical.positive 2
  change 0<D.B at hB
  change 0<D.C at hC
  refine ⟨no_subcritical_pure D K nu hnu hnon hRK 1 (D.B-1) (by change D.B-1<D.B; omega),
    mixed.2.2.1,mixed.2.2.2,
    no_subcritical_pure D K nu hnu hnon hRK 2 (D.C-1) (by change D.C-1<D.C; omega),
    mixed.1,mixed.2.1⟩

end NS25Lean.GenericReturn

namespace NS25Lean.GenericPhysical
variable {H Gamma : NumericalSemigroup}

/-- Physical level multiplication is delta*q, with the original m unchanged. -/
theorem Presentation.physical_return_multiplier (D : Presentation H Gamma)
    (x q h : ℕ) (he : x=q*D.m+h) :
    D.delta*x=(D.delta*q)*D.m+D.delta*h := by rw [he]; ring

theorem Presentation.cut_additive_value (D : Presentation H Gamma)
    (x y : {x : ℕ // x∈D.normalizedCut}) :
    (D.cutEquiv ⟨x.val+y.val,D.cut_add x.property y.property.1⟩).val=
      (D.cutEquiv x).val+(D.cutEquiv y).val := by
  change D.delta*(x.val+y.val)=D.delta*x.val+D.delta*y.val
  ring

end NS25Lean.GenericPhysical
