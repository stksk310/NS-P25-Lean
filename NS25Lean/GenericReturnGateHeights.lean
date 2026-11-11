import NS25Lean.GenericReturnCanonicalRepresentatives
import NS25Lean.GenericReturnMixedRectangle
import NS25Lean.P3IdealHeightsR61

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturn
open SharedTail ErasedSourceScreen PureInternalTransverse
open L5A2B4AR1 L5A2B4AR5B
open scoped Classical
variable {H : NumericalSemigroup}

local instance (D : Positive H) : NeZero D.a := ⟨(D.triple.positive 0).ne'⟩

def returnUnion {ι : Type*} [Nonempty ι] (H : NumericalSemigroup) (nu : ι→ℕ) : RelativeIdeal H where
  carrier := {z | ∃ q, z∈returnIdeal H (nu q)}
  nonempty := by
    obtain ⟨z,hz⟩ := (returnIdeal H (nu (Classical.arbitrary ι))).nonempty
    exact ⟨z,Classical.arbitrary ι,hz⟩
  bddBelow := ⟨0,by rintro z ⟨q,⟨n,hn,rfl⟩,hz⟩; exact Int.natCast_nonneg n⟩
  add_mem := by
    rintro z h ⟨q,hq⟩ hh
    exact ⟨q,(returnIdeal H (nu q)).add_mem hq hh⟩

theorem returnUnion_subset {ι : Type*} [Nonempty ι] (nu : ι→ℕ) (z : ℤ)
    (hz : z∈returnUnion H nu) : z∈H.asRelativeIdeal := by
  obtain ⟨q,hq⟩ := hz
  exact hq.1

/-- Actual membership height, obtained from least integer representatives. -/
abbrev unionHeight {ι : Type*} [Nonempty ι] (D : Positive H) (nu : ι→ℕ)
    (x y : ℕ) : ℕ :=
  P3R61.idealHeight (returnUnion H nu) D.a (returnUnion_subset nu)
    ((x*D.b+y*D.c : ℕ) : ZMod D.a)

theorem individual_gate_rep (D : Positive H) (nu x y tx ty k d : ℕ)
    (hxy : D.ChartA x y) (ht : D.ChartA tx ty) (hdk : d≤k)
    (he : (x : ℤ)*D.b+y*D.c-nu=
      (tx : ℤ)*D.b+ty*D.c+((d : ℤ)-k)*D.a) :
    (returnIdeal H nu).aperyRepresentative D.a ((x*D.b+y*D.c : ℕ) : ZMod D.a)=
      ((x*D.b+y*D.c : ℕ) : ℤ)+(D.a : ℤ)*(k-d) := by
  let r : ZMod D.a := (x*D.b+y*D.c : ℕ)
  have hbase := chartA_representative D x y hxy
  have htbase := chartA_representative D tx ty ht
  have hmod : r-(nu : ZMod D.a)=((tx*D.b+ty*D.c : ℕ) : ZMod D.a) := by
    have hh := congrArg (fun z : ℤ => (z : ZMod D.a)) he
    simpa [r,Int.cast_sub,Int.cast_add,Int.cast_mul] using hh
  rw [returnIdeal_aperyRepresentative_eq_max H nu D.a (D.triple.member (Finsupp.single 0 1)) r]
  rw [show H.asRelativeIdeal.aperyRepresentative D.a r=(x*D.b+y*D.c : ℕ) from hbase,
    hmod,htbase]
  have hsub : ((k-d : ℕ) : ℤ)=(k : ℤ)-d := Int.ofNat_sub hdk
  have hval : (nu : ℤ)+(tx*D.b+ty*D.c : ℕ)=
      (x*D.b+y*D.c : ℕ)+(D.a : ℤ)*(k-d) := by
    push_cast
    nlinarith only [he]
  rw [hval]
  apply max_eq_right
  exact le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg D.a)
    (sub_nonneg.mpr (by exact_mod_cast hdk)))

theorem rb_individual_gate_reps (D : Positive H) (nu i j d : ℕ)
    (hr : RB D i j d) (he : (i : ℤ)*D.b+j*D.c=(nu : ℤ)+d*D.a) :
    (returnIdeal H nu).aperyRepresentative D.a (((D.z-1)*D.b : ℕ) : ZMod D.a)=
      ((D.z-1)*D.b : ℕ)+(D.a : ℤ)*(D.A-d) ∧
    (returnIdeal H nu).aperyRepresentative D.a ((D.z*D.b : ℕ) : ZMod D.a)=
      (D.z*D.b : ℕ)+(D.a : ℤ)*(D.A-d) ∧
    (returnIdeal H nu).aperyRepresentative D.a (((D.C-1)*D.c : ℕ) : ZMod D.a)=
      ((D.C-1)*D.c : ℕ)+(D.a : ℤ)*(D.u-d) := by
  obtain ⟨hpi,hiB,hj0,hjq,hd0,hdu⟩ := hr
  have sums := D.coefficient_sums
  have rel := relations_int D
  have hp := D.p_pos
  have hq := D.q_pos
  have hz := D.z_pos
  have hv := D.v_pos
  have hdA : d≤D.A := by omega
  have hcG : D.ChartA (D.z-1) 0 := ⟨by omega,by omega,Or.inr hq⟩
  have hcGp : D.ChartA D.z 0 := ⟨by omega,by omega,Or.inr hq⟩
  have hcY : D.ChartA 0 (D.C-1) := ⟨by omega,by omega,Or.inl hp⟩
  have hcT : D.ChartA (D.B-1-i) (D.q-j) := ⟨by omega,by omega,Or.inr (by omega)⟩
  have hcTp : D.ChartA (D.B-i) (D.q-j) := ⟨by omega,by omega,Or.inr (by omega)⟩
  have hcTY : D.ChartA (D.B-i) (D.q-1-j) := ⟨by omega,by omega,Or.inr (by omega)⟩
  have hzm : ((D.z-1 : ℕ) : ℤ)=(D.z : ℤ)-1 := by omega
  have hBm : ((D.B-1-i : ℕ) : ℤ)=(D.B : ℤ)-1-i := by omega
  have hBi : ((D.B-i : ℕ) : ℤ)=(D.B : ℤ)-i := by omega
  have hqj : ((D.q-j : ℕ) : ℤ)=(D.q : ℤ)-j := by omega
  have hqm : ((D.q-1-j : ℕ) : ℤ)=(D.q : ℤ)-1-j := by omega
  have hCm : ((D.C-1 : ℕ) : ℤ)=(D.C : ℤ)-1 := by omega
  have hBsum : (D.B : ℤ)=D.p+D.z := by exact_mod_cast sums.2.1
  have hCsum : (D.C : ℤ)=D.q+D.v := by exact_mod_cast sums.2.2
  constructor
  · have hh := individual_gate_rep D nu (D.z-1) 0 (D.B-1-i) (D.q-j) D.A d hcG hcT hdA (by
      simp only [Nat.cast_zero,zero_mul,add_zero,hzm,hBm,hqj]
      nlinarith only [he,rel.1,hBsum])
    simpa only [zero_mul,add_zero] using hh
  constructor
  · have hh := individual_gate_rep D nu D.z 0 (D.B-i) (D.q-j) D.A d hcGp hcTp hdA (by
      simp only [Nat.cast_zero,zero_mul,add_zero,hBi,hqj]
      nlinarith only [he,rel.1,hBsum])
    simpa only [zero_mul,add_zero] using hh
  · have hh := individual_gate_rep D nu 0 (D.C-1) (D.B-i) (D.q-1-j) D.u d hcY hcTY hdu.le (by
      simp only [Nat.cast_zero,zero_mul,zero_add,hCm,hBi,hqm]
      nlinarith only [he,rel.2.1,hCsum])
    simpa only [zero_mul,zero_add] using hh

def depthMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (depth : ι→ℕ) : ℕ :=
  (Finset.univ.image depth).max' (by simp)

theorem depth_le_maximum {ι : Type*} [Fintype ι] [Nonempty ι]
    (depth : ι→ℕ) (q : ι) : depth q≤depthMaximum depth :=
  Finset.le_max' _ _ (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩)

theorem depthMaximum_attained {ι : Type*} [Fintype ι] [Nonempty ι] (depth : ι→ℕ) :
    ∃ q, depth q=depthMaximum depth := by
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp (Finset.max'_mem (Finset.univ.image depth) (by simp))
  exact ⟨q,he⟩

theorem union_gate_height {ι : Type*} [Fintype ι] [Nonempty ι]
    (D : Positive H) (nu depth : ι→ℕ) (x y k : ℕ)
    (hc : D.ChartA x y) (hdk : ∀ q, depth q≤k)
    (hsingle : ∀ q, (returnIdeal H (nu q)).aperyRepresentative D.a
      ((x*D.b+y*D.c : ℕ) : ZMod D.a)=
      (x*D.b+y*D.c : ℕ)+(D.a : ℤ)*(k-depth q)) :
    unionHeight D nu x y=k-depthMaximum depth := by
  let I := returnUnion H nu
  let r : ZMod D.a := (x*D.b+y*D.c : ℕ)
  have ha : (0 : ℤ)<D.a := by exact_mod_cast D.triple.positive 0
  have hheight := P3R61.idealHeight_eq I D.a (returnUnion_subset nu) r
  rw [show H.asRelativeIdeal.aperyRepresentative D.a r=(x*D.b+y*D.c : ℕ) from
    chartA_representative D x y hc] at hheight
  obtain ⟨qmax,hmax⟩ := depthMaximum_attained depth
  have hupper := I.aperyRepresentative_le D.a r
    (show (returnIdeal H (nu qmax)).aperyRepresentative D.a r∈I from
      ⟨qmax,(returnIdeal H (nu qmax)).aperyRepresentative_mem D.a r⟩)
    ((returnIdeal H (nu qmax)).aperyRepresentative_mod D.a r)
  rw [hsingle qmax,hmax] at hupper
  obtain ⟨q,hq⟩ := I.aperyRepresentative_mem D.a r
  have hlower := (returnIdeal H (nu q)).aperyRepresentative_le D.a r hq (I.aperyRepresentative_mod D.a r)
  rw [hsingle q] at hlower
  have hle := depth_le_maximum depth q
  have hmaxle : depthMaximum depth≤k := by rw [←hmax]; exact hdk qmax
  have hsub : k-depthMaximum depth≤k-depth q := by omega
  have hsubZ : ((k-depthMaximum depth : ℕ) : ℤ)≤(k-depth q : ℕ) := by exact_mod_cast hsub
  have hh : (P3R61.idealHeight I D.a (returnUnion_subset nu) r : ℤ)=((k-depthMaximum depth : ℕ) : ℤ) := by
    rw [Int.ofNat_sub hmaxle]
    have hleZ : (depth q : ℤ)≤depthMaximum depth := by exact_mod_cast hle
    nlinarith only [hheight,hupper,hlower,hleZ,ha]
  exact_mod_cast hh

theorem rb_prefix_gate_heights {ι : Type*} [Fintype ι] [Nonempty ι]
    (D : Positive H) (nu i j depth : ι→ℕ)
    (hr : ∀ q, RB D (i q) (j q) (depth q))
    (he : ∀ q, (i q : ℤ)*D.b+j q*D.c=(nu q : ℤ)+depth q*D.a) :
    unionHeight D nu (D.z-1) 0=D.A-depthMaximum depth ∧
    unionHeight D nu D.z 0=D.A-depthMaximum depth ∧
    unionHeight D nu 0 (D.C-1)=D.u-depthMaximum depth := by
  have sums := D.coefficient_sums
  have hp := D.p_pos
  have hq := D.q_pos
  have hz := D.z_pos
  have hcG : D.ChartA (D.z-1) 0 := ⟨by omega,by omega,Or.inr hq⟩
  have hcGp : D.ChartA D.z 0 := ⟨by omega,by omega,Or.inr hq⟩
  have hcY : D.ChartA 0 (D.C-1) := ⟨by omega,by omega,Or.inl hp⟩
  have hA (q : ι) : depth q≤D.A := by have := (hr q).2.2.2.2.2; omega
  have hu (q : ι) : depth q≤D.u := (hr q).2.2.2.2.2.le
  refine ⟨union_gate_height D nu depth _ _ D.A hcG hA ?_,
    union_gate_height D nu depth _ _ D.A hcGp hA ?_,
    union_gate_height D nu depth _ _ D.u hcY hu ?_⟩
  · intro q
    simpa only [zero_mul,add_zero] using (rb_individual_gate_reps D _ _ _ _ (hr q) (he q)).1
  · intro q
    simpa only [zero_mul,add_zero] using (rb_individual_gate_reps D _ _ _ _ (hr q) (he q)).2.1
  · intro q
    simpa only [zero_mul,zero_add] using (rb_individual_gate_reps D _ _ _ _ (hr q) (he q)).2.2

theorem lt_prefix_gate_heights {ι : Type*} [Fintype ι] [Nonempty ι]
    (D : Positive H) (nu i j depth : ι→ℕ)
    (hr : ∀ q, LT D (i q) (j q) (depth q))
    (he : ∀ q, (i q : ℤ)*D.b+j q*D.c=(nu q : ℤ)+depth q*D.a) :
    unionHeight D nu (D.B-1) 0=D.w-depthMaximum depth ∧
    unionHeight D nu 0 (D.v-1)=D.A-depthMaximum depth ∧
    unionHeight D nu 0 D.v=D.A-depthMaximum depth := by
  have sums := D.coefficient_sums
  have hp := D.p_pos
  have hq := D.q_pos
  have hv := D.v_pos
  have hcX : D.ChartA (D.B-1) 0 := ⟨by omega,by omega,Or.inr hq⟩
  have hcG : D.ChartA 0 (D.v-1) := ⟨by omega,by omega,Or.inl hp⟩
  have hcGp : D.ChartA 0 D.v := ⟨by omega,by omega,Or.inl hp⟩
  have hA (q : ι) : depth q≤D.A := by have := (hr q).2.2.2.2.2; omega
  have hw (q : ι) : depth q≤D.w := (hr q).2.2.2.2.2.le
  have single (q : ι) :
      (returnIdeal H (nu q)).aperyRepresentative D.a (((D.B-1)*D.b : ℕ) : ZMod D.a)=
        ((D.B-1)*D.b : ℕ)+(D.a : ℤ)*(D.w-depth q) ∧
      (returnIdeal H (nu q)).aperyRepresentative D.a (((D.v-1)*D.c : ℕ) : ZMod D.a)=
        ((D.v-1)*D.c : ℕ)+(D.a : ℤ)*(D.A-depth q) ∧
      (returnIdeal H (nu q)).aperyRepresentative D.a ((D.v*D.c : ℕ) : ZMod D.a)=
        (D.v*D.c : ℕ)+(D.a : ℤ)*(D.A-depth q) := by
    obtain ⟨hi0,hip,hqj,hjC,hd0,hdw⟩ := hr q
    have hcTX : D.ChartA (D.p-1-i q) (D.C-j q) := ⟨by omega,by omega,Or.inl (by omega)⟩
    have hcT : D.ChartA (D.p-i q) (D.C-1-j q) := ⟨by omega,by omega,Or.inl (by omega)⟩
    have hcTp : D.ChartA (D.p-i q) (D.C-j q) := ⟨by omega,by omega,Or.inl (by omega)⟩
    have hBm : ((D.B-1 : ℕ) : ℤ)=(D.B : ℤ)-1 := by omega
    have hvm : ((D.v-1 : ℕ) : ℤ)=(D.v : ℤ)-1 := by omega
    have hpi : ((D.p-i q : ℕ) : ℤ)=(D.p : ℤ)-i q := by omega
    have hpm : ((D.p-1-i q : ℕ) : ℤ)=(D.p : ℤ)-1-i q := by omega
    have hCj : ((D.C-j q : ℕ) : ℤ)=(D.C : ℤ)-j q := by omega
    have hCm : ((D.C-1-j q : ℕ) : ℤ)=(D.C : ℤ)-1-j q := by omega
    have hBsum : (D.B : ℤ)=D.p+D.z := by exact_mod_cast sums.2.1
    have hCsum : (D.C : ℤ)=D.q+D.v := by exact_mod_cast sums.2.2
    constructor
    · have hh := individual_gate_rep D (nu q) (D.B-1) 0 (D.p-1-i q) (D.C-j q) D.w (depth q)
        hcX hcTX hdw.le (by
          simp only [Nat.cast_zero,zero_mul,add_zero,hBm,hpm,hCj]
          nlinarith only [he q,(relations_int D).2.2,hBsum])
      simpa only [zero_mul,add_zero] using hh
    constructor
    · have hh := individual_gate_rep D (nu q) 0 (D.v-1) (D.p-i q) (D.C-1-j q) D.A (depth q)
        hcG hcT (hA q) (by
          simp only [Nat.cast_zero,zero_mul,zero_add,hvm,hpi,hCm]
          nlinarith only [he q,(relations_int D).1,hCsum])
      simpa only [zero_mul,zero_add] using hh
    · have hh := individual_gate_rep D (nu q) 0 D.v (D.p-i q) (D.C-j q) D.A (depth q)
        hcGp hcTp (hA q) (by
          simp only [Nat.cast_zero,zero_mul,zero_add,hpi,hCj]
          nlinarith only [he q,(relations_int D).1,hCsum])
      simpa only [zero_mul,zero_add] using hh
  refine ⟨union_gate_height D nu depth _ _ D.w hcX hw ?_,
    union_gate_height D nu depth _ _ D.A hcG hA ?_,
    union_gate_height D nu depth _ _ D.A hcGp hA ?_⟩
  · intro q; simpa only [zero_mul,add_zero] using (single q).1
  · intro q; simpa only [zero_mul,zero_add] using (single q).2.1
  · intro q; simpa only [zero_mul,zero_add] using (single q).2.2

end NS25Lean.GenericReturn
