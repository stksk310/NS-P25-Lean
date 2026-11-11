import NS25Lean.GenericReturnTriples
import NS25Lean.SharedTailPrimitiveLattice
import NS25Lean.SharedTailPermutation
import NS25Lean.P3ShadowArithmeticR59

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.GenericReturn
open SharedTail ErasedSourceScreen PureInternalTransverse
variable {H : NumericalSemigroup}

theorem same_degree_lattice (D : Positive H) (E F x y z : ℕ)
    (he : x*D.a+y*D.b+z*D.c=E*D.a+F*D.b) :
    ∃ l k : ℤ, (x : ℤ)=E-(D.A : ℤ)*l-(D.w : ℤ)*k ∧
      (y : ℤ)=F+(D.p : ℤ)*l-(D.z : ℤ)*k ∧
      (z : ℤ)=(D.q : ℤ)*l+(D.C : ℤ)*k := by
  have heZ : (x : ℤ)*D.a+y*D.b+z*D.c=(E : ℤ)*D.a+F*D.b := by exact_mod_cast he
  obtain ⟨l,k,hx,hy,hz⟩ := D.integer_kernel_basis ((x : ℤ)-E) ((y : ℤ)-F) z
    (by nlinarith only [heZ])
  exact ⟨l,k,by linarith,by linarith,hz⟩

theorem rb_mixed_rectangle (D : Positive H) (nu i j d E F : ℕ)
    (hr : RB D i j d) (he : i*D.b+j*D.c=nu+d*D.a)
    (hE : E≤D.w) (hF : F≤D.z) : ¬InReturn H nu (E*D.a+F*D.b) := by
  rintro ⟨hx,n,hn,hret⟩
  obtain ⟨x,y,z,hfac⟩ := factorization_int D n ⟨n,hn,rfl⟩
  have hfacN : n=x*D.a+y*D.b+z*D.c := by exact_mod_cast hfac
  have hsame : x*D.a+(i+y)*D.b+(j+z)*D.c=(E+d)*D.a+F*D.b := by
    nlinarith only [he,hret,hfacN]
  obtain ⟨l,k,ha,hb,hc⟩ := same_degree_lattice D (E+d) F x (i+y) (j+z) hsame
  have hsumA : (D.A : ℤ)=D.u+D.w := by exact_mod_cast D.coefficient_sums.1
  have hsumC : (D.C : ℤ)=D.q+D.v := by exact_mod_cast D.coefficient_sums.2.2
  rw [hsumA] at ha
  rw [hsumC] at hc
  apply P3R59.rb_shadow_arithmetic D.p D.q D.u D.v D.w D.z (E+d) F x (i+y) (j+z) l k
  · exact_mod_cast D.p_pos
  · exact_mod_cast D.q_pos
  · exact_mod_cast D.u_pos
  · exact_mod_cast D.v_pos
  · exact_mod_cast D.w_pos
  · exact_mod_cast D.z_pos
  · have hdu := hr.2.2.2.2.2
    exact_mod_cast (show E+d<D.u+D.w by omega)
  · exact_mod_cast hF
  · positivity
  · have hi := hr.1; have hp := D.p_pos
    exact_mod_cast (show 0 < i+y by omega)
  · have hj := hr.2.2.1
    exact_mod_cast (show 0<j+z by omega)
  · simpa only [Nat.cast_add] using ha
  · simpa only [Nat.cast_add] using hb
  · simpa only [Nat.cast_add] using hc

theorem lt_mixed_rectangle (D : Positive H) (nu i j d E F : ℕ)
    (hr : LT D i j d) (he : i*D.b+j*D.c=nu+d*D.a)
    (hE : E≤D.w) (hF : F≤D.z) : ¬InReturn H nu (E*D.a+F*D.b) := by
  rintro ⟨hx,n,hn,hret⟩
  obtain ⟨x,y,z,hfac⟩ := factorization_int D n ⟨n,hn,rfl⟩
  have hfacN : n=x*D.a+y*D.b+z*D.c := by exact_mod_cast hfac
  have hsame : x*D.a+(i+y)*D.b+(j+z)*D.c=(E+d)*D.a+F*D.b := by
    nlinarith only [he,hret,hfacN]
  obtain ⟨l,k,ha,hb,hc⟩ := same_degree_lattice D (E+d) F x (i+y) (j+z) hsame
  have hsumA : (D.A : ℤ)=D.u+D.w := by exact_mod_cast D.coefficient_sums.1
  have hsumC : (D.C : ℤ)=D.q+D.v := by exact_mod_cast D.coefficient_sums.2.2
  rw [hsumA] at ha
  rw [hsumC] at hc
  apply P3R59.lt_shadow_arithmetic D.p D.q D.u D.v D.w D.z (E+d) F x (i+y) (j+z) l k
  · exact_mod_cast D.p_pos
  · exact_mod_cast D.q_pos
  · exact_mod_cast D.u_pos
  · exact_mod_cast D.v_pos
  · exact_mod_cast D.w_pos
  · exact_mod_cast D.z_pos
  · have hdw := hr.2.2.2.2.2
    exact_mod_cast (show E+d<2*D.w by omega)
  · exact_mod_cast hF
  · positivity
  · have hi := hr.1
    exact_mod_cast (show 0 < i+y by omega)
  · have hj := hr.2.2.1
    exact_mod_cast (show D.q<j+z by omega)
  · simpa only [Nat.cast_add] using ha
  · simpa only [Nat.cast_add] using hb
  · simpa only [Nat.cast_add] using hc

theorem mixed_rectangle (D : Positive H) (nu i j d E F : ℕ)
    (hr : RB D i j d ∨ LT D i j d) (he : i*D.b+j*D.c=nu+d*D.a)
    (hE : E≤D.w) (hF : F≤D.z) : ¬InReturn H nu (E*D.a+F*D.b) := by
  rcases hr with hr | hr
  · exact rb_mixed_rectangle D nu i j d E F hr he hE hF
  · exact lt_mixed_rectangle D nu i j d E F hr he hE hF

theorem transpose_rb (D : Positive H) (i j d : ℕ) :
    RB D i j d ↔ LT D.swapBC j i d := by
  change (D.p < i ∧ i < D.B ∧ 0 < j ∧ j < D.q ∧ 0 < d ∧ d < D.u) ↔
    (0 < j ∧ j < D.q ∧ D.p < i ∧ i < D.B ∧ 0 < d ∧ d < D.u)
  omega

theorem transpose_lt (D : Positive H) (i j d : ℕ) :
    LT D i j d ↔ RB D.swapBC j i d := by
  change (0 < i ∧ i < D.p ∧ D.q < j ∧ j < D.C ∧ 0 < d ∧ d < D.w) ↔
    (D.q < j ∧ j < D.C ∧ 0 < i ∧ i < D.p ∧ 0 < d ∧ d < D.w)
  omega

theorem mixed_rectangle_transpose (D : Positive H) (nu i j d E F : ℕ)
    (hr : RB D i j d ∨ LT D i j d) (he : i*D.b+j*D.c=nu+d*D.a)
    (hE : E≤D.u) (hF : F≤D.v) : ¬InReturn H nu (E*D.a+F*D.c) := by
  have ht : RB D.swapBC j i d ∨ LT D.swapBC j i d := by
    rcases hr with hr | hr
    · exact Or.inr ((transpose_rb D i j d).mp hr)
    · exact Or.inl ((transpose_lt D i j d).mp hr)
  have he' : j*D.swapBC.b+i*D.swapBC.c=nu+d*D.swapBC.a := by
    simpa only [Positive.swapBC_a,Positive.swapBC_b,Positive.swapBC_c,add_comm] using he
  simpa only [Positive.swapBC_a,Positive.swapBC_b] using
    mixed_rectangle D.swapBC nu j i d E F ht he' hE hF

theorem mixed_predecessors_absent (D : Positive H) (nu i j d : ℕ)
    (hr : RB D i j d ∨ LT D i j d) (he : i*D.b+j*D.c=nu+d*D.a) :
    ¬InReturn H nu ((D.w-1)*D.a+D.z*D.b) ∧
    ¬InReturn H nu (D.w*D.a+(D.z-1)*D.b) ∧
    ¬InReturn H nu ((D.u-1)*D.a+D.v*D.c) ∧
    ¬InReturn H nu (D.u*D.a+(D.v-1)*D.c) :=
  ⟨mixed_rectangle D nu i j d _ _ hr he (by omega) le_rfl,
    mixed_rectangle D nu i j d _ _ hr he le_rfl (by omega),
    mixed_rectangle_transpose D nu i j d _ _ hr he (by omega) le_rfl,
    mixed_rectangle_transpose D nu i j d _ _ hr he le_rfl (by omega)⟩

end NS25Lean.GenericReturn
