import NS25Lean.SharedTailPositiveCritical

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.SharedTail
open ErasedSourceScreen PureInternalTransverse

def swapBCIndex : Fin 3→Fin 3 | 0 => 0 | 1 => 2 | 2 => 1
@[simp] theorem swapBCIndex_twice (i : Fin 3) : swapBCIndex (swapBCIndex i)=i := by
  fin_cases i <;> rfl
def swapBCExponent : Exponent→+Exponent where
  toFun e := vector (e 0) (e 2) (e 1)
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' e f := by ext i; fin_cases i <;> simp

@[simp] theorem swapBCExponent_apply (e : Exponent) (i : Fin 3) :
    swapBCExponent e i=e (swapBCIndex i) := by fin_cases i <;> simp [swapBCExponent,swapBCIndex]
@[simp] theorem swapBCExponent_twice (e : Exponent) : swapBCExponent (swapBCExponent e)=e := by
  ext i; fin_cases i <;> simp [swapBCIndex]
@[simp] theorem swapBCExponent_single (i : Fin 3) (n : ℕ) :
    swapBCExponent (Finsupp.single i n)=Finsupp.single (swapBCIndex i) n := by
  ext j; fin_cases i <;> fin_cases j <;> simp [swapBCIndex]

def swapTriple {H : NumericalSemigroup} (T : Triple H) : Triple H where
  weight := T.weight.comp swapBCExponent
  positive i := by
    change 0<T.weight (swapBCExponent (Finsupp.single i 1))
    rw [swapBCExponent_single]
    exact T.positive (swapBCIndex i)
  member e := T.member _
  factor h hh := by
    obtain ⟨e,he⟩ := T.factor h hh
    exact ⟨swapBCExponent e,by simpa only [AddMonoidHom.comp_apply,swapBCExponent_twice] using he⟩

@[simp] theorem swapTriple_g {H : NumericalSemigroup} (T : Triple H) (i : Fin 3) :
    (swapTriple T).g i=T.g (swapBCIndex i) := by
  change T.weight (swapBCExponent (Finsupp.single i 1))=T.weight (Finsupp.single (swapBCIndex i) 1)
  rw [swapBCExponent_single]

def swapCritical {H : NumericalSemigroup} {T : Triple H} (C : Critical T) : Critical (swapTriple T) where
  exponent i := C.exponent (swapBCIndex i)
  positive i := C.positive _
  outside i := by
    obtain ⟨e,hei,hew⟩ := C.outside (swapBCIndex i)
    refine ⟨swapBCExponent e,by simpa using hei,?_⟩
    change T.weight (swapBCExponent (swapBCExponent e))=
      C.exponent (swapBCIndex i)*(swapTriple T).g i
    rw [swapBCExponent_twice,swapTriple_g]
    exact hew
  least i n e hn hei hew := by
    apply C.least (swapBCIndex i) n (swapBCExponent e) hn
    · simpa using hei
    · rw [swapTriple_g] at hew
      exact hew

/-- Literal b/c transpose of the whole positive structural package. -/
def Positive.swapBC {H : NumericalSemigroup} (D : Positive H) : Positive H where
  triple := swapTriple D.triple
  critical := swapCritical D.critical
  p := D.q
  q := D.p
  u := D.w
  v := D.z
  w := D.u
  z := D.v
  p_pos := D.q_pos
  q_pos := D.p_pos
  u_pos := D.w_pos
  v_pos := D.z_pos
  w_pos := D.u_pos
  z_pos := D.v_pos
  center := by simpa [swapCritical,swapBCIndex,add_comm] using D.center
  middle := by simpa [swapCritical,swapBCIndex] using D.boundary
  boundary := by simpa [swapCritical,swapBCIndex] using D.middle
  primitive := by simpa [swapBCIndex,Nat.gcd_comm] using D.primitive

@[simp] theorem Positive.swapBC_a {H : NumericalSemigroup} (D : Positive H) : D.swapBC.a=D.a := by
  simp [Positive.a,Positive.swapBC,swapBCIndex]
@[simp] theorem Positive.swapBC_b {H : NumericalSemigroup} (D : Positive H) : D.swapBC.b=D.c := by
  simp [Positive.b,Positive.swapBC,swapBCIndex]
@[simp] theorem Positive.swapBC_c {H : NumericalSemigroup} (D : Positive H) : D.swapBC.c=D.b := by
  simp [Positive.c,Positive.swapBC,swapBCIndex]
@[simp] theorem Positive.swapBC_A {H : NumericalSemigroup} (D : Positive H) : D.swapBC.A=D.A := rfl
@[simp] theorem Positive.swapBC_B {H : NumericalSemigroup} (D : Positive H) : D.swapBC.B=D.C := rfl
@[simp] theorem Positive.swapBC_C {H : NumericalSemigroup} (D : Positive H) : D.swapBC.C=D.B := rfl

end NS25Lean.SharedTail
