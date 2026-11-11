import NS25Lean.P2PureInternalTransverse

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.CriticalPermutation
open ErasedSourceScreen PureInternalTransverse

def swap (e : Exponent) : Exponent := vector (e 0) (e 2) (e 1)
@[simp] theorem swap_zero (e : Exponent) : swap e 0=e 0 := by simp [swap]
@[simp] theorem swap_one (e : Exponent) : swap e 1=e 2 := by simp [swap]
@[simp] theorem swap_two (e : Exponent) : swap e 2=e 1 := by simp [swap]
@[simp] theorem swap_involutive (e : Exponent) : swap (swap e)=e := by
  ext i
  fin_cases i <;> simp

def swapHom : Exponent→+Exponent where
  toFun := swap
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' := by intro e f; ext i; fin_cases i <;> simp

def triple {H : NumericalSemigroup} (T : Triple H) : Triple H where
  weight := T.weight.comp swapHom
  positive := by
    intro i
    fin_cases i
    · simpa [swapHom,swap,vector] using T.positive 0
    · simpa [swapHom,swap,vector] using T.positive 2
    · simpa [swapHom,swap,vector] using T.positive 1
  member := fun e => T.member (swap e)
  factor := by
    intro h hh
    obtain ⟨e,he⟩ := T.factor h hh
    exact ⟨swap e,by simpa [swapHom] using he⟩

@[simp] theorem g_zero {H : NumericalSemigroup} (T : Triple H) : (triple T).g 0=T.g 0 := by
  simp [Triple.g,triple,swapHom,swap,vector]
@[simp] theorem g_one {H : NumericalSemigroup} (T : Triple H) : (triple T).g 1=T.g 2 := by
  simp [Triple.g,triple,swapHom,swap,vector]
@[simp] theorem g_two {H : NumericalSemigroup} (T : Triple H) : (triple T).g 2=T.g 1 := by
  simp [Triple.g,triple,swapHom,swap,vector]
@[simp] theorem weight {H : NumericalSemigroup} (T : Triple H) (e : Exponent) :
    (triple T).weight e=T.weight (swap e) := rfl

def critical {H : NumericalSemigroup} {T : Triple H} (C : Critical T) : Critical (triple T) where
  exponent := ![C.exponent 0,C.exponent 2,C.exponent 1]
  positive := by intro i; fin_cases i <;> simpa using C.positive _
  outside := by
    intro i
    fin_cases i
    · obtain ⟨e,he,hw⟩ := C.outside 0
      exact ⟨swap e,by simpa using he,by simpa using hw⟩
    · obtain ⟨e,he,hw⟩ := C.outside 2
      exact ⟨swap e,by simpa using he,by simpa using hw⟩
    · obtain ⟨e,he,hw⟩ := C.outside 1
      exact ⟨swap e,by simpa using he,by simpa using hw⟩
  least := by
    intro i n e hn he hw
    fin_cases i
    · exact C.least 0 n (swap e) hn (by simpa using he) (by simpa using hw)
    · exact C.least 2 n (swap e) hn (by simpa using he) (by simpa using hw)
    · exact C.least 1 n (swap e) hn (by simpa using he) (by simpa using hw)

end NS25Lean.CriticalPermutation
