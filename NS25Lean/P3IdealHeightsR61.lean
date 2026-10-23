import NS25Lean.P3PrefixRoutingR60

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R61

variable {H : NumericalSemigroup}

/-- An actual subideal representative differs from the semigroup representative
by a nonnegative integral number of moduli. -/
theorem exists_idealHeight (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (s : ZMod a) :
    ∃ k : ℕ, I.aperyRepresentative a s =
      H.asRelativeIdeal.aperyRepresentative a s + (a : ℤ) * k := by
  apply RelativeIdeal.exists_eq_add_mul_of_le_of_modEq a
  · exact H.asRelativeIdeal.aperyRepresentative_le a s
      (hsub _ (I.aperyRepresentative_mem a s)) (I.aperyRepresentative_mod a s)
  · rw [I.aperyRepresentative_mod, H.asRelativeIdeal.aperyRepresentative_mod]

/-- Natural height of the actual ideal over the actual semigroup Apéry set. -/
def idealHeight (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (s : ZMod a) : ℕ :=
  Classical.choose (exists_idealHeight I a hsub s)

theorem idealHeight_eq (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (s : ZMod a) :
    I.aperyRepresentative a s = H.asRelativeIdeal.aperyRepresentative a s +
      (a : ℤ) * idealHeight I a hsub s :=
  Classical.choose_spec (exists_idealHeight I a hsub s)

/-- The height is characterized uniquely by the literal weight equality. -/
theorem idealHeight_unique (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (s : ZMod a) (k : ℕ)
    (hk : I.aperyRepresentative a s = H.asRelativeIdeal.aperyRepresentative a s +
      (a : ℤ) * k) : idealHeight I a hsub s = k := by
  have he := idealHeight_eq I a hsub s
  have ha : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have : (idealHeight I a hsub s : ℤ) = k := by nlinarith
  exact_mod_cast this

/-- The integer carry equation uses the frozen, actual step quotients. -/
theorem idealHeight_step_eq (I : RelativeIdeal H) (a b : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (hb : b ∈ H) (s : ZMod a) :
    (I.aperyStepQuotient a b hb s : ℤ) =
      (H.asRelativeIdeal.aperyStepQuotient a b hb s : ℤ) +
      idealHeight I a hsub s - idealHeight I a hsub (s + b) := by
  have hi := I.apery_step_eq a b hb s
  have hh := H.asRelativeIdeal.apery_step_eq a b hb s
  rw [idealHeight_eq I a hsub s, idealHeight_eq I a hsub (s + b)] at hi
  have ha : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  nlinarith

/-- A canonical semigroup cell in the ideal has height zero. -/
theorem canonical_height_zero (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (x : ℤ)
    (hcan : H.asRelativeIdeal.aperyRepresentative a (x : ZMod a) = x)
    (hx : x ∈ I) : idealHeight I a hsub (x : ZMod a) = 0 := by
  have hi := I.aperyRepresentative_le a (x : ZMod a) hx rfl
  have he := idealHeight_eq I a hsub (x : ZMod a)
  rw [hcan] at he
  have ha : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have hn := Nat.cast_nonneg (α := ℤ) (idealHeight I a hsub (x : ZMod a))
  have : (idealHeight I a hsub (x : ZMod a) : ℤ) = 0 := by nlinarith
  exact_mod_cast this

/-- A canonical cell translated into the ideal bounds its actual natural height. -/
theorem canonical_height_le (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (x : ℤ) (k : ℕ)
    (hcan : H.asRelativeIdeal.aperyRepresentative a (x : ZMod a) = x)
    (hx : x + (a : ℤ) * k ∈ I) : idealHeight I a hsub (x : ZMod a) ≤ k := by
  have hi := I.aperyRepresentative_le a (x : ZMod a) hx (by simp)
  have he := idealHeight_eq I a hsub (x : ZMod a)
  rw [hcan] at he
  have ha : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have : (idealHeight I a hsub (x : ZMod a) : ℤ) ≤ k := by nlinarith
  exact_mod_cast this

/-- A zero ideal edge equates the neighboring height with carry plus seed height. -/
theorem zero_step_height_transfer (I : RelativeIdeal H) (a b : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (hb : b ∈ H) (s : ZMod a)
    (hz : I.aperyStepQuotient a b hb s = 0) :
    idealHeight I a hsub (s + b) =
      H.asRelativeIdeal.aperyStepQuotient a b hb s + idealHeight I a hsub s := by
  have he := idealHeight_step_eq I a b hsub hb s
  rw [hz] at he
  simp only [Nat.cast_zero] at he
  have : (idealHeight I a hsub (s + b) : ℤ) =
      H.asRelativeIdeal.aperyStepQuotient a b hb s + idealHeight I a hsub s := by
    simpa using (show (idealHeight I a hsub (s + b) : ℤ) =
      (H.asRelativeIdeal.aperyStepQuotient a b hb s : ℤ) +
      idealHeight I a hsub s by omega)
  exact_mod_cast this

/-- Along a zero-carry zero edge, a height-zero neighbor forces a height-zero seed. -/
theorem zero_carry_seed_height_zero (I : RelativeIdeal H) (a b : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (hb : b ∈ H) (s : ZMod a)
    (hz : I.aperyStepQuotient a b hb s = 0)
    (hcarry : H.asRelativeIdeal.aperyStepQuotient a b hb s = 0)
    (hnext : idealHeight I a hsub (s + b) = 0) : idealHeight I a hsub s = 0 := by
  have he := zero_step_height_transfer I a b hsub hb s hz
  omega

/-- Height zero also recovers membership of the canonical semigroup cell. -/
theorem canonical_mem_of_height_zero (I : RelativeIdeal H) (a : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (s : ZMod a)
    (hz : idealHeight I a hsub s = 0) :
    H.asRelativeIdeal.aperyRepresentative a s ∈ I := by
  have he := idealHeight_eq I a hsub s
  rw [hz] at he
  simp only [Nat.cast_zero, mul_zero, add_zero] at he
  simpa [he] using I.aperyRepresentative_mem a s

/-- A zero b-edge from a canonical ideal neighbor recovers seed membership. -/
theorem zero_b_seed_mem (I : RelativeIdeal H) (a b : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (hb : b ∈ H)
    (x : ℤ)
    (hcan : H.asRelativeIdeal.aperyRepresentative a ((x + b : ℤ) : ZMod a) = x + b)
    (hx : x + b ∈ I)
    (hz : I.aperyStepQuotient a b hb (x : ZMod a) = 0) : x ∈ I := by
  have hrep : I.aperyRepresentative a ((x + b : ℤ) : ZMod a) = x + b := by
    apply le_antisymm (I.aperyRepresentative_le a _ hx rfl)
    have hl := H.asRelativeIdeal.aperyRepresentative_le a _
      (hsub _ (I.aperyRepresentative_mem a ((x + b : ℤ) : ZMod a)))
      (I.aperyRepresentative_mod a ((x + b : ℤ) : ZMod a))
    rw [hcan] at hl
    exact hl
  have he := I.apery_step_eq a b hb (x : ZMod a)
  rw [hz] at he
  simp only [Nat.cast_zero, mul_zero, add_zero] at he
  have he' : I.aperyRepresentative a (x : ZMod a) = x := by
    have hrep' : I.aperyRepresentative a ((x : ZMod a) + b) = x + b := by simpa using hrep
    rw [hrep'] at he
    linarith
  simpa [he'] using I.aperyRepresentative_mem a (x : ZMod a)

/-- The c-version of seed membership uses the same actual-edge theorem. -/
theorem zero_c_seed_mem (I : RelativeIdeal H) (a c : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal) (hc : c ∈ H)
    (x : ℤ)
    (hcan : H.asRelativeIdeal.aperyRepresentative a ((x + c : ℤ) : ZMod a) = x + c)
    (hx : x + c ∈ I)
    (hz : I.aperyStepQuotient a c hc (x : ZMod a) = 0) : x ∈ I :=
  zero_b_seed_mem I a c hsub hc x hcan hx hz

/-- A canonical b-neighbor and two zero actual edges exclude every opposite
candidate lying strictly below the literal carry level. -/
theorem stencil_zero_b_contradiction (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (hb : b ∈ H) (hc : c ∈ H) (x y : ℤ) (K k : ℕ)
    (hcanB : H.asRelativeIdeal.aperyRepresentative a ((x + b : ℤ) : ZMod a) = x + b)
    (hmemB : x + b ∈ I) (hopp : x + c = y + (a : ℤ) * K)
    (hu : I.aperyStepQuotient a b hb (x : ZMod a) = 0)
    (hv : I.aperyStepQuotient a c hc (x : ZMod a) = 0)
    (hcand : y + (a : ℤ) * k ∈ I) (hlt : k < K) : False := by
  have hrepB : I.aperyRepresentative a ((x + b : ℤ) : ZMod a) = x + b := by
    apply le_antisymm (I.aperyRepresentative_le a _ hmemB rfl)
    have hl := H.asRelativeIdeal.aperyRepresentative_le a _
      (hsub _ (I.aperyRepresentative_mem a ((x + b : ℤ) : ZMod a)))
      (I.aperyRepresentative_mod a ((x + b : ℤ) : ZMod a))
    rw [hcanB] at hl
    exact hl
  have hbe := I.apery_step_eq a b hb (x : ZMod a)
  have hce := I.apery_step_eq a c hc (x : ZMod a)
  rw [hu] at hbe
  rw [hv] at hce
  simp only [Nat.cast_zero, mul_zero, add_zero] at hbe hce
  have hrepB' : I.aperyRepresentative a ((x : ZMod a) + b) = x + b := by
    simpa using hrepB
  rw [hrepB'] at hbe
  have hrep0 : I.aperyRepresentative a (x : ZMod a) = x := by linarith
  rw [hrep0] at hce
  have hmod : ((y + (a : ℤ) * k : ℤ) : ZMod a) = (x : ZMod a) + c := by
    have hm := congrArg (fun z : ℤ => (z : ZMod a)) hopp
    simpa using hm.symm
  have hl := I.aperyRepresentative_le a ((x : ZMod a) + c) hcand hmod
  have ha : (0 : ℤ) < a := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne a)
  have hlt' : (k : ℤ) < K := by exact_mod_cast hlt
  nlinarith

/-- The symmetric stencil with the canonical c-neighbor. -/
theorem stencil_zero_c_contradiction (I : RelativeIdeal H) (a b c : ℕ) [NeZero a]
    (hsub : ∀ x : ℤ, x ∈ I → x ∈ H.asRelativeIdeal)
    (hb : b ∈ H) (hc : c ∈ H) (x y : ℤ) (K k : ℕ)
    (hcanC : H.asRelativeIdeal.aperyRepresentative a ((x + c : ℤ) : ZMod a) = x + c)
    (hmemC : x + c ∈ I) (hopp : x + b = y + (a : ℤ) * K)
    (hu : I.aperyStepQuotient a b hb (x : ZMod a) = 0)
    (hv : I.aperyStepQuotient a c hc (x : ZMod a) = 0)
    (hcand : y + (a : ℤ) * k ∈ I) (hlt : k < K) : False :=
  stencil_zero_b_contradiction I a c b hsub hc hb x y K k hcanC hmemC hopp hv hu hcand hlt

end NS25Lean.P3R61




