import NS25Lean.FourBasePreparation

set_option autoImplicit false
set_option linter.style.header false
noncomputable section
namespace NS25Lean.EC.R70
open ChosenBase L2B L2C
variable {Gamma : NumericalSemigroup}

/-- COMMAND04 B.1, using the actual nonnegative Betti sum at an arbitrary pivot. -/
theorem p0_betti_structure (B : Data Gamma) (hp : chosenDefect B = 0)
    (d : ℕ) (hd : Betti B d) :
    componentCount B d = 2 ∧ B.pivot ∈ essentialVariables B d := by
  classical
  have hz := chosenDefect_eq_essential_sum B
  rw [hp] at hz
  have hterm := Finset.single_le_sum
    (fun e (_ : e ∈ bettiDegrees B) =>
      Nat.zero_le (componentCount B e - 1 -
        if B.pivot ∈ essentialVariables B e then 1 else 0))
    ((mem_bettiDegrees B d).mpr hd)
  rw [← hz] at hterm
  change 2 ≤ componentCount B d at hd
  by_cases he : B.pivot ∈ essentialVariables B d
  · simp only [ite_eq_left he] at hterm
    exact ⟨by omega, he⟩
  · simp only [ite_eq_right he] at hterm
    omega

/-- The internal Betti load vanishes; it is not identified with the defect. -/
theorem p0_internalLoad_zero (B : Data Gamma) (hp : chosenDefect B = 0) :
    internalLoad B B.pivot = 0 := by
  classical
  rw [internalLoad_eq_sum]
  apply Finset.sum_eq_zero
  intro d hd
  have he := (p0_betti_structure B hp d ((mem_bettiDegrees B d).mp hd)).2
  have hv := essential_subset_variables B d he
  simp only [ite_eq_right (not_not.mpr hv)]

/-- The actual polynomial kernel equals its boundary monomial ideal. -/
theorem p0_J_eq_MK (k : Type*) [Field k] (B : Data Gamma)
    (hp : chosenDefect B = 0) : B.J k = B.MK k :=
  J_eq_MK_of_internalLoad_zero k B (p0_internalLoad_zero B hp)

/-- P0-AUTOMON, for every actual chosen minimal generator and coefficient field. -/
theorem p0_automon (k : Type*) [Field k] (B : Data Gamma)
    (hp : chosenDefect B = 0) : IsMonomialIdeal k (B.J k) :=
  monomial_pivot k B (p0_internalLoad_zero B hp)

/-- Explicit all-indices form, with the original displayed family retained. -/
theorem p0_every_pivot (k : Type*) [Field k] (B : Data Gamma) (i : Fin 4)
    (hp : chosenDefect (atPivot B i) = 0) :
    IsMonomialIdeal k ((atPivot B i).J k) :=
  p0_automon k (atPivot B i) hp

end NS25Lean.EC.R70
