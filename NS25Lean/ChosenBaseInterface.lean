import NS25Lean.ChosenBaseSocle

set_option linter.style.header false

noncomputable section
namespace NS25Lean.ChosenBase
open ToricPresentation MvPolynomial
variable (k : Type*) [Field k] {Gamma : NumericalSemigroup}

/-- The quotient socle is equivalently annihilated by the three remaining variables. -/
theorem Data.socleA_iff_tail_variables (B : Data Gamma) (x : B.A k) :
    x ∈ B.socleA k ↔ ∀ j : Fin 3, B.psi k (X j) * x = 0 := by
  have hpsi (j : Fin 3) : B.psi k (X j) = B.monomialClass k (B.degrees j.succ) := by
    simp [Data.psi, Data.monomialClass]
  constructor
  · intro hx j
    rw [hpsi]
    apply hx
    intro he
    have he' := congrArg (fun h : Gamma.toAddSubmonoid => h.val) he
    have hp := B.degrees_positive j.succ
    change (B.degrees j.succ).val = 0 at he'
    omega
  · intro hx h hh
    have hgen : h ∈ AddSubmonoid.closure (Set.range B.degrees) := by
      rw [B.degrees_generate]; trivial
    induction hgen using AddSubmonoid.closure_induction with
    | mem h hm =>
        obtain ⟨i, rfl⟩ := hm
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [B.degrees_zero]
          have hz : B.monomialClass k B.q = 0 := by
            apply Ideal.Quotient.eq_zero_iff_mem.mpr
            exact Ideal.subset_span (Set.mem_singleton _)
          rw [hz, zero_mul]
        · rw [← hpsi]; exact hx j
    | zero => exact (hh rfl).elim
    | add a b ha hb iha ihb =>
        by_cases haz : a = 0
        · subst a
          simpa using ihb (by simpa using hh)
        · rw [← B.monomialClass_mul k, mul_right_comm, iha haz, zero_mul]

@[simp] theorem Data.quotientEquiv_mk (B : Data Gamma) (f : Poly k 3) :
    B.quotientEquiv k (Ideal.Quotient.mk (B.J k) f) = B.psi k f := rfl

/-- An explicit annihilator interface in R_q/J_q, with no copied type cardinality. -/
theorem Data.soclePolynomialQuotient_iff_variables (B : Data Gamma)
    (x : Poly k 3 ⧸ B.J k) :
    x ∈ B.soclePolynomialQuotient k ↔
      ∀ j : Fin 3, Ideal.Quotient.mk (B.J k) (X j) * x = 0 := by
  change B.quotientEquiv k x ∈ B.socleA k ↔ _
  rw [B.socleA_iff_tail_variables k]
  constructor
  · intro hx j
    apply (B.quotientEquiv k).injective
    rw [map_mul, map_zero, B.quotientEquiv_mk k]
    exact hx j
  · intro hx j
    have he := congrArg (B.quotientEquiv k) (hx j)
    simpa only [map_mul, map_zero, B.quotientEquiv_mk k] using he

/-- Joint source surface: exact quotient decomposition, type, and MUJ for an arbitrary pivot. -/
theorem Data.chosen_base_exact (B : Data Gamma) :
    B.J k = B.IH k ⊔ B.MK k ∧
    B.quotientType k = Gamma.asRelativeIdeal.idealType ∧
    (B.J k).spanFinrank = Presentation.rho Gamma :=
  ⟨B.J_eq_IH_sup_MK k, B.quotient_type_eq k, B.muj k⟩

/-- No distinguished ordering is imposed on the four input generators. -/
theorem every_pivot_exact (Gamma : NumericalSemigroup) (m a b c : ℕ)
    (h : FourGeneratedBridge.IsMinimallyGeneratedByFour Gamma m a b c) (i : Fin 4) :
    let B := Data.ofFourTuple Gamma m a b c h i
    B.J k = B.IH k ⊔ B.MK k ∧
    B.quotientType k = Gamma.asRelativeIdeal.idealType ∧
    (B.J k).spanFinrank = Presentation.rho Gamma :=
  (Data.ofFourTuple Gamma m a b c h i).chosen_base_exact k

end NS25Lean.ChosenBase
