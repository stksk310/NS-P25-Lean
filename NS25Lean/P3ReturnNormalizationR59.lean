import NS25Lean.P3StrictReturnFormsR58

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R59
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2C4OR3
  L5A2B4AR1
variable {Gamma : NumericalSemigroup}

def normalizedRoleWeight (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) : ℕ :=
  ![routingA B e, routingB B e, routingC B e] i

theorem normalizedRoleWeight_scale (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    routingD B e * normalizedRoleWeight B e i = weights B (e i) := by
  have h := P3R58.routing_scale_weights B e
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem routingD_positive (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    0 < routingD B e := tailGcd_pos (chosenBase_minimalFour B e).n₁_pos

theorem routing_scaled_mem_iff (B : Data Gamma) (e : Fin 3 ≃ Fin 3) (x : ℕ) :
    routingD B e * x ∈ B.H ↔ x ∈ routingH B e := by
  rw [chosenBase_tail_eq_generatedThree B e]
  exact (buildTailScaling Gamma B.q.val (routingN1 B e) (routingN2 B e)
    (routingN3 B e) (chosenBase_minimalFour B e)).mul_mem_iff x

theorem normalized_nonprincipal_original (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ℕ) (hnon : r * B.q.val ∉ routingH B e) :
    (routingD B e * r) * B.q.val ∉ B.H := by
  intro h
  apply hnon
  apply (routing_scaled_mem_iff B e (r * B.q.val)).mp
  simpa only [Nat.mul_assoc] using h

/-- The finite principal prefix covers every positive return, by frozen return nesting. -/
theorem positive_return_reduces (H : NumericalSemigroup) (m : ℕ) (hm : 0 < m)
    (z : ℤ) (n : ℕ) (hn : 0 < n) (hz : z ∈ returnIdeal H (n * m)) :
    ∃ r : ℕ, 0 < r ∧ r ≤ principalIndex H m hm ∧ z ∈ returnIdeal H (r * m) := by
  have hpos : z ∈ positiveReturnCarrier H m := ⟨n, hn, hz⟩
  rw [positiveReturnCarrier_eq_finalCarrier H m hm] at hpos
  rcases hpos with hpre | hprincipal
  · obtain ⟨r, hr, hrq, hz⟩ := hpre
    exact ⟨r, hr, hrq.le, hz⟩
  · exact ⟨principalIndex H m hm, (principalIndex_spec H m hm).1,
      le_rfl, hz.1, hprincipal⟩

theorem original_predecessor_scale (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (n : ℕ) (i : Fin 3) :
    routingD B e * n - weights B (e i) =
      routingD B e * (n - normalizedRoleWeight B e i) := by
  rw [← normalizedRoleWeight_scale B e i, Nat.mul_sub_left_distrib]

theorem original_K_iff_normalized_positive_return (B : Data Gamma)
    (e : Fin 3 ≃ Fin 3) (x : ℕ) :
    routingD B e * x ∈ B.K ↔
      ∃ r : ℕ, 0 < r ∧ (x : ℤ) ∈ returnIdeal (routingH B e) (r * B.q.val) := by
  have hI : (x : ℤ) ∈ routingI B e ↔ routingD B e * x ∈ B.K := by
    change (x : ℤ) ∈ (buildTailScaling Gamma B.q.val (routingN1 B e)
      (routingN2 B e) (routingN3 B e) (chosenBase_minimalFour B e)).ideal ↔ _
    rw [TailScaling.mem_ideal_nat]
    change routingD B e * x ∈ aperyTail Gamma.toAddSubmonoid
      (generatedThree (routingN1 B e) (routingN2 B e) (routingN3 B e)) B.q.val ↔ _
    rw [← chosenBase_tail_eq_generatedThree B e]
    rfl
  rw [← hI, mem_routingI_iff_positive_return]
  rfl

theorem boundaryKilled_has_normalized_predecessor (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) (n : ℕ) (C : FiberComponent M.base (routingD M.base e * n))
    (hk : BoundaryKilled M (routingD M.base e * n) C) :
    ∃ i : Fin 3, ∃ r : ℕ, 0 < r ∧
      r ≤ principalIndex (routingH M.base e) M.base.q.val M.base.q_positive ∧
      ((n - normalizedRoleWeight M.base e i : ℕ) : ℤ) ∈
        returnIdeal (routingH M.base e) (r * M.base.q.val) := by
  obtain ⟨u, hu, j, hj, hK⟩ := hk
  obtain ⟨i, rfl⟩ := e.surjective j
  rw [original_predecessor_scale] at hK
  obtain ⟨r, hr, hret⟩ := (original_K_iff_normalized_positive_return M.base e _).mp hK
  obtain ⟨s, hs, hsq, hsret⟩ := positive_return_reduces _ _ M.base.q_positive _ r hr hret
  exact ⟨i, s, hs, hsq, hsret⟩

theorem killedCount_zero_of_normalized_predecessors_absent (M : MultiplicityBase Gamma)
    (e : Fin 3 ≃ Fin 3) (n : ℕ)
    (habs : ∀ i : Fin 3, ∀ r : ℕ, 0 < r →
      r ≤ principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
      ((n - normalizedRoleWeight M.base e i : ℕ) : ℤ) ∉
        returnIdeal (routingH M.base e) (r * M.base.q.val)) :
    killedCount M (routingD M.base e * n) = 0 := by
  haveI : IsEmpty {C : FiberComponent M.base (routingD M.base e * n) //
      BoundaryKilled M (routingD M.base e * n) C} := ⟨by
    intro C
    obtain ⟨i, r, hr, hrq, hret⟩ := boundaryKilled_has_normalized_predecessor M e n C.val C.property
    exact habs i r hr hrq hret⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- Frozen original subcritical obstruction transported with the true multiplier D*r. -/
theorem normalized_nonprincipal_misses_subcritical_pure (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i : Fin 3)
    (X r : ℕ) (hX : X < criticalExponent M.base (e i)) (hr : 0 < r)
    (hnon : r * M.base.q.val ∉ routingH M.base e) :
    ((X * normalizedRoleWeight M.base e i : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (r * M.base.q.val) := by
  intro hret
  obtain ⟨y, hy, he⟩ := hret.2
  have hyorig := (routing_scaled_mem_iff M.base e y).mpr hy
  obtain ⟨v⟩ := fiber_nonempty M.base ⟨routingD M.base e * y, hyorig⟩
  have heN : X * normalizedRoleWeight M.base e i = y + r * M.base.q.val := by
    push_cast at he
    omega
  apply P3R58.p3_nonprincipal_misses_subcritical_pure M hp (e i) X
    (routingD M.base e * r) hX
    (Nat.mul_pos (routingD_positive M.base e) hr)
    (normalized_nonprincipal_original M.base e r hnon) v.val
  rw [v.property, ← normalizedRoleWeight_scale M.base e i]
  change X * (routingD M.base e * normalizedRoleWeight M.base e i) =
    routingD M.base e * y + (routingD M.base e * r) * M.base.q.val
  nlinarith only [congrArg (fun z => routingD M.base e * z) heN]

theorem normalized_nonprincipal_misses_pure_predecessor (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (r : ℕ) (hr : 0 < r)
    (hnon : r * M.base.q.val ∉ routingH M.base e) :
    (((criticalExponent M.base (e 2) - 1) * routingC M.base e : ℕ) : ℤ) ∉
      returnIdeal (routingH M.base e) (r * M.base.q.val) := by
  apply normalized_nonprincipal_misses_subcritical_pure M hp e 2 _ r
    (by have h := (criticalExponent_spec M.base (e 2)).1; omega) hr hnon

theorem normalized_critical_pure_predecessor (B : Data Gamma) (e : Fin 3 ≃ Fin 3) :
    criticalExponent B (e 2) * routingC B e - normalizedRoleWeight B e 2 =
      (criticalExponent B (e 2) - 1) * routingC B e := by
  change criticalExponent B (e 2) * routingC B e - routingC B e = _
  rw [Nat.sub_mul, one_mul]

/-- All physical component flags vanish when the three actual predecessor returns vanish. -/
theorem critical_killedCount_zero_of_normalized_predecessors_absent
    (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (habs : ∀ i : Fin 3, ∀ r : ℕ, 0 < r →
      r ≤ principalIndex (routingH M.base e) M.base.q.val M.base.q_positive →
      ((criticalExponent M.base (e 2) * routingC M.base e -
        normalizedRoleWeight M.base e i : ℕ) : ℤ) ∉
        returnIdeal (routingH M.base e) (r * M.base.q.val)) :
    killedCount M (criticalExponent M.base (e 2) * weights M.base (e 2)) = 0 := by
  have hs : routingD M.base e * (criticalExponent M.base (e 2) * routingC M.base e) =
      criticalExponent M.base (e 2) * weights M.base (e 2) := by
    rw [← (P3R58.routing_scale_weights M.base e).2.2]
    ring
  rw [← hs]
  exact killedCount_zero_of_normalized_predecessors_absent M e _ habs


end NS25Lean.P3R59


