import NS25Lean.P3ReturnNormalizationR59

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R59
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2C4H L5A2B4AR1
  L5A2C4A L5A2C4D L5A2C4OR5 L5A2C4OR6
variable {Gamma : NumericalSemigroup}

theorem critical_no_fullsupport (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (L A B : ℕ) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B) :
    criticalExponent M.base (e 2) * routingC M.base e ≠
      L * routingA M.base e + A * routingB M.base e + B * routingC M.base e := by
  intro he
  have ha := routingA_pos M.base e
  have hc : 0 < routingC M.base e := by
    have hs := (P3R58.routing_scale_weights M.base e).2.2
    have hp := weights_positive M.base (e 2)
    nlinarith
  have hLa : 0 < L * routingA M.base e := Nat.mul_pos hL ha
  have hBc : B < criticalExponent M.base (e 2) := by
    by_contra hn
    have hprod := Nat.mul_le_mul_right (routingC M.base e)
      (by omega : criticalExponent M.base (e 2) ≤ B)
    omega
  have hrel : (criticalExponent M.base (e 2) - B) * routingC M.base e =
      L * routingA M.base e + A * routingB M.base e := by
    rw [Nat.sub_mul]
    omega
  have hmin := coherent_third_minimality M.base e (P3R58.p3_coherentHerzogData M hp e)
    (criticalExponent M.base (e 2) - B) L A (by omega) hrel
  change criticalExponent M.base (e 2) ≤ criticalExponent M.base (e 2) - B at hmin
  omega

theorem normalized_generator_le_third_critical (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    normalizedRoleWeight M.base e i ≤ criticalExponent M.base (e 2) * routingC M.base e := by
  have hr := (coherent_normalized_relations M.base e
    (P3R58.p3_coherentHerzogData M hp e)).2.2
  have hW := P3R58.p3_coefficients_positive M hp e 2 0 (by decide)
  have hZ := P3R58.p3_coefficients_positive M hp e 2 1 (by decide)
  change criticalExponent M.base (e 2) * routingC M.base e =
    P3R57.roleCoefficient M hp e 2 0 * routingA M.base e +
    P3R57.roleCoefficient M hp e 2 1 * routingB M.base e at hr
  have hC := (criticalExponent_spec M.base (e 2)).1
  fin_cases i
  · change routingA M.base e ≤ _
    have h := Nat.mul_le_mul_right (routingA M.base e) (by omega : 1 ≤ P3R57.roleCoefficient M hp e 2 0)
    rw [hr]
    simp only [one_mul] at h
    exact h.trans (Nat.le_add_right _ _)
  · change routingB M.base e ≤ _
    have h := Nat.mul_le_mul_right (routingB M.base e) (by omega : 1 ≤ P3R57.roleCoefficient M hp e 2 1)
    rw [hr]
    simp only [one_mul] at h
    exact h.trans (Nat.le_add_left _ _)
  · change routingC M.base e ≤ _
    simpa only [one_mul] using Nat.mul_le_mul_right (routingC M.base e) (by omega : 1 ≤ criticalExponent M.base (e 2))

theorem principal_fullsupport_critical_absent (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n L A B : ℕ) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (he : n * M.base.q.val = L * routingA M.base e +
      A * routingB M.base e + B * routingC M.base e) :
    (criticalExponent M.base (e 2) * routingC M.base e : ℕ) -
      (n * M.base.q.val : ℤ) ∉ (routingH M.base e).asRelativeIdeal := by
  rintro ⟨y, hy, hye⟩
  obtain ⟨x, z, w, hfac⟩ := routingH_factorization M.base e hy
  have hnat : criticalExponent M.base (e 2) * routingC M.base e = n * M.base.q.val + y := by
    omega
  apply critical_no_fullsupport M hp e (L + x) (A + z) (B + w)
    (by omega) (by omega) (by omega)
  rw [hnat, he, hfac]
  ring

theorem principal_fullsupport_predecessors_absent (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (n L A B : ℕ) (hL : 0 < L) (hA : 0 < A) (hB : 0 < B)
    (he : n * M.base.q.val = L * routingA M.base e +
      A * routingB M.base e + B * routingC M.base e) (i : Fin 3) :
    ((criticalExponent M.base (e 2) * routingC M.base e -
      normalizedRoleWeight M.base e i : ℕ) : ℤ) ∉
        returnIdeal (routingH M.base e) (n * M.base.q.val) := by
  intro hret
  have hg : normalizedRoleWeight M.base e i ∈ routingH M.base e := by
    apply (routing_scaled_mem_iff M.base e _).mp
    rw [normalizedRoleWeight_scale]
    exact (M.base.tailDegrees (e i)).property
  have hadd := (routingH M.base e).asRelativeIdeal.add_mem hret.2 hg
  apply principal_fullsupport_critical_absent M hp e n L A B hL hA hB he
  have heq : ((criticalExponent M.base (e 2) * routingC M.base e -
      normalizedRoleWeight M.base e i : ℕ) : ℤ) - (n * M.base.q.val : ℕ) +
      normalizedRoleWeight M.base e i =
      (criticalExponent M.base (e 2) * routingC M.base e : ℕ) - (n * M.base.q.val : ℤ) := by
    rw [Nat.cast_sub (normalized_generator_le_third_critical M hp e i)]
    push_cast
    ring
  rw [heq] at hadd
  exact hadd

end NS25Lean.P3R59
