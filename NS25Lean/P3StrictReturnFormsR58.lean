import NS25Lean.P3NonprincipalPureR58

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R58
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2B4AR4R1
variable {Gamma : NumericalSemigroup}

/-- An original nonprincipal return in the canonical critical rectangle must have
one of the strict RB/LT forms. The arm is a conclusion, not an input witness.
This pointwise result does not prove that distinct return levels use the same arm. -/
theorem nonprincipal_strict_return_form (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (ell i j d : ℕ) (hell : 0 < ell) (hnon : ell * M.base.q.val ∉ M.base.H)
    (hi : i < criticalExponent M.base (e 1))
    (hj : j < criticalExponent M.base (e 2))
    (hcorner : i < P3R57.roleCoefficient M hp e 0 1 ∨
      j < P3R57.roleCoefficient M hp e 0 2)
    (hlive : ∀ k : Fin 3,
      criticalExponent M.base (e 0) * weights M.base (e 0) - weights M.base k ∈ M.base.apery)
    (he : i * weights M.base (e 1) + j * weights M.base (e 2) =
      ell * M.base.q.val + d * weights M.base (e 0)) :
    0 < d ∧
    ((P3R57.roleCoefficient M hp e 0 1 < i ∧
      0 < j ∧ j < P3R57.roleCoefficient M hp e 0 2 ∧
      d < P3R57.roleCoefficient M hp e 1 0) ∨
    (0 < i ∧ i < P3R57.roleCoefficient M hp e 0 1 ∧
      P3R57.roleCoefficient M hp e 0 2 < j ∧
      d < P3R57.roleCoefficient M hp e 2 0)) := by
  have hsum := p3_coefficient_sums M hp e
  have hd : 0 < d := by
    by_contra hn
    have hz : d = 0 := by omega
    have hm := L3C.weight_mem_H M.base
      (Finsupp.single (e 1) i + Finsupp.single (e 2) j)
    simp only [map_add, weight_single] at hm
    apply hnon
    convert hm using 1 <;> simp only [hz, zero_mul, add_zero] at he <;> omega
  have hi0 : 0 < i := by
    by_contra hn
    have hz : i = 0 := by omega
    apply p3_nonprincipal_misses_subcritical_pure M hp (e 2) j ell hj hell hnon
      (Finsupp.single (e 0) d)
    simpa only [hz, zero_mul, zero_add, add_zero, weight_single, add_comm] using he
  have hj0 : 0 < j := by
    by_contra hn
    have hz : j = 0 := by omega
    apply p3_nonprincipal_misses_subcritical_pure M hp (e 1) i ell hi hell hnon
      (Finsupp.single (e 0) d)
    simpa only [hz, zero_mul, zero_add, add_zero, weight_single, add_comm] using he
  have houtside : ¬ (i ≤ P3R57.roleCoefficient M hp e 0 1 ∧
      j ≤ P3R57.roleCoefficient M hp e 0 2) := by
    rintro ⟨hip, hjq⟩
    have hr := P3R57.roleCoefficient_relation M hp e 0
    simp only [P3R57.roleCoefficient_self, zero_mul, zero_add] at hr
    rcases hcorner with hic | hjc
    · let v := Finsupp.single (e 0) d +
        Finsupp.single (e 1) (P3R57.roleCoefficient M hp e 0 1 - i - 1) +
        Finsupp.single (e 2) (P3R57.roleCoefficient M hp e 0 2 - j)
      have hw : weight M.base v =
          d * weights M.base (e 0) +
          (P3R57.roleCoefficient M hp e 0 1 - i - 1) * weights M.base (e 1) +
          (P3R57.roleCoefficient M hp e 0 2 - j) * weights M.base (e 2) := by
        simp only [v, map_add, weight_single]
      have hpadd := Nat.sub_add_cancel (by omega : i + 1 ≤ P3R57.roleCoefficient M hp e 0 1)
      have hqadd := Nat.sub_add_cancel hjq
      have hv : criticalExponent M.base (e 0) * weights M.base (e 0) -
          weights M.base (e 1) = weight M.base v + ell * M.base.q.val := by
        have hsub : P3R57.roleCoefficient M hp e 0 1 - i - 1 =
            P3R57.roleCoefficient M hp e 0 1 - (i + 1) := by omega
        have htotal : criticalExponent M.base (e 0) * weights M.base (e 0) =
            weight M.base v + ell * M.base.q.val + weights M.base (e 1) := by
          rw [hw, hsub]
          nlinarith only [he, hr, hpadd, hqadd]
        omega
      have ha := hlive (e 1)
      rw [M.base.apery_eq_compl] at ha
      exact ha.2 (L5A2R49.boundary_of_positive_shift M.base v _ ell hell hv ha.1)
    · let v := Finsupp.single (e 0) d +
        Finsupp.single (e 1) (P3R57.roleCoefficient M hp e 0 1 - i) +
        Finsupp.single (e 2) (P3R57.roleCoefficient M hp e 0 2 - j - 1)
      have hw : weight M.base v =
          d * weights M.base (e 0) +
          (P3R57.roleCoefficient M hp e 0 1 - i) * weights M.base (e 1) +
          (P3R57.roleCoefficient M hp e 0 2 - j - 1) * weights M.base (e 2) := by
        simp only [v, map_add, weight_single]
      have hpadd := Nat.sub_add_cancel hip
      have hqadd := Nat.sub_add_cancel (by omega : j + 1 ≤ P3R57.roleCoefficient M hp e 0 2)
      have hv : criticalExponent M.base (e 0) * weights M.base (e 0) -
          weights M.base (e 2) = weight M.base v + ell * M.base.q.val := by
        have hsub : P3R57.roleCoefficient M hp e 0 2 - j - 1 =
            P3R57.roleCoefficient M hp e 0 2 - (j + 1) := by omega
        have htotal : criticalExponent M.base (e 0) * weights M.base (e 0) =
            weight M.base v + ell * M.base.q.val + weights M.base (e 2) := by
          rw [hw, hsub]
          nlinarith only [he, hr, hpadd, hqadd]
        omega
      have ha := hlive (e 2)
      rw [M.base.apery_eq_compl] at ha
      exact ha.2 (L5A2R49.boundary_of_positive_shift M.base v _ ell hell hv ha.1)
  refine ⟨hd, ?_⟩
  rcases hcorner with hic | hjc
  · right
    have hjq : P3R57.roleCoefficient M hp e 0 2 < j := by omega
    refine ⟨hi0, hic, hjq, ?_⟩
    by_contra hn
    have hwd : P3R57.roleCoefficient M hp e 2 0 ≤ d := by omega
    have hr := P3R57.roleCoefficient_relation M hp e 2
    simp only [P3R57.roleCoefficient_self, zero_mul, add_zero] at hr
    have hsubd := Nat.sub_add_cancel hwd
    have hsubj := Nat.sub_add_cancel hj.le
    have he' : (P3R57.roleCoefficient M hp e 2 1 + i) * weights M.base (e 1) =
        weight M.base (Finsupp.single (e 0) (d - P3R57.roleCoefficient M hp e 2 0) +
          Finsupp.single (e 2) (criticalExponent M.base (e 2) - j)) + ell * M.base.q.val := by
      simp only [map_add, weight_single, Nat.add_mul]
      nlinarith only [he, hr, hsubd, hsubj]
    exact p3_nonprincipal_misses_subcritical_pure M hp (e 1)
      (P3R57.roleCoefficient M hp e 2 1 + i) ell (by omega) hell hnon _ he'
  · left
    have hip : P3R57.roleCoefficient M hp e 0 1 < i := by omega
    refine ⟨hip, hj0, hjc, ?_⟩
    by_contra hn
    have hud : P3R57.roleCoefficient M hp e 1 0 ≤ d := by omega
    have hr := P3R57.roleCoefficient_relation M hp e 1
    simp only [P3R57.roleCoefficient_self, zero_mul, add_zero] at hr
    have hsubd := Nat.sub_add_cancel hud
    have hsubi := Nat.sub_add_cancel hi.le
    have he' : (P3R57.roleCoefficient M hp e 1 2 + j) * weights M.base (e 2) =
        weight M.base (Finsupp.single (e 0) (d - P3R57.roleCoefficient M hp e 1 0) +
          Finsupp.single (e 1) (criticalExponent M.base (e 1) - i)) + ell * M.base.q.val := by
      simp only [map_add, weight_single, Nat.add_mul]
      nlinarith only [he, hr, hsubd, hsubi]
    exact p3_nonprincipal_misses_subcritical_pure M hp (e 2)
      (P3R57.roleCoefficient M hp e 1 2 + j) ell (by omega) hell hnon _ he'

end NS25Lean.P3R58
