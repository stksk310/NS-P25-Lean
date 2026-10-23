import NS25Lean.P3R2PhysicalDictionaryR57

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R57
open ChosenBase L2B L5A1 L5A2B4AR4R1
variable {Gamma : NumericalSemigroup}

/-- Coefficients of the actual mixed critical representative, with no free geometry fields. -/
def roleCoefficient (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (e : Fin 3 ≃ Fin 3) (i j : Fin 3) : ℕ :=
  (P3R55.axisRole M hp (e i)).witness.val (e j)

theorem roleCoefficient_relation (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    criticalExponent M.base (e i) * weights M.base (e i) =
      roleCoefficient M hp e i 0 * weights M.base (e 0) +
      roleCoefficient M hp e i 1 * weights M.base (e 1) +
      roleCoefficient M hp e i 2 * weights M.base (e 2) := by
  have hw := (P3R55.axisRole M hp (e i)).witness.property
  rw [L5A2B4AR3.weight_three_coordinates M.base e] at hw
  exact (P3R55.axisIndex_degree M hp (e i)).symm.trans hw.symm

@[simp] theorem roleCoefficient_swap (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i j : Fin 3) :
    roleCoefficient M hp (swapRole e) i j =
      roleCoefficient M hp e ((Equiv.swap 1 2) i) ((Equiv.swap 1 2) j) := rfl

@[simp] theorem roleCoefficient_self (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    roleCoefficient M hp e i i = 0 := by
  simpa only [roleCoefficient, P3R55.axisRole_pureRole] using
    (P3R55.axisRole M hp (e i)).witness_pure_zero

theorem roleCoefficient_lt_critical (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (i j : Fin 3) (hij : j ≠ i) :
    roleCoefficient M hp e i j < criticalExponent M.base (e j) := by
  apply P3R55.mixed_coordinate_lt_critical M hp (P3R55.axisRole M hp (e i)) (e j)
  simpa only [P3R55.axisRole_pureRole] using (fun h => hij (e.injective h))

theorem critical_pair_minimum (B : Data Gamma) (i j k : Fin 3)
    (hji : j ≠ i) (hki : k ≠ i) (x y z : ℕ) (hx : 0 < x)
    (he : x * weights B i = y * weights B j + z * weights B k) :
    criticalExponent B i ≤ x := by
  apply criticalExponent_min B i x
  refine ⟨hx, Finsupp.single j y + Finsupp.single k z, ?_, ?_⟩
  · simp [hji.symm, hki.symm]
  · simpa only [map_add, weight_single] using he.symm

/-- RB cone X>0>Y, written with L=-Y. These are actual weights and actual coefficients. -/
theorem actual_rb_horizontal_cone (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (d X L : ℕ) (hd : 0 < d) (hdu : d < roleCoefficient M hp e 1 0)
    (he : X * weights M.base (e 1) =
      d * weights M.base (e 0) + L * weights M.base (e 2)) :
    roleCoefficient M hp e 1 2 + criticalExponent M.base (e 2) ≤ L := by
  have ha := weights_positive M.base (e 0)
  have hb := weights_positive M.base (e 1)
  have hc := weights_positive M.base (e 2)
  have hX : 0 < X := by nlinarith
  have hXc := critical_pair_minimum M.base (e 1) (e 0) (e 2)
    (e.injective.ne (by decide)) (e.injective.ne (by decide)) X d L hX he
  have hr := roleCoefficient_relation M hp e 1
  simp only [roleCoefficient_self, zero_mul, add_zero] at hr
  have hLv : roleCoefficient M hp e 1 2 < L := by nlinarith
  have hLsub := Nat.sub_add_cancel (le_of_lt hLv)
  have hXsub := Nat.sub_add_cancel hXc
  have hdsub := Nat.sub_add_cancel (le_of_lt hdu)
  have hrel : (L - roleCoefficient M hp e 1 2) * weights M.base (e 2) =
      (roleCoefficient M hp e 1 0 - d) * weights M.base (e 0) +
      (X - criticalExponent M.base (e 1)) * weights M.base (e 1) := by nlinarith
  have hmin := critical_pair_minimum M.base (e 2) (e 0) (e 1)
    (e.injective.ne (by decide)) (e.injective.ne (by decide))
    (L - roleCoefficient M hp e 1 2) (roleCoefficient M hp e 1 0 - d)
    (X - criticalExponent M.base (e 1)) (Nat.sub_pos_of_lt hLv) hrel
  omega

/-- RB cone Y>0>X, written with L=-X. -/
theorem actual_rb_vertical_cone (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (d Y L : ℕ) (hd : 0 < d) (hdu : d < roleCoefficient M hp e 1 0)
    (he : Y * weights M.base (e 2) =
      d * weights M.base (e 0) + L * weights M.base (e 1)) :
    roleCoefficient M hp e 2 1 ≤ L := by
  have ha := weights_positive M.base (e 0)
  have hb := weights_positive M.base (e 1)
  have hc := weights_positive M.base (e 2)
  have hY : 0 < Y := by nlinarith
  have hYc := critical_pair_minimum M.base (e 2) (e 0) (e 1)
    (e.injective.ne (by decide)) (e.injective.ne (by decide)) Y d L hY he
  have hr := roleCoefficient_relation M hp e 2
  simp only [roleCoefficient_self, zero_mul, add_zero] at hr
  have hdc : d < criticalExponent M.base (e 0) := by
    have hu := roleCoefficient_lt_critical M hp e 1 0 (by decide)
    omega
  by_contra hn
  have hL : L < roleCoefficient M hp e 2 1 := by omega
  have hYsub := Nat.sub_add_cancel hYc
  have hLsub := Nat.sub_add_cancel (le_of_lt hL)
  have hdw : roleCoefficient M hp e 2 0 < d := by nlinarith
  have hdsub := Nat.sub_add_cancel (le_of_lt hdw)
  have hrel : (d - roleCoefficient M hp e 2 0) * weights M.base (e 0) =
      (Y - criticalExponent M.base (e 2)) * weights M.base (e 2) +
      (roleCoefficient M hp e 2 1 - L) * weights M.base (e 1) := by nlinarith
  have hmin := critical_pair_minimum M.base (e 0) (e 2) (e 1)
    (e.injective.ne (by decide)) (e.injective.ne (by decide))
    (d - roleCoefficient M hp e 2 0) (Y - criticalExponent M.base (e 2))
    (roleCoefficient M hp e 2 1 - L) (Nat.sub_pos_of_lt hdw) hrel
  omega

/-- LT horizontal cone is the actual legal swap of the proved RB vertical cone. -/
theorem actual_lt_horizontal_cone (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (d X L : ℕ) (hd : 0 < d) (hdw : d < roleCoefficient M hp e 2 0)
    (he : X * weights M.base (e 1) =
      d * weights M.base (e 0) + L * weights M.base (e 2)) :
    roleCoefficient M hp e 1 2 ≤ L := by
  simpa only [roleCoefficient_swap, swapRole_zero, swapRole_one, swapRole_two,
    Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_def] using
    actual_rb_vertical_cone M hp (swapRole e) d X L hd (by simpa [Equiv.swap_apply_def] using hdw)
      (by simpa using he)

/-- LT vertical cone is the actual legal swap of the proved RB horizontal cone. -/
theorem actual_lt_vertical_cone (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (d Y L : ℕ) (hd : 0 < d) (hdw : d < roleCoefficient M hp e 2 0)
    (he : Y * weights M.base (e 2) =
      d * weights M.base (e 0) + L * weights M.base (e 1)) :
    roleCoefficient M hp e 2 1 + criticalExponent M.base (e 1) ≤ L := by
  simpa only [roleCoefficient_swap, swapRole_zero, swapRole_one, swapRole_two,
    Equiv.swap_apply_left, Equiv.swap_apply_right, Equiv.swap_apply_def] using
    actual_rb_horizontal_cone M hp (swapRole e) d Y L hd (by simpa [Equiv.swap_apply_def] using hdw)
      (by simpa using he)

end NS25Lean.P3R57
