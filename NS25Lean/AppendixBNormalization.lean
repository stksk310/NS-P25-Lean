import NS25Lean.AppendixBSupport
import NS25Lean.AppendixBReduced
import NS25Lean.AppendixBRigidity

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C
variable {Gamma : NumericalSemigroup}

theorem weights_not_dvd (B : Data Gamma) (i j : Fin 4) (hij : i ≠ j) :
    ¬ weights B i ∣ weights B j := by
  rintro ⟨k, hk⟩
  apply B.minimal j
  have hm : weights B i ∈ AddSubmonoid.closure
      ((fun l => (B.family l).val) '' {l | l ≠ j}) :=
    AddSubmonoid.subset_closure ⟨i, hij, rfl⟩
  have hmul := (AddSubmonoid.closure
    ((fun l => (B.family l).val) '' {l | l ≠ j})).nsmul_mem hm k
  change weights B j ∈ _
  rw [hk]
  simpa [nsmul_eq_mul, mul_comm] using hmul

theorem pair_quotient_ge_two (B : Data Gamma) (i j : Fin 4) (hij : i ≠ j) :
    2 ≤ weights B i / (weights B i).gcd (weights B j) := by
  let g := (weights B i).gcd (weights B j)
  have he : g * (weights B i / g) = weights B i :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hp := weights_positive B i
  have hn := weights_not_dvd B i j hij
  have hd : g ∣ weights B j := Nat.gcd_dvd_right _ _
  by_contra h
  have hone : weights B i / g = 1 := by nlinarith
  have hg : g = weights B i := by simpa [hone] using he
  exact hn (hg ▸ hd)

theorem common_weight_divisor_eq_one (B : Data Gamma) (g : ℕ)
    (h : ∀ i, g ∣ weights B i) : g = 1 := by
  have hall : ∀ n ∈ Gamma.toAddSubmonoid, g ∣ n := by
    intro n hn
    rw [← B.generates] at hn
    induction hn using AddSubmonoid.closure_induction with
    | mem n hn => obtain ⟨i, rfl⟩ := hn; exact h i
    | zero => exact dvd_zero g
    | add x y hx hy ihx ihy => exact dvd_add ihx ihy
  obtain ⟨c, hc⟩ := Gamma.exists_conductor
  have hd0 := hall c (hc c le_rfl)
  have hd1 := hall (c + 1) (hc (c + 1) (by omega))
  have hg1 : g ∣ 1 := (Nat.dvd_add_right hd0).mp hd1
  exact Nat.eq_one_of_dvd_one hg1

/-- An explicit permutation naming both disjoint pairs, on the original family. -/
theorem two_pair_permutation (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i)
    (hcount : (purePairDegrees B).card = 2) :
    ∃ (p : Fin 4 ≃ Fin 4) (d e : ℕ),
      purePairDegrees B = {d, e} ∧ d ≠ e ∧
      fiberVariables B d = {p 0, p 1} ∧ fiberVariables B e = {p 2, p 3} := by
  classical
  obtain ⟨d, e, hde, hset⟩ := Finset.card_eq_two.mp hcount
  have hd : d ∈ purePairDegrees B := by simp [hset]
  have he : e ∈ purePairDegrees B := by simp [hset]
  obtain ⟨i, j, a, b, hij, _, _, _, _, hdij, _⟩ :=
    purePair_fiber_exactly_two_pure_powers B hpos d hd
  obtain ⟨k, l, c, f, hkl, _, _, _, _, hekl, _⟩ :=
    purePair_fiber_exactly_two_pure_powers B hpos e he
  have hdis := purePair_supports_disjoint B hpos d e hd he hde
  rw [hdij, hekl] at hdis
  have hik : i ≠ k := by intro h; subst k; exact Finset.disjoint_left.mp hdis (Finset.mem_insert_self _ _) (by simp)
  have hil : i ≠ l := by intro h; subst l; exact Finset.disjoint_left.mp hdis (Finset.mem_insert_self _ _) (by simp)
  have hjk : j ≠ k := by intro h; subst k; exact Finset.disjoint_left.mp hdis (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)) (by simp)
  have hjl : j ≠ l := by intro h; subst l; exact Finset.disjoint_left.mp hdis (Finset.mem_insert_of_mem (Finset.mem_singleton_self j)) (by simp)
  let f : Fin 4 → Fin 4 := ![i, j, k, l]
  have hf : Function.Injective f := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [f, Ne.symm]
  let p : Fin 4 ≃ Fin 4 := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  exact ⟨p, d, e, hset, hde, hdij, hekl⟩

/-- Pair gcd normalization, including all coprimalities and minimality bounds. -/
theorem pair_gcd_normalization (B : Data Gamma) (p : Fin 4 ≃ Fin 4) :
    ∃ u v a b c d : ℕ,
      0 < u ∧ 0 < v ∧ a.Coprime b ∧ c.Coprime d ∧ u.Coprime v ∧
      2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c ∧ 2 ≤ d ∧
      weights B (p 0) = u * a ∧ weights B (p 1) = u * b ∧
      weights B (p 2) = v * c ∧ weights B (p 3) = v * d := by
  let u := (weights B (p 0)).gcd (weights B (p 1))
  let v := (weights B (p 2)).gcd (weights B (p 3))
  have hu : 0 < u := Nat.gcd_pos_of_pos_left _ (weights_positive B (p 0))
  have hv : 0 < v := Nat.gcd_pos_of_pos_left _ (weights_positive B (p 2))
  have huv : u.Coprime v := by
    apply common_weight_divisor_eq_one B
    intro i
    obtain ⟨j, rfl⟩ := p.surjective i
    fin_cases j
    · exact dvd_trans (Nat.gcd_dvd_left u v) (Nat.gcd_dvd_left _ _)
    · exact dvd_trans (Nat.gcd_dvd_left u v) (Nat.gcd_dvd_right _ _)
    · exact dvd_trans (Nat.gcd_dvd_right u v) (Nat.gcd_dvd_left _ _)
    · exact dvd_trans (Nat.gcd_dvd_right u v) (Nat.gcd_dvd_right _ _)
  refine ⟨u, v, weights B (p 0) / u, weights B (p 1) / u,
    weights B (p 2) / v, weights B (p 3) / v, hu, hv,
    Nat.coprime_div_gcd_div_gcd hu, Nat.coprime_div_gcd_div_gcd hv, huv, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pair_quotient_ge_two B _ _ (p.injective.ne (by decide))
  · simpa [u, Nat.gcd_comm] using pair_quotient_ge_two B (p 1) (p 0) (p.injective.ne (by decide))
  · exact pair_quotient_ge_two B _ _ (p.injective.ne (by decide))
  · simpa [v, Nat.gcd_comm] using pair_quotient_ge_two B (p 3) (p 2) (p.injective.ne (by decide))
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm
  · exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)).symm

theorem every_variable_in_pair (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i)
    (hcount : (purePairDegrees B).card = 2) (i : Fin 4) :
    ∃ d ∈ purePairDegrees B, i ∈ fiberVariables B d := by
  classical
  obtain ⟨p, d, e, hset, hde, hd, he⟩ := two_pair_permutation B hpos hcount
  obtain ⟨j, rfl⟩ := p.surjective i
  fin_cases j
  · exact ⟨d, by simp [hset], by simp [hd]⟩
  · exact ⟨d, by simp [hset], by simp [hd]⟩
  · exact ⟨e, by simp [hset], by simp [he]⟩
  · exact ⟨e, by simp [hset], by simp [he]⟩

theorem two_pair_no_other_singleton (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i)
    (hcount : (purePairDegrees B).card = 2) (d : ℕ) (hd : Betti B d)
    (hnot : d ∉ purePairDegrees B) (C : FiberComponent B d) :
    (componentSupport B d C).card ≠ 1 := by
  intro hC
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hC
  obtain ⟨e, he, hie⟩ := every_variable_in_pair B hpos hcount i
  obtain ⟨E, hE⟩ := purePair_variable_singleton B hpos e he i hie
  have heB := ((mem_purePairDegrees B e).mp he).1
  have hde := singleton_active_degree_unique B d e (betti_positive B d hd)
    (betti_positive B e heB) hd heB C E i hi hE
  exact hnot (hde ▸ he)

theorem two_pair_other_support_four (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i)
    (hcount : (purePairDegrees B).card = 2) (d : ℕ) (hd : Betti B d)
    (hnot : d ∉ purePairDegrees B) : (fiberVariables B d).card = 4 := by
  obtain ⟨C, E, _, _, _, _, _, _, hclass⟩ := equality_support_classification B hpos d hd
  have hC := two_pair_no_other_singleton B hpos hcount d hd hnot C
  have hE := two_pair_no_other_singleton B hpos hcount d hd hnot E
  rcases hclass with h | h | h
  · exact False.elim (hC h.2.2.1)
  · rcases h.2.2 with h | h
    · exact False.elim (hC h.1)
    · exact False.elim (hE h.2)
  · exact h.1

theorem purePair_oriented_payload (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (d : ℕ) (hd : d ∈ purePairDegrees B)
    (i j : Fin 4) (hij : i ≠ j) (hvars : fiberVariables B d = {i, j}) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ d = a * weights B i ∧ d = b * weights B j ∧
      (∀ f : Fin 4 →₀ ℕ, weight B f = d ↔ f = Finsupp.single i a ∨ f = Finsupp.single j b) := by
  obtain ⟨r, s, a, b, hrs, ha, hb, hra, hsb, hvar, hfull⟩ :=
    purePair_fiber_exactly_two_pure_powers B hpos d hd
  have he : ({r, s} : Finset (Fin 4)) = {i, j} := hvar.symm.trans hvars
  have hr : r = i ∨ r = j := by
    have hm : r ∈ ({i, j} : Finset (Fin 4)) := he ▸ Finset.mem_insert_self _ _
    simpa using hm
  have hs : s = i ∨ s = j := by
    have hm : s ∈ ({i, j} : Finset (Fin 4)) := he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self s)
    simpa using hm
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
  · exact False.elim (hrs rfl)
  · exact ⟨a, b, ha, hb, hra, hsb, hfull⟩
  · exact ⟨b, a, hb, ha, hsb, hra, fun f => (hfull f).trans or_comm⟩
  · exact False.elim (hrs rfl)

theorem normalized_pair_fiber (B : Data Gamma)
    (hpos : ∀ k : Fin 4, 0 < internalLoad B k) (d : ℕ) (hd : d ∈ purePairDegrees B)
    (i j : Fin 4) (hij : i ≠ j) (hvars : fiberVariables B d = {i, j})
    (u a b : ℕ) (hu : 0 < u) (ha : 0 < a) (hb : 0 < b) (hc : a.Coprime b)
    (hi : weights B i = u * a) (hj : weights B j = u * b) :
    d = u * a * b ∧ (∀ f : Fin 4 →₀ ℕ, weight B f = u * a * b ↔
      f = Finsupp.single i b ∨ f = Finsupp.single j a) := by
  obtain ⟨R, S, hR, hS, hdi, hdj, hfull⟩ := purePair_oriented_payload B hpos d hd i j hij hvars
  have hdL := two_pure_power_degree_eq_lcm B d i j hij R S hR hS hdi hdj hfull
  have hdprod : d = u * a * b := by
    rw [hdL, hi, hj, Nat.lcm_mul_left, hc.lcm_eq_mul, mul_assoc]
  have hRb : R = b := by rw [hi, hdprod] at hdi; nlinarith
  have hSa : S = a := by rw [hj, hdprod] at hdj; nlinarith
  exact ⟨hdprod, by simpa [hdprod, hRb, hSa] using hfull⟩

/-- Constructed normalized source data, linked pointwise to the original four variables. -/
structure NormalizedPairs (B : Data Gamma) where
  perm : Fin 4 ≃ Fin 4
  u : ℕ
  v : ℕ
  alpha : ℕ
  beta : ℕ
  gamma : ℕ
  delta : ℕ
  u_pos : 0 < u
  v_pos : 0 < v
  alpha_ge : 2 ≤ alpha
  beta_ge : 2 ≤ beta
  gamma_ge : 2 ≤ gamma
  delta_ge : 2 ≤ delta
  ab_coprime : alpha.Coprime beta
  cd_coprime : gamma.Coprime delta
  uv_coprime : u.Coprime v
  weight0 : weights B (perm 0) = u * alpha
  weight1 : weights B (perm 1) = u * beta
  weight2 : weights B (perm 2) = v * gamma
  weight3 : weights B (perm 3) = v * delta
  pair_degrees : purePairDegrees B = {u * alpha * beta, v * gamma * delta}
  degrees_ne : u * alpha * beta ≠ v * gamma * delta
  pair0 : ∀ f : Fin 4 →₀ ℕ, weight B f = u * alpha * beta ↔
    f = Finsupp.single (perm 0) beta ∨ f = Finsupp.single (perm 1) alpha
  pair1 : ∀ f : Fin 4 →₀ ℕ, weight B f = v * gamma * delta ↔
    f = Finsupp.single (perm 2) delta ∨ f = Finsupp.single (perm 3) gamma

theorem normalizedPairs_exists (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i)
    (hcount : (purePairDegrees B).card = 2) : Nonempty (NormalizedPairs B) := by
  classical
  obtain ⟨p, d, e, hset, hde, hdvars, hevars⟩ := two_pair_permutation B hpos hcount
  obtain ⟨u, v, a, b, c, f, hu, hv, hab, hcf, huv, ha, hb, hc, hf, h0, h1, h2, h3⟩ :=
    pair_gcd_normalization B p
  have hd : d ∈ purePairDegrees B := by simp [hset]
  have he : e ∈ purePairDegrees B := by simp [hset]
  obtain ⟨hdval, hdfull⟩ := normalized_pair_fiber B hpos d hd (p 0) (p 1)
    (p.injective.ne (by decide)) hdvars u a b hu (by omega) (by omega) hab h0 h1
  obtain ⟨heval, hefull⟩ := normalized_pair_fiber B hpos e he (p 2) (p 3)
    (p.injective.ne (by decide)) hevars v c f hv (by omega) (by omega) hcf h2 h3
  exact ⟨⟨p, u, v, a, b, c, f, hu, hv, ha, hb, hc, hf, hab, hcf, huv,
    h0, h1, h2, h3, by simpa [hdval, heval] using hset,
    by simpa [hdval, heval] using hde, hdfull, hefull⟩⟩

end NS25Lean.L4A
