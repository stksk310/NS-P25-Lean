import NS25Lean.P2DAResidueR49

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2R49First

open ChosenBase L2B L2B2A L2B2A2 L3A L3B L3C
open scoped MonomialOrder
variable {Gamma : NumericalSemigroup}

/-- Adapted from the 2026-09-17 DA4 proof source; the residue-zero premise
is discharged by the actual minimal-boundary SUP theorem in R49. -/
theorem full_support_generator_weight_dvd_pivot (k : Type*) [Field k]
    (B : Data Gamma) (_hJ : IsMonomialIdeal k (B.J k))
    (a : Exponent) (ha : a ∈ fullSupportGenerators (B.J k)) :
    B.q.val ∣ weight B a := by
  have hr := L5A2R49.full_support_residue_zero k B a ha
  change weight B a % B.q.val = 0 % B.q.val at hr
  exact Nat.dvd_of_mod_eq_zero (by simpa using hr)

/-- The actual least positive multiplier returning the pivot degree to the tail monoid. -/
def firstReturnMultiplier (B : Data Gamma) : ℕ := by
  classical
  exact Nat.find (show ∃ e : ℕ, 1 ≤ e ∧ e * B.q.val ∈ B.H by
    refine ⟨weights B 0, weights_positive B 0, ?_⟩
    change (B.tailDegrees 0).val * B.q.val ∈ B.H
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      B.H.nsmul_mem (B.tailDegrees 0).property B.q.val)

theorem firstReturnMultiplier_spec (B : Data Gamma) :
    1 ≤ firstReturnMultiplier B ∧
      firstReturnMultiplier B * B.q.val ∈ B.H := by
  classical
  exact Nat.find_spec (show ∃ e : ℕ, 1 ≤ e ∧ e * B.q.val ∈ B.H by
    refine ⟨weights B 0, weights_positive B 0, ?_⟩
    change (B.tailDegrees 0).val * B.q.val ∈ B.H
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      B.H.nsmul_mem (B.tailDegrees 0).property B.q.val)

theorem firstReturnMultiplier_pos (B : Data Gamma) :
    0 < firstReturnMultiplier B := firstReturnMultiplier_spec B |>.1

theorem firstReturnMultiplier_mem (B : Data Gamma) :
    firstReturnMultiplier B * B.q.val ∈ B.H := firstReturnMultiplier_spec B |>.2

theorem firstReturnMultiplier_minimal (B : Data Gamma) {e : ℕ}
    (he : 1 ≤ e) (hm : e * B.q.val ∈ B.H) : firstReturnMultiplier B ≤ e := by
  classical
  exact Nat.find_min' (show ∃ e : ℕ, 1 ≤ e ∧ e * B.q.val ∈ B.H by
    refine ⟨weights B 0, weights_positive B 0, ?_⟩
    change (B.tailDegrees 0).val * B.q.val ∈ B.H
    simpa [nsmul_eq_mul, Nat.mul_comm] using
      B.H.nsmul_mem (B.tailDegrees 0).property B.q.val) ⟨he, hm⟩

/-- A minimal generator of the actual monomial boundary ideal has boundary weight. -/
theorem minimal_boundary_weight_mem (k : Type*) [Field k] (B : Data Gamma)
    (hJM : B.J k = B.MK k) (u : Exponent)
    (hu : u ∈ minimalExponents (B.J k)) : weight B u ∈ B.K := by
  have hum : MvPolynomial.monomial u (1 : k) ∈ B.MK k := hJM ▸ hu.1
  rw [Data.MK] at hum
  obtain ⟨v, hv, hvu⟩ := (monomial_mem_span_iff _ u).mp hum
  have huv : u ≤ v := hu.2 (by
    rw [hJM, Data.MK]
    exact Ideal.subset_span ⟨v, hv, rfl⟩) hvu
  have he : u = v := le_antisymm huv hvu
  subst v
  simpa only [Set.mem_setOf_eq, ← weight_eq_degree] using hv

/-- Removing a used variable from a minimal boundary monomial lands in Apéry. -/
theorem minimal_boundary_remove_apery (k : Type*) [Field k] (B : Data Gamma)
    (hJM : B.J k = B.MK k) (u : Exponent)
    (hu : u ∈ minimalExponents (B.J k)) (j : Fin 3) (hj : 0 < u j) :
    weight B u - weights B j ∈ B.apery := by
  have he := removed_weight B (weight B u) ⟨u, rfl⟩ j hj
  change weights B j + weight B (u - Finsupp.single j 1) = weight B u at he
  rw [B.apery_eq_compl]
  refine ⟨?_, ?_⟩
  · have hm := (Presentation.factorizationMap B.tailDegrees
      (u - Finsupp.single j 1)).property
    rw [← weight_eq_degree] at hm
    convert hm using 1 <;> omega
  · intro hk
    have hpred : MvPolynomial.monomial (u - Finsupp.single j 1) (1 : k) ∈ B.J k :=
      boundary_monomial_mem_J k B _ (by
        have hw : weight B (u - Finsupp.single j 1) = weight B u - weights B j := by
          omega
        rwa [hw])
    have hsub : u - Finsupp.single j 1 ≤ u := by
      intro x
      simp only [Finsupp.tsub_apply]
      omega
    have hle := hu.2 hpred hsub
    have hc := hle j
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hc
    omega

private theorem removed_weight_value (B : Data Gamma) (u : Exponent)
    (j : Fin 3) (hj : 0 < u j) :
    weight B (u - Finsupp.single j 1) = weight B u - weights B j := by
  have h := removed_weight B (weight B u) ⟨u, rfl⟩ j hj
  change weights B j + weight B (u - Finsupp.single j 1) = weight B u at h
  omega

private theorem factorization_nonzero_of_positive (B : Data Gamma) {d : ℕ}
    (hd : 0 < d) (u : FactorizationFiber B d) : ∃ j, 0 < u.val j := by
  by_contra hn
  push Not at hn
  have hu : u.val = 0 := by ext j; exact Nat.eq_zero_of_le_zero (hn j)
  have he := u.property
  rw [hu, map_zero] at he
  omega

private theorem fin3_same_remaining (i j a b : Fin 3) (hij : i ≠ j)
    (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i) (hbj : b ≠ j) : a = b := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;> simp_all

private theorem fin3_other_pair (i j r x : Fin 3) (hij : i ≠ j)
    (hri : r ≠ i) (hrj : r ≠ j) (hxr : x ≠ r) : x = i ∨ x = j := by
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases x <;> simp_all

/-- FIRST: a full-support minimal boundary generator occurs at the actual first return. -/
theorem full_support_generator_first_return (k : Type*) [Field k] (B : Data Gamma)
    (hJ : IsMonomialIdeal k (B.J k)) (hJM : B.J k = B.MK k)
    (g : Exponent) (hg : g ∈ fullSupportGenerators (B.J k)) :
    weight B g = firstReturnMultiplier B * B.q.val := by
  obtain ⟨d, hd⟩ := full_support_generator_weight_dvd_pivot k B hJ g hg
  have hweight : weight B g = d * B.q.val := by
    simpa [Nat.mul_comm] using hd
  have hdpos : 1 ≤ d := by
    have hgK := minimal_boundary_weight_mem k B hJM g hg.1
    have hwpos : 0 < weight B g := lt_of_lt_of_le B.q_positive hgK.2.1
    by_contra hn
    have hz : d = 0 := by omega
    rw [hz, zero_mul] at hweight
    omega
  have hdH : d * B.q.val ∈ B.H := by
    rw [← hweight]
    exact weight_mem_H B g
  have hkd : firstReturnMultiplier B ≤ d :=
    firstReturnMultiplier_minimal B hdpos hdH
  have hdk : d ≤ firstReturnMultiplier B := by
    by_contra hn
    have hlt : firstReturnMultiplier B < d := by omega
    obtain ⟨v⟩ := fiber_nonempty B
      ⟨firstReturnMultiplier B * B.q.val, firstReturnMultiplier_mem B⟩
    have hvdeg : 0 < firstReturnMultiplier B * B.q.val :=
      Nat.mul_pos (firstReturnMultiplier_pos B) B.q_positive
    obtain ⟨j, hvj⟩ := factorization_nonzero_of_positive B hvdeg v
    have hgj := hg.2 j
    have hrem := removed_weight B (weight B g) ⟨g, rfl⟩ j hgj
    have hvrem := removed_weight B (firstReturnMultiplier B * B.q.val) v j hvj
    have hvprop : weight B v.val = firstReturnMultiplier B * B.q.val := v.property
    have hmul : (d - firstReturnMultiplier B) * B.q.val +
        firstReturnMultiplier B * B.q.val = d * B.q.val := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hlt.le]
    have hK : weight B (g - Finsupp.single j 1) ∈ B.K := by
      apply L3C.degree_in_K_of_positive_pivot B (g - Finsupp.single j 1)
        (weight B (v.val - Finsupp.single j 1))
        (d - firstReturnMultiplier B)
      · exact B.H_le (weight_mem_H B _)
      · omega
      · rw [removed_weight_value B g j hgj,
          removed_weight_value B v.val j hvj, hweight, hvprop]
        omega
    have hmem := boundary_monomial_mem_J k B _ hK
    have hsub : g - Finsupp.single j 1 ≤ g := by
      intro x
      simp only [Finsupp.tsub_apply]
      omega
    have hle := hg.1.2 hmem hsub
    have hc := hle j
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hc
    omega
  rw [hweight, Nat.le_antisymm hdk hkd]

/-- The first-return degree has exactly the full-support factorization. -/
theorem full_support_first_return_factorization_unique (k : Type*) [Field k]
    (B : Data Gamma) (hJ : IsMonomialIdeal k (B.J k))
    (hJM : B.J k = B.MK k)
    (hunique : ∀ d, d ∈ B.apery → Subsingleton (FactorizationFiber B d))
    (g : Exponent) (hg : g ∈ fullSupportGenerators (B.J k))
    (v : FactorizationFiber B (firstReturnMultiplier B * B.q.val)) : v.val = g := by
  have hfirst := full_support_generator_first_return k B hJ hJM g hg
  have hvdeg : 0 < firstReturnMultiplier B * B.q.val :=
    Nat.mul_pos (firstReturnMultiplier_pos B) B.q_positive
  obtain ⟨j, hvj⟩ := factorization_nonzero_of_positive B hvdeg v
  have hgj := hg.2 j
  have ha := minimal_boundary_remove_apery k B hJM g hg.1 j hgj
  have hgrem := removed_weight B (weight B g) ⟨g, rfl⟩ j hgj
  have hvrem := removed_weight B (firstReturnMultiplier B * B.q.val) v j hvj
  let g' : FactorizationFiber B (weight B g - weights B j) :=
    ⟨g - Finsupp.single j 1, removed_weight_value B g j hgj⟩
  let v' : FactorizationFiber B (weight B g - weights B j) :=
    ⟨v.val - Finsupp.single j 1, by
      have hvprop : weight B v.val = firstReturnMultiplier B * B.q.val := v.property
      rw [removed_weight_value B v.val j hvj, hvprop, ← hfirst]⟩
  have he := congrArg Subtype.val ((hunique _ ha).elim g' v')
  have he' := congrArg (fun w => Finsupp.single j 1 + w) he
  simpa only [g', v', remove_variable_add g j hgj,
    remove_variable_add v.val j hvj] using he'.symm

/-- DEPTH, including the actual Apéry representative and support complement. -/
theorem minimal_boundary_depth (k : Type*) [Field k] (B : Data Gamma)
    (hJ : IsMonomialIdeal k (B.J k)) (hJM : B.J k = B.MK k)
    (hunique : ∀ d, d ∈ B.apery → Subsingleton (FactorizationFiber B d))
    (g u : Exponent) (hg : g ∈ fullSupportGenerators (B.J k))
    (hu : u ∈ minimalExponents (B.J k)) (hug : u ≠ g) :
    ∃ r : Exponent, ∃ ell : ℕ,
      weight B r ∈ B.apery ∧
      weight B u = weight B r + ell * B.q.val ∧
      (∀ j, 0 < u j → r j = 0) ∧
      1 ≤ ell ∧ ell < firstReturnMultiplier B ∧ r ≠ 0 := by
  have huK := minimal_boundary_weight_mem k B hJM u hu
  obtain ⟨ω, hω, ell, heq⟩ := apery_decomposition B (weight B u)
    (B.H_le (weight_mem_H B u))
  have hell : 1 ≤ ell := by
    by_contra hn
    have hz : ell = 0 := by omega
    have : weight B u = ω := by simpa [hz] using heq
    exact (B.apery_eq_compl ▸ hω).2 (this ▸ huK)
  obtain ⟨r⟩ := fiber_nonempty B ⟨ω, (B.apery_eq_compl ▸ hω).1⟩
  have hrω : weight B r.val = ω := r.property
  have hsupport : ∀ j, 0 < u j → r.val j = 0 := by
    intro j huj
    by_contra hrj0
    have hrj : 0 < r.val j := Nat.pos_of_ne_zero hrj0
    have hap := minimal_boundary_remove_apery k B hJM u hu j huj
    have hurem := removed_weight B (weight B u) ⟨u, rfl⟩ j huj
    have hrrem := removed_weight B ω r j hrj
    have hK : weight B (u - Finsupp.single j 1) ∈ B.K := by
      apply L3C.degree_in_K_of_positive_pivot B (u - Finsupp.single j 1)
        (weight B (r.val - Finsupp.single j 1)) ell
      · exact B.H_le (weight_mem_H B _)
      · exact hell
      · rw [removed_weight_value B u j huj,
          removed_weight_value B r.val j hrj, hrω]
        omega
    exact (B.apery_eq_compl ▸ hap).2 (by
      have hw := removed_weight_value B u j huj
      rwa [← hw])
  have hfirst := full_support_generator_first_return k B hJ hJM g hg
  have huweightpos : 0 < weight B u := lt_of_lt_of_le B.q_positive huK.2.1
  obtain ⟨j, huj⟩ := factorization_nonzero_of_positive B huweightpos ⟨u, rfl⟩
  have helllt : ell < firstReturnMultiplier B := by
    by_contra hn
    have hkell : firstReturnMultiplier B ≤ ell := by omega
    rcases lt_or_eq_of_le hkell with hlt | he
    · have hgj := hg.2 j
      have hap := minimal_boundary_remove_apery k B hJM u hu j huj
      have hurem := removed_weight B (weight B u) ⟨u, rfl⟩ j huj
      have hgrem := removed_weight B (weight B g) ⟨g, rfl⟩ j hgj
      have hmul : (ell - firstReturnMultiplier B) * B.q.val +
          firstReturnMultiplier B * B.q.val = ell * B.q.val := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hlt.le]
      have hK : weight B (u - Finsupp.single j 1) ∈ B.K := by
        apply L3C.degree_in_K_of_positive_pivot B (u - Finsupp.single j 1)
          (weight B r.val + weight B (g - Finsupp.single j 1))
          (ell - firstReturnMultiplier B)
        · exact Gamma.toAddSubmonoid.add_mem (B.H_le (weight_mem_H B _))
            (B.H_le (weight_mem_H B _))
        · omega
        · rw [removed_weight_value B u j huj,
            removed_weight_value B g j hgj, heq, hfirst, hrω]
          omega
      exact (B.apery_eq_compl ▸ hap).2 (by
        have hw := removed_weight_value B u j huj
        rwa [← hw])
    · subst ell
      have hgj := hg.2 j
      have hap := minimal_boundary_remove_apery k B hJM u hu j huj
      have hurem := removed_weight B (weight B u) ⟨u, rfl⟩ j huj
      have hgrem := removed_weight B (weight B g) ⟨g, rfl⟩ j hgj
      have hsumj : 0 < (r.val + g) j := by simp only [Finsupp.add_apply]; omega
      have hsumrem := removed_weight B (weight B (r.val + g))
        ⟨r.val + g, rfl⟩ j hsumj
      have hweightsum : weight B (r.val + g) = weight B u := by
        rw [map_add, hrω, hfirst, heq]
      let u' : FactorizationFiber B (weight B u - weights B j) :=
        ⟨u - Finsupp.single j 1, removed_weight_value B u j huj⟩
      let w' : FactorizationFiber B (weight B u - weights B j) :=
        ⟨r.val + g - Finsupp.single j 1, by
          rw [removed_weight_value B (r.val + g) j hsumj, hweightsum]⟩
      have hp := congrArg Subtype.val ((hunique _ hap).elim u' w')
      have hp' := congrArg (fun w => Finsupp.single j 1 + w) hp
      have hrg : u = r.val + g := by
        simpa only [u', w', remove_variable_add u j huj,
          remove_variable_add (r.val + g) j hsumj] using hp'
      have hgu : g ≤ u := by
        rw [hrg]
        intro x
        simp only [Finsupp.add_apply]
        omega
      have hugle : u ≤ g := hu.2 hg.1.1 hgu
      exact hug (le_antisymm hugle hgu)
  have hrne : r.val ≠ 0 := by
    intro hr0
    have hreturn : ell * B.q.val ∈ B.H := by
      have hω0 : ω = 0 := by rw [← hrω, hr0, map_zero]
      have huet : weight B u = ell * B.q.val := by simpa [hω0] using heq
      rw [← huet]
      exact weight_mem_H B u
    have hmin := firstReturnMultiplier_minimal B hell hreturn
    omega
  exact ⟨r.val, ell, hrω.symm ▸ hω, by simpa [hrω] using heq,
    hsupport, hell, helllt, hrne⟩

/-- Border purity: a minimal boundary exponent with another actual factorization is pure. -/
theorem nonunique_minimal_border_pure (k : Type*) [Field k] (B : Data Gamma)
    (hJ : IsMonomialIdeal k (B.J k)) (hJM : B.J k = B.MK k)
    (hunique : ∀ d, d ∈ B.apery → Subsingleton (FactorizationFiber B d))
    (hq : q_fs (B.J k) = 1)
    (g u v : Exponent) (hg : g ∈ fullSupportGenerators (B.J k))
    (hu : u ∈ minimalExponents (B.J k)) (hvdeg : weight B v = weight B u)
    (hvu : v ≠ u) :
    ∃ i : Fin 3, 0 < u i ∧ ∀ j, j ≠ i → u j = 0 := by
  have huK := minimal_boundary_weight_mem k B hJM u hu
  have huweightpos : 0 < weight B u := lt_of_lt_of_le B.q_positive huK.2.1
  obtain ⟨i, hui⟩ := factorization_nonzero_of_positive B huweightpos ⟨u, rfl⟩
  have hdisjoint : ∀ j, 0 < u j → v j = 0 := by
    intro j huj
    by_contra hvj0
    have hvj : 0 < v j := Nat.pos_of_ne_zero hvj0
    have hap := minimal_boundary_remove_apery k B hJM u hu j huj
    have hurem := removed_weight B (weight B u) ⟨u, rfl⟩ j huj
    have hvrem := removed_weight B (weight B u) ⟨v, hvdeg⟩ j hvj
    let u' : FactorizationFiber B (weight B u - weights B j) :=
      ⟨u - Finsupp.single j 1, removed_weight_value B u j huj⟩
    let v' : FactorizationFiber B (weight B u - weights B j) :=
      ⟨v - Finsupp.single j 1, by
        rw [removed_weight_value B v j hvj, hvdeg]⟩
    have he := congrArg Subtype.val ((hunique _ hap).elim u' v')
    have he' := congrArg (fun w => Finsupp.single j 1 + w) he
    apply hvu
    simpa only [u', v', remove_variable_add u j huj,
      remove_variable_add v j hvj] using he'.symm
  have hug : u ≠ g := by
    intro he
    subst u
    have hvproof : weight B v = firstReturnMultiplier B * B.q.val := by
      rw [hvdeg, full_support_generator_first_return k B hJ hJM g hg]
    have hvuniq := full_support_first_return_factorization_unique
      k B hJ hJM hunique g hg (⟨v, hvproof⟩ :
        FactorizationFiber B (firstReturnMultiplier B * B.q.val))
    exact hvu hvuniq
  obtain ⟨r, ell, hrA, hdepth, hsup, hell, helllt, hrne⟩ :=
    minimal_boundary_depth k B hJ hJM hunique g u hg hu hug
  refine ⟨i, hui, ?_⟩
  intro j hji
  by_contra huj0
  have huj : 0 < u j := Nat.pos_of_ne_zero huj0
  have hvweightpos : 0 < weight B v := hvdeg ▸ huweightpos
  obtain ⟨iv, hviv⟩ := factorization_nonzero_of_positive B hvweightpos ⟨v, rfl⟩
  obtain ⟨ir, hrir⟩ : ∃ ir, 0 < r ir := by
    by_contra hn
    push Not at hn
    exact hrne (by ext x; exact Nat.eq_zero_of_le_zero (hn x))
  have hir_i : ir ≠ i := fun he => by subst ir; simpa [hsup i hui] using hrir
  have hir_j : ir ≠ j := fun he => by subst ir; simpa [hsup j huj] using hrir
  have hivi : iv = ir := by
    have hiv_i : iv ≠ i := fun he => by subst iv; simpa [hdisjoint i hui] using hviv
    have hiv_j : iv ≠ j := fun he => by subst iv; simpa [hdisjoint j huj] using hviv
    exact fin3_same_remaining i j iv ir hji.symm hiv_i hiv_j hir_i hir_j
  subst iv
  have hvpure : ∀ x, x ≠ ir → v x = 0 := by
    intro x hx
    have hxi : x = i ∨ x = j := by
      exact fin3_other_pair i j ir x hji.symm hir_i hir_j hx
    rcases hxi with hxi | hxj
    · simpa [hxi] using hdisjoint i hui
    · simpa [hxj] using hdisjoint j huj
  have hrpure : ∀ x, x ≠ ir → r x = 0 := by
    intro x hx
    have hxi : x = i ∨ x = j := by
      exact fin3_other_pair i j ir x hji.symm hir_i hir_j hx
    rcases hxi with hxi | hxj
    · simpa [hxi] using hsup i hui
    · simpa [hxj] using hsup j huj
  have hvform : v = Finsupp.single ir (v ir) := by
    ext x
    by_cases hx : x = ir
    · subst x; simp
    · simp [hx, hvpure x hx]
  have hrform : r = Finsupp.single ir (r ir) := by
    ext x
    by_cases hx : x = ir
    · subst x; simp
    · simp [hx, hrpure x hx]
  have hrv : r ir < v ir := by
    have hqpos : 0 < ell * B.q.val := Nat.mul_pos hell B.q_positive
    have hwv : weight B v = v ir * weights B ir := by
      calc
        weight B v = weight B (Finsupp.single ir (v ir)) := congrArg (weight B) hvform
        _ = v ir * weights B ir := by simp [weight_single]
    have hwr : weight B r = r ir * weights B ir := by
      calc
        weight B r = weight B (Finsupp.single ir (r ir)) := congrArg (weight B) hrform
        _ = r ir * weights B ir := by simp [weight_single]
    rw [← hvdeg, hwv, hwr] at hdepth
    nlinarith [weights_positive B ir]
  have hrlev : r ≤ v := by
    intro x
    rw [hvform, hrform]
    by_cases hx : x = ir
    · subst x; simpa using hrv.le
    · simp [hx]
  have hreturn : ell * B.q.val ∈ B.H := by
    have hdiff : weight B (v - r) = ell * B.q.val := by
      have hadd := congrArg (weight B) (tsub_add_cancel_of_le hrlev)
      rw [map_add] at hadd
      rw [hvdeg, hdepth] at hadd
      omega
    rw [← hdiff]
    exact weight_mem_H B _
  have hmin := firstReturnMultiplier_minimal B hell hreturn
  omega

end NS25Lean.L5A2R49First


