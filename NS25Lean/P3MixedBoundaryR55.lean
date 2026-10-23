import NS25Lean.P3CriticalDictionaryR55
import NS25Lean.P3NonuniqueDegreeR55

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R55
open ChosenBase L2B L5A1 L5A2B4AR4R1
variable {Gamma : NumericalSemigroup}

/-- Liveness of the actual pure component controls every smaller pure power. -/
theorem live_pure_power_apery (M : MultiplicityBase Gamma) {h : ℕ}
    (R : PureMixedCriticalRole M.base h)
    (hlive : ¬ BoundaryKilled M h R.pureComponent)
    (n : ℕ) (hn : n < criticalExponent M.base R.pureRole) :
    weight M.base (Finsupp.single R.pureRole n) ∈ M.base.apery := by
  have hc := (criticalExponent_spec M.base R.pureRole).1
  have he : weight M.base (Finsupp.single R.pureRole
      (criticalExponent M.base R.pureRole - 1)) = h - weights M.base R.pureRole := by
    rw [weight_single]
    have hd := R.degree_eq_critical
    have hw := weights_positive M.base R.pureRole
    have ha := Nat.sub_add_cancel (show 1 ≤ criticalExponent M.base R.pureRole by omega)
    have hs : (criticalExponent M.base R.pureRole - 1) * weights M.base R.pureRole +
        weights M.base R.pureRole = h := by nlinarith
    omega
  have ha : weight M.base (Finsupp.single R.pureRole
      (criticalExponent M.base R.pureRole - 1)) ∈ M.base.apery := by
    rw [M.base.apery_eq_compl]
    exact ⟨L3C.weight_mem_H _ _, fun hk => hlive ((role_pure_killed_iff M R).mpr (he ▸ hk))⟩
  apply L3C.apery_weight_of_le M.base _ _ _ ha
  intro i
  by_cases hi : i = R.pureRole
  · subst i; simp only [Finsupp.single_eq_same]; omega
  · simp [hi]

/-- A killed mixed predecessor has a true minimal boundary divisor, below all
    three coordinate critical powers and strictly below its critical degree. -/
theorem mixed_minimal_boundary (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (k : Type*) [Field k] {h : ℕ}
    (R : PureMixedCriticalRole M.base h)
    (hk : BoundaryKilled M h R.mixedComponent) :
    ∃ u : Fin 3 →₀ ℕ, u ∈ L3A.minimalExponents (M.base.J k) ∧
      u ≤ R.witness.val ∧ u R.pureRole = 0 ∧
      (∀ i, u i < criticalExponent M.base i) ∧ weight M.base u < h := by
  classical
  obtain ⟨j, hj, hK⟩ : ∃ j, 0 < R.witness.val j ∧ h - weights M.base j ∈ M.base.K := by
    rcases (role_mixed_killed_iff M R).mp hk with hl | hr
    · exact ⟨R.otherLeft, R.witness_left_pos, hl⟩
    · exact ⟨R.otherRight, R.witness_right_pos, hr⟩
  have he := L3B.removed_weight M.base h R.witness j hj
  have hpred : weight M.base (R.witness.val - Finsupp.single j 1) ∈ M.base.K := by
    convert hK using 1 <;> omega
  obtain ⟨u, hu, hmin⟩ := L3A.exists_minimal_le (M.base.J k)
    (R.witness.val - Finsupp.single j 1)
    ((monomial_mem_chosen_iff_boundary k M.base _).mpr hpred)
  have hu' : u ≤ R.witness.val := hu.trans tsub_le_self
  have hz : u R.pureRole = 0 := Nat.eq_zero_of_le_zero (by
    simpa only [R.witness_pure_zero] using hu' R.pureRole)
  refine ⟨u, hmin, hu', hz, ?_, ?_⟩
  · intro i
    by_cases hi : i = R.pureRole
    · subst i; rw [hz]; exact (criticalExponent_spec M.base R.pureRole).1
    · exact lt_of_le_of_lt (hu' i) (mixed_coordinate_lt_critical M hp R i hi)
  · have hw := congrArg (weight M.base) (add_tsub_cancel_of_le hu)
    rw [map_add] at hw
    have hpj := weights_positive M.base j
    omega

/-- Under the all-pure-live contradiction premise, a true mixed boundary
    divisor uses both actual complementary coordinates. -/
theorem all_pure_live_minimal_pair (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3)
    (hall : ∀ j, ¬ BoundaryKilled M (axisIndex M hp j).val (axisRole M hp j).pureComponent)
    (k : Type*) [Field k] {h : ℕ} (R : PureMixedCriticalRole M.base h)
    (u : Fin 3 →₀ ℕ) (hu : u ∈ L3A.minimalExponents (M.base.J k))
    (hzero : u R.pureRole = 0) (hbound : ∀ i, u i < criticalExponent M.base i) :
    0 < u R.otherLeft ∧ 0 < u R.otherRight := by
  classical
  have hK := (monomial_mem_chosen_iff_boundary k M.base u).mp hu.1
  have no_single (j : Fin 3) (he : u = Finsupp.single j (u j)) : False := by
    have ha := live_pure_power_apery M (axisRole M hp j) (hall j) (u j)
      (by simpa using hbound j)
    have ha' : weight M.base (Finsupp.single j (u j)) ∈ M.base.apery := by
      simpa only [axisRole_pureRole] using ha
    rw [← he] at ha'
    rw [M.base.apery_eq_compl] at ha'
    exact ha'.2 hK
  constructor
  · by_contra hn
    have hz : u R.otherLeft = 0 := by omega
    apply no_single R.otherRight
    ext j
    by_cases hj : j = R.pureRole
    · subst j; simp [hzero, R.pure_ne_right]
    · rcases (role_other_axes R j).mp hj with rfl | rfl
      · simp [hz, R.other_ne]
      · simp
  · by_contra hn
    have hz : u R.otherRight = 0 := by omega
    apply no_single R.otherLeft
    ext j
    by_cases hj : j = R.pureRole
    · subst j; simp [hzero, R.pure_ne_left]
    · rcases (role_other_axes R j).mp hj with rfl | rfl
      · simp
      · simp [hz, R.other_ne.symm]

/-- The complementary remainder vanishes for a pair-supported minimal divisor
    below a mixed witness opposite a live pure component. -/
theorem live_pure_pair_return_zero (M : MultiplicityBase Gamma)
    (hR0 : (P3R51.internalDegrees M).card = 0) (k : Type*) [Field k]
    {h : ℕ} (R : PureMixedCriticalRole M.base h)
    (hlive : ¬ BoundaryKilled M h R.pureComponent)
    (u : Fin 3 →₀ ℕ) (hu : u ∈ L3A.minimalExponents (M.base.J k))
    (hle : u ≤ R.witness.val) (hl : 0 < u R.otherLeft) (hr : 0 < u R.otherRight) :
    ∃ ell : ℕ, 0 < ell ∧ weight M.base u = ell * M.base.q.val := by
  classical
  obtain ⟨v, ell, hv, hell, he, hcomp, _⟩ :=
    P3R54.r0_minimal_boundary_unique_return M hR0 k u hu
  have hvl := hcomp R.otherLeft hl
  have hvr := hcomp R.otherRight hr
  have hvpure : v = Finsupp.single R.pureRole (v R.pureRole) := by
    ext j
    by_cases hj : j = R.pureRole
    · subst j; simp
    · rcases (role_other_axes R j).mp hj with rfl | rfl
      · simp [hvl, R.pure_ne_left.symm]
      · simp [hvr, R.pure_ne_right.symm]
  have hv0 : v R.pureRole = 0 := by
    by_contra hn
    have hp : 0 < v R.pureRole := Nat.pos_of_ne_zero hn
    let rest := (R.witness.val - u) + Finsupp.single R.pureRole (v R.pureRole - 1)
    have hsum := congrArg (weight M.base) (add_tsub_cancel_of_le hle)
    rw [map_add, R.witness.property] at hsum
    have hvw : weight M.base v = v R.pureRole * weights M.base R.pureRole :=
      (congrArg (weight M.base) hvpure).trans (weight_single _ _ _)
    have hrest : weight M.base rest = weight M.base (R.witness.val - u) +
        (v R.pureRole - 1) * weights M.base R.pureRole := by
      simp only [rest, map_add, weight_single]
    have hsub := Nat.sub_add_cancel (show 1 ≤ v R.pureRole by omega)
    have he' : h - weights M.base R.pureRole = weight M.base rest + ell * M.base.q.val := by
      have hw := weights_positive M.base R.pureRole
      have hs : weight M.base rest + ell * M.base.q.val + weights M.base R.pureRole = h := by
        nlinarith
      omega
    have hdH : h - weights M.base R.pureRole ∈ M.base.H := by
      have ha := live_pure_power_apery M R hlive
        (criticalExponent M.base R.pureRole - 1) (by
          have hc := (criticalExponent_spec M.base R.pureRole).1; omega)
      rw [M.base.apery_eq_compl] at ha
      have hc := (criticalExponent_spec M.base R.pureRole).1
      have hd := R.degree_eq_critical
      have hw := weights_positive M.base R.pureRole
      have hca := Nat.sub_add_cancel (show 1 ≤ criticalExponent M.base R.pureRole by omega)
      rw [weight_single] at ha
      have hs : (criticalExponent M.base R.pureRole - 1) * weights M.base R.pureRole +
          weights M.base R.pureRole = h := by nlinarith
      convert ha.1 using 1 <;> omega
    exact hlive ((role_pure_killed_iff M R).mpr
      (L5A2R49.boundary_of_positive_shift M.base rest _ ell (by omega) he' hdH))
  refine ⟨ell, hell, ?_⟩
  have hz : v = 0 := by simpa only [hv0, Finsupp.single_zero] using hvpure
  simpa only [hz, map_zero, zero_add] using he

/-- A zero-remainder pair return below a live pure critical degree is already
    the first return of the original pivot (no tail-gcd normalization). -/
theorem live_pure_pair_return_first (M : MultiplicityBase Gamma)
    (k : Type*) [Field k] {h : ℕ} (R : PureMixedCriticalRole M.base h)
    (hlive : ¬ BoundaryKilled M h R.pureComponent)
    (u : Fin 3 →₀ ℕ) (hu : u ∈ L3A.minimalExponents (M.base.J k))
    (hl : 0 < u R.otherLeft) (hr : 0 < u R.otherRight) (hsmall : weight M.base u < h)
    (ell : ℕ) (hell : 0 < ell) (he : weight M.base u = ell * M.base.q.val) :
    ell = L5A2R49First.firstReturnMultiplier M.base := by
  classical
  let q := L5A2R49First.firstReturnMultiplier M.base
  have hqm := L5A2R49First.firstReturnMultiplier_mem M.base
  have hqp := L5A2R49First.firstReturnMultiplier_pos M.base
  have hqle : q ≤ ell := L5A2R49First.firstReturnMultiplier_minimal M.base (by omega)
    (he ▸ L3C.weight_mem_H M.base u)
  obtain ⟨v⟩ := fiber_nonempty M.base ⟨q * M.base.q.val, hqm⟩
  have hshared : ∃ i, 0 < u i ∧ 0 < v.val i := by
    by_cases hvl : 0 < v.val R.otherLeft
    · exact ⟨R.otherLeft, hl, hvl⟩
    by_cases hvr : 0 < v.val R.otherRight
    · exact ⟨R.otherRight, hr, hvr⟩
    have hz : v.val = Finsupp.single R.pureRole (v.val R.pureRole) := by
      ext j
      by_cases hj : j = R.pureRole
      · subst j; simp
      · rcases (role_other_axes R j).mp hj with rfl | rfl
        · simp [Nat.eq_zero_of_not_pos hvl, R.pure_ne_left.symm]
        · simp [Nat.eq_zero_of_not_pos hvr, R.pure_ne_right.symm]
    have hvw : v.val R.pureRole * weights M.base R.pureRole = q * M.base.q.val := by
      have hvw := v.property
      rw [hz, weight_single] at hvw
      exact hvw
    have hn : v.val R.pureRole < criticalExponent M.base R.pureRole := by
      have hd := R.degree_eq_critical
      have hw := weights_positive M.base R.pureRole
      have hm := M.base.q_positive
      nlinarith
    have ha := live_pure_power_apery M R hlive (v.val R.pureRole) hn
    have ha' : q * M.base.q.val ∈ M.base.apery := by
      rwa [weight_single, hvw] at ha
    rw [M.base.apery_eq_compl] at ha'
    exact False.elim (ha'.2 (L5A2R49.boundary_of_positive_shift M.base 0 _ q
      (by omega) (by simp) hqm))
  obtain ⟨i, hui, hvi⟩ := hshared
  by_contra hn
  have hlt : q < ell := by omega
  have hwu := L3B.removed_weight M.base (weight M.base u) ⟨u, rfl⟩ i hui
  change weights M.base i + weight M.base (u - Finsupp.single i 1) = weight M.base u at hwu
  have hwv := L3B.removed_weight M.base (q * M.base.q.val) v i hvi
  have hdiff : weight M.base (u - Finsupp.single i 1) =
      weight M.base (v.val - Finsupp.single i 1) + (ell - q) * M.base.q.val := by
    have hsub := Nat.sub_add_cancel hqle
    have hs : weight M.base (u - Finsupp.single i 1) + q * M.base.q.val =
        weight M.base (v.val - Finsupp.single i 1) + ell * M.base.q.val := by omega
    nlinarith
  have hK := L5A2R49.boundary_of_positive_shift M.base
    (v.val - Finsupp.single i 1) _ (ell - q) (by omega) hdiff (L3C.weight_mem_H _ _)
  exact (minimal_predecessor_standard k M.base hu i hui)
    ((monomial_mem_chosen_iff_boundary k M.base _).mpr hK)

/-- M02 §3 interim gate with the original M, defect and R0 binders. -/
theorem r0_some_pure_killed (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0) :
    ∃ h ∈ positiveDegrees M, ∃ R : PureMixedCriticalRole M.base h,
      BoundaryKilled M h R.pureComponent := by
  classical
  by_contra hn
  have hpos (j : Fin 3) : (axisIndex M hp j).val ∈ positiveDegrees M := by
    rw [← P3R51.active_eq_positive M hp]
    exact (axisIndex M hp j).property
  have hall (j : Fin 3) :
      ¬ BoundaryKilled M (axisIndex M hp j).val (axisRole M hp j).pureComponent := by
    intro hk; exact hn ⟨_, hpos j, axisRole M hp j, hk⟩
  let q := L5A2R49First.firstReturnMultiplier M.base
  have hpair (j : Fin 3) : ∃ u : FactorizationFiber M.base (q * M.base.q.val),
      u.val j = 0 ∧ (∀ i, i ≠ j → 0 < u.val i) ∧
        q * M.base.q.val < (axisIndex M hp j).val := by
    let R := axisRole M hp j
    have hK : BoundaryKilled M (axisIndex M hp j).val R.mixedComponent := by
      rcases r0_role_killed_dichotomy M hp hR0 (hpos j) R with hpure | hmixed
      · exact False.elim (hall j hpure.1)
      · exact hmixed.2
    obtain ⟨u, hu, hle, hz, hb, hs⟩ := mixed_minimal_boundary M hp ℚ R hK
    obtain ⟨hl, hr⟩ := all_pure_live_minimal_pair M hp hall ℚ R u hu hz hb
    obtain ⟨ell, hell, he⟩ := live_pure_pair_return_zero M hR0 ℚ R (hall j) u hu hle hl hr
    have heq := live_pure_pair_return_first M ℚ R (hall j) u hu hl hr hs ell hell he
    have hw : weight M.base u = q * M.base.q.val := by simpa only [heq, q] using he
    refine ⟨⟨u, hw⟩, ?_, ?_, ?_⟩
    · simpa only [R, axisRole_pureRole] using hz
    · intro i hi
      have hi' : i ≠ R.pureRole := by simpa only [R, axisRole_pureRole] using hi
      rcases (role_other_axes R i).mp hi' with rfl | rfl
      · exact hl
      · exact hr
    · rwa [hw] at hs
  obtain ⟨u, hu, hupos, _⟩ := hpair 0
  obtain ⟨v, _, hvpos, _⟩ := hpair 1
  have hne : u ≠ v := by
    intro he
    have hv := hvpos 0 (by decide)
    have hv' := congrArg (fun w : FactorizationFiber M.base (q * M.base.q.val) => w.val 0) he
    omega
  obtain ⟨d, hd, hle⟩ := nonunique_has_active_below M _ u v hne
  obtain ⟨j, hj⟩ := axisIndex_exhausts_active M hp d hd
  obtain ⟨_, _, _, hs⟩ := hpair j
  omega

end NS25Lean.P3R55
