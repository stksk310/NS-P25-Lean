import NS25Lean.P3MixedBoundaryR55
import NS25Lean.P2SectorCPureBoundarySourceQuotientR40

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R56
open ChosenBase L2B L5A1 L5A2B4AR4R1
variable {Gamma : NumericalSemigroup}

/-- Every transverse predecessor of an actual live mixed component is Apéry. -/
theorem live_mixed_predecessor_apery (M : MultiplicityBase Gamma) {h : ℕ}
    (R : PureMixedCriticalRole M.base h)
    (hlive : ¬ BoundaryKilled M h R.mixedComponent)
    (i : Fin 3) (hi : i ≠ R.pureRole) : h - weights M.base i ∈ M.base.apery := by
  have hpos := P3R55.role_witness_positive R i hi
  have he := L3B.removed_weight M.base h R.witness i hpos
  rw [M.base.apery_eq_compl]
  refine ⟨?_, ?_⟩
  · have hm := L3C.weight_mem_H M.base (R.witness.val - Finsupp.single i 1)
    convert hm using 1 <;> omega
  · intro hk
    exact hlive ⟨R.witness, R.witness_component, i, hpos, hk⟩

/-- A genuine minimal pure border lies strictly below its killed critical power. -/
theorem minimal_killed_pure (M : MultiplicityBase Gamma) (k : Type*) [Field k]
    {h : ℕ} (R : PureMixedCriticalRole M.base h)
    (hk : BoundaryKilled M h R.pureComponent) :
    ∃ X : ℕ, 0 < X ∧ X < criticalExponent M.base R.pureRole ∧
      Finsupp.single R.pureRole X ∈ L3A.minimalExponents (M.base.J k) := by
  classical
  have hK := (P3R55.role_pure_killed_iff M R).mp hk
  have hpw : weight M.base (Finsupp.single R.pureRole
      (criticalExponent M.base R.pureRole - 1)) = h - weights M.base R.pureRole := by
    rw [weight_single, Nat.sub_mul, Nat.one_mul]
    exact congrArg (fun n => n - weights M.base R.pureRole) R.degree_eq_critical.symm
  have hm := (monomial_mem_chosen_iff_boundary k M.base _).mpr (hpw.symm ▸ hK)
  obtain ⟨u, hle, hmin⟩ := L3A.exists_minimal_le (M.base.J k) _ hm
  have hu : u = Finsupp.single R.pureRole (u R.pureRole) := by
    ext i
    by_cases hi : i = R.pureRole
    · subst i; simp
    · have hb := hle i
      simpa only [Finsupp.single_eq_of_ne hi, Nat.le_zero] using hb
  have hpos : 0 < u R.pureRole := by
    by_contra hn
    have hz : u = 0 := by rw [hu]; simp [show u R.pureRole = 0 by omega]
    have hb := (monomial_mem_chosen_iff_boundary k M.base _).mp hmin.1
    rw [hz, map_zero] at hb
    have := hb.2.1
    have := M.base.q_positive
    omega
  refine ⟨u R.pureRole, hpos, ?_, hu ▸ hmin⟩
  have hb := hle R.pureRole
  simp only [Finsupp.single_eq_same] at hb
  have hc := (criticalExponent_spec M.base R.pureRole).1
  omega

/-- Mixed liveness kills every possible transverse term in a pure border return. -/
theorem pure_border_remainder_zero (M : MultiplicityBase Gamma)
    (k : Type*) [Field k] {h : ℕ} (R : PureMixedCriticalRole M.base h)
    (hlive : ¬ BoundaryKilled M h R.mixedComponent)
    (X : ℕ) (hX : 0 < X) (hXA : X < criticalExponent M.base R.pureRole)
    (hmin : Finsupp.single R.pureRole X ∈ L3A.minimalExponents (M.base.J k))
    (v : Fin 3 →₀ ℕ) (ell : ℕ) (hell : 0 < ell)
    (he : weight M.base (Finsupp.single R.pureRole X) =
      weight M.base v + ell * M.base.q.val) : v = 0 := by
  classical
  ext i
  by_cases hi : i = R.pureRole
  · subst i
    exact L5A2R49.minimal_boundary_support_complement k _ _ v hmin ell (by omega) he _
      (by simpa using hX)
  · by_contra hn
    have hvpos : 0 < v i := Nat.pos_of_ne_zero hn
    let w := Finsupp.single R.pureRole (criticalExponent M.base R.pureRole - X) +
      (v - Finsupp.single i 1)
    have hvr := L3B.removed_weight M.base (weight M.base v) ⟨v, rfl⟩ i hvpos
    change weights M.base i + weight M.base (v - Finsupp.single i 1) = weight M.base v at hvr
    have hww : weight M.base w =
        (criticalExponent M.base R.pureRole - X) * weights M.base R.pureRole +
          weight M.base (v - Finsupp.single i 1) := by simp only [w, map_add, weight_single]
    rw [weight_single] at he
    have hd := R.degree_eq_critical
    have hsplit : criticalExponent M.base R.pureRole * weights M.base R.pureRole =
        (criticalExponent M.base R.pureRole - X) * weights M.base R.pureRole +
          X * weights M.base R.pureRole := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hXA.le]
    have hdecomp : h - weights M.base i = weight M.base w + ell * M.base.q.val := by omega
    have ha := live_mixed_predecessor_apery M R hlive i hi
    rw [M.base.apery_eq_compl] at ha
    exact ha.2 (L5A2R49.boundary_of_positive_shift M.base w _ ell (by omega) hdecomp ha.1)

/-- The R0 gate yields an actual pure minimal border with zero actual remainder. -/
theorem r0_pure_minimal_zero_return (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0)
    (k : Type*) [Field k] :
    ∃ (j : Fin 3) (X ell : ℕ), 0 < X ∧ X < criticalExponent M.base j ∧
      Finsupp.single j X ∈ L3A.minimalExponents (M.base.J k) ∧ 0 < ell ∧
      weight M.base (Finsupp.single j X) = ell * M.base.q.val := by
  obtain ⟨h, hh, R, hk⟩ := P3R55.r0_some_pure_killed M hp hR0
  have hlive : ¬ BoundaryKilled M h R.mixedComponent := by
    rcases P3R55.r0_role_killed_dichotomy M hp hR0 hh R with hP | hQ
    · exact hP.2
    · exact False.elim (hQ.1 hk)
  obtain ⟨X, hX, hXA, hmin⟩ := minimal_killed_pure M k R hk
  obtain ⟨v, ell, hv, hell, he, _, _⟩ :=
    P3R54.r0_minimal_boundary_unique_return M hR0 k _ hmin
  have hz := pure_border_remainder_zero M k R hlive X hX hXA hmin v ell hell he
  refine ⟨R.pureRole, X, ell, hX, hXA, hmin, hell, ?_⟩
  simpa only [hz, map_zero, zero_add] using he

/-- Exhaust both kinds of factorization of the earlier original pivot return. -/
theorem pure_border_return_first (M : MultiplicityBase Gamma)
    (k : Type*) [Field k] {h : ℕ} (R : PureMixedCriticalRole M.base h)
    (hlive : ¬ BoundaryKilled M h R.mixedComponent)
    (X : ℕ) (hX : 0 < X) (hXA : X < criticalExponent M.base R.pureRole)
    (hmin : Finsupp.single R.pureRole X ∈ L3A.minimalExponents (M.base.J k))
    (ell : ℕ) (hell : 0 < ell)
    (he : weight M.base (Finsupp.single R.pureRole X) = ell * M.base.q.val) :
    ell = L5A2R49First.firstReturnMultiplier M.base := by
  classical
  let q := L5A2R49First.firstReturnMultiplier M.base
  have hqm := L5A2R49First.firstReturnMultiplier_mem M.base
  have hqp := L5A2R49First.firstReturnMultiplier_pos M.base
  have hqle : q ≤ ell := L5A2R49First.firstReturnMultiplier_minimal M.base (by omega)
    (he ▸ L3C.weight_mem_H M.base _)
  by_contra hn
  have hlt : q < ell := by omega
  have hdelta : (ell - q) * M.base.q.val + q * M.base.q.val = ell * M.base.q.val := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hqle]
  obtain ⟨v⟩ := fiber_nonempty M.base ⟨q * M.base.q.val, hqm⟩
  by_cases hvj : 0 < v.val R.pureRole
  · have huj : 0 < (Finsupp.single R.pureRole X) R.pureRole := by simpa using hX
    have hwu := L3B.removed_weight M.base _
      (⟨Finsupp.single R.pureRole X, rfl⟩ :
        FactorizationFiber M.base (weight M.base (Finsupp.single R.pureRole X))) R.pureRole huj
    change weights M.base R.pureRole +
      weight M.base (Finsupp.single R.pureRole X - Finsupp.single R.pureRole 1) =
        weight M.base (Finsupp.single R.pureRole X) at hwu
    have hwv := L3B.removed_weight M.base _ v R.pureRole hvj
    change weights M.base R.pureRole + weight M.base (v.val - Finsupp.single R.pureRole 1) =
      q * M.base.q.val at hwv
    have hdiff : weight M.base (Finsupp.single R.pureRole X - Finsupp.single R.pureRole 1) =
        weight M.base (v.val - Finsupp.single R.pureRole 1) + (ell - q) * M.base.q.val := by omega
    have hK := L5A2R49.boundary_of_positive_shift M.base
      (v.val - Finsupp.single R.pureRole 1) _ (ell - q) (by omega) hdiff (L3C.weight_mem_H _ _)
    exact (minimal_predecessor_standard k M.base hmin R.pureRole huj)
      ((monomial_mem_chosen_iff_boundary k M.base _).mpr hK)
  · have hvzero : v.val R.pureRole = 0 := by omega
    obtain ⟨i, hi⟩ : ∃ i : Fin 3, 0 < v.val i := by
      by_contra hnone
      push Not at hnone
      have hz : v.val = 0 := by ext i; exact Nat.eq_zero_of_le_zero (hnone i)
      have hw := v.property
      rw [hz, map_zero] at hw
      have hm := M.base.q_positive
      have hqp' : 0 < q := hqp
      nlinarith
    have hij : i ≠ R.pureRole := by intro heq; subst i; omega
    let w := Finsupp.single R.pureRole (criticalExponent M.base R.pureRole - X) +
      (v.val - Finsupp.single i 1)
    have hvr := L3B.removed_weight M.base _ v i hi
    change weights M.base i + weight M.base (v.val - Finsupp.single i 1) = q * M.base.q.val at hvr
    have hww : weight M.base w =
        (criticalExponent M.base R.pureRole - X) * weights M.base R.pureRole +
          weight M.base (v.val - Finsupp.single i 1) := by simp only [w, map_add, weight_single]
    rw [weight_single] at he
    have hd := R.degree_eq_critical
    have hsplit : criticalExponent M.base R.pureRole * weights M.base R.pureRole =
        (criticalExponent M.base R.pureRole - X) * weights M.base R.pureRole +
          X * weights M.base R.pureRole := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hXA.le]
    have hdecomp : h - weights M.base i = weight M.base w + (ell - q) * M.base.q.val := by omega
    have ha := live_mixed_predecessor_apery M R hlive i hij
    rw [M.base.apery_eq_compl] at ha
    exact ha.2 (L5A2R49.boundary_of_positive_shift M.base w _ (ell - q) (by omega) hdecomp ha.1)

/-- Every factorization of a strictly subcritical pure degree is pure. -/
theorem subcritical_pure_fiber_unique (B : Data Gamma) (j : Fin 3)
    (X : ℕ) (hXA : X < criticalExponent B j)
    (v : FactorizationFiber B (X * weights B j)) : v.val = Finsupp.single j X :=
  L5A2C4OR40.factorization_below_critical_is_pure B j hXA v.val v.property

/-- The full original first return, including the actual minimal border and all
    factorizations, for any killed pure critical component under R0. -/
theorem killed_pure_first_return (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0)
    (k : Type*) [Field k] {h : ℕ} (hh : h ∈ positiveDegrees M)
    (R : PureMixedCriticalRole M.base h) (hk : BoundaryKilled M h R.pureComponent) :
    ∃ X : ℕ, 0 < X ∧ X < criticalExponent M.base R.pureRole ∧
      Finsupp.single R.pureRole X ∈ L3A.minimalExponents (M.base.J k) ∧
      X * weights M.base R.pureRole =
        L5A2R49First.firstReturnMultiplier M.base * M.base.q.val ∧
      ∀ v : FactorizationFiber M.base (X * weights M.base R.pureRole),
        v.val = Finsupp.single R.pureRole X := by
  have hlive : ¬ BoundaryKilled M h R.mixedComponent := by
    rcases P3R55.r0_role_killed_dichotomy M hp hR0 hh R with hP | hQ
    · exact hP.2
    · exact False.elim (hQ.1 hk)
  obtain ⟨X, hX, hXA, hmin⟩ := minimal_killed_pure M k R hk
  obtain ⟨v, ell, hv, hell, he, _, _⟩ :=
    P3R54.r0_minimal_boundary_unique_return M hR0 k _ hmin
  have hz := pure_border_remainder_zero M k R hlive X hX hXA hmin v ell hell he
  have he' : weight M.base (Finsupp.single R.pureRole X) = ell * M.base.q.val := by
    simpa only [hz, map_zero, zero_add] using he
  have hfirst := pure_border_return_first M k R hlive X hX hXA hmin ell hell he'
  refine ⟨X, hX, hXA, hmin, ?_, subcritical_pure_fiber_unique M.base R.pureRole X hXA⟩
  simpa only [weight_single, hfirst] using he'

/-- Exact original R55Open.first_pure_return_target; no principal-index premise. -/
theorem r0_first_pure_return (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0) :
    ∃ (j : Fin 3) (X : ℕ), 0 < X ∧ X < criticalExponent M.base j ∧
      X * weights M.base j = L5A2R49First.firstReturnMultiplier M.base * M.base.q.val ∧
      ∀ v : FactorizationFiber M.base (X * weights M.base j), v.val = Finsupp.single j X := by
  obtain ⟨h, hh, R, hk⟩ := P3R55.r0_some_pure_killed M hp hR0
  obtain ⟨X, hX, hXA, hmin, he, hv⟩ := killed_pure_first_return M hp hR0 ℚ hh R hk
  exact ⟨R.pureRole, X, hX, hXA, he, hv⟩

/-- Any two killed pure critical components have the same pure axis. -/
theorem r0_killed_pure_axis_unique (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0)
    {h g : ℕ} (hh : h ∈ positiveDegrees M) (hg : g ∈ positiveDegrees M)
    (R : PureMixedCriticalRole M.base h) (S : PureMixedCriticalRole M.base g)
    (hR : BoundaryKilled M h R.pureComponent) (hS : BoundaryKilled M g S.pureComponent) :
    R.pureRole = S.pureRole := by
  classical
  obtain ⟨X, hX, hXA, hminX, heX, hunique⟩ := killed_pure_first_return M hp hR0 ℚ hh R hR
  obtain ⟨Y, hY, hYA, hminY, heY, _⟩ := killed_pure_first_return M hp hR0 ℚ hg S hS
  let v : FactorizationFiber M.base (X * weights M.base R.pureRole) :=
    ⟨Finsupp.single S.pureRole Y, (weight_single _ _ _).trans (heY.trans heX.symm)⟩
  have he := congrArg (fun u : Fin 3 →₀ ℕ => u R.pureRole) (hunique v)
  by_contra hn
  have he' : (Finsupp.single S.pureRole Y) R.pureRole = X := by
    simpa only [v, Finsupp.single_eq_same] using he
  rw [Finsupp.single_eq_of_ne hn] at he'
  omega

end NS25Lean.P3R56
