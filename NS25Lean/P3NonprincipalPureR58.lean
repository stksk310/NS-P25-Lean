import NS25Lean.P3DecoratedZeroR58

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R58
open ChosenBase L2B L5A1 FourGeneratedBridge L5A2B4AR4R1
variable {Gamma : NumericalSemigroup}

/-- Any subcritical pure return opposite a live mixed component has a pure remainder.
Unlike the earlier minimal-border lemma this needs no minimal-generator hypothesis. -/
theorem subcritical_pure_return_remainder (M : MultiplicityBase Gamma) {h : ℕ}
    (R : PureMixedCriticalRole M.base h)
    (hlive : ¬ BoundaryKilled M h R.mixedComponent)
    (X ell : ℕ) (hX : X < criticalExponent M.base R.pureRole)
    (v : Fin 3 →₀ ℕ) (hell : 0 < ell)
    (he : X * weights M.base R.pureRole = weight M.base v + ell * M.base.q.val) :
    ∀ i, i ≠ R.pureRole → v i = 0 := by
  intro i hi
  by_contra hn
  have hvpos : 0 < v i := Nat.pos_of_ne_zero hn
  let w := Finsupp.single R.pureRole (criticalExponent M.base R.pureRole - X) +
    (v - Finsupp.single i 1)
  have hvr := L3B.removed_weight M.base (weight M.base v) ⟨v, rfl⟩ i hvpos
  change weights M.base i + weight M.base (v - Finsupp.single i 1) = weight M.base v at hvr
  have hww : weight M.base w =
      (criticalExponent M.base R.pureRole - X) * weights M.base R.pureRole +
        weight M.base (v - Finsupp.single i 1) := by simp only [w, map_add, weight_single]
  have hsplit : criticalExponent M.base R.pureRole * weights M.base R.pureRole =
      (criticalExponent M.base R.pureRole - X) * weights M.base R.pureRole +
        X * weights M.base R.pureRole := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hX.le]
  have hd := R.degree_eq_critical
  have hdecomp : h - weights M.base i = weight M.base w + ell * M.base.q.val := by omega
  have ha := P3R56.live_mixed_predecessor_apery M R hlive i hi
  rw [M.base.apery_eq_compl] at ha
  exact ha.2 (L5A2R49.boundary_of_positive_shift M.base w _ ell hell hdecomp ha.1)

/-- A return meeting a subcritical pure power with live opposite component is already principal. -/
theorem subcritical_pure_return_principal (M : MultiplicityBase Gamma) {h : ℕ}
    (R : PureMixedCriticalRole M.base h)
    (hlive : ¬ BoundaryKilled M h R.mixedComponent)
    (X ell : ℕ) (hX : X < criticalExponent M.base R.pureRole)
    (v : Fin 3 →₀ ℕ) (hell : 0 < ell)
    (he : X * weights M.base R.pureRole = weight M.base v + ell * M.base.q.val) :
    ell * M.base.q.val ∈ M.base.H := by
  have hv : v = Finsupp.single R.pureRole (v R.pureRole) := by
    ext i
    by_cases hi : i = R.pureRole
    · subst i; simp
    · simp [hi, subcritical_pure_return_remainder M R hlive X ell hX v hell he i hi]
  rw [hv, weight_single] at he
  have hm := M.base.q_positive
  have hw := weights_positive M.base R.pureRole
  have hle : v R.pureRole ≤ X := by nlinarith
  have heq : ell * M.base.q.val = (X - v R.pureRole) * weights M.base R.pureRole := by
    rw [Nat.sub_mul]
    omega
  rw [heq, ← weight_single]
  exact L3C.weight_mem_H M.base _

/-- At defect three a nonprincipal return cannot hit any subcritical pure tail power.
The return multiplier here is the ORIGINAL unnormalized multiplier. -/
theorem p3_nonprincipal_misses_subcritical_pure (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (j : Fin 3) (X ell : ℕ)
    (hX : X < criticalExponent M.base j) (hell : 0 < ell)
    (hnon : ell * M.base.q.val ∉ M.base.H)
    (v : Fin 3 →₀ ℕ) :
    X * weights M.base j ≠ weight M.base v + ell * M.base.q.val := by
  intro he
  let R := P3R55.axisRole M hp j
  have hR : R.pureRole = j := P3R55.axisRole_pureRole M hp j
  have hK : weight M.base (Finsupp.single j X) ∈ M.base.K :=
    L5A2R49.boundary_of_positive_shift M.base v _ ell hell
      (by simpa only [weight_single] using he) (L3C.weight_mem_H M.base _)
  have hP : BoundaryKilled M (P3R55.axisIndex M hp j).val R.pureComponent := by
    by_contra hlive
    have ha := P3R55.live_pure_power_apery M R hlive X (by simpa only [hR] using hX)
    rw [M.base.apery_eq_compl] at ha
    exact ha.2 (by simpa only [hR] using hK)
  have hh : (P3R55.axisIndex M hp j).val ∈ positiveDegrees M := by
    rw [← P3R51.active_eq_positive M hp]
    exact (P3R55.axisIndex M hp j).property
  have hsig := P3R51.positive_signature M hp _ hh
  have hk1 : killedCount M (P3R55.axisIndex M hp j).val = 1 := by
    rcases hsig with hsig | hsig
    · exact False.elim ((no_boundaryKilled_of_killedCount_zero M _ hsig.2 R.pureComponent) hP)
    · exact hsig.2
  have hQ : ¬ BoundaryKilled M (P3R55.axisIndex M hp j).val R.mixedComponent := by
    rcases P3R57.one_killed_role_dichotomy M R hk1 with h | h
    · exact h.2
    · exact False.elim (h.1 hP)
  exact hnon (subcritical_pure_return_principal M R hQ X ell
    (by simpa only [hR] using hX) v hell (by simpa only [hR] using he))

end NS25Lean.P3R58
