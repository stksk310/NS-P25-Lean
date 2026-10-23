import NS25Lean.P3CriticalFibersR54
import NS25Lean.P3R0AperyStructureR54

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R55
open ChosenBase L2B L5A1 L5A2B4AR4R1
variable {Gamma : NumericalSemigroup}

open Classical in
abbrev CriticalIndex (M : MultiplicityBase Gamma) := ↥(activeDegreeFinset M)

def criticalRole (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (x : CriticalIndex M) : PureMixedCriticalRole M.base x.val :=
  Classical.choice (P3R54.p3_actual_pureMixedCriticalRole M hp x.val x.property)

theorem criticalRole_axis_injective (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) :
    Function.Injective (fun x : CriticalIndex M => (criticalRole M hp x).pureRole) := by
  intro x y he
  apply Subtype.ext
  exact (criticalRole M hp x).degree_eq_critical.trans
    ((congrArg (fun j => criticalExponent M.base j * weights M.base j) he).trans
      (criticalRole M hp y).degree_eq_critical.symm)

/-- Every actual critical degree is assigned to its own distinct pure axis. -/
def criticalAxisEquiv (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3) :
    CriticalIndex M ≃ Fin 3 := by
  classical
  apply Equiv.ofBijective (fun x => (criticalRole M hp x).pureRole)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨criticalRole_axis_injective M hp, ?_⟩
  have hc := (P3R51.p3_active_classification M hp).1
  simpa only [CriticalIndex, Fintype.card_coe, Fintype.card_fin] using hc

def axisIndex (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (j : Fin 3) : CriticalIndex M := (criticalAxisEquiv M hp).symm j

def axisRole (M : MultiplicityBase Gamma) (hp : chosenDefect M.base = 3)
    (j : Fin 3) : PureMixedCriticalRole M.base (axisIndex M hp j).val :=
  criticalRole M hp (axisIndex M hp j)

@[simp] theorem axisRole_pureRole (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (j : Fin 3) : (axisRole M hp j).pureRole = j :=
  (criticalAxisEquiv M hp).apply_symm_apply j

theorem axisIndex_degree (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (j : Fin 3) :
    (axisIndex M hp j).val = criticalExponent M.base j * weights M.base j := by
  simpa using (axisRole M hp j).degree_eq_critical

theorem axisIndex_injective (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) :
    Function.Injective (fun j => (axisIndex M hp j).val) := by
  intro i j he
  exact (criticalAxisEquiv M hp).symm.injective (Subtype.ext he)

theorem axisIndex_exhausts_active (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (h : ℕ) (hh : h ∈ activeDegreeFinset M) :
    ∃ j, (axisIndex M hp j).val = h := by
  refine ⟨criticalAxisEquiv M hp ⟨h, hh⟩, ?_⟩
  exact congrArg Subtype.val ((criticalAxisEquiv M hp).symm_apply_apply ⟨h, hh⟩)

theorem role_other_axes {B : Data Gamma} {h : ℕ} (R : PureMixedCriticalRole B h)
    (j : Fin 3) : j ≠ R.pureRole ↔ j = R.otherLeft ∨ j = R.otherRight := by
  have hmem : j ∈ ({R.pureRole, R.otherLeft, R.otherRight} : Finset (Fin 3)) := by
    rw [R.roles_cover]; exact Finset.mem_univ j
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  constructor
  · intro hn; exact hmem.resolve_left hn
  · rintro (rfl | rfl)
    · exact R.pure_ne_left.symm
    · exact R.pure_ne_right.symm

theorem role_witness_positive {B : Data Gamma} {h : ℕ} (R : PureMixedCriticalRole B h)
    (j : Fin 3) (hj : j ≠ R.pureRole) : 0 < R.witness.val j := by
  rcases (role_other_axes R j).mp hj with rfl | rfl
  · exact R.witness_left_pos
  · exact R.witness_right_pos

/-- The actual pure representative, not an assumed pure-killed package. -/
theorem role_pure_representative {B : Data Gamma} {h : ℕ}
    (R : PureMixedCriticalRole B h) :
    ∃ u : FactorizationFiber B h,
      (fiberGraph B h).connectedComponentMk u = R.pureComponent ∧
      u.val = Finsupp.single R.pureRole (criticalExponent B R.pureRole) := by
  obtain ⟨u, hu⟩ := R.pureComponent.exists_rep
  have he := fiber_eq_single_of_componentSupport B h R.pureComponent R.pureRole
    R.pureSupport u hu
  have hw := u.property
  rw [he, weight_single] at hw
  have hw' := hw.trans R.degree_eq_critical
  have hp := weights_positive B R.pureRole
  have hn : u.val R.pureRole = criticalExponent B R.pureRole := by nlinarith
  exact ⟨u, hu, he.trans (congrArg (Finsupp.single R.pureRole) hn)⟩

theorem role_pure_killed_iff (M : MultiplicityBase Gamma) {h : ℕ}
    (R : PureMixedCriticalRole M.base h) :
    BoundaryKilled M h R.pureComponent ↔ h - weights M.base R.pureRole ∈ M.base.K := by
  constructor
  · rintro ⟨u, hu, j, hj, hk⟩
    have hm := (mem_componentSupport M.base h R.pureComponent j).mpr ⟨u, hu, hj⟩
    rw [R.pureSupport, Finset.mem_singleton] at hm
    simpa only [hm] using hk
  · intro hk
    obtain ⟨u, hu, he⟩ := role_pure_representative R
    refine ⟨u, hu, R.pureRole, ?_, hk⟩
    simpa only [he, Finsupp.single_eq_same] using (criticalExponent_spec M.base R.pureRole).1

theorem role_mixed_killed_iff (M : MultiplicityBase Gamma) {h : ℕ}
    (R : PureMixedCriticalRole M.base h) :
    BoundaryKilled M h R.mixedComponent ↔
      h - weights M.base R.otherLeft ∈ M.base.K ∨
        h - weights M.base R.otherRight ∈ M.base.K := by
  constructor
  · rintro ⟨u, hu, j, hj, hk⟩
    have hm := (mem_componentSupport M.base h R.mixedComponent j).mpr ⟨u, hu, hj⟩
    rw [R.mixedSupport, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact Or.inl hk
    · exact Or.inr hk
  · rintro (hk | hk)
    · exact ⟨R.witness, R.witness_component, R.otherLeft, R.witness_left_pos, hk⟩
    · exact ⟨R.witness, R.witness_component, R.otherRight, R.witness_right_pos, hk⟩

theorem role_components_exhaust {B : Data Gamma} {h : ℕ}
    (R : PureMixedCriticalRole B h) (C : FiberComponent B h) :
    C = R.pureComponent ∨ C = R.mixedComponent := by
  classical
  letI := Fintype.ofFinite (FiberComponent B h)
  have hc : (Finset.univ : Finset (FiberComponent B h)).card = 2 := by
    simpa only [componentCount, Nat.card_eq_fintype_card, Finset.card_univ] using
      R.componentCount_eq_two
  have he : ({R.pureComponent, R.mixedComponent} : Finset _) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp only [hc, Finset.card_pair R.components_ne]
    exact le_refl 2
  have hm : C ∈ ({R.pureComponent, R.mixedComponent} : Finset _) :=
    he.symm ▸ Finset.mem_univ C
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

/-- Exactly one of the two actual components is killed under original R0. -/
theorem r0_role_killed_dichotomy (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR0 : (P3R51.internalDegrees M).card = 0)
    {h : ℕ} (hh : h ∈ positiveDegrees M) (R : PureMixedCriticalRole M.base h) :
    (BoundaryKilled M h R.pureComponent ∧ ¬ BoundaryKilled M h R.mixedComponent) ∨
      (¬ BoundaryKilled M h R.pureComponent ∧ BoundaryKilled M h R.mixedComponent) := by
  classical
  have hk := P3R54.r0_positive_killed M hR0 h hh
  have hs := P3R51.positive_signature M hp h hh
  have hk1 : killedCount M h = 1 := by
    rcases hs with hs | hs
    · exact False.elim (by have hz := hs.2; omega)
    · exact hs.2
  obtain ⟨hsub, ⟨C⟩⟩ := Nat.card_eq_one_iff_unique.mp hk1
  have hnot : ¬ (BoundaryKilled M h R.pureComponent ∧ BoundaryKilled M h R.mixedComponent) := by
    rintro ⟨hP, hQ⟩
    exact R.components_ne (congrArg Subtype.val (hsub.elim ⟨_, hP⟩ ⟨_, hQ⟩))
  rcases role_components_exhaust R C.val with hC | hC
  · have hP : BoundaryKilled M h R.pureComponent := hC ▸ C.property
    exact Or.inl ⟨hP, fun hQ => hnot ⟨hP, hQ⟩⟩
  · have hQ : BoundaryKilled M h R.mixedComponent := hC ▸ C.property
    exact Or.inr ⟨fun hP => hnot ⟨hP, hQ⟩, hQ⟩

/-- Every mixed coordinate is strictly below that coordinate's actual critical exponent. -/
theorem mixed_coordinate_lt_critical (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) {h : ℕ}
    (R : PureMixedCriticalRole M.base h) (i : Fin 3) (hi : i ≠ R.pureRole) :
    R.witness.val i < criticalExponent M.base i := by
  classical
  by_contra hn
  have hle : criticalExponent M.base i ≤ R.witness.val i := by omega
  let S := axisRole M hp i
  have hSi : S.pureRole = i := axisRole_pureRole M hp i
  let k := if i = R.otherLeft then R.otherRight else R.otherLeft
  have hk : k ≠ R.pureRole ∧ k ≠ i := by
    rcases (role_other_axes R i).mp hi with hil | hir
    · simp only [k, hil, ite_true]
      exact ⟨R.pure_ne_right.symm, hil ▸ R.other_ne.symm⟩
    · have hn : i ≠ R.otherLeft := by rw [hir]; exact R.other_ne.symm
      simp only [k, hn, ite_false]
      exact ⟨R.pure_ne_left.symm, hir ▸ R.other_ne⟩
  have hdecomp : Finsupp.single i (criticalExponent M.base i) +
      (R.witness.val - Finsupp.single i (criticalExponent M.base i)) = R.witness.val := by
    ext j
    by_cases hj : j = i
    · subst j; simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]
      omega
    · simp [hj]
  let z : FactorizationFiber M.base h :=
    ⟨(R.witness.val - Finsupp.single i (criticalExponent M.base i)) + S.witness.val, by
      have he := congrArg (weight M.base) hdecomp
      rw [map_add, weight_single, R.witness.property] at he
      rw [map_add, S.witness.property, axisIndex_degree]
      omega⟩
  have hzk : 0 < z.val k := by
    have hv := role_witness_positive R k hk.1
    simp only [z, Finsupp.add_apply, Finsupp.tsub_apply,
      Finsupp.single_eq_of_ne hk.2, Nat.sub_zero]
    omega
  have hzC : (fiberGraph M.base h).connectedComponentMk z = R.mixedComponent := by
    apply components_eq_of_shared_support M.base h _ R.mixedComponent k
    · exact (mem_componentSupport M.base h _ k).mpr ⟨z, rfl, hzk⟩
    · exact (mem_componentSupport M.base h _ k).mpr
        ⟨R.witness, R.witness_component, role_witness_positive R k hk.1⟩
  have hzi : 0 < z.val R.pureRole := by
    have hv := role_witness_positive S R.pureRole (by rw [hSi]; exact hi.symm)
    simp only [z, Finsupp.add_apply]
    omega
  have hmem := (mem_componentSupport M.base h R.mixedComponent R.pureRole).mpr
    ⟨z, hzC, hzi⟩
  rw [R.mixedSupport] at hmem
  simpa only [Finset.mem_insert, Finset.mem_singleton,
    R.pure_ne_left, R.pure_ne_right, or_self] using hmem

end NS25Lean.P3R55
