import NS25Lean.P3RoleTransportR57
import NS25Lean.P3FirstPureReturnR56
import NS25Lean.P3PrincipalRoutingR54

set_option linter.style.header false
set_option linter.style.haveILetI false
noncomputable section
namespace NS25Lean.P3R57
open ChosenBase L2B L5A1 L5A2C4H L5A2C4I L5A2B4AR4R1 CombinatorialCore
variable {Gamma : NumericalSemigroup}

/-- A live internal fiber makes every represented predecessor genuinely Apéry. -/
theorem internal_predecessor_apery (M : MultiplicityBase Gamma) {h : ℕ}
    (hin : h ∈ P3R51.internalDegrees M) (u : FactorizationFiber M.base h)
    (i : Fin 3) (hi : 0 < u.val i) : h - weights M.base i ∈ M.base.apery := by
  classical
  have hz : killedCount M h = 0 := (Finset.mem_filter.mp hin).2
  have hlive := L5A1.no_boundaryKilled_of_killedCount_zero M h hz
    ((fiberGraph M.base h).connectedComponentMk u)
  rw [M.base.apery_eq_compl]
  refine ⟨?_, ?_⟩
  · have he := L3B.removed_weight M.base h u i hi
    have hm := L3C.weight_mem_H M.base (u.val - Finsupp.single i 1)
    convert hm using 1 <;> omega
  · intro hk
    exact hlive ⟨u, rfl, i, hi, hk⟩

theorem one_killed_role_dichotomy (M : MultiplicityBase Gamma) {h : ℕ}
    (R : PureMixedCriticalRole M.base h) (hk1 : killedCount M h = 1) :
    (BoundaryKilled M h R.pureComponent ∧ ¬ BoundaryKilled M h R.mixedComponent) ∨
      (¬ BoundaryKilled M h R.pureComponent ∧ BoundaryKilled M h R.mixedComponent) := by
  classical
  obtain ⟨hsub, ⟨C⟩⟩ := Nat.card_eq_one_iff_unique.mp hk1
  have hn : ¬ (BoundaryKilled M h R.pureComponent ∧ BoundaryKilled M h R.mixedComponent) := by
    rintro ⟨hP, hQ⟩
    exact R.components_ne (congrArg Subtype.val (hsub.elim ⟨_, hP⟩ ⟨_, hQ⟩))
  rcases P3R55.role_components_exhaust R C.val with hC | hC
  · have hP : BoundaryKilled M h R.pureComponent := hC ▸ C.property
    exact Or.inl ⟨hP, fun hQ => hn ⟨hP, hQ⟩⟩
  · have hQ : BoundaryKilled M h R.mixedComponent := hC ▸ C.property
    exact Or.inr ⟨fun hP => hn ⟨hP, hQ⟩, hQ⟩

/-- The unique boundary axis is physical; all three predecessors at either other axis are Apéry. -/
theorem r2_unique_boundary_axis (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR2 : (P3R51.internalDegrees M).card = 2) :
    ∃ j : Fin 3,
      killedCount M (P3R55.axisIndex M hp j).val = 1 ∧
      ∀ i : Fin 3, i ≠ j →
        (P3R55.axisIndex M hp i).val ∈ P3R51.internalDegrees M ∧
        ∀ k : Fin 3, (P3R55.axisIndex M hp i).val - weights M.base k ∈ M.base.apery := by
  classical
  obtain ⟨h, hh, huniq⟩ := r2_boundary_unique M hp hR2
  have hpos : h ∈ positiveDegrees M := (Finset.mem_filter.mp hh).1
  have hact : h ∈ activeDegreeFinset M := by rwa [P3R51.active_eq_positive M hp]
  obtain ⟨j, hj⟩ := P3R55.axisIndex_exhausts_active M hp h hact
  refine ⟨j, ?_, ?_⟩
  · rw [hj]; exact ((P3R51.mem_boundaryDegrees_iff M hp h).mp hh).2
  · intro i hij
    have hiAct := (P3R55.axisIndex M hp i).property
    have hiPos : (P3R55.axisIndex M hp i).val ∈ positiveDegrees M := by
      rwa [← P3R51.active_eq_positive M hp]
    have hz : killedCount M (P3R55.axisIndex M hp i).val = 0 := by
      by_contra hn
      have hb : (P3R55.axisIndex M hp i).val ∈ P3R51.boundaryDegrees M :=
        Finset.mem_filter.mpr ⟨hiPos, hn⟩
      have he : (P3R55.axisIndex M hp i).val = (P3R55.axisIndex M hp j).val :=
        (huniq _ hb).trans hj.symm
      exact hij (P3R55.axisIndex_injective M hp he)
    have hin : (P3R55.axisIndex M hp i).val ∈ P3R51.internalDegrees M :=
      Finset.mem_filter.mpr ⟨hiPos, hz⟩
    refine ⟨hin, ?_⟩
    intro k
    let R := P3R55.axisRole M hp i
    by_cases hki : k = i
    · obtain ⟨u, hu, he⟩ := P3R55.role_pure_representative R
      apply internal_predecessor_apery M hin u k
      simpa [he, R, hki] using (criticalExponent_spec M.base i).1
    · apply internal_predecessor_apery M hin R.witness k
      apply P3R55.role_witness_positive R k
      simpa [R] using hki

/-- A legal actual role can place the unique boundary degree in the third slot. -/
theorem r2_legal_boundary_role (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (hR2 : (P3R51.internalDegrees M).card = 2) :
    ∃ e : Fin 3 ≃ Fin 3,
      killedCount M (criticalExponent M.base (e 2) * weights M.base (e 2)) = 1 ∧
      ∀ i : Fin 3, i ≠ 2 → ∀ k : Fin 3,
        criticalExponent M.base (e i) * weights M.base (e i) - weights M.base k ∈
          M.base.apery := by
  obtain ⟨j, hj, hother⟩ := r2_unique_boundary_axis M hp hR2
  let e : Fin 3 ≃ Fin 3 := Equiv.swap 2 j
  have he : e 2 = j := Equiv.swap_apply_left 2 j
  refine ⟨e, ?_, ?_⟩
  · rw [he, ← P3R55.axisIndex_degree M hp j]; exact hj
  · intro i hi k
    rw [← P3R55.axisIndex_degree M hp (e i)]
    apply (hother (e i) ?_).2 k
    intro heq
    exact hi (e.injective (heq.trans he.symm))

/-- This implication selects an actual role only after its physical directional bound is proved. -/
theorem select_direction_of_dual_bound (M : MultiplicityBase Gamma) (e : Fin 3 ≃ Fin 3)
    (hdual : letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      let D := routingData M.base e
      2 ≤ ResidueData.cExceptionalCount D → ResidueData.bExceptionalCount D ≤ 1) :
    ∃ f : Fin 3 ≃ Fin 3,
      letI : NeZero (routingA M.base f) := ⟨Nat.ne_of_gt (routingA_pos M.base f)⟩
      ResidueData.cExceptionalCount (routingData M.base f) ≤ 1 := by
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  by_cases hc : ResidueData.cExceptionalCount (routingData M.base e) ≤ 1
  · exact ⟨e, hc⟩
  · refine ⟨swapRole e, ?_⟩
    rw [routing_cExceptional_swap M.base e]
    exact hdual (by omega)

/-- Same-M/e downstream type implication, without assuming a fresh merge witness. -/
theorem type_of_selected_exceptional_le_one (M : MultiplicityBase Gamma)
    (hp : chosenDefect M.base = 3) (e : Fin 3 ≃ Fin 3)
    (hc : letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
      ResidueData.cExceptionalCount (routingData M.base e) ≤ 1) :
    Gamma.asRelativeIdeal.idealType ≤ Presentation.rho Gamma - 2 := by
  apply P3R52Bridge.p3_strong_of_fresh_compensation M hp
  refine ⟨e, ?_⟩
  letI : NeZero (routingA M.base e) := ⟨Nat.ne_of_gt (routingA_pos M.base e)⟩
  dsimp only
  omega

end NS25Lean.P3R57
