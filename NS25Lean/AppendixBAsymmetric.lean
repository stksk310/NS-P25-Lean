import NS25Lean.AppendixBAligned
import NS25Lean.AppendixBProtected

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L4A
open ChosenBase L2C
variable {Gamma : NumericalSemigroup} {B : Data Gamma}

/-- Singleton-support components witness actual source essentiality. -/
theorem singleton_support_essential (B : Data Gamma) (d : ℕ) (C : FiberComponent B d)
    (i : Fin 4) (hC : componentSupport B d C = {i}) : i ∈ essentialVariables B d := by
  have hi : i ∈ componentSupport B d C := by simp [hC]
  obtain ⟨u, hu, hui⟩ := (mem_componentSupport B d C i).mp hi
  apply (mem_essentialVariables B d i).mpr
  refine ⟨C, (mem_componentEssential B d C i).mpr ?_⟩
  intro v hv
  have he := singleton_component_unique_rep B d C i hC v u hv hu
  simpa [he] using hui

theorem purePair_variable_essential (B : Data Gamma)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : d ∈ purePairDegrees B)
    (i : Fin 4) (hi : i ∈ fiberVariables B d) : i ∈ essentialVariables B d := by
  obtain ⟨C, hC⟩ := purePair_variable_singleton B hpos d hd i hi
  exact singleton_support_essential B d C i hC

namespace NormalizedPairs

theorem purePair_card_two (N : NormalizedPairs B) : (purePairDegrees B).card = 2 := by
  classical
  simp [N.pair_degrees, N.degrees_ne]

theorem pair0_variables (N : NormalizedPairs B) :
    fiberVariables B (N.u * N.alpha * N.beta) = {N.perm 0, N.perm 1} :=
  (two_pure_power_fiber_is_pair B _ (N.perm 0) (N.perm 1)
    (N.perm.injective.ne (by decide)) N.beta N.alpha (by have := N.beta_ge; omega)
    (by have := N.alpha_ge; omega) N.pair0).2

theorem pair1_variables (N : NormalizedPairs B) :
    fiberVariables B (N.v * N.gamma * N.delta) = {N.perm 2, N.perm 3} :=
  (two_pure_power_fiber_is_pair B _ (N.perm 2) (N.perm 3)
    (N.perm.injective.ne (by decide)) N.delta N.gamma (by have := N.delta_ge; omega)
    (by have := N.gamma_ge; omega) N.pair1).2

theorem a_mem_T (N : NormalizedPairs B) : N.a ∈ N.T := by
  rw [N.reduced_T]
  exact (mem_twoGenerator N.a N.b (N.w * N.a)).mpr ⟨N.w, 0, by ring⟩

theorem b_mem_T (N : NormalizedPairs B) : N.b ∈ N.T := by
  rw [N.reduced_T]
  exact (mem_twoGenerator N.a N.b (N.w * N.b)).mpr ⟨0, N.w, by ring⟩

theorem beta_not_dvd_of_a_lt_b (N : NormalizedPairs B) (hab : N.a < N.b)
    (r : ℕ) (hr : r ∈ minimalPositiveGenerators N.T) : ¬ N.beta ∣ N.v * r := by
  intro hd
  have hbpos : 0 < N.b := reduced_generator_positive _ _ (by have := N.beta_ge; omega)
  apply minimal_generator_not_dvd N.T N.b r N.b_mem_T hbpos (N.zero_sum_lt hab) hr
  exact (gcd_divisibility_bridge N.beta N.v r (by have := N.beta_ge; omega)).mp hd

theorem alpha_not_dvd_of_b_lt_a (N : NormalizedPairs B) (hba : N.b < N.a)
    (r : ℕ) (hr : r ∈ minimalPositiveGenerators N.T) : ¬ N.alpha ∣ N.v * r := by
  intro hd
  have hapos : 0 < N.a := reduced_generator_positive _ _ (by have := N.alpha_ge; omega)
  apply minimal_generator_not_dvd N.T N.a r N.a_mem_T hapos (N.zero_sum_gt hba) hr
  exact (gcd_divisibility_bridge N.alpha N.v r (by have := N.alpha_ge; omega)).mp hd

/-- In the increasing reduced pair, every vertex of the aligned first component
contains the original variable perm 0. -/
theorem aligned_zero_essential (N : NormalizedPairs B) (hab : N.a < N.b)
    (d : ℕ) (hd : N.AlignedBetti d) : N.perm 0 ∈ essentialVariables B d := by
  obtain ⟨r, hr, hdeg⟩ := N.aligned_degree_minimal d hd
  obtain ⟨hb, C, E, hne, hall, hC, hE⟩ := hd
  apply (mem_essentialVariables B d (N.perm 0)).mpr
  refine ⟨C, (mem_componentEssential B d C (N.perm 0)).mpr ?_⟩
  intro f hf
  have hside := N.leftSupported_of_component d C hC f hf
  have hz := (N.rightValue_zero_iff f.val).mpr hside
  have hw := (N.weight_split f.val).symm.trans f.property
  apply Nat.pos_of_ne_zero
  intro hf0
  apply N.beta_not_dvd_of_a_lt_b hab r hr
  refine ⟨f.val (N.perm 1), ?_⟩
  have hp := N.u_pos
  simp only [hz, mul_zero, add_zero, leftValue, hf0, mul_zero, zero_add] at hw
  nlinarith [hdeg, hw]

/-- The reversed inequality selects the original variable perm 1. -/
theorem aligned_one_essential (N : NormalizedPairs B) (hba : N.b < N.a)
    (d : ℕ) (hd : N.AlignedBetti d) : N.perm 1 ∈ essentialVariables B d := by
  obtain ⟨r, hr, hdeg⟩ := N.aligned_degree_minimal d hd
  obtain ⟨hb, C, E, hne, hall, hC, hE⟩ := hd
  apply (mem_essentialVariables B d (N.perm 1)).mpr
  refine ⟨C, (mem_componentEssential B d C (N.perm 1)).mpr ?_⟩
  intro f hf
  have hside := N.leftSupported_of_component d C hC f hf
  have hz := (N.rightValue_zero_iff f.val).mpr hside
  have hw := (N.weight_split f.val).symm.trans f.property
  apply Nat.pos_of_ne_zero
  intro hf1
  apply N.alpha_not_dvd_of_b_lt_a hba r hr
  refine ⟨f.val (N.perm 0), ?_⟩
  have hp := N.u_pos
  simp only [hz, mul_zero, add_zero, leftValue, hf1, mul_zero, add_zero] at hw
  nlinarith [hdeg, hw]

/-- Complementary supports in the actual four-variable universe are unique. -/
theorem pair_support_complement (N : NormalizedPairs B) (S T : Finset (Fin 4))
    (hdis : Disjoint S T) (hun : S ∪ T = Finset.univ) :
    (S = {N.perm 0, N.perm 1} → T = {N.perm 2, N.perm 3}) ∧
    (S = {N.perm 2, N.perm 3} → T = {N.perm 0, N.perm 1}) := by
  classical
  have hm (k : Fin 4) : k ∈ T ↔ k ∉ S := by
    constructor
    · intro hk hs
      exact Finset.disjoint_left.mp hdis hs hk
    · intro hk
      have hu : k ∈ S ∪ T := by rw [hun]; exact Finset.mem_univ k
      exact (Finset.mem_union.mp hu).resolve_left hk
  constructor <;> intro hS <;> ext k <;> rw [hm k, hS]
  · obtain ⟨k, rfl⟩ := N.perm.surjective k
    fin_cases k <;> simp [N.perm.injective.eq_iff]
  · obtain ⟨k, rfl⟩ := N.perm.surjective k
    fin_cases k <;> simp [N.perm.injective.eq_iff]

/-- A non-pure Betti fiber with one pure-pair component support must be aligned. -/
theorem aligned_of_pair_support (N : NormalizedPairs B)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d)
    (hn : d ∉ purePairDegrees B) (C : FiberComponent B d)
    (hC : componentSupport B d C = {N.perm 0, N.perm 1} ∨
      componentSupport B d C = {N.perm 2, N.perm 3}) : N.AlignedBetti d := by
  classical
  have hvars : fiberVariables B d = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using
      two_pair_other_support_four B hpos N.purePair_card_two d hd hn)
  obtain ⟨D, E, hne, hall, hDpos, hEpos, hdis, hun⟩ := equality_two_components B hpos d hd
  rw [hvars] at hun
  have hp := N.pair_support_complement (componentSupport B d D) (componentSupport B d E) hdis hun
  have hp' := N.pair_support_complement (componentSupport B d E) (componentSupport B d D)
    hdis.symm (by simpa [Finset.union_comm] using hun)
  rcases hall C with he | he
  · subst C
    rcases hC with hC | hC
    · exact ⟨hd, D, E, hne, hall, hC, hp.1 hC⟩
    · exact ⟨hd, E, D, hne.symm, fun F => (hall F).symm, hp.2 hC, hC⟩
  · subst C
    rcases hC with hC | hC
    · exact ⟨hd, E, D, hne.symm, fun F => (hall F).symm, hC, hp'.1 hC⟩
    · exact ⟨hd, D, E, hne, hall, hp'.2 hC, hC⟩



/-- Rigidity and the actual two-degree pair list force every non-single-vertex
component of a non-pure Betti fiber into the aligned partition. -/
theorem nonaligned_component_unique (N : NormalizedPairs B)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d)
    (hn : d ∉ purePairDegrees B) (hna : ¬ N.AlignedBetti d)
    (C : FiberComponent B d) (u v : FactorizationFiber B d)
    (hu : (fiberGraph B d).connectedComponentMk u = C)
    (hv : (fiberGraph B d).connectedComponentMk v = C) : u = v := by
  have hlo := Finset.card_pos.mpr (componentSupport_nonempty B d (betti_positive B d hd) C)
  have hhi := componentSupport_card_le_two B hpos d hd C
  have hnot := two_pair_no_other_singleton B hpos N.purePair_card_two d hd hn C
  have htwo : (componentSupport B d C).card = 2 := by omega
  obtain ⟨i, j, hij, hC⟩ := Finset.card_eq_two.mp htwo
  by_contra hne
  obtain ⟨hpure, hvars, _⟩ := two_variable_component_rigidity B d C i j hij hC u v hu hv hne
  have hs : componentSupport B d C =
      fiberVariables B (Nat.lcm (weights B i) (weights B j)) := hC.trans hvars.symm
  apply hna
  apply N.aligned_of_pair_support hpos d hd hn C
  have hp : Nat.lcm (weights B i) (weights B j) = N.u * N.alpha * N.beta ∨
      Nat.lcm (weights B i) (weights B j) = N.v * N.gamma * N.delta := by
    simpa only [N.pair_degrees, Finset.mem_insert, Finset.mem_singleton] using hpure
  rcases hp with hp | hp
  · left; rw [hs, hp, N.pair0_variables]
  · right; rw [hs, hp, N.pair1_variables]

/-- Every variable present in a nonaligned non-pure Betti fiber is source-essential. -/
theorem nonaligned_variable_essential (N : NormalizedPairs B)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (d : ℕ) (hd : Betti B d)
    (hn : d ∉ purePairDegrees B) (hna : ¬ N.AlignedBetti d)
    (i : Fin 4) (hi : i ∈ fiberVariables B d) : i ∈ essentialVariables B d := by
  obtain ⟨u, hui⟩ := (mem_variables B d i).mp hi
  let C := (fiberGraph B d).connectedComponentMk u
  apply (mem_essentialVariables B d i).mpr
  refine ⟨C, (mem_componentEssential B d C i).mpr ?_⟩
  intro v hv
  have he := N.nonaligned_component_unique hpos d hd hn hna C v u hv rfl
  simpa [he] using hui

theorem first_pair_absent_second (N : NormalizedPairs B) :
    N.perm 0 ∉ fiberVariables B (N.v * N.gamma * N.delta) ∧
    N.perm 1 ∉ fiberVariables B (N.v * N.gamma * N.delta) := by
  simp [N.pair1_variables, N.perm.injective.eq_iff]

theorem first_pair_essential_first (N : NormalizedPairs B)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) :
    N.perm 0 ∈ essentialVariables B (N.u * N.alpha * N.beta) ∧
    N.perm 1 ∈ essentialVariables B (N.u * N.alpha * N.beta) := by
  have hm : N.u * N.alpha * N.beta ∈ purePairDegrees B := by simp [N.pair_degrees]
  exact ⟨purePair_variable_essential B hpos _ hm _ (by simp [N.pair0_variables]),
    purePair_variable_essential B hpos _ hm _ (by simp [N.pair0_variables])⟩

/-- The a<b choice is essential in every Betti fiber where it occurs. -/
theorem asymmetric_zero_essential (N : NormalizedPairs B)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (hab : N.a < N.b)
    (d : ℕ) (hd : Betti B d) (hi : N.perm 0 ∈ fiberVariables B d) :
    N.perm 0 ∈ essentialVariables B d := by
  classical
  by_cases hp : d ∈ purePairDegrees B
  · exact purePair_variable_essential B hpos d hp _ hi
  · by_cases ha : N.AlignedBetti d
    · exact N.aligned_zero_essential hab d ha
    · exact N.nonaligned_variable_essential hpos d hd hp ha _ hi

/-- The b<a choice is essential in every Betti fiber where it occurs. -/
theorem asymmetric_one_essential (N : NormalizedPairs B)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (hba : N.b < N.a)
    (d : ℕ) (hd : Betti B d) (hi : N.perm 1 ∈ fiberVariables B d) :
    N.perm 1 ∈ essentialVariables B d := by
  classical
  by_cases hp : d ∈ purePairDegrees B
  · exact purePair_variable_essential B hpos d hp _ hi
  · by_cases ha : N.AlignedBetti d
    · exact N.aligned_one_essential hba d ha
    · exact N.nonaligned_variable_essential hpos d hd hp ha _ hi

/-- Source Proposition protected-base, a<b branch, at the actual original variable. -/
theorem asymmetric_zero_protected (N : NormalizedPairs B)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (hab : N.a < N.b) :
    L2B.chosenDefect (atPivot B (N.perm 0)) = 1 :=
  chosenDefect_eq_one_of_essential B hpos (N.perm 0) (N.asymmetric_zero_essential hpos hab)

/-- Source Proposition protected-base, b<a branch, at the actual original variable. -/
theorem asymmetric_one_protected (N : NormalizedPairs B)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (hba : N.b < N.a) :
    L2B.chosenDefect (atPivot B (N.perm 1)) = 1 :=
  chosenDefect_eq_one_of_essential B hpos (N.perm 1) (N.asymmetric_one_essential hpos hba)

theorem asymmetric_protected (N : NormalizedPairs B)
    (hpos : ∀ i : Fin 4, 0 < internalLoad B i) (hne : N.a ≠ N.b) :
    ∃ i : Fin 4, L2B.chosenDefect (atPivot B i) = 1 := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨N.perm 0, N.asymmetric_zero_protected hpos h⟩
  · exact ⟨N.perm 1, N.asymmetric_one_protected hpos h⟩

end NormalizedPairs
end NS25Lean.L4A
