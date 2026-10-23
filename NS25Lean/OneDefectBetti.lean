import NS25Lean.OneDefectNormalization

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3B
open ChosenBase L2B L2B2A L2B2A2 MvPolynomial
variable {Gamma : NumericalSemigroup}

theorem exists_tail_index (B : Data Gamma) (i : Fin 4) (hi : i ≠ B.pivot) :
    ∃ j : Fin 3, B.order j.succ = i := by
  have hn : B.order.symm i ≠ 0 := by
    intro he
    have hh := congrArg B.order he
    simp only [Equiv.apply_symm_apply, Data.order, Equiv.swap_apply_left] at hh
    exact hi hh
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hn
  exact ⟨j, by rw [hj, Equiv.apply_symm_apply]⟩

theorem tailLift_at_tail (B : Data Gamma) (u : Fin 3 →₀ ℕ) (j : Fin 3) :
    L2C.tailLift B u (B.order j.succ) = u j :=
  Finsupp.mapDomain_apply (B.order.injective.comp (Fin.succ_injective 3)) u j

def aperyFiberEquiv (B : Data Gamma) (d : ℕ) (ha : d ∈ B.apery) :
    FactorizationFiber B d ≃ L2C.FactorizationFiber B d := by
  let f : FactorizationFiber B d → L2C.FactorizationFiber B d :=
    fun u => ⟨L2C.tailLift B u.val, (L2C.weight_tailLift B u.val).trans u.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v he
    exact Subtype.ext (L2C.tailLift_injective B (congrArg Subtype.val he))
  · intro v
    have hv : v.val ∈ Set.range (Finsupp.mapDomain (fun j : Fin 3 => B.order j.succ)) := by
      apply (Finsupp.mem_range_mapDomain_iff _
        (B.order.injective.comp (Fin.succ_injective 3)) _).mpr
      intro i hi
      have he : i = B.pivot := by
        by_contra hn
        exact hi (exists_tail_index B i hn)
      rw [he]
      exact L2C.apery_pivot_coordinate_zero B d ha v
    obtain ⟨u, hu⟩ := hv
    have hu' : L2C.tailLift B u = v.val := hu
    refine ⟨⟨u, ?_⟩, Subtype.ext hu'⟩
    rw [← L2C.weight_tailLift, hu']
    exact v.property

theorem aperyFiberEquiv_val (B : Data Gamma) (d : ℕ) (ha : d ∈ B.apery)
    (u : FactorizationFiber B d) : (aperyFiberEquiv B d ha u).val = L2C.tailLift B u.val := rfl

/-- In Apéry, the full four-generator graph really is the tail graph. -/
def aperyGraphEquiv (B : Data Gamma) (d : ℕ) (ha : d ∈ B.apery) :
    fiberGraph B d ≃g L2C.fiberGraph B d where
  toEquiv := aperyFiberEquiv B d ha
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨hne, i, hu, hv⟩
      have hip : i ≠ B.pivot := by
        intro he
        subst i
        rw [aperyFiberEquiv_val, L2C.tailLift_pivot_zero] at hu
        omega
      obtain ⟨j, rfl⟩ := exists_tail_index B i hip
      refine ⟨fun he => hne (congrArg (aperyFiberEquiv B d ha) he), j, ?_, ?_⟩
      · simpa only [aperyFiberEquiv_val, tailLift_at_tail] using hu
      · simpa only [aperyFiberEquiv_val, tailLift_at_tail] using hv
    · rintro ⟨hne, j, hu, hv⟩
      refine ⟨fun he => hne ((aperyFiberEquiv B d ha).injective he), B.order j.succ, ?_, ?_⟩
      · simpa only [aperyFiberEquiv_val, tailLift_at_tail] using hu
      · simpa only [aperyFiberEquiv_val, tailLift_at_tail] using hv

theorem apery_betti_iff (B : Data Gamma) (d : ℕ) :
    AperyBetti B d ↔ d ∈ B.apery ∧ L2C.Betti B d := by
  by_cases ha : d ∈ B.apery
  · have he : componentCount B d = L2C.componentCount B d :=
      Nat.card_congr (aperyGraphEquiv B d ha).connectedComponentEquiv
    change (d ∈ B.apery ∧ 1 < componentCount B d) ↔
      (d ∈ B.apery ∧ 2 ≤ L2C.componentCount B d)
    simp only [ha, true_and, he]
    omega
  · simp [AperyBetti, ha]

theorem unique_full_apery_betti (M : MultiplicityBase Gamma) (h : ℕ)
    (hz : ∀ d, d ≠ h → fiberContribution M d = 0) (ht : InternalTieAt M h) :
    ∀ d, (d ∈ M.base.apery ∧ L2C.Betti M.base d) ↔ d = h := by
  intro d
  rw [← apery_betti_iff]
  exact unique_apery_betti M h hz ht d

theorem survivor_card (M : MultiplicityBase Gamma) (h : ℕ) :
    Nat.card {C : FiberComponent M.base h // ¬ BoundaryKilled M h C} =
      componentCount M.base h - killedCount M h := by
  classical
  letI := Fintype.ofFinite (FiberComponent M.base h)
  simp only [componentCount, killedCount, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

theorem exactly_one_survivor (M : MultiplicityBase Gamma) (h : ℕ)
    (hs : componentCount M.base h - killedCount M h = 1) :
    ∃! C : FiberComponent M.base h, ¬ BoundaryKilled M h C := by
  obtain ⟨C, hC⟩ := Nat.card_eq_one_iff_exists.mp ((survivor_card M h).trans hs)
  exact ⟨C.val, C.property, fun D hD => congrArg Subtype.val (hC ⟨D, hD⟩)⟩

end NS25Lean.L3B

