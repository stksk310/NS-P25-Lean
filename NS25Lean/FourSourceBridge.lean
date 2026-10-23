import NS25Lean.FourMonomialPivot
import NS25Lean.FourStarPresentation

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L2C
open ChosenBase FourGeneratedBridge
variable {Gamma : NumericalSemigroup}

theorem tailLift_pivot_zero (B : Data Gamma) (u : Fin 3 →₀ ℕ) :
    tailLift B u B.pivot = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, hj⟩
  have h0 : B.order 0 = B.pivot := by simp [Data.order]
  exact Fin.succ_ne_zero j (B.order.injective (hj.trans h0.symm))

theorem weight_mem_H_of_pivot_zero (B : Data Gamma) (u : Fin 4 →₀ ℕ)
    (hu : u B.pivot = 0) : weight B u ∈ B.H := by
  rw [weight_eq_sum]
  apply AddSubmonoid.sum_mem
  intro j _
  by_cases hj : j = B.pivot
  · subst j; simp only [hu, zero_mul]; exact B.H.zero_mem
  · have hm : weights B j ∈ B.H := by
      apply AddSubmonoid.subset_closure
      rw [B.tail_range]
      exact ⟨j, hj, rfl⟩
    exact B.H.nsmul_mem hm (u j)

theorem exists_full_tail (B : Data Gamma) (d : ℕ) (hd : d ∈ B.H) :
    ∃ u : FactorizationFiber B d, u.val B.pivot = 0 := by
  obtain ⟨u, hu⟩ := Presentation.factorizationMap_surjective B.tailDegrees B.tailDegrees_generate ⟨d, hd⟩
  refine ⟨⟨tailLift B u, ?_⟩, tailLift_pivot_zero B u⟩
  rw [weight_tailLift, L2B.weight_eq_degree]
  exact congrArg Subtype.val hu

theorem exists_pivot_factorization (B : Data Gamma) (d : ℕ)
    (hq : B.q.val ≤ d) (hd : d - B.q.val ∈ Gamma) :
    ∃ u : FactorizationFiber B d, 0 < u.val B.pivot := by
  obtain ⟨u, hu⟩ := Presentation.factorizationMap_surjective B.family
    (ToricPresentation.subtype_degrees_generate _ _ B.generates.symm) ⟨d - B.q.val, hd⟩
  have hw : weight B u = d - B.q.val := (weight_eq_degree B u).trans (congrArg Subtype.val hu)
  refine ⟨⟨u + Finsupp.single B.pivot 1, ?_⟩, ?_⟩
  · rw [map_add, weight_single, one_mul, hw]
    change d - B.q.val + B.q.val = d
    omega
  · simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega

theorem pivot_factorization_boundary (B : Data Gamma) (d : ℕ)
    (u : FactorizationFiber B d) (hu : 0 < u.val B.pivot) :
    B.q.val ≤ d ∧ d - B.q.val ∈ Gamma := by
  have he := remove_copies B u.val B.pivot 1 hu
  rw [one_mul, u.property] at he
  change weight B (u.val - Finsupp.single B.pivot 1) + B.q.val = d at he
  refine ⟨by omega, ?_⟩
  have he' : d - B.q.val = weight B (u.val - Finsupp.single B.pivot 1) := by omega
  rw [he']; exact weight_mem B _

theorem mem_K_iff_two_kinds (B : Data Gamma) (d : ℕ) :
    d ∈ B.K ↔ (∃ u : FactorizationFiber B d, 0 < u.val B.pivot) ∧
      (∃ v : FactorizationFiber B d, v.val B.pivot = 0) := by
  constructor
  · intro hd
    exact ⟨exists_pivot_factorization B d hd.2.1 hd.2.2, exists_full_tail B d hd.1⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨?_, pivot_factorization_boundary B d u hu⟩
    rw [← v.property]; exact weight_mem_H_of_pivot_zero B v.val hv

theorem source_no_cross_edge (B : Data Gamma) (d : ℕ)
    (hd : IsMinimalTailGenerator B.H B.K d) (u v : FactorizationFiber B d)
    (hu : 0 < u.val B.pivot) (hv : v.val B.pivot = 0) :
    ¬ (fiberGraph B d).Adj u v := by
  rintro ⟨_, j, huj, hvj⟩
  have hj : j ≠ B.pivot := by intro h; subst j; omega
  have he₁ := remove_copies B u.val j 1 huj
  have he₂ := remove_copies B v.val j 1 hvj
  rw [one_mul, u.property] at he₁
  rw [one_mul, v.property] at he₂
  have hm : weights B j ∈ B.H := by
    apply AddSubmonoid.subset_closure
    rw [B.tail_range]; exact ⟨j, hj, rfl⟩
  have hk : d - weights B j ∈ B.K := by
    apply (mem_K_iff_two_kinds B _).mpr
    constructor
    · refine ⟨⟨u.val - Finsupp.single j 1, by omega⟩, ?_⟩
      simpa [Finsupp.tsub_apply, Ne.symm hj] using hu
    · refine ⟨⟨v.val - Finsupp.single j 1, by omega⟩, ?_⟩
      simp [Finsupp.tsub_apply, Ne.symm hj, hv]
  rcases hd.2 (weights B j) hm (Nat.ne_of_gt (weights_positive B j)) with hlt | hn
  · omega
  · exact hn hk

theorem source_pivot_preserved (B : Data Gamma) (d : ℕ)
    (hd : IsMinimalTailGenerator B.H B.K d) (u v : FactorizationFiber B d)
    (hu : 0 < u.val B.pivot)
    (hc : (fiberGraph B d).connectedComponentMk u = (fiberGraph B d).connectedComponentMk v) :
    0 < v.val B.pivot := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hc
  clear hc
  induction p with
  | nil => exact hu
  | @cons u w v ha p ih =>
    apply ih
    by_contra hn
    exact source_no_cross_edge B d hd u w hu (by omega) ha

theorem source_implies_betti_essential (B : Data Gamma) (d : ℕ)
    (hd : IsMinimalTailGenerator B.H B.K d) :
    Betti B d ∧ B.pivot ∈ essentialVariables B d := by
  obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := (mem_K_iff_two_kinds B d).mp hd.1
  have hne : (fiberGraph B d).connectedComponentMk u ≠
      (fiberGraph B d).connectedComponentMk v := by
    intro h
    have := source_pivot_preserved B d hd u v hu h
    omega
  refine ⟨(betti_iff_nontrivial B d).mpr ⟨⟨_, _, hne⟩⟩, ?_⟩
  apply (mem_essentialVariables B d B.pivot).mpr
  refine ⟨(fiberGraph B d).connectedComponentMk u, ?_⟩
  apply (mem_componentEssential B d _ B.pivot).mpr
  intro w hw
  exact source_pivot_preserved B d hd u w hu hw.symm

theorem essential_separates (B : Data Gamma) (d : ℕ)
    (hi : B.pivot ∈ essentialVariables B d) (u v : FactorizationFiber B d)
    (hu : 0 < u.val B.pivot) (hv : v.val B.pivot = 0) :
    (fiberGraph B d).connectedComponentMk u ≠ (fiberGraph B d).connectedComponentMk v := by
  obtain ⟨C, hC⟩ := (mem_essentialVariables B d B.pivot).mp hi
  obtain ⟨w, hw⟩ := C.exists_rep
  have hwp := (mem_componentEssential B d C B.pivot).mp hC w hw
  have huC := (same_component_of_shared B d u w B.pivot hu hwp).trans hw
  intro he
  have hvC := he.symm.trans huC
  have := (mem_componentEssential B d C B.pivot).mp hC v hvC
  omega

theorem betti_essential_implies_source (B : Data Gamma) (d : ℕ)
    (hd : Betti B d) (hi : B.pivot ∈ essentialVariables B d) :
    IsMinimalTailGenerator B.H B.K d := by
  obtain ⟨C, hC⟩ := (mem_essentialVariables B d B.pivot).mp hi
  obtain ⟨u, hu⟩ := C.exists_rep
  have hup := (mem_componentEssential B d C B.pivot).mp hC u hu
  haveI := (betti_iff_nontrivial B d).mp hd
  obtain ⟨E, hE⟩ := exists_ne C
  obtain ⟨v, hv⟩ := E.exists_rep
  have hvp : v.val B.pivot = 0 := by
    by_contra hn
    have he := same_component_of_shared B d v u B.pivot (Nat.pos_of_ne_zero hn) hup
    exact hE (hv.symm.trans (he.trans hu))
  refine ⟨(mem_K_iff_two_kinds B d).mpr ⟨⟨u, hup⟩, ⟨v, hvp⟩⟩, ?_⟩
  intro h hh hh0
  by_cases hlt : d < h
  · exact Or.inl hlt
  · right
    intro hk
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (mem_K_iff_two_kinds B (d - h)).mp hk
    obtain ⟨w, hw⟩ := exists_full_tail B h hh
    obtain ⟨j, hj⟩ := positive_coordinate B w.val (by rw [w.property]; omega)
    let a' : FactorizationFiber B d := ⟨a.val + w.val, by rw [map_add, a.property, w.property]; omega⟩
    let b' : FactorizationFiber B d := ⟨b.val + w.val, by rw [map_add, b.property, w.property]; omega⟩
    have ha' : 0 < a'.val B.pivot := by dsimp [a']; omega
    have hb' : b'.val B.pivot = 0 := by dsimp [b']; omega
    apply essential_separates B d hi a' b' ha' hb'
    exact same_component_of_shared B d a' b' j (by dsimp [a']; omega) (by dsimp [b']; omega)

theorem source_iff_betti_essential (B : Data Gamma) (d : ℕ) :
    IsMinimalTailGenerator B.H B.K d ↔ Betti B d ∧ B.pivot ∈ essentialVariables B d :=
  ⟨source_implies_betti_essential B d, fun h => betti_essential_implies_source B d h.1 h.2⟩

theorem sourceCount_eq_essential_card (B : Data Gamma) :
    L2B.sourceCount B = ((bettiDegrees B).filter
      (fun d => B.pivot ∈ essentialVariables B d)).card := by
  classical
  rw [L2B.sourceCount, tailGeneratorCount]
  calc
    _ = Nat.card {d // d ∈ (bettiDegrees B).filter
        (fun d => B.pivot ∈ essentialVariables B d)} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun d => by
        simp only [Finset.mem_filter, mem_bettiDegrees]
        exact source_iff_betti_essential B d)
    _ = _ := Nat.subtype_card _ (fun _ => Iff.rfl)

theorem chosenDefect_eq_essential_sum (B : Data Gamma) :
    L2B.chosenDefect B = ∑ d ∈ bettiDegrees B,
      (componentCount B d - 1 - if B.pivot ∈ essentialVariables B d then 1 else 0) := by
  classical
  rw [L2B.chosenDefect, rho_eq_betti_sum, sourceCount_eq_essential_card]
  rw [Finset.card_filter, ← Finset.sum_tsub_distrib]
  intro d hd
  have hb : 2 ≤ componentCount B d := (mem_bettiDegrees B d).mp hd
  split_ifs <;> omega

end NS25Lean.L2C
