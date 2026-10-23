import NS25Lean.P2Sectors
import NS25Lean.OneDefectSplit

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2R49

open ChosenBase L2B L5A1 MvPolynomial
variable {Gamma : NumericalSemigroup}

/-- Every positive-contribution degree is boundary, so actual Apéry fibers have
zero contribution. This lemma uses the actual killed-component predicate. -/
theorem apery_contribution_zero_of_positive_killed (M : MultiplicityBase Gamma)
    (hk : ∀ h, h ∈ positiveDegrees M → 0 < killedCount M h)
    (d : ℕ) (hd : d ∈ M.base.apery) : fiberContribution M d = 0 := by
  by_contra hn
  have hp : d ∈ positiveDegrees M := (mem_positiveDegrees M d).mpr (by omega)
  have hz := L3B.apery_killedCount_zero M d hd
  have := hk d hp
  omega

theorem sectorA_apery_contribution_zero (P : P2Data Gamma) (hA : SectorA P.M)
    (d : ℕ) (hd : d ∈ P.M.base.apery) : fiberContribution P.M d = 0 := by
  rcases hA with ⟨h, hs, hc, hk⟩
  apply apery_contribution_zero_of_positive_killed P.M _ d hd
  intro e he
  have : e = h := by simpa only [hs, Finset.mem_singleton] using he
  subst e
  omega

/-- The MP-1 monomialization repair: both active D degrees are boundary;
there is no remaining positive contribution at an actual Apéry degree. -/
theorem sectorD_apery_contribution_zero (P : P2Data Gamma) (hD : SectorD P.M)
    (d : ℕ) (hd : d ∈ P.M.base.apery) : fiberContribution P.M d = 0 := by
  rcases hD with ⟨h, g, _, hs, ⟨hc, hk⟩, ⟨gc, gk⟩⟩
  apply apery_contribution_zero_of_positive_killed P.M _ d hd
  intro e he
  have : e = h ∨ e = g := by simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using he
  rcases this with heh | heg
  · rw [heh, hk]; omega
  · rw [heg, gk]; omega

theorem apery_unique_of_contribution_zero (M : MultiplicityBase Gamma)
    (hz : ∀ d, d ∈ M.base.apery → fiberContribution M d = 0)
    (d : ℕ) (hd : d ∈ M.base.apery) : Subsingleton (FactorizationFiber M.base d) :=
  L3B.apery_fiber_unique_below M.base (d + 1)
    (fun e _ he => L3B.apery_component_le_one M e (hz e he) he) d (by omega) hd

theorem sectorA_apery_unique (P : P2Data Gamma) (hA : SectorA P.M)
    (d : ℕ) (hd : d ∈ P.M.base.apery) : Subsingleton (FactorizationFiber P.M.base d) :=
  apery_unique_of_contribution_zero P.M (sectorA_apery_contribution_zero P hA) d hd

theorem sectorD_apery_unique (P : P2Data Gamma) (hD : SectorD P.M)
    (d : ℕ) (hd : d ∈ P.M.base.apery) : Subsingleton (FactorizationFiber P.M.base d) :=
  apery_unique_of_contribution_zero P.M (sectorD_apery_contribution_zero P hD) d hd

/-- Arbitrary-field toric monomialization from actual Apéry uniqueness. -/
theorem J_eq_MK_of_apery_unique (B : Data Gamma)
    (hu : ∀ d, d ∈ B.apery → Subsingleton (FactorizationFiber B d))
    (k : Type*) [Field k] : B.J k = B.MK k := by
  rw [B.J_eq_IH_sup_MK k]
  apply sup_eq_right.mpr
  rw [IH_eq_relationIdeal, Presentation.relationIdeal]
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨u, v⟩, huv, rfl⟩
  change weight B u = weight B v at huv
  change monomial u (1 : k) - monomial v 1 ∈ B.MK k
  by_cases hk : weight B u ∈ B.K
  · apply (B.MK k).sub_mem
    · exact Ideal.subset_span ⟨u, by simpa only [Set.mem_setOf_eq, ← weight_eq_degree] using hk, rfl⟩
    · exact Ideal.subset_span ⟨v, by simpa only [Set.mem_setOf_eq, ← weight_eq_degree, ← huv] using hk, rfl⟩
  · have ha : weight B u ∈ B.apery := by
      rw [B.apery_eq_compl]
      exact ⟨(weight_eq_degree B u).symm ▸
        (Presentation.factorizationMap B.tailDegrees u).property, hk⟩
    have he : u = v := congrArg Subtype.val ((hu _ ha).elim ⟨u, rfl⟩ ⟨v, huv.symm⟩)
    simp only [he, sub_self, Ideal.zero_mem]

theorem sectorA_J_eq_MK (P : P2Data Gamma) (hA : SectorA P.M)
    (k : Type*) [Field k] : P.J k = P.M.base.MK k :=
  J_eq_MK_of_apery_unique P.M.base (sectorA_apery_unique P hA) k

theorem sectorD_J_eq_MK (P : P2Data Gamma) (hD : SectorD P.M)
    (k : Type*) [Field k] : P.J k = P.M.base.MK k :=
  J_eq_MK_of_apery_unique P.M.base (sectorD_apery_unique P hD) k

theorem sectorA_monomial (P : P2Data Gamma) (hA : SectorA P.M)
    (k : Type*) [Field k] : IsMonomialIdeal k (P.J k) := by
  rw [sectorA_J_eq_MK P hA k]
  exact ⟨_, rfl⟩

theorem sectorD_monomial (P : P2Data Gamma) (hD : SectorD P.M)
    (k : Type*) [Field k] : IsMonomialIdeal k (P.J k) := by
  rw [sectorD_J_eq_MK P hD k]
  exact ⟨_, rfl⟩

end NS25Lean.L5A2R49
