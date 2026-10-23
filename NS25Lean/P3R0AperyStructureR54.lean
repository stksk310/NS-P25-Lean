import NS25Lean.P3ActiveClassificationR51
import NS25Lean.P2DAMonomializationR49
import NS25Lean.P2SectorYFinalClosure
import NS25Lean.P2DAFirstReturnR49

set_option linter.style.header false
noncomputable section
namespace NS25Lean.P3R54
open ChosenBase L2B L5A1
variable {Gamma : NumericalSemigroup}

/-- Original R0 excludes every zero-killed positive degree. No defect premise is needed. -/
theorem r0_positive_killed (M : MultiplicityBase Gamma)
    (hR0 : (P3R51.internalDegrees M).card = 0)
    (h : ℕ) (hh : h ∈ positiveDegrees M) : 0 < killedCount M h := by
  classical
  have hempty := Finset.card_eq_zero.mp hR0
  by_contra hn
  have hz : killedCount M h = 0 := by omega
  have hin : h ∈ P3R51.internalDegrees M := Finset.mem_filter.mpr ⟨hh, hz⟩
  rw [hempty] at hin
  simp at hin

theorem r0_apery_contribution_zero (M : MultiplicityBase Gamma)
    (hR0 : (P3R51.internalDegrees M).card = 0)
    (d : ℕ) (hd : d ∈ M.base.apery) : fiberContribution M d = 0 :=
  L5A2R49.apery_contribution_zero_of_positive_killed M (r0_positive_killed M hR0) d hd

/-- M02 §2.1, for the actual original Apéry set and actual factorization fibers. -/
theorem r0_apery_fiber_unique (M : MultiplicityBase Gamma)
    (hR0 : (P3R51.internalDegrees M).card = 0)
    (d : ℕ) (hd : d ∈ M.base.apery) : Subsingleton (FactorizationFiber M.base d) :=
  L5A2R49.apery_unique_of_contribution_zero M (r0_apery_contribution_zero M hR0) d hd

theorem r0_J_eq_MK (M : MultiplicityBase Gamma)
    (hR0 : (P3R51.internalDegrees M).card = 0)
    (k : Type*) [Field k] : M.base.J k = M.base.MK k :=
  L5A2R49.J_eq_MK_of_apery_unique M.base (r0_apery_fiber_unique M hR0) k

theorem r0_J_monomial (M : MultiplicityBase Gamma)
    (hR0 : (P3R51.internalDegrees M).card = 0)
    (k : Type*) [Field k] : IsMonomialIdeal k (M.base.J k) := by
  rw [r0_J_eq_MK M hR0 k]
  exact ⟨_, rfl⟩

/-- Distinct actual standard monomials have distinct residues modulo the original pivot. -/
theorem r0_standard_residue_injective (M : MultiplicityBase Gamma)
    (hR0 : (P3R51.internalDegrees M).card = 0)
    (k : Type*) [Field k] {u v : Fin 3 →₀ ℕ}
    (hu : u ∈ L3A.standardExponents (M.base.J k))
    (hv : v ∈ L3A.standardExponents (M.base.J k))
    (he : Nat.ModEq M.base.q.val (weight M.base u) (weight M.base v)) : u = v := by
  have hau := (standard_iff_chosen_apery k M.base u).mp hu
  have hav := (standard_iff_chosen_apery k M.base v).mp hv
  have hw := apery_mod_unique M.base hau hav he
  exact congrArg Subtype.val ((r0_apery_fiber_unique M hR0 _ hau).elim
    ⟨u, rfl⟩ ⟨v, hw.symm⟩)

/-- M02 §2.1–2.2 together: every actual minimal border has one positive return
to one actual standard factorization, with literal complementary support. -/
theorem r0_minimal_boundary_unique_return (M : MultiplicityBase Gamma)
    (hR0 : (P3R51.internalDegrees M).card = 0) (k : Type*) [Field k]
    (u : Fin 3 →₀ ℕ) (hu : u ∈ L3A.minimalExponents (M.base.J k)) :
    ∃ v : Fin 3 →₀ ℕ, ∃ ell : ℕ,
      weight M.base v ∈ M.base.apery ∧ 0 < ell ∧
      weight M.base u = weight M.base v + ell * M.base.q.val ∧
      (∀ j : Fin 3, 0 < u j → v j = 0) ∧
      ∀ (v' : Fin 3 →₀ ℕ) (ell' : ℕ),
        weight M.base v' ∈ M.base.apery →
        weight M.base u = weight M.base v' + ell' * M.base.q.val →
          v' = v ∧ ell' = ell := by
  obtain ⟨v, ell, hv, hell, he⟩ := L5A2R49.minimal_boundary_decomposition k M.base u hu
  refine ⟨v, ell, hv, hell, he, ?_, ?_⟩
  · exact L5A2R49.minimal_boundary_support_complement k M.base u v hu ell hell he
  · intro v' ell' hv' he'
    have hmod := congrArg (fun n : ℕ => n % M.base.q.val) (he.symm.trans he')
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero,
      Nat.zero_mod, add_zero, Nat.mod_mod] at hmod
    have hw := apery_mod_unique M.base hv hv' hmod
    have heq : v' = v := congrArg Subtype.val
      ((r0_apery_fiber_unique M hR0 _ hv).elim ⟨v', hw.symm⟩ ⟨v, rfl⟩)
    refine ⟨heq, ?_⟩
    have hq := M.base.q_positive
    nlinarith

end NS25Lean.P3R54
