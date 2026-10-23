import NS25Lean.AppendixACuts
import NS25Lean.AppendixAFerrersAudit
import Mathlib.Order.Preorder.Finite

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

/-- Source-use replacement for the overbroad bounded-lens wording: actual
common cut corners admit a maximal standard point strictly between them. -/
theorem maximal_between_cuts (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u v : PlanarExponent) (hu : u ∈ cuts F G) (hv : v ∈ cuts F G)
    (huy : u 0 < v 0) (hvz : v 1 < u 1) :
    ∃ t ∈ planarMaxD F G, u 0 ≤ t 0 ∧ t 0 < v 0 ∧ v 1 ≤ t 1 ∧ t 1 < u 1 := by
  classical
  let seed : PlanarExponent := Finsupp.single 0 (u 0) + Finsupp.single 1 (v 1)
  have hs0 : seed 0 = u 0 := by simp [seed]
  have hs1 : seed 1 = v 1 := by simp [seed]
  have hsu : seed ≤ u := by intro i; fin_cases i <;> simp [seed] <;> omega
  have hsD : seed ∈ planarD F G := by
    intro hsA
    have hh := (cuts_common_minimal F G hu).1.2 hsA hsu
    have hh1 := hh 1
    omega
  obtain ⟨t, hst, ht⟩ := (planarD_finite F G).exists_le_maximal hsD
  have htsoc : t ∈ planarMaxD F G := by
    refine ⟨ht.1, fun i => ?_⟩
    by_contra hi
    have he := ht.2 hi (by simp)
    have hh := he i
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hh
    omega
  have ht0 : t 0 < v 0 := by
    by_contra hn
    apply ht.1
    apply (planarA F G).mem_of_dvd _ (cuts_common_minimal F G hv).1.1
    apply monomial_one_dvd_monomial_one.mpr
    intro i
    fin_cases i
    · change v 0 ≤ t 0; omega
    · change v 1 ≤ t 1; have := hst 1; omega
  have ht1 : t 1 < u 1 := by
    by_contra hn
    apply ht.1
    apply (planarA F G).mem_of_dvd _ (cuts_common_minimal F G hu).1.1
    apply monomial_one_dvd_monomial_one.mpr
    intro i
    fin_cases i
    · change u 0 ≤ t 0; have := hst 0; omega
    · change u 1 ≤ t 1; omega
  exact ⟨t, htsoc, by have := hst 0; omega, ht0, by have := hst 1; omega, ht1⟩

theorem common_corner_or_mixed_killer (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u v : PlanarExponent) (hu : u ∈ cuts F G) (hv : v ∈ cuts F G)
    (huy : u 0 < v 0) (hvz : v 1 < u 1) :
    ∃ t ∈ planarMaxD F G, u 0 ≤ t 0 ∧ t 0 < v 0 ∧ v 1 ≤ t 1 ∧ t 1 < u 1 ∧
      (t ∈ planarE F G ∨ ∃ w : PlanarExponent, w ≤ t ∧
        Minimal (fun z => monomial z (1 : k) ∈ planarJ F G) w ∧
        monomial w (1 : k) ∉ planarA F G ∧ 0 < w 0 ∧ 0 < w 1) := by
  obtain ⟨t, ht, h0, h1, h2, h3⟩ := maximal_between_cuts F G u v hu hv huy hvz
  refine ⟨t, ht, h0, h1, h2, h3, ?_⟩
  by_cases he : t ∈ planarE F G
  · exact Or.inl he
  · right
    apply FerrersAudit.mixed_killer_between_common_corners
      (planarA F G) (planarJ F G) u v t
      (cuts_common_minimal F G hu).2 (cuts_common_minimal F G hv).2 ht.1 _ h1 h3
    simpa [planarE] using he

end NS25Lean.L3C
