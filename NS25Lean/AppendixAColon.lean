import NS25Lean.AppendixALayers
import NS25Lean.AppendixACompletion

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

def colonExponents (F : InternalFrontend k M h) (G : NormalizedSources F) : Set PlanarExponent :=
  {u | ∃ s, 0 < G.exponents s (F.normal.perm 0) ∧ u = planarSource F G s} ∪
  {u | ∃ s, G.exponents s (F.normal.perm 0) = 0 ∧ u = planarSource F G s - planarTie F}

theorem exact_colon_monomial (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) :
    monomial u (1 : k) ∈ planarJ F G ↔ ∃ w ∈ colonExponents F G, w ≤ u := by
  rw [planar_colon_monomial, planarB, layerIdeal, planar_monomial_mem_span_iff]
  constructor
  · rintro ⟨w, ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩, hle⟩
    · exact ⟨planarSource F G s - planarTie F, Or.inr ⟨s, by omega, rfl⟩,
        tsub_le_iff_right.mpr hle⟩
    · exact ⟨planarSource F G s, Or.inl ⟨s, hs, rfl⟩,
        (add_le_add_iff_left (planarTie F)).mp (by simpa [add_comm] using hle)⟩
  · rintro ⟨w, ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩, hle⟩
    · exact ⟨planarTie F + planarSource F G s, Or.inr ⟨s, hs, rfl⟩,
        by simpa [add_comm] using add_le_add_left hle (planarTie F)⟩
    · exact ⟨planarSource F G s, Or.inl ⟨s, by omega, rfl⟩,
        tsub_le_iff_right.mp hle⟩

theorem zero_layer_killing (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) (huD : u ∈ planarD F G) (huE : u ∉ planarE F G) :
    ∃ s, G.exponents s (F.normal.perm 0) = 0 ∧ planarSource F G s ≤ u + planarTie F := by
  have huJ : monomial u (1 : k) ∈ planarJ F G := by simpa [planarE] using huE
  obtain ⟨w, hw, hwu⟩ := (exact_colon_monomial F G u).mp huJ
  rcases hw with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
  · exfalso
    apply huD
    exact (planar_monomial_mem_span_iff _ u).mpr ⟨planarSource F G s, ⟨s, rfl⟩, hwu⟩
  · exact ⟨s, hs, tsub_le_iff_right.mp hwu⟩

/-- Exact equality of polynomial ideals, not just their monomial predicates. -/
theorem exact_colon_ideal (F : InternalFrontend k M h) (G : NormalizedSources F) :
    planarJ F G = Ideal.span ((fun u => monomial u (1 : k)) '' colonExponents F G) := by
  apply le_antisymm
  · intro p hp
    apply mem_ideal_span_monomial_image.mpr
    intro u hu
    have hpB : p * monomial (planarTie F) (1 : k) ∈ planarB F G := by
      simpa only [planarJ, Submodule.mem_colon_singleton, smul_eq_mul] using hp
    have hc : u + planarTie F ∈ (p * monomial (planarTie F) (1 : k)).support := by
      simpa only [mem_support_iff, coeff_mul_monomial, mul_one] using hu
    have hm : monomial (u + planarTie F) (1 : k) ∈ planarB F G :=
      (planar_monomial_mem_span_iff _ _).mpr (mem_ideal_span_monomial_image.mp hpB _ hc)
    exact (exact_colon_monomial F G u).mp ((planar_colon_monomial F G u).mpr hm)
  · apply Ideal.span_le.mpr
    rintro _ ⟨u, hu, rfl⟩
    exact (exact_colon_monomial F G u).mpr ⟨u, hu, le_rfl⟩

theorem zero_layer_colon_coordinates (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) :
    (planarSource F G s - planarTie F) 0 = planarSource F G s 0 - F.normal.b ∧
    (planarSource F G s - planarTie F) 1 = planarSource F G s 1 - F.normal.c := by
  simp [planarTie]

end NS25Lean.L3C
