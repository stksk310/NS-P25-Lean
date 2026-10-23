import NS25Lean.AppendixAGroebner
import Mathlib.RingTheory.Ideal.Colon

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L3C
open ChosenBase L2B L2B2A L2B2A2 L3B MvPolynomial
variable {Gamma : NumericalSemigroup} {k : Type*} [Field k]
variable {M : MultiplicityBase Gamma} {h : ℕ}

abbrev PlanarExponent := Fin 2 →₀ ℕ
abbrev PlanarPolynomial (k : Type*) [CommSemiring k] := MvPolynomial (Fin 2) k

def planarProjection (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ) : PlanarExponent :=
  Finsupp.equivFunOnFinite.symm (fun i => u (F.normal.perm i.succ))

def layerExponent (F : InternalFrontend k M h) (r : ℕ) (u : PlanarExponent) : Fin 3 →₀ ℕ :=
  Finsupp.single (F.normal.perm 0) r + Finsupp.single (F.normal.perm 1) (u 0) +
    Finsupp.single (F.normal.perm 2) (u 1)

@[simp] theorem layerExponent_x (F : InternalFrontend k M h) (r : ℕ) (u : PlanarExponent) :
    layerExponent F r u (F.normal.perm 0) = r := by
  classical
  simp [layerExponent, F.normal.perm.injective.eq_iff]

@[simp] theorem layerExponent_planar (F : InternalFrontend k M h)
    (r : ℕ) (u : PlanarExponent) (i : Fin 2) :
    layerExponent F r u (F.normal.perm i.succ) = u i := by
  classical
  fin_cases i <;> simp [layerExponent, F.normal.perm.injective.eq_iff]

theorem layerExponent_projection (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ) :
    layerExponent F (u (F.normal.perm 0)) (planarProjection F u) = u := by
  ext j
  obtain ⟨i, rfl⟩ := F.normal.perm.surjective j
  fin_cases i <;> simp [layerExponent, planarProjection, F.normal.perm.injective.eq_iff]

theorem le_layerExponent_iff (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ)
    (r : ℕ) (v : PlanarExponent) :
    u ≤ layerExponent F r v ↔ u (F.normal.perm 0) ≤ r ∧ planarProjection F u ≤ v := by
  constructor
  · intro hu
    refine ⟨by simpa using hu (F.normal.perm 0), fun i => ?_⟩
    simpa [planarProjection] using hu (F.normal.perm i.succ)
  · rintro ⟨hx, hyz⟩ j
    obtain ⟨i, rfl⟩ := F.normal.perm.surjective j
    fin_cases i
    · simpa using hx
    · simpa [planarProjection, layerExponent, F.normal.perm.injective.eq_iff] using hyz 0
    · simpa [planarProjection, layerExponent, F.normal.perm.injective.eq_iff] using hyz 1

def planarTie (F : InternalFrontend k M h) : PlanarExponent :=
  Finsupp.single 0 F.normal.b + Finsupp.single 1 F.normal.c

def planarSource (F : InternalFrontend k M h) (G : NormalizedSources F)
    (s : Source M.base) : PlanarExponent := planarProjection F (G.exponents s)

theorem planarProjection_wrap (F : InternalFrontend k M h) (u : Fin 3 →₀ ℕ) :
    planarProjection F (wrap F u) = planarTie F + planarProjection F u := by
  classical
  ext i
  fin_cases i <;>
    simp [planarProjection, wrap, transverse, planarTie, F.normal.beta_eq,
      F.normal.perm.injective.eq_iff]

def layerExponents (F : InternalFrontend k M h) (G : NormalizedSources F) (r : ℕ) :
    Set PlanarExponent :=
  {u | ∃ s, G.exponents s (F.normal.perm 0) ≤ r ∧ u = planarSource F G s} ∪
    {u | ∃ s, r < G.exponents s (F.normal.perm 0) ∧
      u = planarTie F + planarSource F G s}

def layerIdeal (F : InternalFrontend k M h) (G : NormalizedSources F) (r : ℕ) :
    Ideal (PlanarPolynomial k) :=
  Ideal.span ((fun u => monomial u (1 : k)) '' layerExponents F G r)

def planarA (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Ideal (PlanarPolynomial k) :=
  Ideal.span ((fun u => monomial u (1 : k)) '' Set.range (planarSource F G))

def planarB (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Ideal (PlanarPolynomial k) := layerIdeal F G 0

def planarJ (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Ideal (PlanarPolynomial k) :=
  (planarB F G).colon {monomial (planarTie F) (1 : k)}

def planarD (F : InternalFrontend k M h) (G : NormalizedSources F) : Set PlanarExponent :=
  {u | monomial u (1 : k) ∉ planarA F G}

def planarE (F : InternalFrontend k M h) (G : NormalizedSources F) : Set PlanarExponent :=
  {u | monomial u (1 : k) ∉ planarJ F G}

theorem planar_monomial_mem_span_iff (S : Set PlanarExponent) (u : PlanarExponent) :
    monomial u (1 : k) ∈ Ideal.span ((fun v => monomial v (1 : k)) '' S) ↔
      ∃ v ∈ S, v ≤ u := by
  classical
  simp [mem_ideal_span_monomial_image]

/-- The displayed layer ideals are exactly the actual initial quotient's layers. -/
theorem actual_layer_monomial (F : InternalFrontend k M h) (G : NormalizedSources F)
    (r : ℕ) (hr : r < F.normal.a) (u : PlanarExponent) :
    monomial (layerExponent F r u) (1 : k) ∈ F.initial.ideal ↔
      monomial u (1 : k) ∈ layerIdeal F G r := by
  rw [initial_eq_oneWrapIdeal, oneWrapIdeal, L3A.monomial_mem_span_iff,
    layerIdeal, planar_monomial_mem_span_iff]
  constructor
  · rintro ⟨v, (hv | ⟨s, rfl⟩) | ⟨s, hs, rfl⟩, hvu⟩
    · have he := Set.mem_singleton_iff.mp hv
      subst v
      have hh := hvu (F.normal.perm 0)
      simp only [F.normal.alpha_eq, Finsupp.single_eq_same, layerExponent_x] at hh
      omega
    · have hh := (le_layerExponent_iff F _ r u).mp hvu
      exact ⟨planarSource F G s, Or.inl ⟨s, hh.1, rfl⟩, hh.2⟩
    · have hh := (le_layerExponent_iff F _ r u).mp hvu
      rw [planarProjection_wrap] at hh
      by_cases hl : G.exponents s (F.normal.perm 0) ≤ r
      · refine ⟨planarSource F G s, Or.inl ⟨s, hl, rfl⟩, ?_⟩
        exact le_trans (by intro i; simp [planarSource]) hh.2
      · exact ⟨planarTie F + planarSource F G s,
          Or.inr ⟨s, Nat.lt_of_not_ge hl, rfl⟩, hh.2⟩
  · rintro ⟨v, ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩, hvu⟩
    · exact ⟨G.exponents s, Or.inl (Or.inr ⟨s, rfl⟩),
        (le_layerExponent_iff F _ r u).mpr ⟨hs, hvu⟩⟩
    · refine ⟨wrap F (G.exponents s), Or.inr ⟨s, by omega, rfl⟩, ?_⟩
      apply (le_layerExponent_iff F _ r u).mpr
      exact ⟨by rw [wrap_x_zero]; omega,
        by simpa [planarProjection_wrap, planarSource] using hvu⟩

theorem layer_zero_eq_B (F : InternalFrontend k M h) (G : NormalizedSources F) :
    layerIdeal F G 0 = planarB F G := rfl

theorem layer_top_eq_A (F : InternalFrontend k M h) (G : NormalizedSources F) :
    layerIdeal F G (F.normal.a - 1) = planarA F G := by
  have he : layerExponents F G (F.normal.a - 1) = Set.range (planarSource F G) := by
    ext u
    constructor
    · rintro (⟨s, _, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact ⟨s, rfl⟩
      · have := G.slab s; omega
    · rintro ⟨s, rfl⟩
      exact Or.inl ⟨s, by have := G.slab s; omega, rfl⟩
  simp only [layerIdeal, he, planarA]

theorem planar_colon_monomial (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) :
    monomial u (1 : k) ∈ planarJ F G ↔
      monomial (u + planarTie F) (1 : k) ∈ planarB F G := by
  rw [planarJ, Submodule.mem_colon_singleton, smul_eq_mul, monomial_mul, one_mul]

theorem planarA_le_planarJ (F : InternalFrontend k M h) (G : NormalizedSources F) :
    planarA F G ≤ planarJ F G := by
  apply Ideal.span_le.mpr
  rintro _ ⟨u, ⟨s, rfl⟩, rfl⟩
  change monomial (planarSource F G s) (1 : k) ∈ planarJ F G
  rw [planar_colon_monomial, planarB, layerIdeal, planar_monomial_mem_span_iff]
  by_cases hs : G.exponents s (F.normal.perm 0) = 0
  · refine ⟨planarSource F G s, Or.inl ⟨s, by omega, rfl⟩, ?_⟩
    intro i; simp
  · exact ⟨planarTie F + planarSource F G s,
      Or.inr ⟨s, Nat.pos_of_ne_zero hs, rfl⟩, by rw [add_comm]⟩

theorem planarE_subset_D (F : InternalFrontend k M h) (G : NormalizedSources F) :
    planarE F G ⊆ planarD F G := by
  intro u hu hA
  exact hu (planarA_le_planarJ F G hA)

theorem layerExponent_injective (F : InternalFrontend k M h) (r : ℕ) :
    Function.Injective (layerExponent F r) := by
  intro u v he
  ext i
  have hi := congrArg (fun w => w (F.normal.perm i.succ)) he
  simpa only [layerExponent_planar] using hi

theorem layerExponent_add_planar (F : InternalFrontend k M h) (r : ℕ)
    (u : PlanarExponent) (i : Fin 2) :
    layerExponent F r (u + Finsupp.single i 1) =
      layerExponent F r u + Finsupp.single (F.normal.perm i.succ) 1 := by
  classical
  ext j
  obtain ⟨l, rfl⟩ := F.normal.perm.surjective j
  fin_cases i <;> fin_cases l <;>
    simp [layerExponent, F.normal.perm.injective.eq_iff]

theorem layerExponent_add_x (F : InternalFrontend k M h) (r : ℕ) (u : PlanarExponent) :
    layerExponent F r u + Finsupp.single (F.normal.perm 0) 1 =
      layerExponent F (r + 1) u := by
  classical
  ext j
  obtain ⟨l, rfl⟩ := F.normal.perm.surjective j
  fin_cases l <;> simp [layerExponent, F.normal.perm.injective.eq_iff]

theorem planarD_finite (F : InternalFrontend k M h) (G : NormalizedSources F) :
    (planarD F G).Finite := by
  let := F.initial.artinian
  have hfin := L3A.standardExponents_finite F.initial.ideal F.initial.monomial
  have : Finite (L3A.standardExponents F.initial.ideal) := hfin.to_subtype
  let f : planarD F G → L3A.standardExponents F.initial.ideal := fun u =>
    ⟨layerExponent F (F.normal.a - 1) u.val, by
      intro hm
      have hh := (actual_layer_monomial F G (F.normal.a - 1)
        (by have := F.normal.a_ge_two; omega) u.val).mp hm
      rw [layer_top_eq_A] at hh
      exact u.property hh⟩
  have : Finite (planarD F G) := Finite.of_injective f (by
    intro u v he
    apply Subtype.ext
    exact layerExponent_injective F _ (congrArg Subtype.val he))
  exact Set.toFinite _

theorem planarE_finite (F : InternalFrontend k M h) (G : NormalizedSources F) :
    (planarE F G).Finite := (planarD_finite F G).subset (planarE_subset_D F G)

/-- The maximal standard monomials of the actual planar top-layer ideal. -/
def planarMaxD (F : InternalFrontend k M h) (G : NormalizedSources F) :
    Set PlanarExponent :=
  {u | u ∈ planarD F G ∧ ∀ i : Fin 2, monomial (u + Finsupp.single i 1) (1 : k) ∈ planarA F G}

theorem planarMaxD_finite (F : InternalFrontend k M h) (G : NormalizedSources F) :
    (planarMaxD F G).Finite := (planarD_finite F G).subset (fun _ hu => hu.1)

theorem planarMaxD_iff_maximal (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) :
    u ∈ planarMaxD F G ↔ Maximal (fun v => v ∈ planarD F G) u := by
  classical
  constructor
  · rintro ⟨hu, hs⟩
    refine ⟨hu, fun v hv huv i => ?_⟩
    by_contra hn
    have hle : u + Finsupp.single i 1 ≤ v := by
      intro j
      by_cases hj : j = i
      · subst j
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        omega
      · simpa [Finsupp.single_apply, hj, Ne.symm hj] using huv j
    exact hv ((planarA F G).mem_of_dvd (monomial_one_dvd_monomial_one.mpr hle) (hs i))
  · rintro ⟨hu, hm⟩
    refine ⟨hu, fun i => ?_⟩
    by_contra hn
    have hle : u ≤ u + Finsupp.single i 1 := by intro j; simp
    have hh := hm hn hle i
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hh
    omega

/-- Exact top-layer monomial socles, before comparing with the original quotient. -/
theorem top_socle_iff (F : InternalFrontend k M h) (G : NormalizedSources F)
    (u : PlanarExponent) :
    layerExponent F (F.normal.a - 1) u ∈ L3A.socleExponents F.initial.ideal ↔
      u ∈ planarMaxD F G := by
  have ha : F.normal.a - 1 < F.normal.a := by have := F.normal.a_ge_two; omega
  have hstd : layerExponent F (F.normal.a - 1) u ∈
      L3A.standardExponents F.initial.ideal ↔ u ∈ planarD F G := by
    change (monomial _ (1 : k) ∉ _) ↔ (monomial _ (1 : k) ∉ _)
    rw [actual_layer_monomial F G _ ha, layer_top_eq_A]
  constructor
  · rintro ⟨hu, hs⟩
    refine ⟨hstd.mp hu, fun i => ?_⟩
    have hh := hs (F.normal.perm i.succ)
    rw [← layerExponent_add_planar, actual_layer_monomial F G _ ha,
      layer_top_eq_A] at hh
    exact hh
  · rintro ⟨hu, hs⟩
    refine ⟨hstd.mpr hu, fun i => ?_⟩
    obtain ⟨l, rfl⟩ := F.normal.perm.surjective i
    refine Fin.cases ?_ (fun j => ?_) l
    · rw [layerExponent_add_x]
      apply F.initial.ideal.mem_of_dvd _ (tie_leading_mem F)
      apply monomial_one_dvd_monomial_one.mpr
      rw [F.normal.alpha_eq]
      apply Finsupp.single_le_iff.mpr
      rw [layerExponent_x]
      have := F.normal.a_ge_two
      omega
    · rw [← layerExponent_add_planar, actual_layer_monomial F G _ ha, layer_top_eq_A]
      exact hs j

end NS25Lean.L3C
