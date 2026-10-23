import NS25Lean.P2SectorCRepairedInterface

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4A

open L2B L5A1 L5A2C3G

variable {Gamma : NumericalSemigroup}

/-- The support-shape split for any actual two-component fiber in three
variables.  This is the internal-fiber counterpart of the frozen boundary
lemma and contains no numerical branch premise. -/
theorem two_component_support_shape_exhaustion (B : ChosenBase.Data Gamma)
    (h : ℕ) (hcard : Nat.card (FiberComponent B h) = 2) (hpos : 0 < h) :
    (∀ C : FiberComponent B h, (componentSupport B h C).card = 1) ∨
      ∃ C D : FiberComponent B h, C ≠ D ∧
        (((componentSupport B h C).card = 1 ∧
            (componentSupport B h D).card = 2) ∨
          ((componentSupport B h C).card = 2 ∧
            (componentSupport B h D).card = 1)) ∧
        ∀ E : FiberComponent B h, E = C ∨ E = D := by
  classical
  letI := Fintype.ofFinite (FiberComponent B h)
  obtain ⟨C, D, hne, hallSet⟩ := Nat.card_eq_two_iff.mp hcard
  have hall (E : FiberComponent B h) : E = C ∨ E = D := by
    have hmem : E ∈ ({C, D} : Set (FiberComponent B h)) :=
      hallSet.symm ▸ Set.mem_univ E
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hCpos : 0 < (componentSupport B h C).card :=
    Finset.card_pos.mpr (componentSupport_nonempty B h hpos C)
  have hDpos : 0 < (componentSupport B h D).card :=
    Finset.card_pos.mpr (componentSupport_nonempty B h hpos D)
  have hpair :
      (componentSupport B h C).card + (componentSupport B h D).card ≤
        ∑ E : FiberComponent B h, (componentSupport B h E).card := by
    have hs : ({C, D} : Finset (FiberComponent B h)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun E _ _ => Nat.zero_le (componentSupport B h E).card)
    simpa [hne] using hle
  have htotal :
      (componentSupport B h C).card + (componentSupport B h D).card ≤ 3 :=
    hpair.trans (sum_componentSupport_card_le_three B h)
  have hCshape : (componentSupport B h C).card = 1 ∨
      (componentSupport B h C).card = 2 := by omega
  have hDshape : (componentSupport B h D).card = 1 ∨
      (componentSupport B h D).card = 2 := by omega
  rcases hCshape with hCpure | hCmixed
  · rcases hDshape with hDpure | hDmixed
    · left
      intro E
      rcases hall E with rfl | rfl
      · exact hCpure
      · exact hDpure
    · exact Or.inr ⟨C, D, hne, Or.inl ⟨hCpure, hDmixed⟩, hall⟩
  · have hDpure : (componentSupport B h D).card = 1 := by omega
    exact Or.inr ⟨C, D, hne, Or.inr ⟨hCmixed, hDpure⟩, hall⟩

/-- The internal `(2,0)` fiber is split from its actual supports into the
pure/pure (symmetric) and pure/mixed (nonsymmetric) alternatives. -/
theorem sectorC_internal_support_shape_exhaustion {P : P2Data Gamma}
    (G : SectorCActualFibers P) :
    (∀ C : internalComponents G,
        (componentSupport P.M.base G.internalDegree C).card = 1) ∨
      ∃ C D : internalComponents G, C ≠ D ∧
        (((componentSupport P.M.base G.internalDegree C).card = 1 ∧
            (componentSupport P.M.base G.internalDegree D).card = 2) ∨
          ((componentSupport P.M.base G.internalDegree C).card = 2 ∧
            (componentSupport P.M.base G.internalDegree D).card = 1)) ∧
        ∀ E : internalComponents G, E = C ∨ E = D := by
  apply two_component_support_shape_exhaustion P.M.base G.internalDegree
  · simpa [componentCount] using G.internalSignature.1
  · exact (positive_contribution_active P.M G.internalDegree (by
      rw [G.internalContribution]
      omega)).1

private theorem card_two_disjoint_singleton_eq_02 (e : Fin 3 ≃ Fin 3)
    (S T : Finset (Fin 3)) (hS : S = {e 1}) (hT : T.card = 2)
    (hdis : Disjoint S T) : T = {e 0, e 2} := by
  classical
  have hcard : (S ∪ T).card = 3 := by
    rw [Finset.card_union_of_disjoint hdis, hS, hT]
    simp
  have hunion : S ∪ T = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hcard)
  have h0 : e 0 ∈ T := by
    have hu : e 0 ∈ S ∪ T := by rw [hunion]; simp
    simpa [hS, e.injective.eq_iff] using hu
  have h2 : e 2 ∈ T := by
    have hu : e 2 ∈ S ∪ T := by rw [hunion]; simp
    simpa [hS, e.injective.eq_iff] using hu
  have h1 : e 1 ∉ T := by
    exact Finset.disjoint_left.mp hdis (by simp [hS])
  apply Finset.ext
  intro j
  obtain ⟨i, rfl⟩ := e.surjective j
  fin_cases i <;> simp [h0, h1, h2, e.injective.eq_iff]

/-- In the actual pure/mixed internal alternative, the internal singleton
orders the two variables of the boundary mixed support.  Thus this theorem
constructs the full paper `a,b,c` reindexing from component supports alone. -/
theorem sectorC_nonsymmetric_reindexing {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (boundaryPure boundaryMixed : boundaryComponents G)
    (hbne : boundaryPure ≠ boundaryMixed)
    (hbp : IsPureBoundaryComponent G boundaryPure)
    (hbm : IsMixedBoundaryComponent G boundaryMixed)
    (internalPure internalMixed : internalComponents G)
    (hine : internalPure ≠ internalMixed)
    (hip : (componentSupport P.M.base G.internalDegree internalPure).card = 1)
    (him : (componentSupport P.M.base G.internalDegree internalMixed).card = 2) :
    ∃ e : Fin 3 ≃ Fin 3,
      componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2} ∧
      componentSupport P.M.base G.boundaryDegree boundaryMixed = {e 0, e 1} ∧
      componentSupport P.M.base G.internalDegree internalPure = {e 1} ∧
      componentSupport P.M.base G.internalDegree internalMixed = {e 0, e 2} := by
  classical
  obtain ⟨c, hbpSet⟩ := Finset.card_eq_one.mp hbp
  obtain ⟨x, y, hxy, hbmSet⟩ := Finset.card_eq_two.mp hbm
  obtain ⟨b, hipSet⟩ := Finset.card_eq_one.mp hip
  have hbc : b ≠ c := by
    intro he
    subst c
    have hdeg := singleton_active_degree_unique P.M.base G.internalDegree G.boundaryDegree
      (positive_contribution_active P.M G.internalDegree (by
        rw [G.internalContribution]
        omega)).1
      (positive_contribution_active P.M G.boundaryDegree (by
        rw [G.boundaryContribution]
        omega)).1
      (by have hc := G.internalSignature.1; unfold componentCount at hc ⊢; omega)
      (by have hc := G.boundarySignature.1; unfold componentCount at hc ⊢; omega)
      internalPure boundaryPure b hipSet hbpSet
    exact G.degree_ne hdeg
  have hbdis := componentSupports_disjoint P.M.base G.boundaryDegree
    boundaryPure boundaryMixed hbne
  have hcx : c ≠ x := by
    intro he
    have hcp : c ∈ componentSupport P.M.base G.boundaryDegree boundaryPure := by
      rw [hbpSet]
      simp
    have hcm : c ∈ componentSupport P.M.base G.boundaryDegree boundaryMixed := by
      rw [hbmSet, he]
      simp
    exact Finset.disjoint_left.mp hbdis hcp hcm
  have hcy : c ≠ y := by
    intro he
    have hcp : c ∈ componentSupport P.M.base G.boundaryDegree boundaryPure := by
      rw [hbpSet]
      simp
    have hcm : c ∈ componentSupport P.M.base G.boundaryDegree boundaryMixed := by
      rw [hbmSet, he]
      simp
    exact Finset.disjoint_left.mp hbdis hcp hcm
  have hcover : ({c} : Finset (Fin 3)) ∪ {x, y} = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hxy, hcx, hcy, Ne.symm hcx, Ne.symm hcy]
  have hbmem : b ∈ ({x, y} : Finset (Fin 3)) := by
    have hu : b ∈ ({c} : Finset (Fin 3)) ∪ {x, y} := by rw [hcover]; simp
    simpa [hbc] using hu
  have hbcase : b = x ∨ b = y := by simpa using hbmem
  rcases hbcase with hbx | hby
  · subst b
    let e : Fin 3 ≃ Fin 3 := Equiv.ofBijective (![y, x, c] : Fin 3 → Fin 3)
      ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [hxy, hcx, hcy, Ne.symm hxy, Ne.symm hcx, Ne.symm hcy], rfl⟩)
    have himSet := card_two_disjoint_singleton_eq_02 e
      (componentSupport P.M.base G.internalDegree internalPure)
      (componentSupport P.M.base G.internalDegree internalMixed)
      (by simpa [e] using hipSet) him
      (componentSupports_disjoint P.M.base G.internalDegree internalPure internalMixed hine)
    exact ⟨e, by simpa [e] using hbpSet, by simpa [e, Finset.pair_comm] using hbmSet,
      by simpa [e] using hipSet, himSet⟩
  · subst b
    let e : Fin 3 ≃ Fin 3 := Equiv.ofBijective (![x, y, c] : Fin 3 → Fin 3)
      ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [hxy, hcx, hcy, Ne.symm hxy, Ne.symm hcx, Ne.symm hcy], rfl⟩)
    have himSet := card_two_disjoint_singleton_eq_02 e
      (componentSupport P.M.base G.internalDegree internalPure)
      (componentSupport P.M.base G.internalDegree internalMixed)
      (by simpa [e] using hipSet) him
      (componentSupports_disjoint P.M.base G.internalDegree internalPure internalMixed hine)
    exact ⟨e, by simpa [e] using hbpSet, by simpa [e] using hbmSet,
      by simpa [e] using hipSet, himSet⟩

/-- Unconditional actual-geometry exhaustion for Sector C.  The symmetric
alternatives remain explicit; only the pure/mixed internal alternative emits
the nonsymmetric paper reindexing.  No branch flag is assumed. -/
theorem sectorC_actual_reindexing_exhaustion (P : P2Data Gamma) (hC : SectorC P.M) :
    ∃ G : SectorCActualFibers P,
      (∀ C : boundaryComponents G, IsPureBoundaryComponent G C) ∨
        ∃ boundaryPure boundaryMixed : boundaryComponents G,
          boundaryPure ≠ boundaryMixed ∧
          IsPureBoundaryComponent G boundaryPure ∧
          IsMixedBoundaryComponent G boundaryMixed ∧
          (PureOrientation G boundaryPure boundaryMixed ∨
            MixedOrientation G boundaryPure boundaryMixed) ∧
          ((∀ C : internalComponents G,
              (componentSupport P.M.base G.internalDegree C).card = 1) ∨
            ∃ internalPure internalMixed : internalComponents G,
              internalPure ≠ internalMixed ∧
              ∃ e : Fin 3 ≃ Fin 3,
                componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2} ∧
                componentSupport P.M.base G.boundaryDegree boundaryMixed = {e 0, e 1} ∧
                componentSupport P.M.base G.internalDegree internalPure = {e 1} ∧
                componentSupport P.M.base G.internalDegree internalMixed = {e 0, e 2}) := by
  obtain ⟨G, hboundary⟩ := sectorC_actual_boundary_interface P hC
  refine ⟨G, ?_⟩
  rcases hboundary with hsym | hnonsym
  · exact Or.inl hsym
  · right
    obtain ⟨boundaryPure, boundaryMixed, hbne, hbp, hbm, _, horientation, _⟩ := hnonsym
    refine ⟨boundaryPure, boundaryMixed, hbne, hbp, hbm, horientation, ?_⟩
    rcases sectorC_internal_support_shape_exhaustion G with hsym | hnonsym
    · exact Or.inl hsym
    · right
      obtain ⟨C, D, hne, hshape, _⟩ := hnonsym
      rcases hshape with hCD | hDC
      · obtain ⟨e, he0, he1, he2, he3⟩ :=
          sectorC_nonsymmetric_reindexing G boundaryPure boundaryMixed hbne hbp hbm
            C D hne hCD.1 hCD.2
        exact ⟨C, D, hne, e, he0, he1, he2, he3⟩
      · obtain ⟨e, he0, he1, he2, he3⟩ :=
          sectorC_nonsymmetric_reindexing G boundaryPure boundaryMixed hbne hbp hbm
            D C hne.symm hDC.2 hDC.1
        exact ⟨D, C, hne.symm, e, he0, he1, he2, he3⟩

/-- The actual critical exponent in paper coordinate `i`. -/
def herzogC (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) : ℕ :=
  criticalExponent B (e i)

/-- A canonical actual outside factorization witnessing the critical exponent. -/
def herzogWitness (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    Fin 3 →₀ ℕ :=
  Classical.choose (criticalExponent_spec B (e i)).2

theorem herzogC_positive (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    0 < herzogC B e i :=
  (criticalExponent_spec B (e i)).1

theorem herzogWitness_zero (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i : Fin 3) : herzogWitness B e i (e i) = 0 :=
  (Classical.choose_spec (criticalExponent_spec B (e i)).2).1

theorem herzogWitness_weight (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i : Fin 3) :
    weight B (herzogWitness B e i) = herzogC B e i * weights B (e i) :=
  (Classical.choose_spec (criticalExponent_spec B (e i)).2).2

theorem weight_three_coordinates (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (v : Fin 3 →₀ ℕ) :
    weight B v = v (e 0) * weights B (e 0) +
      v (e 1) * weights B (e 1) + v (e 2) * weights B (e 2) := by
  rw [weight_eq_sum, ← Equiv.sum_comp e]
  simp [Fin.sum_univ_succ, Nat.add_assoc]

abbrev c1 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) := herzogC B e 0
abbrev c2 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) := herzogC B e 1
abbrev c3 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) := herzogC B e 2

abbrev r12 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 0 (e 1)
abbrev r13 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 0 (e 2)
abbrev r21 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 1 (e 0)
abbrev r23 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 1 (e 2)
abbrev r31 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 2 (e 0)
abbrev r32 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :=
  herzogWitness B e 2 (e 1)

/-- The three source-exact Herzog equalities, derived from the actual minimal
outside-factorization witnesses rather than stored as fields. -/
theorem actual_herzog_relations (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    c1 B e * weights B (e 0) =
        r12 B e * weights B (e 1) + r13 B e * weights B (e 2) ∧
      c2 B e * weights B (e 1) =
        r21 B e * weights B (e 0) + r23 B e * weights B (e 2) ∧
      c3 B e * weights B (e 2) =
        r31 B e * weights B (e 0) + r32 B e * weights B (e 1) := by
  have h1 := herzogWitness_weight B e 0
  have h2 := herzogWitness_weight B e 1
  have h3 := herzogWitness_weight B e 2
  rw [weight_three_coordinates B e] at h1 h2 h3
  simp only [herzogWitness_zero, zero_mul, zero_add, add_zero] at h1 h2 h3
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- The actual internal and boundary Sector-C degrees are precisely the
critical degrees `h2` and `h3` after the nonsymmetric support reindexing. -/
theorem actual_internal_boundary_critical_degrees {P : P2Data Gamma}
    (G : SectorCActualFibers P) (e : Fin 3 ≃ Fin 3)
    (internalPure : internalComponents G) (boundaryPure : boundaryComponents G)
    (hi : componentSupport P.M.base G.internalDegree internalPure = {e 1})
    (hb : componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2}) :
    G.internalDegree = c2 P.M.base e * weights P.M.base (e 1) ∧
      G.boundaryDegree = c3 P.M.base e * weights P.M.base (e 2) := by
  constructor
  · apply singleton_active_degree_eq_critical P.M.base G.internalDegree
      (positive_contribution_active P.M G.internalDegree (by
        rw [G.internalContribution]
        omega)).1
      (by have hc := G.internalSignature.1; unfold componentCount at hc ⊢; omega)
      internalPure (e 1) hi
  · apply singleton_active_degree_eq_critical P.M.base G.boundaryDegree
      (positive_contribution_active P.M G.boundaryDegree (by
        rw [G.boundaryContribution]
        omega)).1
      (by have hc := G.boundarySignature.1; unfold componentCount at hc ⊢; omega)
      boundaryPure (e 2) hb

/-- The explicit paper-coordinate reindexing forced by an actual pure/mixed
boundary pair.  In the paper's `a,b,c` order, coordinate `2` is the pure
support and coordinates `0,1` are the mixed support of `h3`. -/
theorem sectorC_boundary_reindexing {P : P2Data Gamma}
    (G : SectorCActualFibers P) (pure mixed : boundaryComponents G)
    (hne : pure ≠ mixed) (hpure : IsPureBoundaryComponent G pure)
    (hmixed : IsMixedBoundaryComponent G mixed) :
    ∃ e : Fin 3 ≃ Fin 3,
      componentSupport P.M.base G.boundaryDegree pure = {e 2} ∧
      componentSupport P.M.base G.boundaryDegree mixed = {e 0, e 1} := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hpure
  obtain ⟨b, c, hbc, hmixed⟩ := Finset.card_eq_two.mp hmixed
  have hdisjoint := componentSupports_disjoint P.M.base G.boundaryDegree pure mixed hne
  have hanot : a ∉ ({b, c} : Finset (Fin 3)) := by
    intro ham
    have hap : a ∈ componentSupport P.M.base G.boundaryDegree pure := by
      rw [ha]
      simp
    have ham' : a ∈ componentSupport P.M.base G.boundaryDegree mixed := by
      rw [hmixed]
      exact ham
    exact Finset.disjoint_left.mp hdisjoint hap ham'
  have hab : a ≠ b := by
    intro hab
    apply hanot
    simp [hab]
  have hac : a ≠ c := by
    intro hac
    apply hanot
    simp [hac]
  let f : Fin 3 → Fin 3 := ![b, c, a]
  have hf : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [f, hab, hac, hbc, Ne.symm hab, Ne.symm hac,
      Ne.symm hbc]
  let e : Fin 3 ≃ Fin 3 := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, rfl⟩)
  refine ⟨e, ?_, ?_⟩
  · simpa [e, f] using ha
  · simpa [e, f] using hmixed

end NS25Lean.L5A2C4A
