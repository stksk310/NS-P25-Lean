import NS25Lean.P2SectorCGeometry

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C3G

open L2B L5A1

variable {Gamma : NumericalSemigroup}

/-- A pure boundary component is defined from its actual factorization support. -/
def IsPureBoundaryComponent {P : P2Data Gamma} (G : SectorCActualFibers P)
    (C : boundaryComponents G) : Prop :=
  (componentSupport P.M.base G.boundaryDegree C).card = 1

/-- A mixed boundary component is defined from its actual factorization support. -/
def IsMixedBoundaryComponent {P : P2Data Gamma} (G : SectorCActualFibers P)
    (C : boundaryComponents G) : Prop :=
  (componentSupport P.M.base G.boundaryDegree C).card = 2

/-- Two actual boundary components in three variables have either pure/pure
support or pure/mixed support.  This is the support-level geometry split; it
does not assert complete-intersection membership. -/
theorem boundary_support_shape_exhaustion {P : P2Data Gamma}
    (G : SectorCActualFibers P)
    (hcard : Nat.card (boundaryComponents G) = 2)
    (hpos : 0 < G.boundaryDegree) :
    (∀ C : boundaryComponents G, IsPureBoundaryComponent G C) ∨
      ∃ C D : boundaryComponents G, C ≠ D ∧
        ((IsPureBoundaryComponent G C ∧ IsMixedBoundaryComponent G D) ∨
         (IsMixedBoundaryComponent G C ∧ IsPureBoundaryComponent G D)) ∧
        ∀ E : boundaryComponents G, E = C ∨ E = D := by
  classical
  letI := Fintype.ofFinite (boundaryComponents G)
  obtain ⟨C, D, hne, hallSet⟩ := Nat.card_eq_two_iff.mp hcard
  have hall (E : boundaryComponents G) : E = C ∨ E = D := by
    have hmem : E ∈ ({C, D} : Set (boundaryComponents G)) :=
      hallSet.symm ▸ Set.mem_univ E
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hCpos : 0 < (componentSupport P.M.base G.boundaryDegree C).card :=
    Finset.card_pos.mpr (componentSupport_nonempty P.M.base G.boundaryDegree hpos C)
  have hDpos : 0 < (componentSupport P.M.base G.boundaryDegree D).card :=
    Finset.card_pos.mpr (componentSupport_nonempty P.M.base G.boundaryDegree hpos D)
  have hpair :
      (componentSupport P.M.base G.boundaryDegree C).card +
          (componentSupport P.M.base G.boundaryDegree D).card ≤
        ∑ E : boundaryComponents G,
          (componentSupport P.M.base G.boundaryDegree E).card := by
    have hs : ({C, D} : Finset (boundaryComponents G)) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hs
      (fun E _ _ => Nat.zero_le (componentSupport P.M.base G.boundaryDegree E).card)
    simpa [hne] using hle
  have hthree := sum_componentSupport_card_le_three P.M.base G.boundaryDegree
  have htotal :
      (componentSupport P.M.base G.boundaryDegree C).card +
          (componentSupport P.M.base G.boundaryDegree D).card ≤ 3 :=
    hpair.trans hthree
  have hCshape :
      (componentSupport P.M.base G.boundaryDegree C).card = 1 ∨
        (componentSupport P.M.base G.boundaryDegree C).card = 2 := by
    omega
  have hDshape :
      (componentSupport P.M.base G.boundaryDegree D).card = 1 ∨
        (componentSupport P.M.base G.boundaryDegree D).card = 2 := by
    omega
  rcases hCshape with hCpure | hCmixed
  · rcases hDshape with hDpure | hDmixed
    · left
      intro E
      rcases hall E with rfl | rfl
      · exact hCpure
      · exact hDpure
    · right
      exact ⟨C, D, hne, Or.inl ⟨hCpure, hDmixed⟩, hall⟩
  · have hDpure : (componentSupport P.M.base G.boundaryDegree D).card = 1 := by
      omega
    right
    exact ⟨C, D, hne, Or.inr ⟨hCmixed, hDpure⟩, hall⟩

/-- The repaired paper's pure orientation, stated only after actual support
geometry has identified the pure and mixed components. -/
def PureOrientation {P : P2Data Gamma} (G : SectorCActualFibers P)
    (pure mixed : boundaryComponents G) : Prop :=
  BoundaryKilled P.M G.boundaryDegree pure ∧
    ¬ BoundaryKilled P.M G.boundaryDegree mixed

/-- The repaired paper's mixed orientation, stated only after actual support
geometry has identified the pure and mixed components. -/
def MixedOrientation {P : P2Data Gamma} (G : SectorCActualFibers P)
    (pure mixed : boundaryComponents G) : Prop :=
  ¬ BoundaryKilled P.M G.boundaryDegree pure ∧
    BoundaryKilled P.M G.boundaryDegree mixed

/-- If two actual components exhaust the boundary fiber and exactly one is
killed, the pure/mixed orientations are disjoint and exhaustive. -/
theorem boundary_orientation_exhaustion {P : P2Data Gamma}
    (G : SectorCActualFibers P) (pure mixed : boundaryComponents G)
    (hne : pure ≠ mixed)
    (hall : ∀ E : boundaryComponents G, E = pure ∨ E = mixed)
    (hkilled : Nat.card (boundaryKilledComponents G) = 1) :
    (PureOrientation G pure mixed ∨ MixedOrientation G pure mixed) ∧
      ¬ (PureOrientation G pure mixed ∧ MixedOrientation G pure mixed) := by
  obtain ⟨K, hKuniq⟩ := Nat.card_eq_one_iff_exists.mp hkilled
  have horientation : PureOrientation G pure mixed ∨ MixedOrientation G pure mixed := by
    rcases hall K.val with hKpure | hKmixed
    · left
      constructor
      · simpa [hKpure] using K.property
      · intro hmixed
        have heq := congrArg Subtype.val (hKuniq ⟨mixed, hmixed⟩)
        exact hne (heq.trans hKpure).symm
    · right
      constructor
      · intro hpure
        have heq := congrArg Subtype.val (hKuniq ⟨pure, hpure⟩)
        exact hne (heq.trans hKmixed)
      · simpa [hKmixed] using K.property
  refine ⟨horientation, ?_⟩
  rintro ⟨⟨hpure, _⟩, ⟨hnpure, _⟩⟩
  exact hnpure hpure

/-- Strongest repaired interface derivable from the checkpoint's actual
objects: the boundary support is pure/pure or pure/mixed, and in the latter
case the killed/live status gives exactly the two repaired orientations. -/
theorem sectorC_actual_boundary_interface (P : P2Data Gamma) (hC : SectorC P.M) :
    ∃ G : SectorCActualFibers P,
      (∀ C : boundaryComponents G, IsPureBoundaryComponent G C) ∨
        ∃ pure mixed : boundaryComponents G, pure ≠ mixed ∧
          IsPureBoundaryComponent G pure ∧ IsMixedBoundaryComponent G mixed ∧
          (∀ E : boundaryComponents G, E = pure ∨ E = mixed) ∧
          ((PureOrientation G pure mixed ∨ MixedOrientation G pure mixed) ∧
            ¬ (PureOrientation G pure mixed ∧ MixedOrientation G pure mixed)) := by
  obtain ⟨G, _, hboundary, _, hkilled, _, _⟩ := sectorC_actual_fibers P hC
  have hpos : 0 < G.boundaryDegree :=
    (positive_contribution_active P.M G.boundaryDegree (by
      rw [G.boundaryContribution]
      omega)).1
  refine ⟨G, ?_⟩
  rcases boundary_support_shape_exhaustion G hboundary hpos with hpure | hmixed
  · exact Or.inl hpure
  · right
    obtain ⟨C, D, hne, hshape, hall⟩ := hmixed
    rcases hshape with ⟨hCpure, hDmixed⟩ | ⟨hCmixed, hDpure⟩
    · exact ⟨C, D, hne, hCpure, hDmixed, hall,
        boundary_orientation_exhaustion G C D hne hall hkilled⟩
    · have hall' (E : boundaryComponents G) : E = D ∨ E = C := by
        rcases hall E with h | h
        · exact Or.inr h
        · exact Or.inl h
      exact ⟨D, C, hne.symm, hDpure, hCmixed, hall',
        boundary_orientation_exhaustion G D C hne.symm hall' hkilled⟩

end NS25Lean.L5A2C3G
