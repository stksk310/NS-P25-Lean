import NS25Lean.P2SectorCRepairedOrientation

set_option linter.style.header false
noncomputable section
namespace NS25Lean.L5A2C4G

open L2B L5A1 L5A2C3G L5A2C4A L5A2C4B L5A2C4C L5A2C4D L5A2C4E
  L5A2C4F ChosenBase

variable {Gamma : NumericalSemigroup}

/-- The actual nonsymmetric Sector-C support pattern.  This predicate contains
only existing fiber components and their proved supports; it contains no gate,
orientation, branch, payment, or terminal conclusion. -/
def NonsymmetricSectorC (P : P2Data Gamma) : Prop :=
  ∃ (G : SectorCActualFibers P)
      (boundaryPure boundaryMixed : boundaryComponents G)
      (internalPure internalMixed : internalComponents G)
      (e : Fin 3 ≃ Fin 3),
    boundaryPure ≠ boundaryMixed ∧ internalPure ≠ internalMixed ∧
      componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2} ∧
      componentSupport P.M.base G.boundaryDegree boundaryMixed = {e 0, e 1} ∧
      componentSupport P.M.base G.internalDegree internalPure = {e 1} ∧
      componentSupport P.M.base G.internalDegree internalMixed = {e 0, e 2}

/-- The actual eta gate is exposed before both notch corners vanish. -/
def DirectPFBranch (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : Prop :=
  coherentP1 B e D ≠ 0 ∨ coherentQ1 B e D ≠ 0

/-- The genuine surviving-notch gate allowed by the repaired interface. -/
def SurvivingNotch (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) : Prop :=
  coherentP1 B e D = 0 ∧ coherentQ1 B e D = 0

/-- The direct eta gate and the surviving notch are exhaustive. -/
theorem directPF_or_survivingNotch (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    DirectPFBranch B e D ∨ SurvivingNotch B e D := by
  by_cases hP : coherentP1 B e D = 0
  · by_cases hQ : coherentQ1 B e D = 0
    · exact Or.inr ⟨hP, hQ⟩
    · exact Or.inl (Or.inr hQ)
  · exact Or.inl (Or.inl hP)

/-- The two actual eta-gate branches are disjoint. -/
theorem directPF_not_survivingNotch (B : Data Gamma) (e : Fin 3 ≃ Fin 3)
    (D : CoherentHerzogData B e) :
    ¬ (DirectPFBranch B e D ∧ SurvivingNotch B e D) := by
  rintro ⟨hDirect, hNotch⟩
  rcases hDirect with hP | hQ
  · exact hP hNotch.1
  · exact hQ hNotch.2

/-- Actual Sector-C geometry is boundary-symmetric, internally symmetric after
the boundary nonsymmetric reindexing, or genuinely nonsymmetric.  No global
pivot trichotomy is used. -/
theorem sectorC_actual_nonsymmetric_exhaustion (P : P2Data Gamma)
    (hC : SectorC P.M) :
    (∃ G : SectorCActualFibers P,
        ∀ C : boundaryComponents G, IsPureBoundaryComponent G C) ∨
      (∃ (G : SectorCActualFibers P)
          (boundaryPure boundaryMixed : boundaryComponents G),
        boundaryPure ≠ boundaryMixed ∧
          IsPureBoundaryComponent G boundaryPure ∧
          IsMixedBoundaryComponent G boundaryMixed ∧
          ∀ C : internalComponents G,
            (componentSupport P.M.base G.internalDegree C).card = 1) ∨
      NonsymmetricSectorC P := by
  rcases sectorC_actual_reindexing_exhaustion P hC with ⟨G, hsym | hnonsym⟩
  · exact Or.inl ⟨G, hsym⟩
  · obtain ⟨boundaryPure, boundaryMixed, hbne, hbp, hbm, _hOrient,
      hinternal⟩ := hnonsym
    rcases hinternal with hsym | hnonsym
    · exact Or.inr (Or.inl ⟨G, boundaryPure, boundaryMixed, hbne, hbp, hbm, hsym⟩)
    · obtain ⟨internalPure, internalMixed, hine, e, hbPure, hbMixed,
        hiPure, hiMixed⟩ := hnonsym
      exact Or.inr (Or.inr ⟨G, boundaryPure, boundaryMixed, internalPure,
        internalMixed, e, hbne, hine, hbPure, hbMixed, hiPure, hiMixed⟩)

private theorem boundary_all_of_two {P : P2Data Gamma}
    (G : SectorCActualFibers P) (pure mixed : boundaryComponents G)
    (hne : pure ≠ mixed) :
    ∀ E : boundaryComponents G, E = pure ∨ E = mixed := by
  have hcard : Nat.card (boundaryComponents G) = 2 := G.boundarySignature.1
  obtain ⟨other, _hother, huniq⟩ := (Nat.card_eq_two_iff' pure).mp hcard
  have hmixed : mixed = other := huniq mixed hne.symm
  intro E
  by_cases hE : E = pure
  · exact Or.inl hE
  · exact Or.inr ((huniq E hE).trans hmixed.symm)

/-- Strongest source-exact checkpoint available before the historical routing
bodies.  Starting only with actual nonsymmetric component supports, it builds
the coherent data, proves the inactive `h1=(2,2)` gate, obtains the structural
orientation, splits DIRECT-PF from the surviving notch, and exports every C4F
pure/mixed numerical premise. -/
theorem actual_nonsymmetric_gate_interface (P : P2Data Gamma)
    (hNS : NonsymmetricSectorC P) :
    ∃ (G : SectorCActualFibers P)
        (boundaryPure boundaryMixed : boundaryComponents G)
        (internalPure internalMixed : internalComponents G)
        (e : Fin 3 ≃ Fin 3) (D : CoherentHerzogData P.M.base e),
      boundaryPure ≠ boundaryMixed ∧ internalPure ≠ internalMixed ∧
      componentSupport P.M.base G.boundaryDegree boundaryPure = {e 2} ∧
      componentSupport P.M.base G.boundaryDegree boundaryMixed = {e 0, e 1} ∧
      componentSupport P.M.base G.internalDegree internalPure = {e 1} ∧
      componentSupport P.M.base G.internalDegree internalMixed = {e 0, e 2} ∧
      LocalSignature P.M (c1 P.M.base e * weights P.M.base (e 0)) 2 2 ∧
      (PureOrientation G boundaryPure boundaryMixed ∨
        MixedOrientation G boundaryPure boundaryMixed) ∧
      (DirectPFBranch P.M.base e D ∨ SurvivingNotch P.M.base e D) ∧
      (PureOrientation G boundaryPure boundaryMixed →
        coherentY3 P.M.base e D = 0 ∧
          coherentZ3 P.M.base e D = cr31 D ∧
          cr31 D + 1 ≤ coherentZ3minus P.M.base e D) ∧
      (cr12 D = 1 → SurvivingNotch P.M.base e D →
        PureOrientation G boundaryPure boundaryMixed) ∧
      (MixedOrientation G boundaryPure boundaryMixed →
        SurvivingNotch P.M.base e D →
          1 ≤ coherentY3 P.M.base e D ∧ 2 ≤ cr12 D ∧
            (coherentZ3 P.M.base e D < cr31 D ∨
              (coherentZ3 P.M.base e D = cr31 D ∧
                coherentZ3minus P.M.base e D = cr31 D))) := by
  rcases hNS with ⟨G, boundaryPure, boundaryMixed, internalPure, internalMixed,
    e, hbne, hine, hbPure, hbMixed, hiPure, hiMixed⟩
  let D : CoherentHerzogData P.M.base e :=
    Classical.choice (exists_coherentHerzogData G e internalPure internalMixed
      boundaryPure boundaryMixed hine hbne hiPure hiMixed hbPure hbMixed)
  have hall := boundary_all_of_two G boundaryPure boundaryMixed hbne
  have hOrient := (boundary_orientation_exhaustion G boundaryPure boundaryMixed
    hbne hall G.boundarySignature.2).1
  have hInactive := actual_h1_inactive_gate G e internalPure internalMixed
    boundaryPure boundaryMixed hine hbne hiPure hiMixed hbPure hbMixed
  refine ⟨G, boundaryPure, boundaryMixed, internalPure, internalMixed, e, D,
    hbne, hine, hbPure, hbMixed, hiPure, hiMixed, hInactive, hOrient,
    directPF_or_survivingNotch P.M.base e D, ?_, ?_, ?_⟩
  · exact pure_orientation_numerical G e boundaryPure boundaryMixed hbPure hbMixed D
  · intro hr12 hNotch
    exact width_one_surviving_notch_pure G e boundaryPure boundaryMixed
      hbPure hbMixed D hOrient hr12 hNotch.1 hNotch.2
  · intro hMixed hNotch
    have hNumerical := mixed_orientation_numerical G e boundaryPure boundaryMixed
      hbPure hbMixed D hMixed
    have hWidth := mixed_orientation_width G e boundaryPure boundaryMixed
      hbPure hbMixed D hMixed hNotch.1
    have hChambers := mixed_orientation_chambers G e boundaryPure boundaryMixed
      hbPure hbMixed D hMixed
    exact ⟨hNumerical.1, hWidth, hChambers⟩

end NS25Lean.L5A2C4G
