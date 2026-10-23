import NS25Lean.P2SectorCSourceHitLocalSquareDictionaryR11

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR13

open L5A2C4H L5A2C4OR1 L5A2C4OR3

variable {Gamma : NumericalSemigroup}

/-- The ambient normalized-tail Apéry carry in the `b` direction.  This is
independent of the cut ideal and is deliberately distinct from `routingData.u`. -/
def tailBCarry (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) : ℕ :=
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  (routingH B e).asRelativeIdeal.aperyStepQuotient
    (routingA B e) (routingB B e) (routingHB B e) s

/-- The ambient normalized-tail Apéry carry in the `c` direction. -/
def tailCCarry (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) : ℕ :=
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  (routingH B e).asRelativeIdeal.aperyStepQuotient
    (routingA B e) (routingC B e) (routingHC B e) s

/-- Exact raw/tail dictionary in the `b` direction.  The subtraction-free
form is valid at every residue, including every wrap boundary. -/
theorem physicalHeight_step_b_with_tailCarry
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    physicalHeight B e s + tailBCarry B e s =
      physicalHeight B e (s + routingB B e) + (routingData B e).u s := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hl0 := physicalHeight_spec B e s
  have hl1 := physicalHeight_spec B e (s + routingB B e)
  have hraw := (routingI B e).apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e) s
  have htail := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingB B e) (routingHB B e) s
  change (routingI B e).aperyRepresentative (routingA B e) s =
    physicalAlpha B e s + (routingA B e : ℤ) * physicalHeight B e s at hl0
  change (routingI B e).aperyRepresentative (routingA B e)
      (s + routingB B e) =
    physicalAlpha B e (s + routingB B e) +
      (routingA B e : ℤ) * physicalHeight B e (s + routingB B e) at hl1
  change physicalAlpha B e s + routingB B e =
    physicalAlpha B e (s + routingB B e) +
      (routingA B e : ℤ) * tailBCarry B e s at htail
  change (routingI B e).aperyRepresentative (routingA B e) s + routingB B e =
    (routingI B e).aperyRepresentative (routingA B e)
      (s + routingB B e) +
      (routingA B e : ℤ) * (routingData B e).u s at hraw
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hprod :
      (routingA B e : ℤ) *
          ((physicalHeight B e s : ℤ) + tailBCarry B e s) =
        (routingA B e : ℤ) *
          (physicalHeight B e (s + routingB B e) + (routingData B e).u s) := by
    linear_combination hraw - hl0 + hl1 - htail
  have hcast :
      (physicalHeight B e s : ℤ) + tailBCarry B e s =
        physicalHeight B e (s + routingB B e) + (routingData B e).u s :=
    mul_left_cancel₀ (ne_of_gt ha) hprod
  exact_mod_cast hcast

/-- Exact raw/tail dictionary in the `c` direction, again globally valid. -/
theorem physicalHeight_step_c_with_tailCarry
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (s : ZMod (routingA B e)) :
    physicalHeight B e s + tailCCarry B e s =
      physicalHeight B e (s + routingC B e) + (routingData B e).v s := by
  letI : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  have hl0 := physicalHeight_spec B e s
  have hl1 := physicalHeight_spec B e (s + routingC B e)
  have hraw := (routingI B e).apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) s
  have htail := (routingH B e).asRelativeIdeal.apery_step_eq
    (routingA B e) (routingC B e) (routingHC B e) s
  change (routingI B e).aperyRepresentative (routingA B e) s =
    physicalAlpha B e s + (routingA B e : ℤ) * physicalHeight B e s at hl0
  change (routingI B e).aperyRepresentative (routingA B e)
      (s + routingC B e) =
    physicalAlpha B e (s + routingC B e) +
      (routingA B e : ℤ) * physicalHeight B e (s + routingC B e) at hl1
  change physicalAlpha B e s + routingC B e =
    physicalAlpha B e (s + routingC B e) +
      (routingA B e : ℤ) * tailCCarry B e s at htail
  change (routingI B e).aperyRepresentative (routingA B e) s + routingC B e =
    (routingI B e).aperyRepresentative (routingA B e)
      (s + routingC B e) +
      (routingA B e : ℤ) * (routingData B e).v s at hraw
  have ha : (0 : ℤ) < routingA B e := by exact_mod_cast routingA_pos B e
  have hprod :
      (routingA B e : ℤ) *
          ((physicalHeight B e s : ℤ) + tailCCarry B e s) =
        (routingA B e : ℤ) *
          (physicalHeight B e (s + routingC B e) + (routingData B e).v s) := by
    linear_combination hraw - hl0 + hl1 - htail
  have hcast :
      (physicalHeight B e s : ℤ) + tailCCarry B e s =
        physicalHeight B e (s + routingC B e) + (routingData B e).v s :=
    mul_left_cancel₀ (ne_of_gt ha) hprod
  exact_mod_cast hcast

/-- The physical cut height at every coherent grid point is capped by the
origin height `H0`.  This is the monotonicity argument used by the repaired
positive-seed bound and does not assume any branch classification. -/
theorem eta_le_H0 (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (i j : ℕ) : L5A2C4C.eta B e i j ≤ L5A2C4C.H0 B e := by
  have hi := L5A2C4C.eta_antitone_left B e 0 j i
  have hj := L5A2C4C.eta_antitone_right B e 0 0 j
  have hi' : L5A2C4C.eta B e i j ≤ L5A2C4C.eta B e 0 j := by
    simpa using hi
  have hj' : L5A2C4C.eta B e 0 j ≤ L5A2C4C.eta B e 0 0 := by
    simpa using hj
  simpa [L5A2C4C.H0] using le_trans hi' hj'

/-- On the coherent Herzog domain the actual physical height is bounded by
`H0`; no global `eta = physicalHeight` rewrite is used. -/
theorem physicalHeight_le_H0_on_herzogDomain
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e) {i j : ℕ}
    (hij : L5A2C4OR5.HerzogLShapeDomain HD i j) :
    physicalHeight B e (gridResidue B e i j) ≤ L5A2C4C.H0 B e := by
  rw [← L5A2C4OR6.eta_eq_physicalHeight_on_herzogDomain B e HD hij]
  exact eta_le_H0 B e i j

/-- The eight boundary-inclusive locations of a canonical Herzog cell. -/
inductive CanonicalLocation where
  | ordinary
  | center
  | upperArmInterior
  | upperRight
  | bottomTop
  | bottomNotchInterior
  | kappa1
  | kappa2
  deriving DecidableEq

/-- Exact conditions of the repaired eight-case atlas.  The inequalities are
written without truncated predecessor notation, so empty boundary classes
remain genuinely empty when a coefficient is one. -/
def CanonicalLocation.Holds
    {B : ChosenBase.Data Gamma} {e : Fin 3 ≃ Fin 3}
    (HD : L5A2C4D.CoherentHerzogData B e)
    (k : CanonicalLocation) (i j : ℕ) : Prop :=
  match k with
  | .ordinary => L5A2C4OR5.HerzogLShapeDomain HD (i + 1) (j + 1)
  | .center => i + 1 = L5A2C4D.cr12 HD ∧ j + 1 = L5A2C4D.cr13 HD
  | .upperArmInterior =>
      i + 1 = L5A2C4D.cr12 HD ∧ L5A2C4D.cr13 HD ≤ j ∧
        j + 1 < L5A2C4A.c3 B e
  | .upperRight =>
      i + 1 = L5A2C4A.c2 B e ∧ j + 1 < L5A2C4D.cr13 HD
  | .bottomTop =>
      j + 1 = L5A2C4A.c3 B e ∧ i + 1 < L5A2C4D.cr12 HD
  | .bottomNotchInterior =>
      j + 1 = L5A2C4D.cr13 HD ∧ L5A2C4D.cr12 HD ≤ i ∧
        i + 1 < L5A2C4A.c2 B e
  | .kappa1 =>
      i + 1 = L5A2C4A.c2 B e ∧ j + 1 = L5A2C4D.cr13 HD
  | .kappa2 =>
      i + 1 = L5A2C4D.cr12 HD ∧ j + 1 = L5A2C4A.c3 B e

/-- Every canonical Herzog cell lies in one of the repaired eight cases. -/
theorem canonicalLocation_exists
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e) {i j : ℕ}
    (hij : L5A2C4OR5.HerzogLShapeDomain HD i j) :
    ∃ k, CanonicalLocation.Holds HD k i j := by
  have hp := L5A2C4D.coherent_coefficients_positive B e HD
  have hs := L5A2C4D.coherent_coefficients B e HD
  unfold L5A2C4OR5.HerzogLShapeDomain at hij
  rcases hij with ⟨hi, hj, hnotch⟩
  rcases hnotch with hip | hjq
  · by_cases hi1 : i + 1 < L5A2C4A.c2 B e
    · by_cases hj1 : j + 1 < L5A2C4A.c3 B e
      · by_cases hd : i + 1 < L5A2C4D.cr12 HD ∨
          j + 1 < L5A2C4D.cr13 HD
        · exact ⟨.ordinary, hi1, hj1, hd⟩
        · by_cases hic : i + 1 = L5A2C4D.cr12 HD
          · by_cases hjc : j + 1 = L5A2C4D.cr13 HD
            · exact ⟨.center, hic, hjc⟩
            · exact ⟨.upperArmInterior, hic, by omega, hj1⟩
          · exact ⟨.bottomNotchInterior, by omega, by omega, hi1⟩
      · by_cases hic : i + 1 = L5A2C4D.cr12 HD
        · exact ⟨.kappa2, hic, by omega⟩
        · exact ⟨.bottomTop, by omega, by omega⟩
    · by_cases hjc : j + 1 = L5A2C4D.cr13 HD
      · exact ⟨.kappa1, by omega, hjc⟩
      · exact ⟨.upperRight, by omega, by omega⟩
  · by_cases hi1 : i + 1 < L5A2C4A.c2 B e
    · by_cases hj1 : j + 1 < L5A2C4A.c3 B e
      · by_cases hd : i + 1 < L5A2C4D.cr12 HD ∨
          j + 1 < L5A2C4D.cr13 HD
        · exact ⟨.ordinary, hi1, hj1, hd⟩
        · by_cases hic : i + 1 = L5A2C4D.cr12 HD
          · by_cases hjc : j + 1 = L5A2C4D.cr13 HD
            · exact ⟨.center, hic, hjc⟩
            · exact ⟨.upperArmInterior, hic, by omega, hj1⟩
          · exact ⟨.bottomNotchInterior, by omega, by omega, hi1⟩
      · by_cases hic : i + 1 = L5A2C4D.cr12 HD
        · exact ⟨.kappa2, hic, by omega⟩
        · exact ⟨.bottomTop, by omega, by omega⟩
    · by_cases hjc : j + 1 = L5A2C4D.cr13 HD
      · exact ⟨.kappa1, by omega, hjc⟩
      · exact ⟨.upperRight, by omega, by omega⟩

/-- The repaired eight cases are pairwise disjoint. -/
theorem canonicalLocation_unique
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e) {i j : ℕ}
    (hij : L5A2C4OR5.HerzogLShapeDomain HD i j)
    {k l : CanonicalLocation}
    (hk : CanonicalLocation.Holds HD k i j)
    (hl : CanonicalLocation.Holds HD l i j) : k = l := by
  have hp := L5A2C4D.coherent_coefficients_positive B e HD
  have hs := L5A2C4D.coherent_coefficients B e HD
  rcases hp with ⟨hp12, hp13, hp21, hp23, hp31, hp32⟩
  rcases hs with ⟨hc1, hc2, hc3⟩
  have hp_lt_c2 : L5A2C4D.cr12 HD < L5A2C4A.c2 B e := by omega
  have hq_lt_c3 : L5A2C4D.cr13 HD < L5A2C4A.c3 B e := by omega
  cases k <;> cases l <;>
    simp only [CanonicalLocation.Holds] at hk hl <;>
    simp only [L5A2C4OR5.HerzogLShapeDomain] at hij hk hl <;>
    simp <;> omega

/-- Unique boundary-inclusive classification of every canonical cell. -/
theorem canonicalLocation_existsUnique
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e) {i j : ℕ}
    (hij : L5A2C4OR5.HerzogLShapeDomain HD i j) :
    ∃! k, CanonicalLocation.Holds HD k i j := by
  obtain ⟨k, hk⟩ := canonicalLocation_exists B e HD hij
  exact ⟨k, hk, fun l hl => canonicalLocation_unique B e HD hij hl hk⟩

/-- A source-hit dictionary whose distinguished residue is explicitly the
branch seed.  Its diagonal target remains `branchDiagonalTarget B e seed` and
is not silently substituted for `seed`. -/
def ActualSourceHitSeedDictionary
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e)
    (seed : ZMod (routingA B e)) : Prop :=
  ∃ i j k,
    L5A2C4OR5.HerzogLShapeDomain HD i j ∧
    gridResidue B e i j = seed ∧
    CanonicalLocation.Holds HD k i j ∧
    (∀ l, CanonicalLocation.Holds HD l i j → l = k) ∧
    (routingData B e).u ((routingData B e).c seed) =
      L5A2C4OR11.coherentCMLocalCarry B e i j ∧
    0 < (routingData B e).u ((routingData B e).c seed) ∧
    (routingData B e).u ((routingData B e).c seed) =
      (routingData B e).v ((routingData B e).b seed)

/-- Corrected actual local-square dictionary: R9's state is first localized
and classified as the seed, and the incoming positive cross is identified at
that same seed.  No target-side interiority is present. -/
theorem actual_sourceHit_cm_shz_local_square_dictionary
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit (routingData B e) incoming target.raw) :
    ActualSourceHitSeedDictionary B e HD
      (L5A2C4OR9.actualSourceHitState B e incoming target hit) := by
  obtain ⟨i, j, hij, hres, hw, hwpos, hopp, _hseam, _hcorr⟩ :=
    L5A2C4OR11.actual_sourceHit_raw_eta_gridLift_dictionary
      B e HD incoming target hit
  obtain ⟨k, hk, huniq⟩ := canonicalLocation_existsUnique B e HD hij
  refine ⟨i, j, k, hij, hres, hk, ?_, hw, hwpos, hopp⟩
  intro l hl
  exact huniq l hl

/-- Canonical-coordinate form of the global `b` raw/tail dictionary. -/
theorem raw_tail_b_dictionary_of_canonical_coordinates
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e)
    {i j i' j' : ℕ}
    (hij : L5A2C4OR5.HerzogLShapeDomain HD i j)
    (hnext : L5A2C4OR5.HerzogLShapeDomain HD i' j')
    (hres : gridResidue B e i' j' =
      gridResidue B e i j + routingB B e) :
    L5A2C4C.eta B e i j + tailBCarry B e (gridResidue B e i j) =
      L5A2C4C.eta B e i' j' + (routingData B e).u (gridResidue B e i j) := by
  have h := physicalHeight_step_b_with_tailCarry B e (gridResidue B e i j)
  rw [← hres] at h
  rw [← L5A2C4OR6.eta_eq_physicalHeight_on_herzogDomain B e HD hij,
    ← L5A2C4OR6.eta_eq_physicalHeight_on_herzogDomain B e HD hnext] at h
  exact h

/-- Canonical-coordinate form of the global `c` raw/tail dictionary. -/
theorem raw_tail_c_dictionary_of_canonical_coordinates
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e)
    {i j i' j' : ℕ}
    (hij : L5A2C4OR5.HerzogLShapeDomain HD i j)
    (hnext : L5A2C4OR5.HerzogLShapeDomain HD i' j')
    (hres : gridResidue B e i' j' =
      gridResidue B e i j + routingC B e) :
    L5A2C4C.eta B e i j + tailCCarry B e (gridResidue B e i j) =
      L5A2C4C.eta B e i' j' + (routingData B e).v (gridResidue B e i j) := by
  have h := physicalHeight_step_c_with_tailCarry B e (gridResidue B e i j)
  rw [← hres] at h
  rw [← L5A2C4OR6.eta_eq_physicalHeight_on_herzogDomain B e HD hij,
    ← L5A2C4OR6.eta_eq_physicalHeight_on_herzogDomain B e HD hnext] at h
  exact h

/-- The diagonal target of a branch seed is a separate object. -/
def branchDiagonalTarget (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ZMod (routingA B e)) : ZMod (routingA B e) :=
  (routingData B e).b ((routingData B e).c r)

/-- The MAX-MIN shadow of a branch seed is also a separate object. -/
def branchShadow (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (r : ZMod (routingA B e)) : ZMod (routingA B e) :=
  r - (routingM B e : ℕ)

/-- Actual R9 source-hit state is the source-target branch seed.  This adapter
records the definition-level fact and exports the separately defined diagonal
target without identifying them. -/
theorem actual_sourceHit_is_branch_seed
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit (routingData B e) incoming target.raw) :
    let D := routingData B e
    let r := L5A2C4OR9.actualSourceHitState B e incoming target hit
    D.IsBranch r ∧ D.u r = 0 ∧ D.v r = 0 ∧
      0 < D.u (D.c r) ∧ D.u (D.c r) = D.v (D.b r) ∧
      branchDiagonalTarget B e r = D.b (D.c r) := by
  dsimp only [branchDiagonalTarget]
  have h := L5A2C4OR10.actual_sourceHit_sourceTarget_cross B e incoming target hit
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2, h.2.2.2.1, rfl⟩

/-- Every actual source-hit seed has a unique coherent Herzog coordinate.
This theorem keeps the seed binder explicit; it does not relabel the diagonal
target as the R9 state. -/
theorem actual_sourceHit_seed_unique_lShape_coordinate
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : L5A2C4D.CoherentHerzogData B e)
    (incoming : L5A2C4K.ResidueData.RawHistory (routingData B e))
    (target : L5A2C4L.ResidueData.BSourceRootedHistory (routingData B e))
    (hit : L5A2C4K.ResidueData.SourceHit (routingData B e) incoming target.raw) :
    let r := L5A2C4OR9.actualSourceHitState B e incoming target hit
    ∃! x : GenericLShape.Index (L5A2C4D.cr12 HD) (L5A2C4D.cr13 HD)
        (L5A2C4D.cr32 HD) (L5A2C4D.cr23 HD),
      GenericLShape.residue (routingA B e) (routingB B e) (routingC B e)
        (L5A2C4D.cr12 HD) (L5A2C4D.cr13 HD)
        (L5A2C4D.cr32 HD) (L5A2C4D.cr23 HD) x = r :=
  L5A2C4OR10.actual_sourceHit_unique_lShape_index B e HD incoming target hit

end NS25Lean.L5A2C4OR13
