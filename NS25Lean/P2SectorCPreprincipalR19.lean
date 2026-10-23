import NS25Lean.P2SectorCFirstPrincipalR19

set_option linter.style.header false
noncomputable section

namespace NS25Lean.L5A2C4OR19

open FourGeneratedBridge L5A2C4A L5A2C4C L5A2C4D L5A2C4H
  L5A2C4OR1 L5A2C4OR3 L5A2C4OR4 L5A2C4OR5 L5A2C4OR6

variable {Gamma : NumericalSemigroup}

private theorem routingA_mem_H (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3) :
    routingA B e ∈ routingH B e := by
  change routingA B e ∈ generatedThree (routingA B e) (routingB B e) (routingC B e)
  exact AddSubmonoid.subset_closure (by simp)

private theorem routingGrid_mem_H (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (n i j : ℕ) :
    normalizedGrid B e n i j ∈ routingH B e := by
  have hn := (routingH B e).toAddSubmonoid.nsmul_mem (routingA_mem_H B e) n
  have hi := (routingH B e).toAddSubmonoid.nsmul_mem (routingHB B e) i
  have hj := (routingH B e).toAddSubmonoid.nsmul_mem (routingHC B e) j
  simpa [normalizedGrid, nsmul_eq_mul, Nat.add_assoc] using
    (routingH B e).toAddSubmonoid.add_mem
      ((routingH B e).toAddSubmonoid.add_mem hn hi) hj

private theorem canonical_coordinate_of_nat (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) (HD : CoherentHerzogData B e) (x : ℕ) :
    ∃ i j : ℕ, HerzogLShapeDomain HD i j ∧
      Int.ModEq (routingA B e) (normalizedGrid B e 0 i j) x := by
  obtain ⟨ij, ⟨hL, hmod⟩, _⟩ := coherent_lShape_unique_coordinate B e HD x
  rcases hL with ⟨hi0, hj0, hi, hj, hcorner⟩
  have hsi : (ij.1.toNat : ℤ) = ij.1 := Int.toNat_of_nonneg hi0
  have hsj : (ij.2.toNat : ℤ) = ij.2 := Int.toNat_of_nonneg hj0
  have hs := coherent_coefficients B e HD
  refine ⟨ij.1.toNat, ij.2.toNat, ?_, ?_⟩
  · unfold HerzogLShapeDomain
    refine ⟨?_, ?_, ?_⟩
    · have hi' : (ij.1.toNat : ℤ) < c2 B e := by
        rw [hsi, hs.2.1]
        exact_mod_cast hi
      exact_mod_cast hi'
    · have hj' : (ij.2.toNat : ℤ) < c3 B e := by
        rw [hsj, hs.2.2]
        exact_mod_cast hj
      exact_mod_cast hj'
    · rcases hcorner with hc | hc
      · exact Or.inl (by exact_mod_cast (hsi ▸ hc))
      · exact Or.inr (by exact_mod_cast (hsj ▸ hc))
  · simpa [normalizedGrid, hsi, hsj] using hmod

/-- Every preprincipal index has a canonical L-coordinate and a strictly
positive integral negative a-height. -/
theorem preprincipal_canonical_negative_height
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n : ℕ} (hn : 0 < n)
    (hpre : n < firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e)) :
    ∃ i j d : ℕ, HerzogLShapeDomain HD i j ∧ 0 < d ∧
      n * routingM B e + d * routingA B e =
        i * routingB B e + j * routingC B e := by
  let : NeZero (routingA B e) := ⟨Nat.ne_of_gt (routingA_pos B e)⟩
  obtain ⟨i, j, hdomain, hmod⟩ := canonical_coordinate_of_nat B e HD (n * routingM B e)
  let beta := normalizedGrid B e 0 i j
  have hcast : (beta : ZMod (routingA B e)) =
      ((n * routingM B e : ℕ) : ZMod (routingA B e)) := by
    exact_mod_cast (ZMod.intCast_eq_intCast_iff _ _ _).2 hmod
  have hnot : n * routingM B e ∉ routingH B e := by
    intro hmem
    have hle := firstPrincipal_le (routingH B e) (routingM B e)
      (routingM_pos B e) hn hmem
    omega
  have hlt : n * routingM B e < beta := by
    by_contra hnotlt
    have hle : (beta : ℤ) ≤ n * routingM B e := by
      exact_mod_cast (show beta ≤ n * routingM B e by omega)
    obtain ⟨k, hk⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
      (routingA B e) hle (by exact_mod_cast hcast.symm)
    have heq : n * routingM B e = beta + routingA B e * k := by exact_mod_cast hk
    apply hnot
    rw [heq]
    exact (routingH B e).toAddSubmonoid.add_mem (routingGrid_mem_H B e 0 i j)
      (by simpa [nsmul_eq_mul, Nat.mul_comm] using
        (routingH B e).toAddSubmonoid.nsmul_mem (routingA_mem_H B e) k)
  have hle' : ((n * routingM B e : ℕ) : ℤ) ≤ (beta : ℤ) := by
    exact_mod_cast Nat.le_of_lt hlt
  obtain ⟨d, hd⟩ := RelativeIdeal.exists_eq_add_mul_of_le_of_modEq
    (routingA B e) hle' (by exact_mod_cast hcast)
  have hdn : beta = n * routingM B e + routingA B e * d := by exact_mod_cast hd
  have hdpos : 0 < d := by
    by_contra h
    have : d = 0 := by omega
    simp [this] at hdn
    omega
  refine ⟨i, j, d, hdomain, hdpos, ?_⟩
  simpa [beta, normalizedGrid, Nat.mul_comm, Nat.add_comm] using hdn.symm

private theorem bottom_return_eta_zero (B : ChosenBase.Data Gamma)
    (e : Fin 3 ≃ Fin 3) {i j n d u v : ℕ} (hn : 0 < n)
    (heq : normalizedGrid B e 0 i j =
      n * routingM B e + normalizedGrid B e d u v) :
    eta B e i j = 0 := by
  have hcut : normalizedGrid B e 0 i j ∈ cyclicCut (routingH B e) (routingM B e) :=
    ⟨routingGrid_mem_H B e 0 i j, n, hn,
      normalizedGrid B e d u v, routingGrid_mem_H B e d u v, heq⟩
  have hI := (actual_cyclicCut_iff_routingI B e _).mp hcut
  have heta := (normalizedGrid_mem_iff_eta_le B e 0 i j).mp hI
  omega

/-- T2 depth and non-axis constraints, derived by actual positive returns at
the two opposite live tails. G2/G3 are permitted only in this abstract stage. -/
theorem preprincipal_positive_depth_bounds
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) {n i j d : ℕ}
    (hn : 0 < n) (hdom : HerzogLShapeDomain HD i j) (_hd : 0 < d)
    (heq : n * routingM B e + d * routingA B e =
      i * routingB B e + j * routingC B e)
    (hG2 : 0 < eta B e (c2 B e - 1) 0)
    (hG3 : 0 < eta B e 0 (c3 B e - 1)) :
    0 < i ∧ 0 < j ∧ (i < cr12 HD → d < cr31 HD) ∧
      (j < cr13 HD → d < cr21 HD) := by
  have hs := coherent_coefficients B e HD
  have hr := coherent_normalized_relations B e HD
  have hI := herzogC_positive B e 1
  have hJ := herzogC_positive B e 2
  have hiBound := hdom.1
  have hjBound := hdom.2.1
  have hipos : 0 < i := by
    by_contra hi
    have hi0 : i = 0 := by omega
    have hsum : c3 B e - 1 - j + j = c3 B e - 1 := by omega
    have hprod := congrArg (fun z => z * routingC B e) hsum
    simp only [Nat.add_mul] at hprod
    have hreturn : normalizedGrid B e 0 0 (c3 B e - 1) =
        n * routingM B e + normalizedGrid B e d 0 (c3 B e - 1 - j) := by
      simp only [normalizedGrid, zero_mul, zero_add, add_zero]
      rw [hi0] at heq
      simp only [zero_mul, zero_add] at heq
      omega
    have hz := bottom_return_eta_zero B e hn hreturn
    omega
  have hjpos : 0 < j := by
    by_contra hj
    have hj0 : j = 0 := by omega
    have hsum : c2 B e - 1 - i + i = c2 B e - 1 := by omega
    have hprod := congrArg (fun z => z * routingB B e) hsum
    simp only [Nat.add_mul] at hprod
    have hreturn : normalizedGrid B e 0 (c2 B e - 1) 0 =
        n * routingM B e + normalizedGrid B e d (c2 B e - 1 - i) 0 := by
      simp only [normalizedGrid, zero_mul, zero_add, add_zero]
      rw [hj0] at heq
      simp only [zero_mul, add_zero] at heq
      omega
    have hz := bottom_return_eta_zero B e hn hreturn
    omega
  refine ⟨hipos, hjpos, ?_, ?_⟩
  · intro hi
    by_contra hdepth
    have hsumD : d - cr31 HD + cr31 HD = d := by omega
    have hsumI : cr12 HD - 1 - i + i + 1 = cr12 HD := by omega
    have hsumJ : c3 B e - j + j = c3 B e := by omega
    have hprodD := congrArg (fun z => z * routingA B e) hsumD
    have hprodI := congrArg (fun z => z * routingB B e) hsumI
    have hprodJ := congrArg (fun z => z * routingC B e) hsumJ
    have hprodSum := congrArg (fun z => z * routingB B e) hs.2.1
    have hprodBottom := congrArg (fun z => z * routingB B e)
      (show c2 B e - 1 + 1 = c2 B e by omega)
    simp only [Nat.add_mul, one_mul] at hprodD hprodI hprodJ hprodSum hprodBottom
    have hreturn : normalizedGrid B e 0 (c2 B e - 1) 0 =
        n * routingM B e +
          normalizedGrid B e (d - cr31 HD) (cr12 HD - 1 - i) (c3 B e - j) := by
      simp only [normalizedGrid, zero_mul, zero_add, add_zero]
      nlinarith only [heq, hr.2.2, hprodD, hprodI, hprodJ, hprodSum, hprodBottom]
    have hz := bottom_return_eta_zero B e hn hreturn
    omega
  · intro hj
    by_contra hdepth
    have hsumD : d - cr21 HD + cr21 HD = d := by omega
    have hsumI : c2 B e - i + i = c2 B e := by omega
    have hsumJ : cr13 HD - 1 - j + j + 1 = cr13 HD := by omega
    have hprodD := congrArg (fun z => z * routingA B e) hsumD
    have hprodI := congrArg (fun z => z * routingB B e) hsumI
    have hprodJ := congrArg (fun z => z * routingC B e) hsumJ
    have hprodSum := congrArg (fun z => z * routingC B e) hs.2.2
    have hprodBottom := congrArg (fun z => z * routingC B e)
      (show c3 B e - 1 + 1 = c3 B e by omega)
    simp only [Nat.add_mul, one_mul] at hprodD hprodI hprodJ hprodSum hprodBottom
    have hreturn : normalizedGrid B e 0 0 (c3 B e - 1) =
        n * routingM B e +
          normalizedGrid B e (d - cr21 HD) (c2 B e - i) (cr13 HD - 1 - j) := by
      simp only [normalizedGrid, zero_mul, zero_add, add_zero]
      nlinarith only [heq, hr.2.1, hprodD, hprodI, hprodJ, hprodSum, hprodBottom]
    have hz := bottom_return_eta_zero B e hn hreturn
    omega

/-- T2 complete three-case preprincipal classification. There is no axis or
fourth chamber and no numerical search filter. -/
theorem preprincipal_inner_top_right
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) (hGate : MixedGateConditions B e HD)
    {n : ℕ} (hn : 0 < n)
    (hpre : n < firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e)) :
    ∃ i j d : ℕ, HerzogLShapeDomain HD i j ∧ 0 < d ∧
      n * routingM B e + d * routingA B e =
        i * routingB B e + j * routingC B e ∧
      ((0 < i ∧ i < cr12 HD ∧ 0 < j ∧ j < cr13 HD ∧
          d < cr21 HD ∧ d < cr31 HD) ∨
       (0 < i ∧ i < cr12 HD ∧ cr13 HD ≤ j ∧ j < c3 B e ∧ d < cr31 HD) ∨
       (cr12 HD ≤ i ∧ i < c2 B e ∧ 0 < j ∧ j < cr13 HD ∧ d < cr21 HD)) := by
  obtain ⟨i, j, d, hdom, hd, heq⟩ := preprincipal_canonical_negative_height B e HD hn hpre
  obtain ⟨hi0, hj0, hleft, hright⟩ := preprincipal_positive_depth_bounds
    B e HD hn hdom hd heq hGate.2.2.1 hGate.2.2.2.1
  refine ⟨i, j, d, hdom, hd, heq, ?_⟩
  by_cases hi : i < cr12 HD
  · by_cases hj : j < cr13 HD
    · exact Or.inl ⟨hi0, hi, hj0, hj, hright hj, hleft hi⟩
    · exact Or.inr (Or.inl ⟨hi0, hi, by omega, hdom.2.1, hleft hi⟩)
  · have hj : j < cr13 HD := hdom.2.2.resolve_left hi
    exact Or.inr (Or.inr ⟨by omega, hdom.1, hj0, hj, hright hj⟩)

/-- The canonical principal monomial uses actual nonnegative coordinates.
It is not selected by searching possible exponents. -/
theorem firstPrincipal_canonical_form
    (B : ChosenBase.Data Gamma) (e : Fin 3 ≃ Fin 3)
    (HD : CoherentHerzogData B e) :
    ∃ delta U V : ℕ, HerzogLShapeDomain HD U V ∧
      firstPrincipal (routingH B e) (routingM B e) (routingM_pos B e) * routingM B e =
        normalizedGrid B e delta U V := by
  obtain ⟨x, y, z, hfac⟩ := routingH_factorization B e
    (firstPrincipal_spec (routingH B e) (routingM B e) (routingM_pos B e)).2
  obtain ⟨U, V, k, hdom, hred⟩ := coherent_exists_reduction B e HD y z
  refine ⟨x + k, U, V, hdom, ?_⟩
  simp only [normalizedGrid, Nat.add_mul]
  nlinarith only [hfac, hred]

/-- Actual mixed surviving-notch T2 adapter: no free numerical gate premise.
All five gates are derived from this packet's actual role provenance. -/
theorem actual_mixed_notch_preprincipal {P : L5A1.P2Data Gamma}
    (R : ActualRolePacket P)
    (hMixed : L5A2C3G.MixedOrientation R.G R.boundaryPure R.boundaryMixed)
    (hNotch : L5A2C4G.SurvivingNotch P.M.base R.e R.HD)
    {n : ℕ} (hn : 0 < n)
    (hpre : n < firstPrincipal (routingH P.M.base R.e) (routingM P.M.base R.e)
      (routingM_pos P.M.base R.e)) :
    ∃ i j d : ℕ, HerzogLShapeDomain R.HD i j ∧ 0 < d ∧
      n * routingM P.M.base R.e + d * routingA P.M.base R.e =
        i * routingB P.M.base R.e + j * routingC P.M.base R.e ∧
      ((0 < i ∧ i < cr12 R.HD ∧ 0 < j ∧ j < cr13 R.HD ∧
          d < cr21 R.HD ∧ d < cr31 R.HD) ∨
       (0 < i ∧ i < cr12 R.HD ∧ cr13 R.HD ≤ j ∧ j < c3 P.M.base R.e ∧ d < cr31 R.HD) ∨
       (cr12 R.HD ≤ i ∧ i < c2 P.M.base R.e ∧ 0 < j ∧ j < cr13 R.HD ∧ d < cr21 R.HD)) :=
  preprincipal_inner_top_right P.M.base R.e R.HD
    (normalized_mixed_notch_G0_G4 R hMixed hNotch) hn hpre

end NS25Lean.L5A2C4OR19
